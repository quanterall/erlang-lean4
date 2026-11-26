%% Hands checks to free workers; callers wait in a queue when all are busy. Workers announce themselves when their
%% base environment is ready and are forgotten when they go down.
-module(lean_check_pool).
-behaviour(gen_server).
-export([start_link/0, ready/1, checkout/1, checkin/1, status/0, record/2]).
-export([init/1, handle_call/3, handle_cast/2, handle_info/2]).

start_link() -> gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

ready(Worker) -> gen_server:cast(?MODULE, {ready, Worker}).
%% a free worker, or {error, no_worker} after Timeout ms
checkout(Timeout) ->
    try gen_server:call(?MODULE, checkout, Timeout)
    catch exit:{timeout, _} -> gen_server:cast(?MODULE, {cancel, self()}), {error, no_worker}
    end.
checkin(Worker) -> gen_server:cast(?MODULE, {checkin, Worker}).
%% a finished check: its status and time (for status/0)
record(Status, Ms) -> gen_server:cast(?MODULE, {record, Status, Ms}).
status() -> gen_server:call(?MODULE, status).

init([]) -> {ok, #{free => [], busy => #{}, waiting => queue:new(), known => #{},
                   counts => #{}, times => [], readies => 0, loaded_at => undefined}}.

-define(KEEP_TIMES, 1000).

handle_call(checkout, From, #{free := [W | Rest], busy := B} = S) ->
    {reply, {ok, W}, S#{free := Rest, busy := B#{W => From}}};
handle_call(checkout, From, #{waiting := Q} = S) ->
    {noreply, S#{waiting := queue:in(From, Q)}};
handle_call(status, _From, #{free := F, busy := B, waiting := Q, known := K, counts := C, times := Ts,
                             readies := Rd, loaded_at := At} = S) ->
    Sorted = lists:sort(Ts),
    N = length(Sorted),
    Stats = #{checks => lists:sum(maps:values(C)), valid => maps:get(valid, C, 0), invalid => maps:get(invalid, C, 0),
              timeout => maps:get(timeout, C, 0), unavailable => maps:get(unavailable, C, 0),
              mean_ms => case N of 0 -> 0; _ -> lists:sum(Sorted) div N end,
              p95_ms => case N of 0 -> 0; _ -> lists:nth(max(1, (95 * N + 99) div 100), Sorted) end,
              worker_restarts => max(0, Rd - application:get_env(lean_check, workers, 1)),
              since_loaded_ms => case At of undefined -> undefined; _ -> erlang:monotonic_time(millisecond) - At end},
    {reply, maps:merge(#{workers => maps:size(K), free => length(F), busy => maps:size(B), waiting => queue:len(Q)}, Stats), S}.

handle_cast({ready, W}, #{known := K, readies := Rd} = S) ->
    K2 = case maps:is_key(W, K) of true -> K; false -> K#{W => erlang:monitor(process, W)} end,
    {noreply, give(W, S#{known := K2, readies := Rd + 1, loaded_at := erlang:monotonic_time(millisecond)})};
handle_cast({record, St, Ms}, #{counts := C, times := Ts} = S) ->
    {noreply, S#{counts := C#{St => maps:get(St, C, 0) + 1}, times := lists:sublist([Ms | Ts], ?KEEP_TIMES)}};
handle_cast({checkin, W}, #{busy := B} = S) ->
    case maps:is_key(W, B) of
        true -> {noreply, give(W, S#{busy := maps:remove(W, B)})};
        false -> {noreply, S}
    end;
handle_cast({cancel, Pid}, #{waiting := Q} = S) ->
    {noreply, S#{waiting := queue:filter(fun({P, _}) -> P =/= Pid end, Q)}}.

handle_info({'DOWN', _, process, W, _}, #{free := F, busy := B, known := K} = S) ->
    {noreply, S#{free := F -- [W], busy := maps:remove(W, B), known := maps:remove(W, K)}};
handle_info(_, S) -> {noreply, S}.

%% a worker becomes free: to the first waiting caller, else to the free list
give(W, #{waiting := Q, busy := B, free := F} = S) ->
    case queue:out(Q) of
        {{value, From}, Q2} -> gen_server:reply(From, {ok, W}), S#{waiting := Q2, busy := B#{W => From}};
        {empty, _} -> S#{free := [W | F -- [W]]}
    end.

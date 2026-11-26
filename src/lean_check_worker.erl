%% One Lean REPL (leanprover-community/repl) behind a port. At start it runs the header (import Mathlib) and keeps
%% the resulting environment as the base: every check runs in a fresh child of it, so checks never see each other.
%%
%% The REPL is started directly (not through `lake env`) with the LEAN_PATH Lake computes once, so the port's OS
%% process is the REPL itself and a timeout can kill it. Protocol: a JSON command per request, ended by a blank
%% line; the response is one JSON object, ended by a blank line.
-module(lean_check_worker).
-behaviour(gen_server).
-export([start_link/1, run/4]).
-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2]).

start_link(I) -> gen_server:start_link(?MODULE, I, []).

%% run Source in a child of the base environment, then #print axioms for each of Names:
%%   {ok, #{messages => [..], sorries => N, sorry_goals => [..], tactics => [..],
%%          axioms => #{Name => {[Axiom] | missing, Statement | none}},
%%          elapsed_ms => T}}
%% | {error, timeout} (the REPL is killed and this worker exits; the supervisor starts a fresh one)
%% | {error, {crashed, Why}}
run(Worker, Source, Names, Timeout) ->
    try gen_server:call(Worker, {run, Source, Names, Timeout}, Timeout + 5000)
    catch exit:{timeout, _} -> {error, timeout};
          exit:{Why, _} -> {error, {crashed, Why}}
    end.

init(I) ->
    process_flag(trap_exit, true),
    Env = application:get_env(lean_check, env_dir, "/env"),
    Repl = application:get_env(lean_check, repl, "/repl/.lake/build/bin/repl"),
    Header = application:get_env(lean_check, header, "import LeanCheckEnv"),
    StartTimeout = application:get_env(lean_check, start_timeout, 900000),
    MaxChecks = application:get_env(lean_check, max_checks, 100),
    LeanPath = string:trim(os:cmd("cd " ++ Env ++ " && lake env printenv LEAN_PATH")),
    Port = open_port({spawn_executable, Repl},
                     [{cd, Env}, {env, [{"LEAN_PATH", LeanPath}]}, binary, stream, use_stdio, exit_status]),
    S0 = #{id => I, port => Port, buf => <<>>, base => undefined, checks => 0, max_checks => MaxChecks},
    case request(S0, #{cmd => list_to_binary(Header)}, StartTimeout) of
        {ok, #{<<"env">> := Base} = R, S1} ->
            case errors(R) of
                [] -> lean_check_pool:ready(self()), {ok, S1#{base := Base}};
                Errs -> {stop, {header_failed, Errs}}
            end;
        {error, Why, _} -> {stop, {start_failed, Why}}
    end.

handle_call({run, Source, Names, Timeout}, _From, #{base := Base, checks := C, max_checks := Max} = S) ->
    T0 = erlang:monotonic_time(millisecond),
    Deadline = T0 + Timeout,
    % allTactics: every tactic with the goals before it, for the verdict's open goals
    case request(S, #{cmd => Source, env => Base, allTactics => true}, Timeout) of
        {ok, R, S1} ->
            Env = maps:get(<<"env">>, R, undefined),
            {Axioms, S2} = axioms(Names, Env, Deadline, S1),
            case Axioms of
                timeout -> kill(S2), {stop, normal, {error, timeout}, S2};
                _ ->
                    Out = #{messages => maps:get(<<"messages">>, R, []),
                            sorries => length(maps:get(<<"sorries">>, R, [])),
                            sorry_goals => maps:get(<<"sorries">>, R, []),
                            tactics => maps:get(<<"tactics">>, R, []),
                            axioms => Axioms,
                            elapsed_ms => erlang:monotonic_time(millisecond) - T0},
                    case C + 1 >= Max of
                        true -> kill(S2), {stop, normal, {ok, Out}, S2};     % a fresh REPL next time
                        false -> {reply, {ok, Out}, S2#{checks := C + 1}}
                    end
            end;
        {error, timeout, S1} -> kill(S1), {stop, normal, {error, timeout}, S1};
        {error, Why, S1} -> {stop, normal, {error, {crashed, Why}}, S1}
    end.

handle_cast(_, S) -> {noreply, S}.

handle_info({Port, {exit_status, St}}, #{port := Port} = S) -> {stop, {repl_exited, St}, S};
handle_info(_, S) -> {noreply, S}.

terminate(_, S) -> kill(S), ok.

%% #print axioms Name in the check's environment, for each name: the axioms, or missing when the name is unknown
axioms(_, undefined, _, S) -> {#{}, S};
axioms(Names, Env, Deadline, S) ->
    lists:foldl(fun(_, {timeout, Sx}) -> {timeout, Sx};
                   (Name, {Acc, Sx}) ->
                        Left = Deadline - erlang:monotonic_time(millisecond),
                        case Left > 0 andalso request(Sx, #{cmd => <<"#print axioms ", Name/binary>>, env => Env}, Left) of
                            {ok, R, Sy} ->
                                % the statement as Lean elaborated it (R4): #check @Name prints "@Name : Type"
                                Left2 = Deadline - erlang:monotonic_time(millisecond),
                                case Left2 > 0 andalso request(Sy, #{cmd => <<"#check @", Name/binary>>, env => Env}, Left2) of
                                    {ok, R2, Sz} -> {Acc#{Name => {parse_axioms(Name, R), parse_check(R2)}}, Sz};
                                    _ -> {timeout, Sy}
                                end;
                            _ -> {timeout, Sx}
                        end
                end, {#{}, S}, Names).

parse_axioms(_Name, R) ->
    Texts = [D || #{<<"data">> := D} <- maps:get(<<"messages">>, R, [])],
    case errors(R) of
        [_ | _] -> missing;
        [] ->
            case [T || T <- Texts, binary:match(T, <<"depends on axioms">>) =/= nomatch] of
                [T | _] ->
                    [_, List] = binary:split(T, <<"[">>),
                    [Inner | _] = binary:split(List, <<"]">>),
                    [string:trim(A) || A <- binary:split(Inner, <<",">>, [global]), string:trim(A) =/= <<>>];
                [] ->
                    case [T || T <- Texts, binary:match(T, <<"does not depend on any axioms">>) =/= nomatch] of
                        [_ | _] -> [];
                        [] -> missing
                    end
            end
    end.

errors(R) -> [M || #{<<"severity">> := <<"error">>} = M <- maps:get(<<"messages">>, R, [])].

%% "@Name : T" -> T (none when the name is unknown)
parse_check(R) ->
    case [D || #{<<"severity">> := <<"info">>, <<"data">> := D} <- maps:get(<<"messages">>, R, [])] of
        [D | _] ->
            case binary:split(D, <<" : ">>) of
                [_, T] -> T;
                _ -> none
            end;
        [] -> none
    end.

%% one JSON request, its JSON response
request(#{port := Port} = S, Cmd, Timeout) ->
    port_command(Port, [json:encode(Cmd), "\n\n"]),
    Deadline = erlang:monotonic_time(millisecond) + Timeout,
    receive_response(S, Deadline).

receive_response(#{port := Port, buf := Buf} = S, Deadline) ->
    case take_object(Buf) of
        {ok, Obj, Rest} -> {ok, Obj, S#{buf := Rest}};
        more ->
            Left = Deadline - erlang:monotonic_time(millisecond),
            receive
                {Port, {data, D}} -> receive_response(S#{buf := <<Buf/binary, D/binary>>}, Deadline);
                {Port, {exit_status, St}} -> {error, {repl_exited, St}, S}
            after max(0, Left) -> {error, timeout, S}
            end
    end.

%% a complete JSON object at the front of the buffer, ended by a blank line (each blank line is tried in turn, in
%% case one falls inside the object)
take_object(Buf) -> take_object(Buf, 0).
take_object(Buf, From) ->
    case binary:match(Buf, <<"\n\n">>, [{scope, {From, byte_size(Buf) - From}}]) of
        nomatch -> more;
        {P, 2} ->
            <<Obj:P/binary, _:2/binary, Rest/binary>> = Buf,
            case string:trim(Obj) of
                <<>> -> take_object(Rest, 0);
                T ->
                    try {ok, json:decode(T), Rest}
                    catch _:_ -> take_object(Buf, P + 2)
                    end
            end
    end.

kill(#{port := Port}) ->
    case erlang:port_info(Port, os_pid) of
        {os_pid, Pid} -> os:cmd("kill -9 " ++ integer_to_list(Pid)), catch port_close(Port), ok;
        undefined -> ok
    end.

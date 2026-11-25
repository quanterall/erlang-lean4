%% The pool and its workers: workers register with the pool when they are ready and are restarted when they die
%% (a timeout kills the worker's REPL, so its gen_server exits and comes back with a fresh one).
-module(lean_check_sup).
-behaviour(supervisor).
-export([start_link/0, init/1]).

start_link() -> supervisor:start_link({local, ?MODULE}, ?MODULE, []).

init([]) ->
    N = application:get_env(lean_check, workers, 1),
    Pool = #{id => pool, start => {lean_check_pool, start_link, []}},
    Workers = [#{id => {worker, I}, start => {lean_check_worker, start_link, [I]}, restart => permanent,
                 shutdown => 5000} || I <- lists:seq(1, N)],
    {ok, {#{strategy => one_for_one, intensity => 20, period => 60}, [Pool | Workers]}}.

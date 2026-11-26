-module(lean_check_app).
-behaviour(application).
-export([start/2, stop/1]).

start(_Type, _Args) ->
    {ok, Sup} = lean_check_sup:start_link(),
    % the HTTP front (R6), when configured
    case application:get_env(lean_check, http) of
        {ok, #{port := _, token_file := _} = Conf} -> {ok, _} = lean_check_http:start(Conf);
        _ -> ok
    end,
    {ok, Sup}.
stop(_State) -> ok.

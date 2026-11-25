%% The screen in front of the workers, without Lean.
-module(lean_check_screen_tests).
-include_lib("eunit/include/eunit.hrl").

s(Src) -> lean_check_screen:screen(Src, #{}).

forbidden_test() ->
    [?assertMatch({error, {forbidden, _}}, s(Src)) || Src <- [
        <<"#eval IO.println \"x\"">>,
        <<"run_cmd do return ()">>,
        <<"elab \"foo\" : term => return default">>,
        <<"macro \"foo\" : term => `(1)">>,
        <<"syntax \"foo\" : term">>,
        <<"initialize IO.println \"x\"">>,
        <<"unsafe def f : Nat := 1">>,
        <<"@[implemented_by g] def f : Nat := 1">>,
        <<"@[extern \"c_fn\"] def f : Nat := 1">>,
        <<"import Mathlib.Data.Nat.Basic\ntheorem t : 1 = 1 := rfl">>,
        <<"theorem t : 2 ^ 10 = 1024 := by native_decide">>,
        <<"set_option trace.Meta.synthInstance true\ntheorem t : 1 = 1 := rfl">>,
        <<"#exit">>]].

allowed_test() ->
    ?assertEqual(ok, s(<<"theorem t (a b : Nat) : a + b = b + a := Nat.add_comm a b">>)),
    ?assertEqual(ok, s(<<"set_option maxHeartbeats 400000 in\ntheorem t : 1 = 1 := rfl">>)),
    ?assertEqual(ok, lean_check_screen:screen(<<"theorem t : 2 ^ 10 = 1024 := by native_decide">>, #{native_decide => true})),
    % forbidden words in comments and strings do not count; names containing them do not either
    ?assertEqual(ok, s(<<"-- #eval would run code\n/- unsafe /- nested -/ elab -/\ntheorem t : \"#eval\" = \"#eval\" := rfl">>)),
    ?assertEqual(ok, s(<<"theorem macro_free : 1 = 1 := rfl\ntheorem t2 : True := trivial">>)).

theorems_test() ->
    ?assertEqual([<<"a">>, <<"Foo.b">>, <<"Foo.Bar.c">>, <<"d">>],
                 lean_check_screen:theorems(<<"theorem a : True := trivial\nnamespace Foo\nlemma b : True := trivial\n"
                                              "namespace Bar\ntheorem c (x : Nat) : x = x := rfl\nend Bar\nend Foo\n"
                                              "-- theorem hidden : True := trivial\ntheorem d : True := trivial">>)).

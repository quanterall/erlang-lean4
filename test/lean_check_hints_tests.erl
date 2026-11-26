%% R3's hints and the HTTP front's JSON conversion, without Lean.
-module(lean_check_hints_tests).
-include_lib("eunit/include/eunit.hrl").

uses(Src) -> [U || #{use := U} <- lean_check_hints:hints(Src, [])].

hints_test() ->
    ?assertMatch([_], uses(<<"theorem t : ∑ i in Finset.range 3, i = 3 := by decide"/utf8>>)),
    ?assertMatch([_], uses(<<"theorem t : (λ x, x) 1 = 1 := rfl"/utf8>>)),
    ?assertMatch([_], uses(<<"theorem t : True :=\nbegin\n  trivial\nend">>)),
    ?assertMatch([_], uses(<<"example : nat.succ 0 = 1 := rfl">>)),
    ?assertMatch([_], uses(<<"theorem t (h : A ∧ B) : A := by\n  cases h with a b\n  exact a"/utf8>>)),
    ?assertEqual([], uses(<<"theorem t (n : ℕ) : ∑ i ∈ Finset.range n, i = ∑ i ∈ Finset.range n, i := rfl"/utf8>>)),
    [#{line := 4}] = lean_check_hints:hints(<<"-- x\n\ntheorem t : True := by\n  assume h\n  trivial"/utf8>>, []).

json_test() ->
    ?assertEqual(#{<<"status">> => <<"invalid">>, <<"reason">> => #{<<"missing_theorem">> => <<"t">>}},
                 lean_check_http:to_json(#{status => invalid, reason => {missing_theorem, <<"t">>}})),
    ?assertEqual([[<<"t">>, <<"sorryAx">>]], lean_check_http:to_json([{<<"t">>, <<"sorryAx">>}])),
    ?assertEqual(true, lean_check_http:to_json(true)).

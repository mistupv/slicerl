-module(temp_tt).

-export([main/0]).

main() -> case {} of {} -> main_0_CLAUSE() end.

main_0_CLAUSE() ->
    A = 3,
    W = {A, {1, 2}},
    transformed_call0(W),
    {Y, {Z1, Z2}} = W.

transformed_call0(VAR1) ->
    case {VAR1} of
      {VAR1} -> f(VAR1);
      _ -> error
    end.

f(VAR1) -> case {VAR1} of {_} -> f_0_CLAUSE(VAR1) end.

f_0_CLAUSE(_) -> 3.
-module(temp_tt).

-export([main/0]).

main() -> case {} of {} -> main_0_CLAUSE() end.

main_0_CLAUSE() -> X = 1, transformed_call0(X, 3).

transformed_call0(VAR1, VAR2) ->
    case {VAR1, VAR2} of
      {VAR1, VAR2} -> f(VAR1, VAR2);
      _ -> error
    end.

f(VAR1, VAR2) ->
    case {VAR1, VAR2} of
      {1, 2} -> f_0_CLAUSE(VAR1, VAR2)
    end.

f_0_CLAUSE(1, 2) -> 3.
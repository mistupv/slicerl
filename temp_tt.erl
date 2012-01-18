-module(temp_tt).

-export([main/0]).

main() -> case {} of _ -> main_0_CLAUSE() end.

main_0_CLAUSE() ->
    I = 1,
    Y = I,
    case Y of
      1 -> A = 0;
      _ -> A = 1
    end,
    transformed_call0(A, A).

transformed_call0(VAR1, VAR2) -> add(VAR1, VAR2).

add(VAR1, VAR2) ->
    case {VAR1, VAR2} of
      {A, 0} -> add_0_CLAUSE(VAR1, VAR2);
      _ -> add_1_CLAUSE(VAR1, VAR2)
    end.

add_0_CLAUSE(A, 0) -> A.

add_1_CLAUSE(A, B) -> A.
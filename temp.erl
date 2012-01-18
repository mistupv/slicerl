-module(temp).


-export([main/0]).

%main() -> X= {1,{1,2}},
%          {Y,Z} = X,
%          {Z1,Z2}=Z,
%          Z1+Z2.
          %{Y,Z}=X.
%f(3) -> 3.

%
main() ->%X= {1,2},
          %{Y,Z} = X,
          I = 1,
          Y=I,
          case Y of
          	%1 -> A=1;
          	1 -> A=0;
          	%_ -> A=0
          	_ -> A=1
          end,
          %A.
          add(A,A).
          %{Result,_}=while(Sum, I,11 ),
          %Result.

%while(Sum, I,Top) ->
%     if I==Top -> {Sum,Top};
%        true ->if I==Top ->{0,0};
%                 true-> {NSum,NI}=a(Sum, I),
%                        while(NSum,NI,Top-1)
%               end
%     end.
%
%a(X,Y)-> X,Y.
%{add(X,Y),(fun (Z)->add(Z,1) end)(Y)}.

add(A,0)->A;
add(A,B) -> A.%+a(A,B).
%
%t({0,0})->0.



%Problema --> En les noves crides a graphMatchging no podem pasarli els nodes del patternMatching original asoles. Hi hauria que pasarli els nodes als que s'esta fent PM (tercer camp)???? 
%Conforme esta la funció graphMatchging ara, necessita els nodes implicats en el PM, sin embargo... les noves crides la part dreta del PM son els nodes als que apunta el tercer camp del diccionari...estos nodes no estan inclosos en els nodes que se li pasen com a argument. Com ho arreglem?? No podem pasarli tots els nodes del arbre pq estem analitzant sols una expressió en particular.
%Possible solució--> Anar pasant tots els nodes acumulats fins ara dins de les expressions...
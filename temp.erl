-module(temp).


-export([main/0]).

main() -> %W= {1,{1,2}},
          %{Y,Z} = W,
          %{Z1,Z2}=Z.
          X={1,2},
          X={1,3},
          case X of
          	{Y,_} -> Y;
          	_ -> 2
          end.
          %Z2=f(Z1).
          %X=[1,2,3,4,5],
          %Y={1,1},
          %f(Y).
          %case X of
          %	1 -> 1;
          %	_ ->2
          %end,
          %case Y of
	%	{1,1} -> 1;
	%	{2,2} -> 2;
	%	{X,1} -> 3;
	%	_     -> 4
	%end.
          %{Y,Z}=X.
          %.

%f(X) -> [g({Y,Z})||Y<-X,Z<-X,Z>4,Y>3].

%f({1,1}) -> 1;
%f({2,2}) -> 2;
%f({X,1}) -> 3;
%f(_) -> 4.



%g(_) ->1.
%
%main() ->
	%X = {1,2},
%	X={3,5},
%	{Y,Z}=X,
%	{A,B,C}=X.
%	case X of
%	     1 -> 0;
%	     {1,2} -> 2 ;
%	     a -> 3;
%	     {1,_} -> 4;
%	     {2,_} -> 5 ;
%	     [1] -> 6;
%	     [1|X] -> 7;
%	     {_,_} -> 8;
%	     _ -> 9
%	end.

%X= {1,2},
          %{Y,Z} = X,
          %I = 1,
          %Y=I,
          %case Y of
          	%1 -> A=1;
          	%1 -> A=0;
          	%_ -> A=0
          	%_ -> A=1
          %end,
          %A.
          %A=1,
          %add(A,A).
          %{Result,_}=while(Sum, I,11 ),
          %Result.
%          X={1,2},
%          g(X).
 	  %case X of
	%	{1,1}    -> 1;
	%	{2,2}    -> 2;
	%	{Z,1}    -> 3;
	%	_        -> 4
	%  end,
	  %Y={1,2},
	  %if
	%	Y=={1,1}    -> 1;
	%	Y=={2,2}    -> 2;
	%	Y=={Y,1}    -> 3;
	%	true        -> 4
	%  end.

%g({1,1})    -> 1;
%g({2,2})    -> 2;
%g({Z,W})    -> 3;
%g(_)        -> 4.


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

%add(A,0)->A;
%add(A,B) -> A.%+a(A,B).
%
%t({0,0})->0.


%Problema --> En les noves crides a graphMatchging no podem pasarli els nodes del patternMatching original asoles. Hi hauria que pasarli els nodes als que s'esta fent PM (tercer camp)???? 
%Conforme esta la funció graphMatchging ara, necessita els nodes implicats en el PM, sin embargo... les noves crides la part dreta del PM son els nodes als que apunta el tercer camp del diccionari...estos nodes no estan inclosos en els nodes que se li pasen com a argument. Com ho arreglem?? No podem pasarli tots els nodes del arbre pq estem analitzant sols una expressió en particular.
%Possible solució--> Anar pasant tots els nodes acumulats fins ara dins de les expressions...
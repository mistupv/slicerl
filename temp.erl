-module(temp).


-export([main/0]).

%main() -> 	%A=B=C=3,
		%D=E=J=4.
%			C=(Y={1,2}),
%			B=C,
%			A=B,
%			{X,_} = A,
%			{X,_} = A.
%	A=3,
%	J={5,5},
%	{X,(J=W)}= {A,{5,5}},
%	{Z1,Z2}=W.
	
	%Z={1,2},
	%X=1,
	%{X,Y}=Z.
	
	
%	C={Y=1,2},
%	B=C,
%	A={B,3},
%	{X,_}=A,
%	{Z1,Z2}=X.


%%            REGLA D'OR 	
%	C={{1,1},2},
%	{A,B}=C,
%	D={{1,1},B},
%	E=D,
%	{Z1,Z2}=E,
%	E.

%	C={1,2},
%	{Z1,Z2} = C,
%	Z = f(C,Z1),
%	Z.
%	
%f(X,Y) -> {A,B}=X.



%0.
%f(X,Y) -> {A,B}=X,
%	  A+Y,
%	  case B of
%	  	1 -> 0;
%	  	_ -> f(X,Y-1) 
%	  end.



%0.	  
%
%g(X) -> case X of
%		1 -> 1;
%		_ -> f(X-1)
%	end.
%
%
%f(X) -> {A,B}=X,
%	C=g(A),
%	B+C.
	
	
	
%	X={1,1},
%	{X1,X2}=X,
%	X1.
	
	%C=Y={1,2},
		
%f(X,Y)->{X,Y}.

%	X = {1,1},
%	case X of
%		%{Q,W,Z} -> Y=2;	
%		%{_,_} -> Y=3;
%		{Y,Z} -> Y=1;
%		_ ->Y=4
%	end,
%	Y.
%	C = {1,2},
%	{A,B} = C,
%	D = {A,B},
%	E=D,
%	{Z1,Z2}=E.



%0.	
%f(X)->%	X = {1,1},
%       case X of
%               {Y,Z} -> Y={1,1};
%               _ ->Y={4,4}
%       end,
%       {Y1,Y2}=Y.
       
       
%		C={1,2},
%		{Z1,Z2} = C,
%		Z = f(C,Z1),
%		Z.
%	
%	f(X,Y) -> {A,B}=X.


%main()-> X={1,2},
%                f(X).
%main() -> X={1,2},
%	f(X).
%
%
%f(X) -> {X1,X2}=X,
%	f(X).




%main(X) -> {X1,X2}=X,
%	main(X).


%XXXXXXXXXXXXXXXXXXXXXXXXX
%main() -> X={1,2},
%	w(X).
%
%w(X) -> f(X).
%
%f(X) ->	{X1,X2}=X,
%	f(X).
%XXXXXXXXXXXXXXXXXXXXXXXXX


%main() -> F=fun(X) -> X end,
%	  F(1).
%	  
%f(X) -> X.


%main() -> X={1,2},
%	f(X).

%f(X) -> {X1,X2}=X,f({X2,X1}).
%f({X1,X2})-> f({X2,X1}).


%	{Z31,Z32}=Z3,
%	Z=Z1+Z31+Z32,
%	Z.
	
	%A={{1,1,1},{1,1,1}},
	%{{X,1,Y},_}=A,
	%{_,{1,Y,X}}=A.
	
		
%	X={1,2},
%	%Y=1,
%	Z= case X of
%		{Q,W} -> 1;
%		_ -> {1,2}
%	  end,
%	{Z1,Z2}=Z.

	
		%{Q,W}=A,
		%{Q,W}=A.
	  %{X,W}= {A,{1,3}},
	  %{Y,X} = W.
	  %X={1,2},
	  %{Y,Z} = X.
  		%J={5,5},
	  	%{X,(W=J)}= {A,{5,5}},
	  %{Y,(Q=J)}= {A,{5,5}},
	  %{Q1,Q2}=Q,
	  	%{Z1,Z2}=W.
	  	
	  %{X,Y,A=B,C}={Z,W,3,D}={1,1,3,1}. 
	  
	  %Y={1,1},
	  %W=Y,
	  %{1,V}=W.
	  
	  %Y=1,
	  %X=1,
	  %1=X.
	  
	  
	  
	 %J={5,undef},
         %{_,(W=J)}= {undef,undef},
         %{Z1,_}=W.
         %f(1).
	  %f(W),
          %{Y,{Z1,Z2}} = W.
          %{Y,{Z1,Z2}} = W.
%          {_,_}=Z.
          %X={1,2},
          %X={1,3},
          %case X of
          %	{Y,_} -> Y;
          %	_ -> 2
          %end,
          %Z2=f(Z1).
%          Z=[1,2,3,4,5],
%          f(Z,Z).
          %Q=1,
          %f(Y,Z).
          %case X of
          %	1 -> 1;
          %	_ ->2
          %end,
          %case Y of
	%	{1,1} -> 1;
	%	{2,2} -> 2;
	%	{X,1} -> 3;
	%	_     -> 4
	 % end.
%	 f(Q,Q).
          %{Y,Z}=X.
          %.

%f(_) -> 3.

%f(Y) -> case Y of
%		{1,1} -> 1;
%		{2,2} -> 2;
%		{X,1} -> 3;
%		_     -> 4
%	  end.

%f(1,1) -> 1;
%f(2,2) -> 2;
%f(1,X) -> 3;
%f(Y,Z) -> [{Y2,W}||Y2<-Y,W<-Z,Y>4,W>3].



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

%main() ->%    Sum = 0,%    I = 1,%    {Result,_} = while(Sum,I,11),%    Result.
%
%while(Sum,I,Top) ->%    if%        I /= Top -> {NSum,NI} = a(Sum,I),%                    while(NSum,NI,Top-1);%        I == Top -> {Sum,Top}%    end.
%   
%a(X,Y) ->%    {add(X,Y),%    fun(Z)->add(Z,1) end(Y)}.
%   
%add(A,0) -> A;%add(A,B) -> A+B.
%
%main() -> A = {{1,2},3},
%          f(A).
%
%main(X2,X1) ->
%	X={X1,X2},
%	g(X,X2).
%	%Y={1,2} 
%
%%f(Y1,Y2) ->
%%	g({Y1,Y2},Y2).
%	
%g(Z,Z2) -> h(Z).
%	
%h(Z) -> {X1,X2}=Z, 
%	main(X1,X2).

%


%main() -> X=f(),g(X).
%
%f() -> {1,2}.
%
%g(X) -> Y= h(X),i(Y).
%
%h(X) -> X.
%
%i(X)-> {Z1,Z2} =X.


%main(A) -> X=g(A).  
%%	X={0,1},
%%	 Y=g(X),
%%	 {Y1,Y2}=Y.
%%	 
%g({a,A}) -> D=1,Y=2;
%g({b,B}) -> E=1,Y=3;
%g({c,c}) -> F=1,Y=4.
	 
	 
	  


%main()->{Z1,Z2}=f(0,0).
%%f(X,Y)->g(X,Y).
%%g(X,Y)->{X,Y}. 



%main()->A={2,3},
%	{Z1,Z2}=f(A).
%%f(A)->g(A).
%%g(A)->{X,Y}=A. 

%main(X,Y) -> {A,B} = h(X,Y). 	
%
%h(X,Y) -> {X,Y}.


%main(0) -> {X1,X2}=g(0).
%g(0)->X={1,2},X.


%PROBLEMA3
%main(A) -> g(A).  
%main(X) ->A={X,X}, g(A).
%
%g({a,A}) -> D=1,Y=2;
%g({b,B}) -> E=1,Y=3;
%g({c,c}) -> F=1,Y=4.

%PROBLEMA2
%main(X,Y) -> 
%	     {A,B} = h(X,Y),
%	     {Z1,Z2} = A. 	
%
%h(X,Y) -> {{X,1},Y}.

%PROBLEMA1
%main() -> A = {{1,2},3},
%          {M1,M2}=f(A).
%
%f(Y) ->
%	%Y=f(X1,X2),
%	%Y={{1,2},3}, 
%	{Z1,Z2}=Y,
%	{A1,A2}=Z1.





%main() -> A = {1,2},
%          {A1,A2}=f(A),
%          {B1,B2}=f(A).
%%
%f(Y) -> {F1,F2}=Y.
%
%g() ->  Z= {3,4},
%	{C1,C2} = f(Z).


%main() -> case 3 of
%		3 -> X={0,0};
%		_ -> X={1,1}
%	  end,
%	  {Z1,Z2}=X.



main() -> A = {{1,2},3},
          {M1,M2}=f(A).


f(Y) ->
	%Y=f(X1,X2),
	%Y={{1,2},3}, 
	{Z1,Z2}=Y,
	{A1,A2}=Z1,
	g(Z2).
	
g(Z) -> Y=h(Z),
	Y.
	

h(X) -> X.






%f(X)->{A,B}=X,
%        {A1,A2}=A.
%%main()->X={{1,2},3},
%	f(X).
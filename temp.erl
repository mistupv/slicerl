-module(temp).


-export([main/0]).

main() -> 	A=3,
	  %{X,W}= {A,{1,3}},
	  %{Y,X} = W.
	  %X={1,2},
	  %{Y,Z} = X.
  		J={5,5},
	  	{X,(J=W)}= {A,{5,5}},
	  %{Y,(Q=J)}= {A,{5,5}},
	  %{Q1,Q2}=Q,
	  	{Z1,Z2}=W.
	  
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
          %Z=[1,2,3,4,5],
          %f(Z,Z).
          %Q=1,
%          f(Y,Z).
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
%f(Y,Z) -> [{Y,W}||Y<-Y,W<-Z,Y>4,W>3].



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

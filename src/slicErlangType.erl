-module(slicErlangType).

%falta tratar las lists comprehensions en las funcones que iteran en la sintaxis

-export([getFunTypes/0,getFunTypes/2]).

getFunTypes() ->
    {ok,Abstract} = smerl:for_file("temp.erl"),
    getFunTypes(lists:reverse(smerl:get_forms(Abstract)),Abstract).
    
getFunTypes(Forms,Abstract) ->
    NForms=typeTransformation(Forms,0,0),
    NAbstract=smerl:set_forms(Abstract,NForms),
    NNAbstract=smerl:set_module(NAbstract, temp_tt),
    smerl:to_src(NNAbstract, "temp_tt.erl"),
    % typer:get_type_inside_erl(["--plt",".dialyzer_plt","--show", "temp_tt.erl"]).
    typer:get_type_inside_erl(["--show", "temp_tt.erl"]).
    
typeTransformation([],_,_)->[];
typeTransformation([{function,LINE,Name,Arity,Clauses}|Funs],IdCalls,IdAF)->
    {Funs1,IdCalls1,IdAF1}=buildNewFunctionsForClauses(Clauses,Name,0,IdCalls,IdAF),
	[{function,LINE,Name,Arity,[buildFunctionClause(Clauses,Name,Arity)]}]
	 ++Funs1
	 ++typeTransformation(Funs,IdCalls1,IdAF1).
	
buildNewFunctionsForClauses([],_,_,IdCalls,IdAF)->{[],IdCalls,IdAF};
buildNewFunctionsForClauses([{clause,_,Patterns,Guards,Body}|Clauses],FName,Id,IdCalls,IdAF)->
    {NBody,Funs1,IdCalls1,IdAF1}=changeCallsList(Body,IdCalls,IdAF),
    {Funs2,IdCalls2,IdAF2}=buildNewFunctionsForClauses(Clauses,FName,Id+1,IdCalls1,IdAF1),
	{[{function,0,list_to_atom(atom_to_list(FName)++"_"++integer_to_list(Id)++"_CLAUSE"),length(Patterns),[{clause,0,Patterns,Guards,NBody}]}]
	  ++Funs2++Funs1,
	  IdCalls2,IdAF2}.
	  
buildFunctionClause(Clauses,Name,Arity)->
    Args=lists:reverse(buildArgs(Arity)),
	{clause,0,Args,[],[{'case',0,{tuple,0,Args},buildCaseClauses(Clauses,Name,0,Args)}]}.
	
buildArgs(0)->[];
buildArgs(Id)->[{var,0,list_to_atom("VAR"++integer_to_list(Id))}]++buildArgs(Id-1).

buildCaseClauses([],_,_,_)->[];
%buildCaseClauses([{clause,_,_,Guards,_}],Name,Id,Args)->
%	[{clause,0,[{var,0,'_'}],Guards,
%	   [{call,0,{atom,0,list_to_atom(atom_to_list(Name)++"_"++integer_to_list(Id)++"_CLAUSE")},Args}]}];
buildCaseClauses([{clause,_,Patterns,Guards,_}|Clauses],Name,Id,Args)->
	[{clause,0,[{tuple,0,Patterns}],Guards,
	    [{call,0,{atom,0,list_to_atom(atom_to_list(Name)++"_"++integer_to_list(Id)++"_CLAUSE")},Args}]}]
	++buildCaseClauses(Clauses,Name,Id+1,Args).
	                                                         
	


%
% Look for calls & change them
%	
changeCalls({var,Line,V},Id,IdAF) -> {{var,Line,V},[],Id,IdAF};
changeCalls({integer,Line,I},Id,IdAF) -> {{integer,Line,I},[],Id,IdAF};
changeCalls({float,Line,F},Id,IdAF) -> {{float,Line,F},[],Id,IdAF};
changeCalls({atom,Line,A},Id,IdAF) -> {{atom,Line,A},[],Id,IdAF};
changeCalls({string,Line,S},Id,IdAF) -> {{string,Line,S},[],Id,IdAF};
changeCalls({char,Line,C},Id,IdAF) -> {{char,Line,C},[],Id,IdAF};
changeCalls({nil,Line},Id,IdAF) -> {{nil,Line},[],Id,IdAF};
changeCalls({cons,Line,H0,T0},Id,IdAF) ->
    {H1,Funs1,Id1,IdAF1} = changeCalls(H0,Id,IdAF),
    {T1,Funs2,Id2,IdAF2} = changeCalls(T0,Id1,IdAF1),				%They see the same variables
    {{cons,Line,H1,T1},Funs1++Funs2,Id2,IdAF2};
%changeCalls({lc,Line,E0,Qs0},Id) ->
%    Qs1 = lc_bc_quals(Qs0),
%    E1 = changeCalls(E0),
%    {lc,Line,E1,Qs1};
changeCalls({tuple,Line,Es0},Id,IdAF) ->
    {Es1,Funs1,Id1,IdAF1} = changeCallsList(Es0,Id,IdAF),
    {{tuple,Line,Es1},Funs1,Id1,IdAF1};
changeCalls({block,Line,Es0},Id,IdAF) ->
    %% Unfold block into a sequence.
    {Es1,Funs1,Id1,IdAF1} = changeCallsList(Es0,Id,IdAF),
    {{block,Line,Es1},Funs1,Id1,IdAF1};
changeCalls({'if',Line,Cs0},Id,IdAF) ->
    {Cs1,Funs1,Id1,IdAF1} = changeCallsClauses(Cs0,Id,IdAF),
    {{'if',Line,Cs1},Funs1,Id1,IdAF1};
changeCalls({'case',Line,E0,Cs0},Id,IdAF) ->
    {E1,Funs1,Id1,IdAF1} = changeCalls(E0,Id,IdAF),
    {Cs1,Funs2,Id2,IdAF2} = changeCallsClauses(Cs0,Id1,IdAF1),
    {{'case',Line,E1,Cs1},Funs1++Funs2,Id2,IdAF2};
changeCalls({'fun',Line,Body},Id,IdAF) ->
    case Body of
	{clauses,Cs0} ->
	    %{Cs1,Funs1,Id1,IdAF1} = changeCallsClauses(Cs0,Id,IdAF),
	    AFName=list_to_atom("ano_fun_"++integer_to_list(IdAF)),
	    {Funs1,Id1,IdAF1}=buildNewFunctionsForClauses(Cs0,AFName,0,Id,IdAF+1),
	    [{clause,_,Args,_,_}|_]=Cs0,
	    {{'fun',Line,{function,AFName,length(Args)}},
	     [{function,0,AFName,length(Args),[buildFunctionClause(Cs0,AFName,length(Args))]}]++Funs1,
	     Id1,IdAF1
	    };
	{function,F,A} ->
	    {{'fun',Line,{function,F,A}},[],Id,IdAF};
	{function,M,F,A} ->			%R10B-6: fun M:F/A.
	    {{'fun',Line,{function,M,F,A}},[],Id,IdAF}
    end;
changeCalls({call,Line,F0,As0},Id,IdAF) ->
    %% N.B. If F an atom then call to local function or BIF, if F a
    %% remote structure (see below) then call to other module,
    %% otherwise apply to "function".
    {F1,Funs1,Id1,IdAF1}=changeCalls(F0,Id+1,IdAF),
    NeededVars=varsExpression(F1),
    {As1,Funs2,Id2,IdAF2}=changeCallsList(As0,Id1,IdAF1),
    FunName=list_to_atom("transformed_call"++integer_to_list(Id)),
    Args=lists:reverse(buildArgs(length(As0++NeededVars))),
    ArgsCall=lists:reverse(buildArgs(length(As0))),
    VarsDict=associateNeededVarsWithArgs(length(As0)+1,NeededVars),
    %io:format("Change: ~p~n",[{F1,VarsDict}]),
    F2=changeVarsExpression(F1,VarsDict),
    {
       {call,Line,{atom,0,FunName},As1++buildVarsAF(NeededVars)},
       Funs1++Funs2++[{function,0,FunName,length(As0),
         [{clause,0,Args,[],[{'case',Line,{tuple,0,Args},
                              [{clause,0,[{tuple,0,Args}],[],[{call,0,F2,ArgsCall}]},
                               {clause,0,[{var,0,'_'}],[],[{atom,0,'error'}]}]}]}]}],
       Id2,IdAF2
    };
changeCalls({match,Line,P0,E0},Id,IdAF) ->
    {E1,Funs1,Id1,IdAF1} = changeCalls(E0,Id,IdAF),
    {{match,Line,P0,E1},Funs1,Id1,IdAF1};
changeCalls({op,Line,Op,A0},Id,IdAF) ->
    {A1,Funs1,Id1,IdAF1} = changeCalls(A0,Id,IdAF),
    {{op,Line,Op,A1},Funs1,Id1,IdAF1};
changeCalls({op,Line,Op,L0,R0},Id,IdAF) ->
    {L1,Funs1,Id1,IdAF1} = changeCalls(L0,Id,IdAF),
    {R1,Funs2,Id2,IdAF2} = changeCalls(R0,Id1,IdAF1),				%They see the same variables
    {{op,Line,Op,L1,R1},Funs1++Funs2,Id2,IdAF2};
changeCalls({lc,Line,E0,G0},Id,IdAF) ->
    {E1,Funs1,Id1,IdAF1} = changeCalls(E0,Id,IdAF),
    {G1,Funs2,Id2,IdAF2} = changeCallsList(G0,Id1,IdAF1),
    {{lc,Line,E1,G1},Funs1++Funs2,Id2,IdAF2};
changeCalls({generate,Line,P0,E0},Id,IdAF) ->
    %{P1,Funs1,Id1,IdAF1} = changeCalls(P0,Id,IdAF),
    {E1,Funs1,Id1,IdAF1} = changeCalls(E0,Id,IdAF),				
    {{generate,Line,P0,E1},Funs1,Id1,IdAF1}.
	  
changeCallsList([],Id,IdAF)->{[],[],Id,IdAF};
changeCallsList([E|Es],Id,IdAF)->
	{E1,Funs1,Id1,IdAF1}=changeCalls(E,Id,IdAF),
	{Es1,Funs2,Id2,IdAF2}=changeCallsList(Es,Id1,IdAF1),
	{[E1|Es1],Funs1++Funs2,Id2,IdAF2}.
	
changeCallsClauses([],Id,IdAF)->{[],[],Id,IdAF};
changeCallsClauses([{clause,Line,Patterns,Guards,Body}|Cs],Id,IdAF)->
	{Body1,Funs1,Id1,IdAF1}=changeCallsList(Body,Id,IdAF),
	{Cs1,Funs2,Id2,IdAF2}=changeCallsClauses(Cs,Id1,IdAF1),
	{[{clause,Line,Patterns,Guards,Body1}|Cs1],Funs1++Funs2,Id2,IdAF2}.
	

associateNeededVarsWithArgs(_,[])->[];	
associateNeededVarsWithArgs(Id,[V|Vs])->
	[{V,list_to_atom("VAR"++integer_to_list(Id))}|associateNeededVarsWithArgs(Id+1,Vs)].
	
	
varsExpression({var,_,Name})-> [Name];
varsExpression({match,_,_,E2})-> varsExpression(E2);
varsExpression({tuple,_,Es}) -> removeDuplicates([Var||E<-Es,Var<-varsExpression(E)]);
varsExpression({cons,_,EH,ET}) -> removeDuplicates(varsExpression(EH)++varsExpression(ET));
varsExpression({op,_,_,E1,E2})-> removeDuplicates(varsExpression(E1)++varsExpression(E2));
varsExpression({op,_,_,E})-> varsExpression(E);
varsExpression({block,_,Es})-> removeDuplicates([Var||E<-Es,Var<-varsExpression(E)]);
varsExpression({'if',_,Cs})-> removeDuplicates([Var||C<-Cs,Var<-varsClause(C)]);
varsExpression({'case',_,E,Cs})-> removeDuplicates(varsExpression(E)++[Var||C<-Cs,Var<-varsClause(C)]);
varsExpression({'fun',_,Body})-> 
    case Body of
	    {clauses,Cs} ->
	      removeDuplicates([Var||C<-Cs,Var<-varsClause(C)]);
	    _ ->
	      []
     end;
varsExpression({call,_,F,As})-> removeDuplicates(varsExpression(F)++[Var||E<-As,Var<-varsExpression(E)]);
varsExpression({lc,_,Ex,Gs})-> removeDuplicates(varsExpression(Ex)++[Var||E<-Gs,Var<-varsExpression(E)]);
varsExpression({generate,_,_,E})-> varsExpression(E);
varsExpression(_)-> [].

%Falta anyadir les variables de les clausules
varsClause({clause,_,Patterns,_,Body})->
  sets:to_list(
    sets:subtract(
      sets:from_list([Var||E<-Body,Var<-varsExpression(E)]),
	  sets:from_list([Var||E<-Patterns,Var<-varsExpression(E)])
	)
  ).

removeDuplicates(List) -> sets:to_list(sets:from_list(List)).

changeVarsExpression(E,[])->E;
changeVarsExpression({var,LINE,Name},VarsDict)->
  [NV_|_]=[NV||{V,NV}<-VarsDict,V==Name],
  {var,LINE,NV_};
changeVarsExpression({match,LINE,E1,E2},VarsDict)->
  {match,LINE,E1,changeVarsExpression(E2,VarsDict)};
changeVarsExpression({tuple,LINE,Es},VarsDict)->
  {tuple,LINE,lists:map(fun (E)-> changeVarsExpression(E,VarsDict) end,Es)};
changeVarsExpression({cons,LINE,EH,ET},VarsDict)->
  {cons,LINE,changeVarsExpression(EH,VarsDict),changeVarsExpression(ET,VarsDict)};
changeVarsExpression({op,LINE,Op,E1,E2},VarsDict)->
  {op,LINE,Op,changeVarsExpression(E1,VarsDict),changeVarsExpression(E2,VarsDict)};
changeVarsExpression({op,LINE,Op,E},VarsDict)->
  {op,LINE,Op,changeVarsExpression(E,VarsDict)};
changeVarsExpression({block,LINE,Es},VarsDict)->
  {block,LINE,lists:map(fun (E)-> changeVarsExpression(E,VarsDict) end,Es)};
changeVarsExpression({'if',LINE,Cs},VarsDict)->
  {'if',LINE,[changeVarsClause(C,VarsDict)||C<-Cs]}; 
changeVarsExpression({'case',LINE,E,Cs},VarsDict)->
  {'case',LINE,changeVarsExpression(E,VarsDict),[changeVarsClause(C,VarsDict)||C<-Cs]}; 
changeVarsExpression({'fun',LINE,Body},VarsDict)->
  case Body of
	    {clauses,Cs} ->
	      {'fun',LINE,{clauses,[changeVarsClause(C,VarsDict)||C<-Cs]}};
	    _ ->
	      {'fun',LINE,Body}
  end;
changeVarsExpression({call,LINE,F,As},VarsDict)->
  {call,LINE,changeVarsExpression(F,VarsDict),lists:map(fun (E)-> changeVarsExpression(E,VarsDict) end,As)}; 
%changeVarsExpression({lc,LINE,E,G},VarsDict)->
%  {lc,LINE,changeVarsExpression(E,VarsDict),lists:map(fun (E)-> changeVarsExpression(G,VarsDict) end,As)};
changeVarsExpression({generate,LINE,P,E},VarsDict)->
  {generate,LINE,P,changeVarsExpression(E,VarsDict)};  
changeVarsExpression(E,_)->E.   
    
changeVarsClause({clause,LINE,Patterns,Guards,Body},VarsDict)->
  {clause,LINE,Patterns,Guards,lists:map(fun (E)-> changeVarsExpression(E,VarsDict) end,Body)}.
  
buildVarsAF([])->[];
buildVarsAF([V|Vs])->[{var,0,V}|buildVarsAF(Vs)].
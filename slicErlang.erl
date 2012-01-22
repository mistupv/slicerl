%c(slicErlang),c(slicErlangDot),slicErlang:start(0),slicErlangDot:start(0).
						%c(slicErlang),c(slicErlangDot),c(slicErlangSlice),slicErlang:start(0),slicErlangDot:start(0),slicErlangSlice:start(0).
						%assadsa						
						
%TODO: 
% Suport a les list comprehension desde la transformacio per als tipos esta per tractar
% Millorar la precisio al obtenir les posibles funcions a aplicar utilitzant la inferencia de tipos (variables residuals)
% Enganchar el input al nodo que defineix la funci贸 que es crida i no de al return
% summaries
% utilitzar la info del graph matching per confirmar que fan matching (stong i weak)						
%PROBLEMA: No s'estan afegint les variables que es declaren en arguments

-module(slicErlang).

-export([start/1,graphForms/4]).

-record(st, {nodes      :: [node_edg()],
	     edges     	:: [edge_edg()],
	     free	:: integer(),
	     vdict      :: varDict(),
	     lasts      :: [integer()],
	     f_lasts    :: [integer()],
	     firsts     :: [integer()],
	     a_nodes    :: [node_edg()]}). %segurament aço fa que sobre el camp nodes. LLEVAR_LO

-type node_edg() :: {node,integer(),node_type()}.
-type edge_edg() :: {edge,integer(),integer(),edge_type()}.
-type node_type() :: any().
-type edge_type() :: any().
-type varDict() :: [{atom(),[integer()],[integer()]}].


%-type value() :: {integer,integer()} | {float,float()} | {string,string()} | {atom,atom()}
%	       | {var,atom()} | {nil} | {tuple,[value()]} | {cons,[value()],[value()]} | {undefined} .
%-type expression() :: any().
%-type pattern() :: any().
%-type guard() :: any().
%-type clause() :: any().
%-type function_() :: any().
%-type generator() :: any().
%:: {function_in,atom(),integer()} |  {function_out,atom(),integer(),integer()}
%		   | clause_in | {clause_out,integer()} | {pattern,pattern()} | {expression,expression()}
%		   | {guards,guard()} | {'case',expression()} | {'if',expression()} 
%		   | {block,expression()} | {lc,expression()} | {gen,generator()} | call | return.



%-spec start(any()) -> ok.
start(_) ->
	{ok,Abstract} = smerl:for_file("temp.erl"),
    	Forms=lists:reverse(smerl:get_forms(Abstract)),
%    	State0 = #st{nodes = [], edges = [], free = 0,vdict = [], 
%                 lasts = [], f_lasts = [], firsts = [],a_nodes = []},
    	{Nodes,Edges,_,_} = graphForms(Forms,0,[],[]),
    	TypeInfo=slicErlangType:getFunTypes(Forms,Abstract),
    	%io:format("Calls: ~w~n",[[Node_||{node,Node_,{call,_}}<-Nodes]]),
    	CallsInfo = lists:sort(buildCallsInfo(Nodes,Edges,[Node_||{node,Node_,{call,_}}<-Nodes])),
    	CallsInfoWithTypes = addTypeInfo(CallsInfo,TypeInfo,0),
    	%io:format("ClausesTypeInfo: ~p ~n",[{CallsInfoWithTypes,TypeInfo}]),
    	AllProgramClauses = [NCIn||{node,NCIn,{clause_in,_,_}}<-Nodes,
                               [NFIn||{node,NFIn,{function_in,_,_,_,_}}<-Nodes,
                                      {edge,NFIn_,NCIn_,control}<-Edges,
                                      NFIn==NFIn_,NCIn_==NCIn] /= [] ],
    	ClausesTypeInfo=getClausesTypeInfo(AllProgramClauses,TypeInfo),
    	ClausesInfoWithTypes = buildClauseInfo(Nodes,Edges,AllProgramClauses,ClausesTypeInfo),
    	%io:format("ClausesTypeInfo: ~p ~n",[{CallsInfoWithTypes}]),
    	{InfoPending,InputOutputEdges} = buildInputOutputEdges(Nodes,Edges,CallsInfoWithTypes,ClausesInfoWithTypes),
    	%io:format("InfoPending: ~p ~n",[InfoPending]),
    	%buildOutputEdges(Nodes,Edges,Free,InfoPending),
    	ReachablePatterns = getReachablePatterns(Nodes,Edges,ClausesInfoWithTypes),
    	%io:format("ReachablePatterns: ~p ~n",[{ReachablePatterns}]),
    	%SummaryEdges = buildSummaryEdges(Edges++InputOutputEdges,ReachablePatterns,CallsInfo),
    
   	NEdges = Edges++InputOutputEdges,%++SummaryEdges,
    	%NEdges = Edges ++ InputOutputEdges,
    
    	{ok, DeviceSerial} = file:open("temp.serial", [write]),
	%io:format("Total nodes: ~p ~nTotal edges: ~p~n",[length(Nodes),length(NEdges)]),
    	io:write(DeviceSerial,{Nodes,NEdges}),
    	ok = file:close(DeviceSerial).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GRAPH FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 


%-spec graphForms([function_()],integer(),varDict()) -> {[node_()],[edge()],integer()}.

graphForms([],Free,_,NodesAcum)->{[],[],Free,NodesAcum};
graphForms([{function,_,Name,Arity,Clauses}|Funs],Free,VarsDict,NodesAcum) ->
	{NodesClauses,EdgesClauses,NFree,_,Firsts,Lasts,FLasts,_,NodesAcumN,_} = graphClauses(Clauses,Free+1, VarsDict, NodesAcum, func,[]),
    	{NodesForms,EdgesForm,NNFree,NodesAcumNN} = graphForms(Funs,NFree,VarsDict,NodesAcumN),
    	N_in = {node,Free,{function_in,Name,Arity,FLasts,Lasts}},
    	{ 
      		[N_in]++NodesClauses++NodesForms,
      		EdgesClauses++EdgesForm++[{edge,Free,First,control}||First <- Firsts],
      		NNFree,
      		NodesAcumNN++[N_in]
    	};
graphForms([_|Funs],Free,VarsDict,NodesAcum)->graphForms(Funs,Free,VarsDict,NodesAcum).


%graphForms([],St)->St;
%graphForms([{function,_,Name,Arity,Clauses}|Funs],#st{free = Free, vdict = VarsDict} = St0) ->
%    	St1 = graphClauses(Clauses,St0#st{free = Free+1}),
%    	St2 = graphForms(Funs,St1#st{
%    	                         vdict = VarsDict,
%                                 nodes = St1#st.nodes
%                                         ++[{node,Free,{function_in,Name,Arity,St1#st.f_lasts,St1#st.lasts}}],
%                                 edges = St1#st.edges++[{edge,Free,First,control}||First <- St1#st.firsts]
%                                 });
%graphForms([_|Funs],St)->graphForms(Funs,St).



%-spec graphFunctionClauses([{[clause()],integer(),[pattern()],[guard()],[expression()]}],integer(),varDict()) -> 
%			{[{node,integer(),node_type()}],[edge()],integer(),varDict(),[integer()],[integer()]}.

graphClauses([],Free,VD,NodesAcum,_,_)->	{[],[],Free,VD,[],[],[],[],NodesAcum,[]};
graphClauses([{clause,_,Patterns,Guards,Body}|Clauses],Free0,VD0,NodesAcum,From,ClausesAcum) ->
    	case From of
    		func -> Type=pat;
    		_ -> Type=patArg
    	end,
    	{N1,E1,Free1,VD1,F1,_,_,NodesAcumN} = graphExpressions(Patterns,Free0+1,VD0,Type,NodesAcum),
       	VD2=VD1++[{Var,NodesDecl,NodesPM}||{Var,NodesDecl,NodesPM}<-VD0,[Var1||{Var1,_,_}<-VD1,Var1==Var]==[]],
    	{N2,E2,Free2,NodesAcumNN} = graphGuards(Guards,Free1,VD2,NodesAcumN),
	case From of
    		%Si es una funció no afegim el node body
    		%func -> N_FreeBody=Free2;
    		_ -> 	N_FreeBody=Free2+1
    	end, 
    	{N3,E3,Free3,VD3,F2,L2,FL2,NodesAcumNNN} =graphExpressionsLast(Body,N_FreeBody,VD2,exp,NodesAcumNN),
    	 case From of
    		%Si es una funció no afegim el node body
    		%func -> N_body=[],EdgeBody=[],EdgesBody_Body=[{edge,Free1,NE,control}||NE<-F2];%de la guarda als first del body
    		_ -> 	N_body=[{node,Free2,{body,Body}}],
    			%io:format("EDGE1 : ~p~n",[{Free1,Free2}]),
    			EdgeBody=[{edge,Free1,Free2,control}], %del node guarda al node body
    			EdgesBody_Body=[{edge,Free2,NE,control}||NE<-F2] %del node body als first del body	
    	end, 
    	%Buscar els nodes calls asi que hi han en N3
    	{N4,E4,Free4,VD4,F3,L3,FL3,FC3,NodesAcumNNNN,ClausesAcumN} = graphClauses(Clauses,Free3,VD0,NodesAcumNNN,From,ClausesAcum++[{Free0,getNumNodes(N1)}]),
    	N_in = {node,Free0,{clause_in,FL2,L2}},
    	%io:format("~n Call: ~w~n ",[{getNumNodes(N_body),getNumNodes(N1),ClausesAcum}]),
    	case From of
    		func -> EdgesLinkClauses=edgesLinkClauses(getNumNodes(N_body),getNumNodes(N1),ClausesAcum,VD3,NodesAcumNNNN++[N_in]);
    		exp_case -> EdgesLinkClauses=edgesLinkClauses(getNumNodes(N_body),getNumNodes(N1),ClausesAcum,VD3,NodesAcumNNNN++[N_in]);
    		exp_if -> EdgesLinkClauses=edgesClausesAll(getNumNodes(N_body),getNumNodes(N1),ClausesAcum)
    	end,
    	%io:format("~n Return: ~w~n~n ",[{EdgesLinkClauses}]),
    	{
      		[N_in]++N1++N2++N3++N4++N_body,
      		removeDuplicates(E1++E2++E3++E4++EdgeBody++EdgesLinkClauses
		       ++[{edge,Free0,Free1,control}] %Clausula amb la guarda
		       ++[{edge,Free1,Free0,data}]
		       ++[{edge,Free0,NP,control}||NP<-F1]
		       ++[{edge,NP,Free1,data}||{node,NP,{term,Term}} <- N1,[NP1||{node,NP1,{term,Term1}} <- N1,NP1 /=NP,sets:size(sets:intersection(sets:from_list(varsExpression(Term)),sets:from_list(varsExpression(Term1))))/=0]/=[]]
		       ++[{edge,NP,Free1,data}||{node,NP,_}<-N1,[NP_||{node,NP_,{term,{var,_,_}}} <- N1,NP_==NP]==[]]
		       ++EdgesBody_Body),
		       %++[{edge,NE,NNNFree,control}||NE<-LastsBody]),
      		Free4,
      		VD3++VD4,%Juntar degumanet ficant sols una entrada per var i juntatnt tots els nodes
      		[Free0]++F3,
      		L2++L3,
      		FL2++FL3,
      		F1++FC3,
      		NodesAcumNNNN++[N_in]++[N_body],
      		%[{Free0,getNumNodes(N1)}]++ClausesAcumN
      		ClausesAcumN
    	}.


getNumNodes([])->[];
getNumNodes([{node,Num,_}|Nodes])->[Num]++getNumNodes(Nodes).


edgesLinkClauses([],_,_,_,_) -> [];
edgesLinkClauses(_,_,[],_,_) -> []; 
edgesLinkClauses([N_body],Patterns,[{N_in,PatternsAcum}|ClausesAcum],Dict,NodesAcum) -> 
	%io:format("~ngraphMatching: N_BODY:~w~n PATTERNS:~w~n PATTERNS_ACUM~w~n",[N_body,Patterns,PatternsAcum]),
	{Res,_,_}=graphMatchingListAll_(Patterns,PatternsAcum,Dict,NodesAcum),
	%io:format("res: ~w~n",[Res]),
	case Res of
		true -> [{edge,N_in,N_body,data}]++edgesLinkClauses([N_body],Patterns,ClausesAcum,Dict,NodesAcum);
		_ -> edgesLinkClauses([N_body],Patterns,ClausesAcum,Dict,NodesAcum)
	end.

edgesClausesAll([],_,_) -> [];
edgesClausesAll(_,_,[]) -> []; 
edgesClausesAll([N_body],Patterns,[{N_in,PatternsAcum}|ClausesAcum]) -> 
		[{edge,N_body,N_in,data}]++edgesClausesAll([N_body],Patterns,ClausesAcum).


%graphClauses([],St) -> St;
%graphClauses([{clause,_,Patterns,Guards,Body}|Clauses],#st{free = Free0, vdict = VD0} = St0) ->
%    	St1 = graphExpressions(Patterns,St0#st{free = Free+1},pat),
%    	NPat = [Node || Node = {node,NP,_} <- St1#st.nodes, [Node_ || Node_ = {node,NP_,_} <- St0#st.nodes,NP_==NP] == []],
%    	VD1=St1#st.vdict ++ [{Var,NodesDecl,NodesPM}||{Var,NodesDecl,NodesPM}<-VD0,[Var1||{Var1,_,_}<-St1#st.vdict,Var1==Var]==[]],
%    	St2 = graphGuards(Guards,St1#st{vdict = VD1}),
%    	St3 =graphExpressionsLast(Body,St2,exp),
%    	St4 = graphClauses(Clauses,St3#st{nodes = [{node,Free0,{clause_in,St3#st.f_lasts,St3#st.lasts}} | St3#st.nodes]
%              edges = removeDuplicates(St3#st.edges
%                         ++ [{edge,Free0,St1#st.free,control} | St1#st.edges] 
%                                            ++ [{edge,Free0,NP,control}||NP<-St1#st.firsts]
%                                            ++ [{edge,NP,St1#st.free,data}||
%                                                     {node,NP,{term,Term}} <- NPat,
%                                                     [NP1||{node,NP1,{term,Term1}} <- NPat,NP1 /=NP, 
%                                     	                 sets:size(sets:intersection(sets:from_list(varsExpression(Term)),
%                                                         sets:from_list(varsExpression(Term1))))/=0]/=[]]
%                                            ++ [{edge,NP,St1#st.free,data}||
%                                                   {node,NP,_} <- NPat,
%                                                   [NP_||{node,NP_,{term,{var,_,_}}} <- NPat,NP_==NP]==[]]
%                                            ++[{edge,St1#st.free,NE,control}||NE<-St3#st.firsts])}).

graphGuards(Guards,Free,VarsDict,NodesAcum) -> 
    	Vars = removeDuplicates(lists:flatten([Var||Guard <- Guards,Var<-lists:map(fun varsExpression/1,Guard)])),
    	N_guard = {node,Free,{guards,Guards}},
    	{
      		[N_guard],
      		[{edge,Node,Free,data}||Var <- Vars,{VarD,NodesDecl,_} <- VarsDict,Var==VarD,Node<-NodesDecl],
      		Free+1,
     		NodesAcum++[N_guard]
    	}.

%graphGuards(Guards, #st{free = Free0, nodes = Nodes0, edges = Edges0, vdict = VDict0}=St0) -> 
%    	Vars = removeDuplicates(lists:flatten([Var||Guard <- Guards,Var<-lists:map(fun varsExpression/1,Guard)])),
%    	St0#st{
%      		nodes = [{node,Free0,{guards,Guards}} | Nodes0],
%      		edges = Edges0 ++ [{edge,Node,Free0,data}||Var <- Vars,{VarD,NodesDecl,_} <- VDict0,Var==VarD,Node <- NodesDecl],
%      		free = Free0+1
%    	}.


graphTerm(Term,Free,VarsDict,NodesAcum)->
	N_term={node,Free,{term,Term}},
	{
		[N_term],
		[],
		Free+1,
		VarsDict,
		[Free],
		[Free],
		NodesAcum++[N_term]
	}.
	
	
%graphTerm(Term, #st{free = Free0, nodes = Nodes0, edges = Edges0, vdict = VDict0}=St0)->
%	St0#st{
%	  	nodes = [{node,Free0,{term,Term}} | Nodes0],
%	  	free = Free0+1,
%          	firsts = [Free],
%	  	lasts = [Free]
%	}.
%  
    
    
%%%%%%%%%%%%%%%%%%%%%%%%% graphExpression %%%%%%%%%%%%%%%%%%%%%%%%%
graphExpression(Term={var,_,V},Free,VarsDict,pat,NodesAcum)->
	{Ns,_,NFree,_,First,Lasts,NodesAcumN}=graphTerm(Term,Free,VarsDict,NodesAcum),
	%io:format("Edge: ~w~n",[{Ns,NFree,First,Lasts,NodesAcumN}]),
	{Ns,[],NFree,VarsDict,%++[{V,[Free],[Free]}],
	First,Lasts,NodesAcumN};
graphExpression(Term={var,_,V},Free,VarsDict,patArg,NodesAcum)->
	{Ns,_,NFree,_,First,Lasts,NodesAcumN}=graphTerm(Term,Free,VarsDict,NodesAcum),
	%io:format("Edge: ~w~n",[{Ns,NFree,First,Lasts,NodesAcumN}]),
	{Ns,[],NFree,VarsDict++[{V,[Free],[Free]}],
	First,Lasts,NodesAcumN};
graphExpression(Term={var,_,V},Free,VarsDict,exp,NodesAcum)->
	{Ns,_,NFree,_,First,Lasts,NodesAcumN}=graphTerm(Term,Free,VarsDict,NodesAcum),
	%io:format("Edge: ~w~n",[[{edge,NodeDecl,Free,data}||{VarD,[NodeDecl|_],_} <- VarsDict,V==VarD]]),
	%io:format("Dict: ~w~n",[VarsDict]),
	{Ns,
	 [{edge,NodeDecl,Free,data}||{VarD,[NodeDecl|_],_} <- VarsDict,V==VarD],
	 NFree,VarsDict,First,Lasts,NodesAcumN};
graphExpression(Term={integer,_,_},Free,VarsDict,_,NodesAcum)->
	graphTerm(Term,Free,VarsDict,NodesAcum);
graphExpression(Term={float,_,_},Free,VarsDict,_,NodesAcum)->
	graphTerm(Term,Free,VarsDict,NodesAcum);
graphExpression(Term={atom,_,_},Free,VarsDict,_,NodesAcum)->
	graphTerm(Term,Free,VarsDict,NodesAcum);
graphExpression(Term={string,_,_},Free,VarsDict,_,NodesAcum)->
	graphTerm(Term,Free,VarsDict,NodesAcum);
graphExpression(Term={char,_,_},Free,VarsDict,_,NodesAcum)->
	graphTerm(Term,Free,VarsDict,NodesAcum);
graphExpression(Term={nil,_},Free,VarsDict,_,NodesAcum)->
	graphTerm(Term,Free,VarsDict,NodesAcum);
graphExpression(Term={cons,_,H0,T0},Free,VarsDict,PatExp,NodesAcum)->
	{N1,E1,NFree,NVarsDict,F1,L1,_,NodesAcumN}=graphExpressions([H0,T0],Free+1,VarsDict,PatExp,NodesAcum),
	N_cons = {node,Free,{op,'[]',Term,F1,L1}},
	{
		[N_cons]++N1,
		E1++[{edge,Free,First,control}||First <- F1],
		NFree,
		NVarsDict,
		[Free],
		L1,
		NodesAcumN++[N_cons]
	};
graphExpression(Term={tuple,_,Es0},Free,VarsDict,PatExp,NodesAcum)->
	{N1,E1,NFree,NVarsDict,F1,L1,_,NodesAcumN}=graphExpressions(Es0,Free+1,VarsDict,PatExp,NodesAcum),
	N_tuple = {node,Free,{op,'{}',Term,F1,L1}},
	{
		[N_tuple]++N1,
		E1++[{edge,Free,First,control}||First <- F1],
		NFree,
		NVarsDict,
		[Free],
		L1,
		NodesAcumN++[N_tuple]
	};
graphExpression(Term={block,_,Body},Free,VarsDict,exp,NodesAcum)->
    	{NodesBody,EdgesBody,NFree,NVarsDict,FirstsBody,LastsBody,FLast,NodesAcumN} =
    		graphExpressionsLast(Body,Free+1,VarsDict,exp,NodesAcum),
    	N_block = {node,Free,{block,Term,FLast,LastsBody}},
    	{
     		[N_block]++NodesBody,
		EdgesBody++[{edge,Free,First,control}||First <- FirstsBody],
      		NFree,
      		NVarsDict,
      		[Free],
      		LastsBody,
      		NodesAcumN++[N_block]
    	};
graphExpression(Term={'if',_,Cs0},Free,VarsDict,exp,NodesAcum)->
    	{NodesClauses,EdgesClauses,NFree,NVarsDict,FirstsClauses,LastsClauses,FLasts,_,NodesAcumN,_}=
    		graphClauses(Cs0,Free+1,VarsDict,NodesAcum,exp_if,[]),
    	N_if = {node,Free,{'if',Term,FLasts,LastsClauses}},
    	{
      		[N_if]++NodesClauses,
      		EdgesClauses++[{edge,Free,First,control}||First <- FirstsClauses],
      		NFree,
      		NVarsDict,
      		[Free],
      		LastsClauses,
      		NodesAcumN++[N_if]
    	};
graphExpression(Term={'case',_,E,Cs0},Free,VarsDict,exp,NodesAcum)->
    	{NodesE,EdgesE,NFree,NVarsDict,FirstsE,_,NodesAcumN}=graphExpression(E,Free+1,VarsDict,exp,NodesAcum), 
	{NodesClauses,EdgesClauses,NNFree,NNVarsDict,FirstsClauses,LastsClauses,FLasts,FPat,NodesAcumNN,_}=
		graphClauses(Cs0,NFree,NVarsDict,NodesAcumN,exp_case,[]),
    	N_case = {node,Free,{'case',Term,FLasts,LastsClauses}},
    	NodesAcumNNN = NodesAcumNN++[N_case],
    	{_,EdgesPM,NNNVarsDict}=graphMatchingListPattern(FPat,Free+1,NNVarsDict,NodesAcumNNN),
    	{
      		[N_case]++NodesE++NodesClauses,
      		EdgesE++EdgesClauses++EdgesPM
       			++[{edge,Free,First,control}||First <- FirstsE]
       			++[{edge,Free,FirstC,control}||FirstC <- FirstsClauses],
      		NNFree,
      		NNNVarsDict,
     		[Free],
      		LastsClauses,
      		NodesAcumNNN
    	};
graphExpression(Term={'fun',_,Body},Free,VarsDict,exp,NodesAcum)->
    	case Body of
	  	{clauses,FCs} ->[{clause,_,Patterns,_,_}|_]=FCs,
	    			{NodesForm,EdgesForm,NFree,NodesAcumN}=
	    				graphForms([{function,0,'_',length(Patterns),FCs}],Free,VarsDict,NodesAcum),
	    			{
	      				NodesForm,
	      				EdgesForm,
	      				NFree,
	      				VarsDict,
	      				[Free],
	      				[NFree-1],
	      				NodesAcumN
	    			};
	  	_ -> graphTerm(Term,Free,VarsDict,NodesAcum)
    	end;
graphExpression({call,_,F0,As0},Free,VarsDict,exp,NodesAcum)->
    	{NodesE,EdgesE,NFree,NVarsDict,FirstsE,_,NodesAcumN}=graphExpression(F0,Free+1,VarsDict,exp,NodesAcum),
    	{NodesEs,EdgesEs,NNFree,NNVarsDict,FirstsEs,_,_,NodesAcumNN}=graphExpressions(As0,NFree,NVarsDict,exp,NodesAcumN),
    	N_call = {node,Free,{call,NNFree}},
    	N_return = {node,NNFree,return},
    	{
      		[N_call,N_return]++NodesE++NodesEs,
      		EdgesE++EdgesEs++[{edge,Free,First,control}||First <- (FirstsE++FirstsEs)]++[{edge,Free,NNFree,control},{edge,Free+1,Free,data}],
      		NNFree+1,
      		NNVarsDict,
      		[Free],
      		[NNFree],
      		NodesAcumNN++[N_call,N_return]
    	};
graphExpression({match,_,P0,E0},Free,VarsDict,PatExp,NodesAcum)->
    	{NodesP,EdgesP,NFree,NVarsDict,FirstsP,_,NodesAcumN}=graphExpression(P0,Free+1,VarsDict,pat,NodesAcum),
    	{NodesE,EdgesE,NNFree,NNVarsDict,FirstsE,LastE,NodesAcumNN}=graphExpression(E0,NFree,NVarsDict,PatExp,NodesAcumN),
    	N_match = {node,Free,{pm,[NFree],LastE}},
	NodesAcumNNN = NodesAcumNN++[N_match],
    	{_,EdgesPM,NNNVarsDict}=graphMatching(Free+1,NFree,NNVarsDict,NodesAcumNNN),
    	{
      		[N_match]++NodesP++NodesE,
      		EdgesP++EdgesE++EdgesPM++[{edge,Free,First,control}||First <- (FirstsP++FirstsE)],
      		NNFree,
      		NNNVarsDict,
      		[Free],
      		LastE,
      		NodesAcumNNN
    	};
graphExpression(Term={op,_,Op,A0},Free,VarsDict,exp,NodesAcum)->
    	{Nodes,Edges,NFree,NVarsDict,Firsts,Lasts,NodesAcumN} = graphExpression(A0,Free+1,VarsDict,exp,NodesAcum),
    	N_op = {node,Free,{op,Op,Term,[Free+1],Lasts}},
    	{
      		[N_op]++Nodes,
      		Edges++[{edge,Free,First,control}||First <- Firsts],
      		NFree,
      		NVarsDict,
      		[Free],
      		Lasts,
      		NodesAcumN++[N_op]
    	};
graphExpression(Term={op,_,Op,A0,A1},Free,VarsDict,exp,NodesAcum)->
    	{Nodes,Edges,NFree,NVarsDict,Firsts,Lasts,NodesAcumN} = graphExpression(A0,Free+1,VarsDict,exp,NodesAcum),
    	{Nodes1,Edges1,NNFree,NNVarsDict,Firsts1,Lasts1,NodesAcumNN} = graphExpression(A1,NFree,VarsDict,exp,NodesAcumN),
    	N_op = {node,Free,{op,Op,Term,[Free+1,NFree],Lasts++Lasts1}},
    	{
      		[N_op]++Nodes++Nodes1,
      		Edges++Edges1++[{edge,Free,First,control}||First <- Firsts++Firsts1],
      		NNFree,
      		NVarsDict++NNVarsDict,
      		[Free],
      		Lasts++Lasts1,
      		NodesAcumNN++[N_op]
    	}.



%graphExpression(Term={var,_,_}, St, pat) ->
%	graphTerm(Term,St);
%graphExpression(Term={var,_,V}, #st{free = Free0, edges = Edges0, vdict = VarsDict0} = St, exp) ->
%	graphTerm(Term,St#st{edges = Edges0 
%	                           ++ [{edge,NodeDecl,Free,data}||{VarD,NodeDecl,_} <- VarsDict0,V==VarD]});
%graphExpression(Term={integer,_,_}, St, _) ->
%	graphTerm(Term, St);
%graphExpression(Term={float,_,_}, St, _) ->
%	graphTerm(Term, St);
%graphExpression(Term={atom,_,_}, St, _) ->
%	graphTerm(Term, St);
%graphExpression(Term={string,_,_}, St, _) ->
%	graphTerm(Term, St);
%graphExpression(Term={char,_,_}, St, _) ->
%	graphTerm(Term, St);
%graphExpression(Term={nil,_}, St, _) ->
%	graphTerm(Term, St);
%graphExpression(Term={cons,_,H0,T0}, #st{free = Free0} = St0,PatExp,NodesAcum)->
%	St1 = graphExpressions([H0,T0],St0#st{free = Free+1},PatExp),
%	St1#st{
%		nodes = [{node,Free0,{op,'[]',Term,F1,L1}} | St1#st.nodes],
%		edges = St1#st.edges ++ [{edge,Free0,First,control}||First <- St1#st.firsts],
%		firsts = [Free0]
%	};
%graphExpression(Term={tuple,_,Es0},Free,VarsDict,PatExp,NodesAcum)->
%	    %io:format("tuple ~n"),
%	{N1,E1,NFree,NVarsDict,F1,L1,_,NodesAcumN}=graphExpressions(Es0,Free+1,VarsDict,PatExp,NodesAcum),
%	N_tuple = {node,Free,{op,'{}',Term,F1,L1}},
%	{
%		[N_tuple]++N1,
%		E1++[{edge,Free,First,control}||First <- F1],
%		NFree,
%		NVarsDict,
%		[Free],
%		L1,
%		NodesAcumN++[N_tuple]
%	};
%graphExpression(Term={block,_,Body},Free,VarsDict,exp,NodesAcum)->
%    {NodesBody,EdgesBody,NFree,NVarsDict,FirstsBody,LastsBody,FLast,NodesAcumN} =graphExpressionsLast(Body,Free+1,VarsDict,exp,NodesAcum),
%    N_block = {node,Free,{block,Term,FLast,LastsBody}},
%    {
%      [N_block]++NodesBody,
%      EdgesBody++[{edge,Free,First,control}||First <- FirstsBody],
%      NFree,
%      NVarsDict,
%      [Free],
%      LastsBody,
%      NodesAcumN++[N_block]
%    };
%graphExpression(Term={'if',_,Cs0},Free,VarsDict,exp,NodesAcum)->
%    {NodesClauses,EdgesClauses,NFree,NVarsDict,FirstsClauses,LastsClauses,FLasts,_,NodesAcumN}=graphClauses(Cs0,Free+1,VarsDict,NodesAcum),
%    N_if = {node,Free,{'if',Term,FLasts,LastsClauses}},
%    {
%      [N_if]++NodesClauses,
%      EdgesClauses++[{edge,Free,First,control}||First <- FirstsClauses],
%      NFree,
%      NVarsDict,
%      [Free],
%      LastsClauses,
%      NodesAcumN++[N_if]
%    };
%graphExpression(Term={'case',_,E,Cs0},Free,VarsDict,exp,NodesAcum)->
%    {NodesE,EdgesE,NFree,NVarsDict,FirstsE,_,NodesAcumN}=graphExpression(E,Free+1,VarsDict,exp,NodesAcum), 
%    {NodesClauses,EdgesClauses,NNFree,NNVarsDict,FirstsClauses,LastsClauses,FLasts,FPat,NodesAcumNN}=graphClauses(Cs0,NFree,NVarsDict,NodesAcumN),
%    N_case = {node,Free,{'case',Term,FLasts,LastsClauses}},
%    NodesAcumNNN = NodesAcumNN++[N_case],
%    {_,EdgesPM,NNNVarsDict}=graphMatchingListPattern(FPat,Free+1,NNVarsDict,NodesAcumNNN),
%    {
%      [N_case]++NodesE++NodesClauses,
%      EdgesE++EdgesClauses++EdgesPM
%       ++[{edge,Free,First,control}||First <- FirstsE]
%       ++[{edge,Free,FirstC,control}||FirstC <- FirstsClauses],
%      NNFree,
%      NNNVarsDict,
%      [Free],
%      LastsClauses,
%      NodesAcumNNN
%    };
%graphExpression(Term={'fun',_,Body},Free,VarsDict,exp,NodesAcum)->
%    case Body of
%	  {clauses,FCs} ->
%	    [{clause,_,Patterns,_,_}|_]=FCs,
%	    {NodesForm,EdgesForm,NFree,NodesAcumN}=graphForms([{function,0,'_',length(Patterns),FCs}],Free,VarsDict,NodesAcum),
%	    {
%	      NodesForm,
%	      EdgesForm,
%	      NFree,
%	      VarsDict,
%	      [Free],
%	      [NFree-1],
%	      NodesAcumN
%	    };
%	  _ ->
%	    graphTerm(Term,Free,VarsDict,NodesAcum)
%    end;
%graphExpression({call,_,F0,As0},Free,VarsDict,exp,NodesAcum)->
%    {NodesE,EdgesE,NFree,NVarsDict,FirstsE,_,NodesAcumN}=graphExpression(F0,Free+1,VarsDict,exp,NodesAcum),
%    {NodesEs,EdgesEs,NNFree,NNVarsDict,FirstsEs,_,_,NodesAcumNN}=graphExpressions(As0,NFree,NVarsDict,exp,NodesAcumN),
%    N_call = {node,Free,{call,NNFree}},
%    N_return = {node,NNFree,return},
%    {
%      [N_call,N_return]++NodesE++NodesEs,
%      EdgesE++EdgesEs++[{edge,Free,First,control}||First <- (FirstsE++FirstsEs)]++[{edge,Free,NNFree,control}],
%      NNFree+1,
%      NNVarsDict,
%      [Free],
%      [NNFree],
%      NodesAcumNN++[N_call,N_return]
%    };
%graphExpression({match,_,P0,E0},Free,VarsDict,PatExp,NodesAcum)->
%    %{Used,Defined} = getUsedDefined(Term,VarsDict),
%    %io:format("VarsDict: ~w\n",[VarsDict]),
%    %io:format("NodesAcum: ~w\n",[NodesAcum]),
%    {NodesP,EdgesP,NFree,NVarsDict,FirstsP,_,NodesAcumN}=graphExpression(P0,Free+1,VarsDict,pat,NodesAcum),%+numberNodesExpr(P0)}),
%    %io:format("NodesAcumN: ~w\n",[NodesAcumN]),
%    {NodesE,EdgesE,NNFree,NNVarsDict,FirstsE,LastE,NodesAcumNN}=graphExpression(E0,NFree,NVarsDict,PatExp,NodesAcumN),
%    N_match = {node,Free,{pm,[NFree],LastE}},
%    NodesAcumNNN = NodesAcumNN++[N_match],
%    %io:format("NNVarsDict: ~w\n",[NNVarsDict]),
%    {_,EdgesPM,NNNVarsDict}=graphMatching(Free+1,NFree,NNVarsDict,NodesAcumNNN),
%    %io:format("NNNVarsDict: ~w\n",[NNNVarsDict]),
%    {
%      [N_match]++NodesP++NodesE,
%      EdgesP++EdgesE++EdgesPM++[{edge,Free,First,control}||First <- (FirstsP++FirstsE)],
%      NNFree,
%      NNNVarsDict,
%      [Free],
%      LastE,
%      NodesAcumNNN
%    };
%graphExpression(Term={op,_,Op,A0},Free,VarsDict,exp,NodesAcum)->
%    {Nodes,Edges,NFree,NVarsDict,Firsts,Lasts,NodesAcumN} = graphExpression(A0,Free+1,VarsDict,exp,NodesAcum),
%    N_op = {node,Free,{op,Op,Term,[Free+1],Lasts}},
%    {
%      [N_op]++Nodes,
%      Edges++[{edge,Free,First,control}||First <- Firsts],
%      NFree,
%      NVarsDict,
%      [Free],
%      Lasts,
%      NodesAcumN++[N_op]
%    };
%graphExpression(Term={op,_,Op,A0,A1},Free,VarsDict,exp,NodesAcum)->
%    {Nodes,Edges,NFree,NVarsDict,Firsts,Lasts,NodesAcumN} = graphExpression(A0,Free+1,VarsDict,exp,NodesAcum),
%    {Nodes1,Edges1,NNFree,NNVarsDict,Firsts1,Lasts1,NodesAcumNN} = graphExpression(A1,NFree,VarsDict,exp,NodesAcumN),
%    N_op = {node,Free,{op,Op,Term,[Free+1,NFree],Lasts++Lasts1}},
%    {
%      [N_op]++Nodes++Nodes1,
%      Edges++Edges1++[{edge,Free,First,control}||First <- Firsts++Firsts1],
%      NNFree,
%      NVarsDict++NNVarsDict,
%      [Free],
%      Lasts++Lasts1,
%      NodesAcumNN++[N_op]
%    }.


%joinPatCase([H1,H2|T]) -> [{edge,H1,H2,control}]++joinPatCase([H2|T]);
%joinPatCase([H2]) -> [];
%joinPatCase([]) -> [].

%%%%%%%%%%%%%%%%%%%%%%%%% %%%%%%%%%%%%%%%%%%%%%%%%% %%%%%%%%%%%%%%%%%%%%%%%%%

%-spec graphExpressions([expression()],integer(),varDict())->{[node_()],[edge()],integer(),varDict(),[integer()],[integer()]}.
graphExpressions([],Free,VarsDict,_,NodesAcum) -> {[],[],Free,VarsDict,[],[],[],NodesAcum};
graphExpressions([Expression|Expressions],Free,VarsDict,PatExp,NodesAcum) ->
	{NodesE,EdgesE,NFree,NVarsDict,FirstsE,LastsE,NodesAcum2}=graphExpression(Expression,Free,VarsDict,PatExp,NodesAcum),
    	{NodesExpressions,EdgesExpression,NNFree,NNVarsDict,Firsts,Lasts,FLasts,NodesAcum3}=
    		case Expressions of
    	     		[] ->  {[],[],NFree,NVarsDict,[],[],[Free],NodesAcum2};
    	    		_ -> graphExpressions(Expressions,NFree,NVarsDict,PatExp,NodesAcum2)
    		end,
    	{
      		NodesE++NodesExpressions,
      		removeDuplicates(EdgesE++EdgesExpression),
      		NNFree,
      		NNVarsDict,
     		FirstsE++Firsts,
		LastsE++Lasts,
	      	FLasts,
	      	NodesAcum3
    	}.
    
%Soles en cosos de funcions, blocks....
graphExpressionsLast([],Free,VarsDict,_,NodesAcum) -> 
	{[],[],Free,VarsDict,[],[],[],NodesAcum};
graphExpressionsLast([Expression|Expressions],Free,VarsDict,PatExp,NodesAcum) ->
	{NodesE,EdgesE,NFree,NVarsDict,FirstsE,LastsE,NodesAcum2}=graphExpression(Expression,Free,VarsDict,PatExp,NodesAcum),
    	{NodesExpressions,EdgesExpression,NNFree,NNVarsDict,Firsts,Lasts,FLasts,NodesAcum3}=
    		case Expressions of
    	     		[] ->  {[],[],NFree,NVarsDict,[],LastsE,[Free],NodesAcum2};
    	     		_ -> graphExpressionsLast(Expressions,NFree,NVarsDict,PatExp,NodesAcum2)
    		end,
    	{
      		NodesE++NodesExpressions,
      		removeDuplicates(EdgesE++EdgesExpression),
      		NNFree,
      		NNVarsDict,
      		FirstsE++Firsts,
      		Lasts,
      		FLasts,
      		NodesAcum3
    	}.
    
    

%-spec  graphLC(expression(),integer(),varDict())->{[{node,integer(),node_type()}],[edge()],integer(),varDict(),[integer()],[integer()]}.	
%graphLC({lc,LINE,E,GensFilt},Free,VarsDict)->
%    N_lc = {node,Free,{lc,{lc,LINE,E,GensFilt}}},
%    {NodesGensFilt,EdgesGensFilt,NFree,NVarsDict,FirstGensFilt,LastsGensFilt} = graphGensFilt(GensFilt,Free+1,VarsDict),
%    {NodesExpLC,EdgesExpLC,NNFree,NNVarsDict,FirstsExpLC,LastsExpLC}=graphExpressions([E],NFree+1,NVarsDict),
%    {
%      [N_lc]++
%	  NodesGensFilt ++
%	  NodesExpLC,
%      EdgesGensFilt ++
%	  [{edge,Free,First,control}||First <- FirstGensFilt] ++
%	  EdgesExpLC ++
%	  [{edge,Last,First,control}||First <- FirstsExpLC , Last <-LastsGensFilt],
%      NNFree,
%      NNVarsDict,
%      [Free],
%      LastsExpLC
%    }.
%
%-spec  graphGensFilt([generator()],integer(),varDict())->{[node_()],[edge()],integer(),varDict(),[integer()],[integer()]}.
%graphGensFilt([],Free,VarsDict)-> {[],[],Free,VarsDict,[],[]};
%graphGensFilt([{generate,LINE,Pattern,Exp}|GensFilt],Free,VarsDict)-> 
%    N_gen = {node,Free,{gen,{gen,LINE,Pattern,Exp}}},
%    {NodesExp,EdgesExp,NFree,NVarsDict,FirstsExp,LastsExp}=graphExpressions([Exp],Free+1,VarsDict),	
%    {NodesPattern,EdgesPattern,NNFree,NNVarsDict}=graphPatternsCase([Pattern],NFree,NVarsDict),
%    {NodesGensFilt,EdgesGenFilt,NNNFree,NNNVarsDict,FirstsGenFilt,LastsGenFilt}=graphGensFilt(GensFilt,NNFree,NNVarsDict),
%    {
%      [N_gen]++NodesExp++NodesPattern++NodesGensFilt,
%      EdgesExp ++
%	  EdgesPattern ++
%	  [{edge,Free,First,control}||First <- FirstsExp] ++
%	  [{edge,Last,NP,control}||{node,NP,_} <- NodesPattern , Last <- LastsExp] ++
%	  EdgesGenFilt,
%      NNNFree,
%      NNNVarsDict,
%      [Free]++FirstsGenFilt,
%      [NP||{node,NP,_} <- NodesPattern]++LastsGenFilt
%    };
%graphGensFilt([Exp|GensFilt],Free,VarsDict)-> 
%    {NodesExp,EdgesExp,NFree,NVarsDict,FirstsExp,LastsExp}=graphExpressions([Exp],Free,VarsDict),
%    {NodesGensFilt,EdgesGenFilt,NNFree,NNVarsDict,FirstsGenFilt,LastsGenFilt}=graphGensFilt(GensFilt,NFree,NVarsDict),
%    {
%      NodesExp++NodesGensFilt,
%      EdgesExp++EdgesGenFilt,
%      NNFree,
%      NNVarsDict,
%      FirstsExp++FirstsGenFilt,
%      LastsExp++LastsGenFilt
%    }.





graphMatching(NP,NE,Dict,NodesAcum)->
	io:format("~ngraphMatching: ~w~n ~w~n ~w~n ~w~n",[NP,NE,Dict,NodesAcum]),
	[{node,NP,TypeNP}|_] = [Node||Node={node,NP_,_}<-NodesAcum,NP_==NP],
	[{node,NE,TypeNE}|_] = [Node||Node={node,NE_,_}<-NodesAcum,NE_==NE],
	case {TypeNP,TypeNE} of
		{{term,TermP},{term,TermE}} -> 
	        	case termEquality(TermP,TermE) of
	             		true -> {true,[{edge,NE,NP,data}],Dict};
	             		_ -> 	case TermP of
	                       			{var,_,V} -> 
	                       				case V of
	                       					'_' -> {true,[],Dict};
	                       					_ -> {true,[{edge,NE,NP,data}],Dict++[{V,[NP],[NE]}]}
	                       				end;
	                        		_ -> 	case TermE of
	                                  			{var,_,V} -> 
	                                  				{NodesPM,NodesDecl}=findPMVar(V,Dict),
	                                  				{Return,Edges,DictTemp}=
	                                  					graphMatchingList(NP,NodesPM,Dict,NodesAcum),
	                                  				{Return,[{edge,NodeDecl,NP,summary_data}||NodeDecl<-NodesDecl]
	                                  					++[{edge,NE,NP,summary_data}]
	                                  					++[{edge,NE,NP,data}]++changeSD(Edges),DictTemp};
	                                  			_ -> {false,[],Dict}
	                             			end
	                   		end
	            	end;
	    	{{term,TermP},_} -> 	
	        	case TermP of
	             		{var,_,V}-> 	case V of
	                       		 		'_' -> {true,[],Dict};
	                       		  		_ ->  {true,[{edge,Last,NP,data}||Last <- firstsLasts(TypeNE)],
	                       		  			  Dict++[{V,[NP],[NE]}]}
                 			 	end;
	             		_ -> 	case TypeNE of
	                       			{op,'{}',_,_,_} -> {false,[],Dict};
	                       			{op,'[]',_,_,_} -> {false,[],Dict};
	                       			{function_in,_,_,_,_} -> {false,[],Dict};
	                       			{op,_,_,_,Lasts} -> {true,[{edge,Last,NP,data}||Last <- Lasts],Dict};
	                       			{call,Return} -> {true,[{edge,Return,NP,data}],Dict};
	                       			_ ->  graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum)
	                   		end
	         	end;
	      	{_,{term,TermE}} -> 
	       		case TermE of
	             		{var,_,V} -> 
	             			%io:format("FindPMVar: ~w~n",[findPMVar(V,Dict)]),
	                        	{NodesPM,NodesDecl}=findPMVar(V,Dict),
	                        	{Return,Edges,DictTemp}=graphMatchingList(NP,NodesPM,Dict,NodesAcum),
	                        	{Return,[{edge,NodeDecl,NP,summary_data}||NodeDecl<-NodesDecl]++
	                        		[{edge,NE,NP,summary_data}]++[{edge,NE,NP,data}]++changeSD(Edges),DictTemp};

	             _ -> case TypeNP of
	                       {op,'{}',_,_,_} -> {false,[],Dict};
	                       {op,'[]',_,_,_} -> {false,[],Dict};
	                       _ -> graphMatchingListPattern(firstsLasts(TypeNP),NE,Dict,NodesAcum)
	                  end
	          end;
	        _ -> 
	          case TypeNP of
	               {op,'{}',_,_,_} -> 
	               		case TypeNE  of 
	               			{op,'[]',_,_,_} -> {false,[],Dict};
	               		     	{function_in,_,_,_,_} -> {false,[],Dict};
				     	{call,Return} -> {true,[{edge,Return,NP,data}],Dict};
				     	{op,'{}',_,_,_} -> case graphMatchingListAll(firstsLasts(TypeNP),firstsLasts(TypeNE),
				     							Dict,NodesAcum) of
							   	{true,DEdges,DictTemp} -> {true,DEdges++[{edge,NE,NP,data}],DictTemp};
							        _ -> {false,[],Dict}
							   end;
				     	_ -> graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum)
				 end;
			{op,'[]',_,_,_} -> 
	               		case TypeNE  of 
	               			{function_in,_,_,_,_} -> {false,[],Dict};
				   	{call,Return} -> {true,[{edge,Return,NP,data}],Dict};
				     	{op,'[]',_,_,_} -> 
				     		case graphMatchingListAll(firstsLasts(TypeNP),firstsLasts(TypeNE),Dict,NodesAcum) of
							{true,DEdges,DictTemp} -> {true,DEdges++[{edge,NE,NP,data}],DictTemp};
							_ -> {false,[],Dict}
						end;
				        _ -> graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum)
				end;
			{pm,_,_} -> graphMatchingListPattern(firstsLasts(TypeNP),NE,Dict,NodesAcum);
			_ -> {false,[],Dict}
		  end
	end.


changeSD(Edges)->[{edge,S,T,summary_data}||{edge,S,T,data}<-Edges].

findPMVar(V,Dict)-> 	case [{NodePM,NodeDecl} || {Var,NodeDecl,NodePM} <-Dict,Var==V] of
				[Head|_] -> Head;
				_ -> {[],[]}
	            	end.
	            
	           
graphMatchingList(_,[],Dict,_) -> {false,[],Dict};
graphMatchingList(NP,[NE|NEs],Dict,NodesAcum)->	
    	%io:format("GML: ~w~n",[{NP,NE}]),
	{Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum),
	{Bool2,DataArcs2,Dict3}=graphMatchingList(NP,NEs,Dict2,NodesAcum),
	{Bool1 or Bool2,DataArcs1++DataArcs2,Dict3}. 
	
	
graphMatchingListPattern([],_,Dict,_) -> {false,[],Dict};
graphMatchingListPattern([NP|NPs],NE,Dict,NodesAcum)->	
    	%io:format("GMLP: ~w~n",[{NP,NE}]),
	{Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum),
	{Bool2,DataArcs2,Dict3}=graphMatchingListPattern(NPs,NE,Dict2,NodesAcum),
	{Bool1 or Bool2,DataArcs1++DataArcs2,Dict3}.

graphMatchingListAll([],[],Dict,_) -> {true,[],Dict};	
graphMatchingListAll([],_,Dict,_) -> {false,[],Dict};	
graphMatchingListAll(_,[],Dict,_) -> {false,[],Dict};
graphMatchingListAll([NP|NPs],[NE|NEs],Dict,NodesAcum)->	
    	%io:format("GMLA: ~w~n",[{NP,NE}]),
	{Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum),
	%io:format("GMLA Results: ~w~n",[{Bool1,NPs,NEs}]),
	case Bool1 of 
		true -> {Bool2,DataArcs2,Dict3}=graphMatchingListAll(NPs,NEs,Dict2,NodesAcum),
	            	{Bool2,DataArcs1++DataArcs2,Dict3};
	     	false-> {false,[],Dict}
	end. 


graphMatchingListAllIO([],[],Dict,_) -> {true,[],Dict};	
graphMatchingListAllIO([],_,Dict,_) -> {false,[],Dict};	
graphMatchingListAllIO(_,[],Dict,_) -> {false,[],Dict};
graphMatchingListAllIO([NP|NPs],[NE|NEs],Dict,NodesAcum)->	
    	%io:format("GMLA: ~w~n",[{NP,NE,Dict}]),
	{Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum),
	%io:format("GMLA Results: ~w~n",[{Bool1,DataArcs1,Dict2}]),
	case Bool1 of 
		true -> {Bool2,DataArcs2,Dict3}=graphMatchingListAll(NPs,NEs,Dict,NodesAcum),
	             	{Bool2,DataArcs1++DataArcs2,Dict3};
	     	false-> {false,[],Dict}
	end. 
	

graphMatchingListAll_([],[],Dict,_) -> {true,[],Dict};	
graphMatchingListAll_([],_,Dict,_) -> {true,[],Dict};	
graphMatchingListAll_(_,[],Dict,_) -> {true,[],Dict};
graphMatchingListAll_([NP|NPs],[NE|NEs],Dict,NodesAcum)->	
    	%io:format("GMLA: ~w~n",[{NP,NE}]),
	{Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum),
	%io:format("GMLA Results: ~w~n",[{Bool1,NPs,NEs}]),
	case Bool1 of 
		true -> {Bool2,DataArcs2,Dict3}=graphMatchingListAll_(NPs,NEs,Dict2,NodesAcum),
	            	{Bool2,DataArcs1++DataArcs2,Dict3};
	     	false-> {false,[],Dict}
	end. 	
	
	

lasts({function_in,_,_,_,Lasts}) -> Lasts;
lasts({clause_in,_,Lasts}) -> Lasts;
lasts({'case',_,_,Lasts}) -> Lasts;
lasts({'if',_,_,Lasts}) -> Lasts;
lasts({block,_,_,Lasts}) -> Lasts;
lasts({call,Return}) -> [Return];
lasts({pm,_,Lasts}) -> Lasts;
lasts({op,_,_,_,Lasts}) -> Lasts.

firstsLasts({function_in,_,_,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({clause_in,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({'case',_,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({'if',_,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({block,_,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({call,Return}) -> [Return];
firstsLasts({pm,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({op,_,_,FirstsLasts,_}) -> FirstsLasts.


%leaves(N,Ns,Es) ->
%	Children=getChildren(N,Ns,Es),
%	Leaves=[N_||N_<-Children,getChildren(N_,Ns,Es)==[]],
%	NonLeaves=[N_||N_<-Children,getChildren(N_,Ns,Es)/=[]],
%	Leaves++[Leaf||NonLeaf<-NonLeaves,Leaf<-leaves(NonLeaf,Ns,Es)].
%	
%getChildren(N,Ns,Es)->[N_||{node,N_,_}<-Ns,{edge,NS,NT,control}<-Es,NS==N,NT==N_].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% INPUT & OUTPUT EDGES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

buildInputOutputEdges(_,_,[],_)-> {[],[]};
buildInputOutputEdges(Nodes,Edges,[CallInfo={NCall,NodeCalled,NodesArgs,NodeReturn,Types}|CallsInfo],ClausesInfo) ->
	NodesIn = getApplicableFunctions(Nodes,Edges,[{NodeCalled,NodesArgs,NodeReturn,Types}],true),
	%NewDataEdges=[{edge,CalledNode,NodeReturn,data}||{_,CalledNodes}<-NodesIn,CalledNode<-CalledNodes],
	ApplicableClausesInfo = [{NFIn,CalledNodes,[ClauseInfo||ClauseInfo={NIn,_,_,_,_}<-ClausesInfo,
	                                                        {edge,NFIn_,NIn_,control}<-Edges,
	                                                        NIn==NIn_,NFIn==NFIn_]}
	                         || {NFIn,CalledNodes}<-NodesIn],
	{MatchingClauses,IOEdges}=inputOutputEdges(Nodes,Edges,{NCall,NodesArgs,NodeReturn,Types},ApplicableClausesInfo),
	{PendingCalls,NewEdges}=buildInputOutputEdges(Nodes,Edges,CallsInfo,ClausesInfo),
	{[{CallInfo,MatchingClauses}|PendingCalls],IOEdges ++ NewEdges}.


getApplicableFunctions(_,_,[],_) -> [];
getApplicableFunctions(Nodes,Edges,[{NodeCalled,NodesArgs,NodeReturn,Types}|CallsInfo],First)->
    	[NCType|_]=[NCType_||{node,NC,NCType_}<-Nodes,NC==NodeCalled],
    	%io:format("NodeCalled: ~w ~n",[{NodeCalled,NCType}]),
	NInCalled=
		case NCType of
	  		{term,TermNC} ->
	  	      		case TermNC of
	  	           	%COULD BE IMPROVED (SAME AS CALL) USING TYPE INFO TO REDUCE THE APPLICABLE FUNCTIONS
	  	           		{var,_,_} -> 
	  	             			[{N_in,[NodeCalled]} ||
	  	             				{node,N_in,{function_in,_,Arity,_,_}}<-Nodes,Arity==length(NodesArgs)];
			       		{'fun',_,{function,Name,Arity}} -> 
			         		[{N_in,[NodeCalled]} ||
			         			{node,N_in,{function_in,Name_,Arity_,_,_}}<-Nodes,Name==Name_,
			         			Arity==Arity_,Arity==length(NodesArgs)];
				   	{atom,_,Name} when First ->
			         		[{N_in,[NodeCalled]} ||
			         			{node,N_in,{function_in,Name_,Arity,_,_}}<-Nodes,Name_==Name,
			         			Arity==length(NodesArgs)];
			       		_ -> []
			    	end;
			{function_in,_,Arity,_,_}-> 
				if 
					Arity == length(NodesArgs)-> [{NodeCalled,[]}];
			      		true -> []
			   	end;
			%COULD BE IMPROVED (SAME AS VAR)
			{call,_} -> 
				[{N_in,[NodeCalled]} ||{node,N_in,{function_in,_,Arity,_,_}}<-Nodes,Arity==length(NodesArgs)];
			{pm,_,_} -> 
			  	getApplicableFunctions(Nodes,Edges,
			  		[{NodeCalled_,NodesArgs,NodeReturn,Types}||NodeCalled_<-firstsLasts(NCType)],false);
			{'case',_,_,_} -> 
				getApplicableFunctions(Nodes,Edges,
			              	[{NodeCalled_,NodesArgs,NodeReturn,Types}||NodeCalled_<-firstsLasts(NCType)],false);
			{'if',_,_,_} -> 
			  	getApplicableFunctions(Nodes,Edges,
			                [{NodeCalled_,NodesArgs,NodeReturn,Types}||NodeCalled_<-firstsLasts(NCType)],false);
			{block,_,_,_} ->
			  	getApplicableFunctions(Nodes,Edges,
			              	[{NodeCalled_,NodesArgs,NodeReturn,Types}||NodeCalled_<-firstsLasts(NCType)],false);		  
		    	_ -> []
	  	end,
	NInCallsInfo=getApplicableFunctions(Nodes,Edges,CallsInfo,false),
	[{NIn,NodesCall++NodesCall_}||{NIn,NodesCall}<-NInCallsInfo,{NIn_,NodesCall_}<-NInCalled,NIn_==NIn]
	 	++[{NIn,NodesCall}||{NIn,NodesCall}<-NInCallsInfo,[NIn_||{NIn_,_}<-NInCalled,NIn_==NIn]==[]]
	  	++[{NIn,NodesCall}||{NIn,NodesCall}<-NInCalled,[NIn_||{NIn_,_}<-NInCallsInfo,NIn_==NIn]==[]].
      		%{removeDuplicates(NInCalled++NInCallsInfo),removeDuplicates(DataEdgesCalled++DataEdgesCallsInfo)}.	
      

%-spec inputOutputEdges([node_()],{integer(),[expression()],[integer()],integer()},[[{integer(),[pattern()],[integer()],guard(),integer()}]])->[edge()].
inputOutputEdges(_,_,_,[]) -> {[],[]};
inputOutputEdges(Nodes,Edges,CallInfo,[{FIn,CalledNodes,ClausesFunction}|ClausesFunctions])->
    	{MatchingClauses0,NewEdges}=inputOutputEdgesFunction(Nodes,Edges,CallInfo,CalledNodes,ClausesFunction),
    	MatchingClauses = [{FIn,CalledNodes,ClauseInfo} ||
    				NIn<-MatchingClauses0,ClauseInfo={NIn_,_,_,_,_}<-ClausesFunction,NIn==NIn_],
    	{MatchingClauses_,NewEdges_}=inputOutputEdges(Nodes,Edges,CallInfo,ClausesFunctions),
    	{MatchingClauses++MatchingClauses_,NewEdges++NewEdges_}.	


%-spec inputOutputEdgesFunction([node_()],{integer(),[expression()],[integer()],integer()},[{integer(),[pattern()],[integer()],guard(),integer()}])->	[edge()].
inputOutputEdgesFunction(_,_,_,_,[]) -> [];
inputOutputEdgesFunction(Nodes,Edges,InfoCall={NCall,NodesArgs,NodeReturn,{_,TArgsCall,_}},CalledNodes,
                          	[{NodeClauseIn,NodesPatterns,Guard,Lasts,{_,TArgsClause}}|ClausesInfo])->
	Strong_ = allArgsHold(fun erl_types:t_is_subtype/2,TArgsCall,TArgsClause),
    	Strong = Strong_ and (Guard==[]),
    	Weak =  allArgsHold(fun (T1,T2) -> not erl_types:t_is_none(erl_types:t_inf(T1,T2)) end,TArgsClause,TArgsCall),
    	%io:format("call_clause_strongN_weakN_strongO_weakO ~p~n",[{NCall,NodeClauseIn,Strong,Weak,StrongO,WeakO}]),
    	%io:format("call_clause_strong_weak ~p~n",[{NCall,NodeClauseIn,Strong,Weak}]),
    	if
		Strong -> 
	    	%NOW IS NOT CHECKING WHETHER THERE IS OR NOT A GRAPH MATCHING. IT IS SUPPOSED TO EXIST.
	    		{_,EdgesMatch,_}=graphMatchingListAllIO(NodesPatterns,NodesArgs,[],Nodes), 
	    		{
	    			[NodeClauseIn],
	    			[{edge,getParentControl(CalledNode,Edges),NodeClauseIn,input}||CalledNode<-CalledNodes]
				 %[{edge,CalledNode,NodeClauseIn,input}||CalledNode<-CalledNodes]
	    				++changeEdgeType(EdgesMatch,data,input)
		 			++[{edge,Last,NodeReturn,output}||Last<-Lasts]
		 	};
		Weak -> 
	   	%NOW IS NOT CHECKING WHETHER THERE IS OR NOT A GRAPH MATCHING. IT IS SUPPOSED TO EXIST.
	    		{_,EdgesMatch,_}=graphMatchingListAllIO(NodesPatterns,NodesArgs,[],Nodes), 
	     		{MatchingClauses,NewEdges}=inputOutputEdgesFunction(Nodes,Edges,InfoCall,CalledNodes,ClausesInfo),
	   		{
	   			[NodeClauseIn|MatchingClauses],
	  			[{edge,getParentControl(CalledNode,Edges),NodeClauseIn,input}||CalledNode<-CalledNodes]
	  			%[{edge,CalledNode,NodeClauseIn,input}||CalledNode<-CalledNodes]
		 			++changeEdgeType(EdgesMatch,data,input)
		 			++[{edge,Last,NodeReturn,output}||Last<-Lasts]
		 			++ NewEdges};
		true -> 
	    		inputOutputEdgesFunction(Nodes,Edges,InfoCall,CalledNodes,ClausesInfo)
    	end.

%-spec buildInputEdges([integer()],[integer()])-> [edge()].
changeEdgeType([],_,_)->[];
changeEdgeType([{edge,NS,NT,OldType}|Es],OldType,NewType)->
	[{edge,NS,NT,NewType}|changeEdgeType(Es,OldType,NewType)];
changeEdgeType([E|Es],OldType,NewType)->
	[E|changeEdgeType(Es,OldType,NewType)].
    
    
allArgsHold(_,[],[])->true;
allArgsHold(F,[TCa|TCas],[TCl|TCls])->
  	%io:format("TCa_TCs: ~w ~n",[{[l,l,l],TCa,[l,l,l],TCl,[l,l,l],F(TCa,TCl)}]),
  	F(TCa,TCl) and allArgsHold(F,TCas,TCls).
  
  
%buildOutputEdges(_,_,_,[])->[];
%buildOutputEdges(_,_,Free,[{CallInfo,MatchingClauses}|Rest])->
%	buildOutputEdgesCall(Nodes,Edges,Free,CallInfo,MatchingClauses).
	

%buildOutputEdgesCall(_,_,Free,_,[])->{[],[],Free};	
%buildOutputEdgesCall(Nodes,Edges,Free,{NCall,NodeCalled,NodesArgs,NodeReturn,Types},
%                     [{FIn,CalledNodes,{NodeClauseIn,_,_,_,_}}|MatchingClauses])->
%	[FirstLastClause|_]=[FirstsLasts||{node,NCI,{clause_in,FirstsLasts,_}}<-Nodes,NCI==NodeClauseIn],
%	%Fer fora i que cada clausula tinga asociat un graf, aixina tambe directament se sabria si se sap o no els finals (si te graf o no), i per supost no se farai una faena ja feta repetides voltes
%	{NGraph,EGraph,NFree}=buildReturnGraph(Nodes,Free+1,FirstLastClause),
%	{
%	 [{node,Free,return}|NGraph],
%	 [{edge,NodeReturn,Free,control}]
%	 ++[{edge,CalledNode,Free,data}||CalledNode<-CalledNodes]
%	 ++EGraph,
%	 NFree
%	}.

	
%buildReturnGraph(_,_,Free,_,_[])->{[],[],Free};
%buildReturnGraph(Nodes,Edges,Free,Parent,IsParentReturn,[FirstLastClause|FirstsLastClause])->
%	[TypeN|_] = [Type||{node,N,Type}<-Nodes,N==FirstLastClause],
%	GraphInfo=
%	case TypeN of
%	    {function_in,NomFunc,Arity,_,_} -> {[],[],Free,[Free],[Free],[Free]};
%		{'case',_,_,_} -> buildReturnGraph(Nodes,Edges,Free,firstsLasts(TypeN));
%		{'if',_,_,_} -> buildReturnGraph(Nodes,Edges,Free,firstsLasts(TypeN));
%		{block,_,_,_}-> buildReturnGraph(Nodes,Edges,Free,firstsLasts(TypeN));
%		%{lc,_}-> "list_compr";
%		%{gen,_}->"gen";
%		{call,_} -> ;
%		return -> ;
%		{term,Term} -> {[{node,Free,TypeN}],[],Free+1};
%		{pm,_,_} -> buildReturnGraph(Nodes,Edges,Free,firstsLasts(TypeN));
%		{op,Op,Term,_,_} -> 
%		    case Op of
%		         '{}'-> {Nodes0,Edges0,NFree,FirstsLasts,Lasts}=buildReturnGraph(Nodes,Edges,Free+1,Free,false,firstsLasts(TypeN)),
%		         		{
%		         			[{node,Free,{op,Op,Term,FirstsLasts,Lasts}}]++Nodes0,
%		         			[{edge,FirstLastClause,Free,output},{edge,Parent,Free,control}]++Edges0,
%		         			NFree,
%		         			FirstsLasts,
%		         			Lasts
%		         		};
%		         '[]'-> {Nodes0,Edges0,NFree,FirstsLasts,Lasts}=buildReturnGraph(Nodes,Edges,Free+1,Free,false,firstsLasts(TypeN)),
%		         		{
%		         			[{node,Free,{op,Op,Term,FirstsLasts,Lasts}}]++Nodes0,
%		         			[{edge,FirstLastClause,Free,output},{edge,Parent,Free,control}]++Edges0,
%		         			NFree,
%		         			FirstsLasts,
%		         			Lasts
%		         		};
%		          _ -> {
%		         			[{node,Free,return}],
%		         			[{edge,Parent,Free,control}]++Edges0,
%		         			Free+1,
%		         			[Free],
%		         			[Free]
%		         		}
%	end,
%	buildReturnGraph(Nodes,Edges,Free,FirstsLastClause)
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SUMMARY EDGES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	

%-spec getReachablePatterns([node_()],[edge()],[{integer(),expression(),integer(),[expression()],[integer()],integer()}])-> [integer()].
getReachablePatterns(_,_,[])->[];
getReachablePatterns(Nodes,Edges,[{_,NodesPatterns,_,Lasts,_}|ClausesInfo])->
	Reachables=removeDuplicates(lists:append([reachablesFrom(Last,Nodes,Edges,[])||Last<-Lasts])),
    	[NodePattern||NodePattern<-NodesPatterns,lists:member(NodePattern,Reachables)]++
		getReachablePatterns(Nodes,Edges,ClausesInfo).

%-spec reachablesFrom(integer(),[node_()],[edge()],[integer()])-> [integer()].
reachablesFrom(Node,Nodes,Edges,PreviouslyAnalyzed)->
    	Parents=[NodeO||{edge,NodeO,NodeD,_}<-Edges,NodeD==Node],
    	ChildrenCall= 
    		case [NodeCall||{node,NodeCall,{call,_}}<-Nodes,NodeCall==Node] of
			[]->[];
			_->[NodeD||{edge,NodeO,NodeD,_}<-Edges,NodeO==Node]
		end,
    	removeDuplicates(
    		PreviouslyAnalyzed++
		lists:flatten([reachablesFrom(NodeP,Nodes,Edges,removeDuplicates(PreviouslyAnalyzed++Parents++ChildrenCall++[Node]))
				|| NodeP<-removeDuplicates(Parents++ChildrenCall),not lists:member(NodeP,PreviouslyAnalyzed)]
			     )
			).


%-spec buildSummaryEdges([edge()],[integer()],[{integer(),expression(),integer(),[expression()],[integer()],integer()}]) -> [edge()].

buildSummaryEdges(_,_,[])-> [];
buildSummaryEdges(Edges,NeedPatterns,[{_,_,NodesArgs,NodeReturn}|CallsInfo])->
	buildSummaryEdgesArgs(Edges,NodeReturn,NeedPatterns,NodesArgs)++
	buildSummaryEdges(Edges,NeedPatterns,CallsInfo).

%-spec buildSummaryEdgesArgs([edge()],integer(),[integer()],[integer()])->[edge()].

buildSummaryEdgesArgs(_,_,_,[])->[];
buildSummaryEdgesArgs(Edges,NodeReturn,NeedPatterns,[NodeArg|NodesArgs])->
    removeDuplicates([{edge,NodeArg_,NodeReturn,summary}||
			   {edge,NodeArg_,NodePattern,input}<-Edges,NodeArg_==NodeArg,lists:member(NodePattern,NeedPatterns)]
		     ++buildSummaryEdgesArgs(Edges,NodeReturn,NeedPatterns,NodesArgs)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% AUXILIAR FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	


%-spec varsExpression(expression())->[atom()].

varsExpression({var,_,'_'})-> [];                                                          
varsExpression({var,_,Name})-> [Name];
varsExpression({match,_,E1,E2})-> removeDuplicates(varsExpression(E1)++varsExpression(E2));
varsExpression({tuple,_,Es}) -> removeDuplicates([Var||E<-Es,Var<-varsExpression(E)]);
varsExpression({cons,_,EH,ET}) -> removeDuplicates(varsExpression(EH)++varsExpression(ET));
varsExpression({op,_,_,E1,E2})-> removeDuplicates(varsExpression(E1)++varsExpression(E2));
varsExpression({op,_,_,E})-> varsExpression(E);
varsExpression(_)-> [].

%-spec getUsedDefined(expression(),varDict())->{[atom()],[atom()]}.
%getUsedDefined({match,_,E1,E2},VarsDict)-> 
%    {Used,Defined}=getUsedDefined(E2,VarsDict),
%    {removeDuplicates([Var||Var<-varsExpression(E1),[Var1 || {Var1,_}<-VarsDict,Var1==Var]==[Var]]++Used),
%     removeDuplicates([Var||Var<-varsExpression(E1),[Var1 || {Var1,_}<-VarsDict,Var1==Var]==[]]++Defined)};
%getUsedDefined({tuple,_,Es},VarsDict) -> getUsedDefinedList(Es,VarsDict);
%getUsedDefined({cons,_,EH,ET},VarsDict) ->getUsedDefinedList([EH,ET],VarsDict);
%getUsedDefined({op,_,_,E1,E2},VarsDict) -> getUsedDefinedList([E1,E2],VarsDict); 
%getUsedDefined({op,_,_,E},VarsDict)-> getUsedDefined(E,VarsDict);
%getUsedDefined({var,_,'_'},_)-> {[],[]};                                                          
%getUsedDefined({var,_,Name},_)-> {[Name],[]};
%getUsedDefined(_,_)->{[],[]}.
%
%%-spec getUsedDefinedList([expression()],varDict())->{[atom()],[atom()]}.
%getUsedDefinedList([],_)->{[],[]};
%getUsedDefinedList([E|Es],VarsDict)->
%    {UsedE,DefinedE}=getUsedDefined(E,VarsDict),
%    {UsedEs,DefinedEs}=getUsedDefinedList(Es,VarsDict),
%    {removeDuplicates(UsedE++UsedEs),removeDuplicates(DefinedE++DefinedEs)}.

%-spec buildCallsInfo([{node,integer(),node_type()}],[edge()],[integer()])->[{integer(),expression(),integer(),[expression()],[integer()],integer()}].
buildCallsInfo(_,_,[])->[];
buildCallsInfo(Nodes,Edges,[NCall|NCalls])->
	Children=[Node||{edge,NCall_,Node,control}<-Edges,{node,Node_,_}<-Nodes,NCall==NCall_,Node_==Node],
    	NodeCalled=lists:min(Children),
    	NodeReturn=lists:max(Children),
    	%[Called|_] = [Exp||{node,NodeCalled_,{expression,Exp}}<-Nodes,NodeCalled_==NodeCalled],
    	NodesArgs=lists:sort(lists:subtract(Children,[NodeCalled,NodeReturn])),
    	%Args=[Exp||NodeArg<-NodesArgs,{node,NodeArg_,{expression,Exp}}<-Nodes,NodeArg==NodeArg_],
    	%[NodeReturn|_]=[Node||{edge,NCall_,Node,control}<-Edges,{node,Node_,return}<-Nodes,NCall==NCall_,Node_==Node],
    	[{NCall,NodeCalled,NodesArgs,NodeReturn}|buildCallsInfo(Nodes,Edges,NCalls)].


%-spec buildClausesInfo([node_()],[edge()],[integer()]) -> [[{integer(),[pattern()],[integer()],integer(),integer()}]].
%buildClausesInfo(_,_,[],_)-> [];
%buildClausesInfo(Nodes,Edges,[NIn|NIns],ClausesTypeInfo) ->
%    NodesClauses = [Node || {edge,NIn_,Node,control}<-Edges,NIn_==NIn],
%	%io:format("~w ~n",[{NIn,NodesClauses}]),
%    [buildClauseInfo(Nodes,Edges,NodesClauses,ClausesTypeInfo)]++buildClausesInfo(Nodes,Edges,NIns,ClausesTypeInfo).

%-spec buildClauseInfo([{node,integer(),node_type()}],[edge()],[integer()]) -> [{integer(),[pattern()],[integer()],integer(),integer()}].
						%-spec buildClauseInfo([node_()],[edge()],[integer()]) -> [{integer(),[pattern()],[integer()],integer(),integer()}].
buildClauseInfo(_,_,[],_)-> [];	
buildClauseInfo(Nodes,Edges,[NClause|NClauses],ClausesTypeInfo)->
   	[NGuard|NsPat_]=lists:reverse(lists:sort([Child||{edge,NClause_,Child,control}<-Edges,NClause==NClause_])),
    	NodesPatterns=lists:reverse(NsPat_),
    	[Guard|_]=[Guard_||{node,NGuard_,{guards,Guard_}}<-Nodes,NGuard_==NGuard],
    	[Type|_]=[{RetType,ArgsTypes}||{NClause_,RetType,ArgsTypes}<-ClausesTypeInfo,NClause_==NClause],
    	[Lasts|_]=[Lasts_||{node,NClause_,{clause_in,_,Lasts_}}<-Nodes,NClause_==NClause],
	%io:format("~w~n",[{NClause,NodesPatterns,Guard,Type}]),
    	[{NClause,NodesPatterns,Guard,Lasts,Type}|buildClauseInfo(Nodes,Edges,NClauses,ClausesTypeInfo)].


addTypeInfo([],_,_)->[];
addTypeInfo([{NCall,NodeCalled,NodesArgs,NodeReturn}|CallsInfo],TypeInfo,Id)->
  	TC=list_to_atom("transformed_call"++integer_to_list(Id)),
  	%io:format("TC: ~p~n",[TC]),
  	ListTypes_= [{RetType,lists:split(length(NodesArgs),ArgsTypes_)}||{TC_,_,{RetType,ArgsTypes_},_}<-TypeInfo,TC_==TC],
  	ListTypes = [{TR,TArgs,Rest}||{TR,{TArgs,Rest}}<-ListTypes_],
  	[Type|_]=ListTypes,
  	[{NCall,NodeCalled,NodesArgs,NodeReturn,Type}|addTypeInfo(CallsInfo,TypeInfo,Id+1)].

getClausesTypeInfo([],_)->[];  
getClausesTypeInfo([NIn|NIns],[{TC,_,{RetType,ArgsTypes},_}|InfoType])->
   	case lists:suffix("CLAUSE",atom_to_list(TC)) of
        	true -> [{NIn,RetType,ArgsTypes}|getClausesTypeInfo(NIns,InfoType)];
        	_ -> getClausesTypeInfo([NIn|NIns],InfoType)
   	end.


-spec removeDuplicates(list()) -> list().
removeDuplicates(List) -> sets:to_list(sets:from_list(List)).

termEquality({integer,_,T},{integer,_,T})->true;
termEquality({atom,_,T},{atom,_,T})->true;
termEquality({float,_,T},{float,_,T})->true;
termEquality({string,_,T},{string,_,T})->true;
termEquality(_,_)->false.



getParentControl(Node,Edges) ->
	%io:format("~p ~n ~p ~n ",[Node,Edges]),
	[Parent|_]=[Parent_||{edge,Parent_,Node_,control}<-Edges,Node_==Node],
	Parent.

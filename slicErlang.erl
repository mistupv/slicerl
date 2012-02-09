%c(slicErlang),c(slicErlangDot),slicErlang:start(0),slicErlangDot:start(0).
%c(slicErlang),c(slicErlangDot),c(slicErlangSlice),slicErlang:start(0),slicErlangDot:start(0),slicErlangSlice:start(0).

-module(slicErlang).

-export([start/1,graphForms/4]).


start(_) ->
	{ok,Abstract} = smerl:for_file("temp.erl"),
    	Forms=lists:reverse(smerl:get_forms(Abstract)),
    	{Nodes,Edges,_,_} = graphForms(Forms,0,[],[]),
	
    	TypeInfo=slicErlangType:getFunTypes(Forms,Abstract),
    	CallsInfo = lists:sort(buildCallsInfo(Nodes,Edges,[Node_||{node,Node_,{call,_}}<-Nodes])),
    	CallsInfoWithTypes = addTypeInfo(CallsInfo,TypeInfo,0),
    	AllProgramClauses = [NCIn||{node,NCIn,{clause_in,_,_}}<-Nodes,
                               [NFIn||{node,NFIn,{function_in,_,_,_,_}}<-Nodes,
                                      {edge,NFIn_,NCIn_,control}<-Edges,
                                      NFIn==NFIn_,NCIn_==NCIn] /= [] ],
    	ClausesTypeInfo=getClausesTypeInfo(AllProgramClauses,TypeInfo),
    	ClausesInfoWithTypes = buildClauseInfo(Nodes,Edges,AllProgramClauses,ClausesTypeInfo),
    	{_,InputOutputEdges} = buildInputOutputEdges(Nodes,Edges,CallsInfoWithTypes,ClausesInfoWithTypes),
    	ReachablePatterns = getReachablePatterns(Nodes,Edges,ClausesInfoWithTypes),
    	SummaryEdges = buildSummaryEdges(Edges++InputOutputEdges,ReachablePatterns,CallsInfo),
   	
   	NEdges = Edges++InputOutputEdges++SummaryEdges,
    
    	{ok, DeviceSerial} = file:open("temp.serial", [write]),
    	io:write(DeviceSerial,{Nodes,NEdges}),
    	ok = file:close(DeviceSerial).








%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GRAPH FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
graphForms([],Free,_,NodesAcum)->{[],[],Free,NodesAcum};
graphForms([{function,_,Name,Arity,Clauses}|Funs],Free,VarsDict,NodesAcum) ->
	{NodesClauses,EdgesClauses,NFree,_,Firsts,Lasts,FLasts,_,NodesAcumN,_} = 
	                               graphClauses(Clauses,Free+1, VarsDict, NodesAcum, func,[]),
    	{NodesForms,EdgesForm,NNFree,NodesAcumNN} = graphForms(Funs,NFree,VarsDict,NodesAcumN),
    	N_in = {node,Free,{function_in,Name,Arity,FLasts,Lasts}},
    	{ 
      		[N_in]++NodesClauses++NodesForms,
      		EdgesClauses++EdgesForm++[{edge,Free,First,control}||First <- Firsts],
      		NNFree,
      		NodesAcumNN++[N_in]
    	};
graphForms([_|Funs],Free,VarsDict,NodesAcum)->graphForms(Funs,Free,VarsDict,NodesAcum).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GRAPH CLAUSES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
graphClauses([],Free,VD,NodesAcum,_,_)->	{[],[],Free,VD,[],[],[],[],NodesAcum,[]};
graphClauses([{clause,_,Patterns,Guards,Body}|Clauses],Free0,VD0,NodesAcum,From,ClausesAcum) ->
    	case From of
    		func -> Type=pat;
    		_ -> Type=patArg
    	end,
    	{N1,E1,Free1,VD1,F1,_,_,NodesAcumN} = graphExpressions(Patterns,Free0+1,VD0,Type,NodesAcum),
       	VD2=VD1++[{Var,NodesDecl,NodesPM} ||
       			{Var,NodesDecl,NodesPM}<-VD0,[Var1||{Var1,_,_}<-VD1,Var1==Var]==[]],
    	{N2,E2,Free2,NodesAcumNN} = graphGuards(Guards,Free1,VD2,NodesAcumN),
    	{N3,E3,Free3,VD3,F2,L2,FL2,NodesAcumNNN}=graphExpressionsLast(Body,Free2+1,VD2,exp,NodesAcumNN),
	N_body=[{node,Free2,{body,Body}}],
    	EdgeBody=[{edge,Free1,Free2,control}], %del node guarda al node body
    	EdgesBody_Body=[{edge,Free2,NE,control}||NE<-F2],%del node body als first del body	
    	%Buscar els nodes calls asi que hi han en N3
    	{N4,E4,Free4,VD4,F3,L3,FL3,FC3,NodesAcumNNNN,ClausesAcumN} = 
    			graphClauses(Clauses,Free3,VD0,NodesAcumNNN,From,ClausesAcum++[{Free0,getNumNodes(N1)}]),
    	N_in = {node,Free0,{clause_in,FL2,L2}},
    	case From of
    		func -> EdgesLinkClauses=edgesLinkClauses(
    				getNumNodes(N_body),getNumNodes(N1),ClausesAcum,VD3,NodesAcumNNNN++[N_in]);
    		exp_case -> EdgesLinkClauses=edgesLinkClauses(
    				getNumNodes(N_body),getNumNodes(N1),ClausesAcum,VD3,NodesAcumNNNN++[N_in]);
    		exp_if -> EdgesLinkClauses=edgesClausesAll(getNumNodes(N_body),getNumNodes(N1),ClausesAcum)
    	end,
    	EdgesPatternGuard=[{edge,NP,Free1,data} ||
    			       {node,NP,{term,Term}} <- N1,
    			       [NP1 ||
    			       		{node,NP1,{term,Term1}} <- N1,
    			                NP1 /=NP,
    			 	        sets:size(sets:intersection(sets:from_list(varsExpression(Term)),
    			 	        sets:from_list(varsExpression(Term1))))/=0] 
    			 	/=[]],
    	{
      	    [N_in]++N1++N2++N3++N4++N_body,
     	    removeDuplicates(E1++E2++E3++E4
     	        ++EdgeBody
     	        ++EdgesLinkClauses
	        ++[{edge,Free0,Free1,control}] %Clausula amb la guarda
		++[{edge,Free1,Free0,data}]
		++[{edge,Free0,NP,control} || NP<-F1]
		++EdgesPatternGuard
		++[{edge,NP,Free1,data} ||
			{node,NP,_}<-N1,
			[NP_ || {node,NP_,{term,{var,_,_}}}<-N1, NP_==NP]  ==[]]
		++EdgesBody_Body),
      	    Free4,
      	    VD3++VD4,
      	    [Free0]++F3,
            L2++L3,
            FL2++FL3,
            F1++FC3,
            NodesAcumNNNN++[N_in]++[N_body],
            ClausesAcumN
    	}.
    	
%%%%%%%%%%%%%%%%%%%%%%%%  edgesLinkClauses  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
edgesLinkClauses([],_,_,_,_) -> [];
edgesLinkClauses(_,_,[],_,_) -> []; 
edgesLinkClauses([N_body],Patterns,[{N_in,PatternsAcum}|ClausesAcum],Dict,NodesAcum) -> 
	{Res,_,_}=graphMatchingListAllLinkClauses(Patterns,PatternsAcum,Dict,NodesAcum,false),
	case Res of
	      true -> [{edge,N_in,N_body,data}]
	              ++ edgesLinkClauses([N_body],Patterns,ClausesAcum,Dict,NodesAcum);
	      _ -> edgesLinkClauses([N_body],Patterns,ClausesAcum,Dict,NodesAcum)
	end.

%%%%%%%%%%%%%%%%%%%%%%%%  edgesClausesAll  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
edgesClausesAll([],_,_) -> [];
edgesClausesAll(_,_,[]) -> []; 
edgesClausesAll([N_body],Patterns,[{N_in,_}|ClausesAcum]) -> 
		[{edge,N_body,N_in,data}]++edgesClausesAll([N_body],Patterns,ClausesAcum).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GRAPH GUARDS & TERMS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
graphGuards(Guards,Free,VarsDict,NodesAcum) -> 
    	Vars = removeDuplicates(lists:flatten([Var||Guard <- Guards,Var<-lists:map(fun varsExpression/1,Guard)])),
    	N_guard = {node,Free,{guards,Guards}},
    	{
      		[N_guard],
      		[{edge,Node,Free,data} ||
      			Var <- Vars,
      			{VarD,NodesDecl,_} <- VarsDict,
      			Var==VarD,
      			Node<-NodesDecl],
      		Free+1,
     		NodesAcum++[N_guard]
    	}.

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
	






%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%    GRAPH EXPRESSIONS         %%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
graphExpression(Term={var,_,V},Free,VarsDict,pat,NodesAcum)->
	{Ns,_,NFree,_,First,Lasts,NodesAcumN}=graphTerm(Term,Free,VarsDict,NodesAcum),
        {EdgeUse,NVarsDict}=
            case V of
        	'_' -> {[], VarsDict};
        	 _ ->
		    case existVarDict(V,VarsDict) of
			true -> 	                       		    	
			    {[{edge,NodeDecl,Free,data} ||
			                		{VarD,NDs,_} <- VarsDict,
			                		NodeDecl<-NDs,
			                       		V==VarD],
			     VarsDict};
			_ -> {[],VarsDict++[{V,[Free],undef}]}
		    end
	    end,
	{Ns,EdgeUse,NFree,NVarsDict,
	First,Lasts,NodesAcumN};
graphExpression(Term={var,_,V},Free,VarsDict,patArg,NodesAcum)->
	{Ns,_,NFree,_,First,Lasts,NodesAcumN}=graphTerm(Term,Free,VarsDict,NodesAcum),
	{Ns,[],NFree,VarsDict++[{V,[Free],[Free]}],
	First,Lasts,NodesAcumN};
graphExpression(Term={var,_,V},Free,VarsDict,exp,NodesAcum)->
	{Ns,_,NFree,_,First,Lasts,NodesAcumN}=graphTerm(Term,Free,VarsDict,NodesAcum),
	{Ns,
	 [{edge,NodeDecl,Free,data}||{VarD,[NodeDecl|_],_} <- VarsDict,V==VarD],
	 NFree,VarsDict,First,Lasts,NodesAcumN};
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
		E1++ [{edge,Free,First,control}||First <- F1],
		NFree,
		NVarsDict,
		[Free],
		L1,
		NodesAcumN++[N_tuple]
	};
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphExpression(Term={'if',_,Cs0},Free,VarsDict,exp,NodesAcum)->
    	{NodesClauses,EdgesClauses,NFree,NVarsDict,FirstsClauses,LastsClauses,FLasts,_,NodesAcumN,_} =
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
    	{_,EdgesPM,NNNVarsDict}=graphMatchingListPattern(FPat,Free+1,NNVarsDict,NodesAcumNNN,false),
    	{
      		[N_case]++NodesE++NodesClauses,
      		EdgesE
      			++EdgesClauses
      			++EdgesPM
       			++[{edge,Free,First,control}||First <- FirstsE]
       			++[{edge,Free,FirstC,control}||FirstC <- FirstsClauses],
      		NNFree,
      		NNNVarsDict,
     		[Free],
      		LastsClauses,
      		NodesAcumNNN
    	};
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphExpression(Term={'fun',_,Body},Free,VarsDict,exp,NodesAcum)->
    	case Body of
	  	{clauses,FCs} ->
	  		[{clause,_,Patterns,_,_}|_]=FCs,
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphExpression({call,_,F0,As0},Free,VarsDict,exp,NodesAcum)->
    	{NodesE,EdgesE,NFree,NVarsDict,FirstsE,_,NodesAcumN}=graphExpression(F0,Free+1,VarsDict,exp,NodesAcum),
    	{NodesEs,EdgesEs,NNFree,NNVarsDict,FirstsEs,_,_,NodesAcumNN}=
    				graphExpressions(As0,NFree,NVarsDict,exp,NodesAcumN),
    	N_call = {node,Free,{call,NNFree}},
    	N_return = {node,NNFree,return},
    	{
      		[N_call,N_return]++NodesE++NodesEs,
      		EdgesE
      			++EdgesEs
      			++[{edge,Free,First,control} || First <- (FirstsE++FirstsEs)]
      			++[{edge,Free,NNFree,control}]
      			++[{edge,Free+1,Free,data}],
      		NNFree+1,
      		NNVarsDict,
      		[Free],
      		[NNFree],
      		NodesAcumNN++[N_call,N_return]
    	};
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphExpression({match,_,P0,E0},Free,VarsDict,PatExp,NodesAcum)->
    	{NodesP,EdgesP,NFree,NVarsDict,FirstsP,LastP,NodesAcumN}=graphExpression(P0,Free+1,VarsDict,pat,NodesAcum),
    	{NodesE,EdgesE,NNFree,NNVarsDict,FirstsE,LastE,NodesAcumNN}=
    			graphExpression(E0,NFree,NVarsDict,PatExp,NodesAcumN),
	N_match = 
	    	case PatExp of
	    		exp -> {node,Free,{pm,[NFree],LastE}};
	    		_ -> {node,Free,{pm,[Free+1,NFree],LastP++LastE}}
	    	end,
	NodesAcumNNN = NodesAcumNN++[N_match],
	{Res,EdgesPMAux,NNNVarsDict}=
		case PatExp of
	    		exp -> graphMatching(Free+1,NFree,NNVarsDict,NodesAcumNNN,PatExp);
	    		_ -> {true,[], NNVarsDict}
	    	end,
    	case Res of
	    	true -> EdgesPM=EdgesPMAux;
	    	_ -> EdgesPM=[]
    	end,
    	{
      		[N_match]
      			++NodesP
      			++NodesE,
      		EdgesP
      			++EdgesE
      			++EdgesPM
      			++[{edge,Free,First,control}||First <- (FirstsP++FirstsE)],
      		NNFree,
      		NNNVarsDict,
      		[Free],
      		case PatExp of
      			exp -> LastE;
      			_ -> LastP++LastE
      		end,
      		NodesAcumNNN
    	};
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphExpression(Term={op,_,Op,A0},Free,VarsDict,exp,NodesAcum)->
    	{Nodes,Edges,NFree,NVarsDict,Firsts,Lasts,NodesAcumN}=graphExpression(A0,Free+1,VarsDict,exp,NodesAcum),
    	N_op = {node,Free,{op,Op,Term,[Free+1],Lasts}},
    	{
      		[N_op]++Nodes,
      		Edges
      			++[{edge,Free,First,control}||First <- Firsts],
      		NFree,
      		NVarsDict,
      		[Free],
      		Lasts,
      		NodesAcumN ++ [N_op]
    	};
    	
graphExpression(Term={op,_,Op,A0,A1},Free,VarsDict,exp,NodesAcum)->
    	{Nodes,Edges,NFree,NVarsDict,Firsts,Lasts,NodesAcumN}=graphExpression(A0,Free+1,VarsDict,exp,NodesAcum),
    	{Nodes1,Edges1,NNFree,NNVarsDict,Firsts1,Lasts1,NodesAcumNN} = 
    				graphExpression(A1,NFree,VarsDict,exp,NodesAcumN),
    	N_op = {node,Free,{op,Op,Term,[Free+1,NFree],Lasts++Lasts1}},
    	{
      		[N_op] 
      			++Nodes
      			++Nodes1,
      		Edges
      			++Edges1
      			++[{edge,Free,First,control}||First <- Firsts++Firsts1],
      		NNFree,
      		NVarsDict ++ NNVarsDict,
      		[Free],
      		Lasts ++ Lasts1,
      		NodesAcumNN ++ [N_op]
    	}; 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphExpression({lc,LINE,E,GensFilt},Free,VarsDict,PatExp,NodesAcum)->
	N_lc = {node,Free,{lc,{lc,LINE,E,GensFilt}}},
	{NodesGensFilt,EdgesGensFilt,NFree,NVarsDict,FirstGensFilt,LastsGensFilt,NodesAcumN} = 
						graphGensFilt(GensFilt,Free+1,VarsDict,PatExp,NodesAcum),
	{NodesExpLC,EdgesExpLC,NNFree,_,FirstsExpLC,_,NodesAcumNN} = 
						graphExpression(E,NFree,NVarsDict,PatExp,NodesAcumN),
	
	LastsGens2ExpAux = [{edge,Last,First,control}||First <- FirstsExpLC , Last <-LastsGensFilt],
	case LastsGens2ExpAux of
		[] -> LastsGens2Exp = [{edge,Free,First,control}||First <- FirstsExpLC];
		_ -> LastsGens2Exp = LastsGens2ExpAux
	end,
    
	{
		[N_lc]
			++ NodesGensFilt 
			++ NodesExpLC,
		EdgesGensFilt 
			++ [{edge,Free,First,control}||First <- FirstGensFilt] %lc -> first dels gens
			++ EdgesExpLC 
			++ LastsGens2Exp, %del ultim del generador al first de la expresió
		NNFree,
		NVarsDict,
		[Free],
		FirstsExpLC,
		NodesAcumNN ++ [N_lc]
	}.

%%%%%%%%%%%%%%%%%%%%%%%%  graphGensFilt  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphGensFilt([],Free,VarsDict,_,NodesAcum)-> {[],[],Free,VarsDict,[],[],NodesAcum};
graphGensFilt([{generate,_,Pattern,Exp}|GensFilt],Free,VarsDict,PatExp,NodesAcum)-> 
	{NodesExp,EdgesExp,NFree,NVarsDict,_,LastsExp,NodesAcumN}=
			graphExpression(Exp,Free,VarsDict,PatExp,NodesAcum),
	{NodesPattern,EdgesPattern,NNFree,NNVarsDict,FirstPattern,NodesAcumNN}=
			graphPatternsLC([Pattern],NFree,NVarsDict,PatExp,NodesAcumN),
	{NodesGensFilt,EdgesGenFilt,NNNFree,NNNVarsDict,FirstsGenFilt,LastsGenFilt,NodesAcumNNN}=
			graphGensFilt(GensFilt,NNFree,NNVarsDict,PatExp,NodesAcumNN),
	{
		NodesExp
		    ++ NodesPattern
		    ++ NodesGensFilt,
		EdgesExp 
		    ++ EdgesPattern 
		    ++ [{edge,LastExp,First,control}||LastExp<- LastsExp,First <- FirstPattern] 
		    ++ EdgesGenFilt,
		NNNFree,
		NNNVarsDict,
		[Free] ++ FirstsGenFilt,
		LastsGenFilt,
		NodesAcumNNN
	};
graphGensFilt([Exp|GensFilt],Free,VarsDict,PatExp,NodesAcum)-> 
	{NodesGuard,EdgesGuard,NFree,NodesAcumN}=graphGuards([[Exp]],Free,VarsDict,NodesAcum),
	{NodesGensFilt,EdgesGenFilt,NNFree,NNVarsDict,FirstsGenFilt,LastsGenFilt,NodesAcumNN}=
					graphGensFilt(GensFilt,NFree,VarsDict,PatExp,NodesAcumN),
	{
	  NodesGuard
	  	++NodesGensFilt,
	  EdgesGuard
	  	++EdgesGenFilt,
	  NNFree,
	  NNVarsDict,
	  [Free] ++ FirstsGenFilt,
	  [Free] ++ LastsGenFilt,
	  NodesAcumNN
	}.
%%%%%%%%%%%%%%%%%%%%%%%%  graphPatternsLC  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphPatternsLC([],Free,VarsDict,_,NodesAcum) -> {[],[],Free,VarsDict,NodesAcum};
graphPatternsLC([Pattern],Free,VarsDict,PatExp,NodesAcum) -> 
    {N1,E1,Free1,VD1,F1,_,_,_} = graphExpressions([Pattern],Free,VarsDict,PatExp,NodesAcum),
    {
	N1,
	removeDuplicates([{edge,Node,Free,data} || 
					Var <- varsExpression(Pattern),
					{Var1,Nodes} <- VarsDict,
					Var1==Var,
					Node<-Nodes]
			   ++E1),
	Free1,
	VD1++[{Var,[Free],[Free]}||
				Var <- varsExpression(Pattern),
				[Var1||{Var1,_,_}<-VD1,
				Var1==Var]==[]],
	F1,
	NodesAcum
    }.


%%%%%%%%%%%%%%%%%%%%%%%%  graphExpressions  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphExpressions([],Free,VarsDict,_,NodesAcum) -> {[],[],Free,VarsDict,[],[],[],NodesAcum};
graphExpressions([Expression|Expressions],Free,VarsDict,PatExp,NodesAcum) ->
	{NodesE,EdgesE,NFree,NVarsDict,FirstsE,LastsE,NodesAcum2}=
			graphExpression(Expression,Free,VarsDict,PatExp,NodesAcum),
    	{NodesExpressions,EdgesExpression,NNFree,NNVarsDict,Firsts,Lasts,FLasts,NodesAcum3} =
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

%%%%%%%%%%%%%%%%%%%%%%%%  graphExpressionsLast  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Soles en cosos de funcions, blocks....
graphExpressionsLast([],Free,VarsDict,_,NodesAcum) -> {[],[],Free,VarsDict,[],[],[],NodesAcum};
graphExpressionsLast([Expression|Expressions],Free,VarsDict,PatExp,NodesAcum) ->
	{NodesE,EdgesE,NFree,NVarsDict,FirstsE,LastsE,NodesAcum2}=
			graphExpression(Expression,Free,VarsDict,PatExp,NodesAcum),
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
    
    
    
    
    





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%      GRAPH MATCHING          %%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
graphMatching(NP,NE,Dict,NodesAcum,From)->
    [{node,NP,TypeNP}|_] = [Node||Node={node,NP_,_}<-NodesAcum,NP_==NP],
    [{node,NE,TypeNE}|_] = [Node||Node={node,NE_,_}<-NodesAcum,NE_==NE],
    %io:format("~ngraphMatching: ~w~n ~w~n ~w~n ~w~n~w~n",[NP,NE,TypeNP,TypeNE,Dict]),

	case {TypeNP,TypeNE} of      
	    {{term,TermP},{term,TermE}} ->    %Los dos son términos
		case termEquality(TermP,TermE) of      %iguales?
	            true -> %{true,[{edge,NE,NP,data}],Dict};
	            	    {true,[],Dict};
	            _ ->    
	                case TermP of
	                    {var,_,V} ->      %No son iguales i PM es var
	                        case V of
	                            '_' ->  
                       	                case From of 		%Es unua llamada desde la construcción de las IO edges
                       			    io -> {true,[{edge,NE,NP,data}],Dict};
                       			    _ -> {true,[],Dict}
                       		        end;
	                       	    _ -> 	
	                       		case existVarDictGM(V,Dict,NP) of
	                       		    true -> %Variable definida
	                       		    	%{NodesPM,_}=findPMVar(V,Dict),
	                       			%EdgeUse = [{edge,NodeDecl,NP,data}||
	                       			%	                   {VarD,[NodeDecl|_],_} <- Dict,
	                       			%	                   V==VarD],
	                       			%{Return,_,_} = graphMatchingList(NP,NodesPM,Dict,NodesAcum,From),
	                       			%{Return,EdgeUse,Dict};	                       			
	                       			{true,[],Dict};
	                       		    _ ->     %Se esta definiendo aqui
	                       		        DictTemp=[{V_,DV,[NE]}||{V_,DV,undef}<-Dict,V_==V]
	                       		        	++[DE||DE={V_,_,_}<-Dict,V_/=V],
	                       		    	EdgeUse=[{edge,NE,NP,data}],
	                     			%DictTemp=Dict++[{V,[NP],[NE]}],
	                     			{true,EdgeUse,DictTemp}
	                       		end
	                       	end;	
	                    _ -> 
	                        case TermE of  
	                            {var,_,V} ->    %No son iguales, PM NO es var i PE es var ---> a=X   (X tiene que estar definida)
	                            	{NodesPM,_}=findPMVar(V,Dict),
	                                {Return,_,DictTemp}=graphMatchingList(NP,NodesPM,Dict,NodesAcum,From),
%	                                {Return,[{edge,NodeDecl,NP,summary_data}||NodeDecl<-NodesDecl]
%	                                  		%++[{edge,NE,NP,summary_data}]
%	                                  		++[{edge,NE,NP,data}]++
%	                                  		%changeEdgeTypeNotAcum(Edges,data,summary_data)ç
							%++changeEdgeTypeNotAcum(Edges,dataAux,data),DictTemp};
					{Return,[],DictTemp};
	                            _ -> {false,[],Dict}
	                        end
	                end
	        end;
            {{term,TermP},_} ->  %El PM es un termino i PE no.	
	        case TermP of
	            {var,_,V}-> 
	            	case V of  %PM es var
	                    '_' -> 
	                    	case From of
	                      	    io -> {true,[{edge,NE,NP,data}],Dict};
	                            _ -> {true,[],Dict}
	                       	end;
	                    _ -> 
	                       	case existVarDictGM(V,Dict,NP) of   
	                            true ->  		%Variable ya declarada
	                       		%EdgeUse=[{edge,NodeDecl,NP,data} ||
	                       		%		{VarD,[NodeDecl|_],_}<-Dict,
	                       		%		V==VarD],
	                       		EdgeUse=[],
	                       		DictTemp=Dict;
	                       	    _ ->    		%Se esta declarando la variable
	                       		EdgeUse=[{edge,Last,NP,data}||Last <- lasts(TypeNE)],%++[{edge,NP,NE,data}],
	                    	        DictTemp=[{V_,DV,[NE]}||{V_,DV,undef}<-Dict,V_==V]
	                       		        ++[DE||DE={V_,_,_}<-Dict,V_/=V]
	                     		%DictTemp=Dict++[{V,[NP],[NE]}]
	                       	end,
	                       	{true,EdgeUse,DictTemp}
                	end;
	             _ ->   %El PM No es variable
	             	case TypeNE of 
                            {op,'{}',_,_,_} -> {false,[],Dict};
                      	    {op,'[]',_,_,_} -> {false,[],Dict};
                       	    {function_in,_,_,_,_} -> {false,[],Dict};
                       	    {op,_,_,_,Lasts} -> {true,[{edge,Last,NP,data}||Last <- Lasts],Dict};
                       	    {call,Return} -> {true,[{edge,Return,NP,data}],Dict};
                       	    _ ->  
                       	        graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum,From)
	               end
	        end;
	    {_,{term,TermE}} -> %PM no es termino pero PE si
		case TermE of
		    {var,_,V} -> %PE es var
			 {NodesPM,NodesDecl}=findPMVar(V,Dict),
			 %[{node,NE,TypeNE}|_] = [Node||Node={node,NE_,_}<-NodesAcum,NE_==NE]
                	 {Return,Edges,DictTemp}=graphMatchingList(NP,NodesPM,Dict,NodesAcum,From),
	                 {
	                     Return,
	                     [{edge,NodeDecl,Last,summary_data} ||  
	                     		NodeDecl<-NodesDecl,
	                     		Last<-lasts(TypeNP),
	                     		not hasValue(Last,NodesAcum, Dict)]
	                         %%++[{edge,NE,NP,summary_data}]
	                         ++[{edge,NE,Last,data} || 
	                         	Last<-lasts(TypeNP),
	                         	not hasValue(Last,NodesAcum, Dict)]
	                         ++Edges,	
	                         %%++changeEdgeTypeNotAcum(Edges,data,summary_data)
	                         DictTemp
	                 };
		    	%end;
		    _ ->     %PE no es Var
	             	case TypeNP of
	                    {op,'{}',_,_,_} -> {false,[],Dict};
	                    {op,'[]',_,_,_} -> {false,[],Dict};
	                    _ -> 
			        graphMatchingListPattern(firstsLasts(TypeNP),NE,Dict,NodesAcum,From)
	                end
		end;
            _ ->    %Ni PM es var ni PE tampoco --> Son listas, tuplas o PM
	        case TypeNP of
		    {op,'{}',_,_,_} ->    
	                case TypeNE  of 
	      		    {op,'[]',_,_,_} -> {false,[],Dict};
	              	    {function_in,_,_,_,_} -> {false,[],Dict};
			    {call,Return} -> {true,[{edge,Return,NP,data}],Dict};
			    {op,'{}',_,_,_} ->
			        FLastsNP=firstsLasts(TypeNP),
				FLastsNE=firstsLasts(TypeNE),
				ResGM=graphMatchingListAll(FLastsNP, FLastsNE,Dict,NodesAcum,From),
				case ResGM of
				    {true,DEdges,DictTemp} ->%{true,DEdges++[{edge,NE,NP,data}],DictTemp};
				    			     {true,DEdges,DictTemp};
				    _ -> {false,[],Dict}
				end;
			    _ -> graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum,From)
			end;
		    {op,'[]',_,_,_} -> 
	               	case TypeNE  of 
	                    {function_in,_,_,_,_} -> {false,[],Dict};
			    {call,Return} -> {true,[{edge,Return,NP,data}],Dict};
			    {op,'[]',_,_,_} -> 
			    FLastsNP=firstsLasts(TypeNP),
			    FLastsNE=firstsLasts(TypeNE),
		            ResGM=graphMatchingListAll(FLastsNP, FLastsNE,Dict,NodesAcum,From),
			    case ResGM of
				{true,DEdges,DictTemp} -> {true,DEdges++[{edge,NE,NP,data}],DictTemp};
				_ -> {false,[],Dict}
			    end;
			_ -> graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum,From)
			end;
		    {pm,_,_} -> 
		        graphMatchingListPattern(firstsLasts(TypeNP),NE,Dict,NodesAcum,From);
		    _ -> {false,[],Dict}
		end
	end.

	            
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingList  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	           
graphMatchingList(_,[],Dict,_,_) -> {false,[],Dict};
graphMatchingList(NP,[NE|NEs],Dict,NodesAcum,FromIO)->	
	%io:format("GML: ~w~n",[{NP,NE}]),
	{Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum,FromIO),
	{Bool2,DataArcs2,Dict3}=graphMatchingList(NP,NEs,Dict2,NodesAcum,FromIO),
	{Bool1 or Bool2,DataArcs1++DataArcs2,Dict3}. 
	
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListPattern  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	
graphMatchingListPattern([],_,Dict,_,_) -> {true,[],Dict};
graphMatchingListPattern([NP|NPs],NE,Dict,NodesAcum,FromIO)->	
    	%io:format("GMLP: ~w~n",[{NP,NE}]),
	{Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum,FromIO),
	{Bool2,DataArcs2,Dict3}=graphMatchingListPattern(NPs,NE,Dict2,NodesAcum,FromIO),
	{Bool1 and Bool2,DataArcs1++DataArcs2,Dict3}.
	
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListAll  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphMatchingListAll([],[],Dict,_,_) -> {true,[],Dict};	
graphMatchingListAll([],_,Dict,_,_) -> {false,[],Dict};	
graphMatchingListAll(_,[],Dict,_,_) -> {false,[],Dict};
graphMatchingListAll([NP|NPs],[NE|NEs],Dict,NodesAcum,FromIO)->	
    	%io:format("GMLA: ~w~n",[{NP,NE}]),
	{Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum,FromIO),
	%io:format("GMLA Results: ~w~n",[{Bool1,NPs,NEs}]),
	case Bool1 of 
	    true -> {Bool2,DataArcs2,Dict3}=graphMatchingListAll(NPs,NEs,Dict2,NodesAcum,FromIO),
	      	    {Bool2,DataArcs1++DataArcs2,Dict3};
	    false-> {false,[],Dict}
	end. 

%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListAllIO  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphMatchingListAllIO([],[],Dict,_,_) -> {true,[],Dict};	
graphMatchingListAllIO([],_,Dict,_,_) -> {false,[],Dict};	
graphMatchingListAllIO(_,[],Dict,_,_) -> {false,[],Dict};
graphMatchingListAllIO([NP|NPs],[NE|NEs],Dict,NodesAcum,FromIO)->	
	{_,DataArcs1,_}=graphMatching(NP,NE,Dict,NodesAcum,FromIO),
	{Bool2,DataArcs2,Dict3}=graphMatchingListAllIO(NPs,NEs,Dict,NodesAcum,FromIO),
	{Bool2,DataArcs1++DataArcs2,Dict3}.
	
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListAllLinkClauses  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphMatchingListAllLinkClauses([],[],Dict,_,_) -> {true,[],Dict};	
graphMatchingListAllLinkClauses([],_,Dict,_,_) -> {true,[],Dict};	
graphMatchingListAllLinkClauses(_,[],Dict,_,_) -> {true,[],Dict};
graphMatchingListAllLinkClauses([NP|NPs],[NE|NEs],Dict,NodesAcum,FromIO)->	
    {Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum,FromIO),
    case Bool1 of 
        true -> 
            {Bool2,DataArcs2,Dict3}=graphMatchingListAllLinkClauses(NPs,NEs,Dict2,NodesAcum,FromIO),
            {Bool2,DataArcs1++DataArcs2,Dict3};
        false-> {false,[],Dict}
    end.     
	







%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%      INPUT & OUTPUT EDGES          %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%  buildInputOutputEdges  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildInputOutputEdges(_,_,[],_)-> {[],[]};
buildInputOutputEdges(Nodes,Edges,[CallInfo={NCall,NodeCalled,NodesArgs,NodeReturn,Types} |CallsInfo],ClausesInfo) ->
    NodesIn = getApplicableFunctions(Nodes,Edges,[{NodeCalled,NodesArgs,NodeReturn,Types}],true),
    ApplicableClausesInfo = [{
    				NFIn,
    				CalledNodes,
    				[ClauseInfo || ClauseInfo={NIn,_,_,_,_}<-ClausesInfo,
	                                       {edge,NFIn_,NIn_,control}<-Edges,
	                                       NIn==NIn_,
	                                       NFIn==NFIn_]
	                     } || {NFIn,CalledNodes}<-NodesIn],
    % io:format("NodeCall: ~w ~nNodesArgs: ~w ~n",[NCall,NodesArgs]),            
    {MatchingClauses,IOEdges}=
    		inputOutputEdges(Nodes,Edges,{NCall,NodesArgs,NodeReturn,Types},ApplicableClausesInfo),
    %io:format("IOEdges: ~w ~n",[IOEdges]),
    {PendingCalls,NewEdges}=buildInputOutputEdges(Nodes,Edges,CallsInfo,ClausesInfo),
    %io:format("NewEdges: ~w ~n",[NewEdges]),
    {
    	[{CallInfo,MatchingClauses}|PendingCalls],
    	IOEdges ++ NewEdges
    }.


%%%%%%%%%%%%%%%%%%%%%%%%  getApplicableFunctions  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
getApplicableFunctions(_,_,[],_) -> [];
getApplicableFunctions(Nodes,Edges,[{NodeCalled,NodesArgs,NodeReturn,Types}|CallsInfo],First)->
    [NCType|_]=[NCType_||{node,NC,NCType_}<-Nodes,NC==NodeCalled],
    NInCalled=
	case NCType of
	    {term,TermNC} ->
	 	case TermNC of
		    {var,_,_} -> 
	  	    	[{N_in,[NodeCalled]} ||
	  	             	 {node,N_in,{function_in,_,Arity,_,_}}<-Nodes,
	  	             	 Arity==length(NodesArgs)];
		    {'fun',_,{function,Name,Arity}} -> 
			[{N_in,[NodeCalled]} ||
			         {node,N_in,{function_in,Name_,Arity_,_,_}}<-Nodes,
			         Name==Name_,
			         Arity==Arity_,Arity==length(NodesArgs)];
		    {atom,_,Name} when First ->
			[{N_in,[NodeCalled]} ||
			         {node,N_in,{function_in,Name_,Arity,_,_}}<-Nodes,
			         Name_==Name,
			         Arity==length(NodesArgs)];
		    _ -> []
		end;
	    {function_in,_,Arity,_,_}-> 
	        if 
		    Arity == length(NodesArgs)-> [{NodeCalled,[]}];
		    true -> []
		end;
	    {call,_} -> 
		[{N_in,[NodeCalled]} || 
				{node,N_in,{function_in,_,Arity,_,_}}<-Nodes,
				Arity==length(NodesArgs)];
	    {pm,_,_} -> 
		getApplicableFunctions(Nodes,Edges,
				[{NodeCalled_,NodesArgs,NodeReturn,Types} || 
					     NodeCalled_<-firstsLasts(NCType)],false);
	    {'case',_,_,_} -> 
		getApplicableFunctions(Nodes,Edges,
				[{NodeCalled_,NodesArgs,NodeReturn,Types} ||
						NodeCalled_<-firstsLasts(NCType)],false);
	    {'if',_,_,_} -> 
		getApplicableFunctions(Nodes,Edges,
			        [{NodeCalled_,NodesArgs,NodeReturn,Types} ||
			        		NodeCalled_<-firstsLasts(NCType)],false);
	    {block,_,_,_} ->
	    	getApplicableFunctions(Nodes,Edges,
			        [{NodeCalled_,NodesArgs,NodeReturn,Types} ||
			        		NodeCalled_<-firstsLasts(NCType)],false);		  
	    _ -> []
	end,
    NInCallsInfo=getApplicableFunctions(Nodes,Edges,CallsInfo,false),
    
    [{NIn,NodesCall++NodesCall_}||{NIn,NodesCall}<-NInCallsInfo,{NIn_,NodesCall_}<-NInCalled,NIn_==NIn]
        ++[{NIn,NodesCall}||{NIn,NodesCall}<-NInCallsInfo,[NIn_||{NIn_,_}<-NInCalled,NIn_==NIn]==[]]
	++[{NIn,NodesCall}||{NIn,NodesCall}<-NInCalled,[NIn_||{NIn_,_}<-NInCallsInfo,NIn_==NIn]==[]].
	
      

%%%%%%%%%%%%%%%%%%%%%%%%  inputOutputEdges  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
inputOutputEdges(_,_,_,[]) -> {[],[]};
inputOutputEdges(Nodes,Edges,CallInfo,[{FIn,CalledNodes,ClausesFunction}|ClausesFunctions])->
    {MatchC0,NewEdges}=inputOutputEdgesFunction(Nodes,Edges,CallInfo,CalledNodes,ClausesFunction),
    MatchingClauses = [{FIn,CalledNodes,ClauseInfo} ||
    				NIn<-MatchC0,
    				ClauseInfo={NIn_,_,_,_,_}<-ClausesFunction,
    				NIn==NIn_],
    {MatchingClauses_,NewEdges_}=inputOutputEdges(Nodes,Edges,CallInfo,ClausesFunctions),
    {
    	MatchingClauses++MatchingClauses_,
    	NewEdges++NewEdges_
    }.	


%%%%%%%%%%%%%%%%%%%%%%%%  inputOutputEdgesFunction  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
inputOutputEdgesFunction(_,_,_,_,[]) -> {[],[]};
inputOutputEdgesFunction(Nodes,Edges,InfoCall={_,NodesArgs,NodeReturn,{_,TArgsCall,_}},CalledNodes,
                          	[{NodeClauseIn,NodesPatterns,Guard,Lasts,{_,TArgsClause}}|ClausesInfo])->
    Strong_ = allArgsHold(fun erl_types:t_is_subtype/2,TArgsCall,TArgsClause),
    Strong = Strong_ and (Guard==[]),
    Weak =  allArgsHold(fun (T1,T2) -> 
    			    not erl_types:t_is_none(erl_types:t_inf(T1,T2)) 
    			end,
    			TArgsClause,TArgsCall),
    if
	Strong -> 
	    {_,EdgesMatch,_}=graphMatchingListAllIO(NodesPatterns,NodesArgs,[],Nodes,io), 
	    {
	        [NodeClauseIn],
	        [{edge,getParentControl(CNode,Edges),NodeClauseIn,input}||CNode<-CalledNodes]
		%[{edge,CalledNode,NodeClauseIn,input}||CalledNode<-CalledNodes]
	    		++changeEdgeType(EdgesMatch,data,input)
		 	++[{edge,Last,NodeReturn,output}||Last<-Lasts]
	    };
	Weak -> 
	    {_,EdgesMatch,_}=graphMatchingListAllIO(NodesPatterns,NodesArgs,[],Nodes,io),
	    {MClauses,NewEdges}=inputOutputEdgesFunction(Nodes,Edges,InfoCall,CalledNodes,ClausesInfo),
	    {
	    	[NodeClauseIn| MClauses],
	  	[{edge,getParentControl(CalledNode,Edges),NodeClauseIn,input}||CalledNode<-CalledNodes]
		 	++changeEdgeType(EdgesMatch,data,input)
		 	++[{edge,Last,NodeReturn,output}||Last<-Lasts]
		 	++ NewEdges};
	true -> 
	    inputOutputEdgesFunction(Nodes,Edges,InfoCall,CalledNodes,ClausesInfo)
    end.






%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%      SUMMARY EDGES           %%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%  getReachablePatterns  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	
getReachablePatterns(_,_,[])->[];
getReachablePatterns(Nodes,Edges,[{_,NodesPatterns,_,Lasts,_}|ClausesInfo])->
	Reachables=removeDuplicates(lists:append([reachablesFrom(Last,Nodes,Edges,[])||Last<-Lasts])),
    	[NodePattern||NodePattern<-NodesPatterns,lists:member(NodePattern,Reachables)]
    		++getReachablePatterns(Nodes,Edges,ClausesInfo).

%%%%%%%%%%%%%%%%%%%%%%%%  reachablesFrom  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
reachablesFrom(Node,Nodes,Edges,PreviouslyAnalyzed)->
    Parents=[NodeO||{edge,NodeO,NodeD,_}<-Edges,NodeD==Node],
    ChildrenCall= 
        case [NodeCall||{node,NodeCall,{call,_}}<-Nodes,NodeCall==Node] of
	    []->[];
	    _->[NodeD||{edge,NodeO,NodeD,_}<-Edges,NodeO==Node]
	end,
    	removeDuplicates(
    		PreviouslyAnalyzed
    		++ lists:flatten(
    			[reachablesFrom(
    				NodeP,
    				Nodes,
    				Edges,
    				removeDuplicates(PreviouslyAnalyzed++Parents++ChildrenCall++[Node])
    			   )  || 
    			   	NodeP<-removeDuplicates(Parents++ChildrenCall),
    			   	not lists:member(NodeP,PreviouslyAnalyzed)]
		)
	).


%%%%%%%%%%%%%%%%%%%%%%%%  buildSummaryEdges  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildSummaryEdges(_,_,[])-> [];
buildSummaryEdges(Edges,NeedPatterns,[{_,_,NodesArgs,NodeReturn}|CallsInfo])->
	buildSummaryEdgesArgs(Edges,NodeReturn,NeedPatterns,NodesArgs)
	++ buildSummaryEdges(Edges,NeedPatterns,CallsInfo).

%%%%%%%%%%%%%%%%%%%%%%%%  buildSummaryEdgesArgs  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildSummaryEdgesArgs(_,_,_,[])->[];
buildSummaryEdgesArgs(Edges,NodeReturn,NeedPatterns,[NodeArg|NodesArgs])->
    removeDuplicates([{edge,NodeArg_,NodeReturn,summary}||
			   {edge,NodeArg_,NodePattern,input}<-Edges,
			   NodeArg_==NodeArg,
			   lists:member(NodePattern,NeedPatterns)]
    ++buildSummaryEdgesArgs(Edges,NodeReturn,NeedPatterns,NodesArgs)).







%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%      AUXILIAR FUNCTIONS           %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

%%%%%%%%%%%%%%%%%%%%%%%%  varsExpression  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
varsExpression({var,_,'_'})-> [];                                                          
varsExpression({var,_,Name})-> [Name];
varsExpression({match,_,E1,E2})-> removeDuplicates(varsExpression(E1)++varsExpression(E2));
varsExpression({tuple,_,Es}) -> removeDuplicates([Var||E<-Es,Var<-varsExpression(E)]);
varsExpression({cons,_,EH,ET}) -> removeDuplicates(varsExpression(EH)++varsExpression(ET));
varsExpression({op,_,_,E1,E2})-> removeDuplicates(varsExpression(E1)++varsExpression(E2));
varsExpression({op,_,_,E})-> varsExpression(E);
varsExpression(_)-> [].

%%%%%%%%%%%%%%%%%%%%%%%%  buildCallsInfo  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
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


%%%%%%%%%%%%%%%%%%%%%%%%  buildClauseInfo  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildClauseInfo(_,_,[],_)-> [];	
buildClauseInfo(Nodes,Edges,[NClause|NClauses],ClausesTypeInfo)->
   	[NGuard|NsPat_]=
   		lists:reverse(lists:sort([Child||{edge,NClause_,Child,control}<-Edges,NClause==NClause_])),
    	NodesPatterns=lists:reverse(NsPat_),
    	[Guard|_]=[Guard_||
    			{node,NGuard_,{guards,Guard_}}<-Nodes,
    			NGuard_==NGuard],
    	[Type|_]=[{RetType,ArgsTypes}||
    			{NClause_,RetType,ArgsTypes}<-ClausesTypeInfo,
    			NClause_==NClause],
    	[Lasts|_]=[Lasts_||
    			{node,NClause_,{clause_in,_,Lasts_}}<-Nodes,
    			NClause_==NClause],
	%io:format("~w~n",[{NClause,NodesPatterns,Guard,Type}]),
    	[{NClause,NodesPatterns,Guard,Lasts,Type} | buildClauseInfo(Nodes,Edges,NClauses,ClausesTypeInfo)].


%%%%%%%%%%%%%%%%%%%%%%%%  addTypeInfo  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
addTypeInfo([],_,_)->[];
addTypeInfo([{NCall,NodeCalled,NodesArgs,NodeReturn}|CallsInfo],TypeInfo,Id)->
  	TC=list_to_atom("transformed_call"++integer_to_list(Id)),
  	%io:format("TC: ~p~n",[TC]),
  	ListTypes_= [{RetType,lists:split(length(NodesArgs),ArgsTypes_)} ||
  					{TC_,_,{RetType,ArgsTypes_},_}<-TypeInfo,
  					TC_==TC],
  	ListTypes = [{TR,TArgs,Rest} || {TR,{TArgs,Rest}}<-ListTypes_],
  	[Type|_]=ListTypes,
  	[{NCall,NodeCalled,NodesArgs,NodeReturn,Type} | addTypeInfo(CallsInfo,TypeInfo,Id+1)].


%%%%%%%%%%%%%%%%%%%%%%%%  getClausesTypeInfo  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
getClausesTypeInfo([],_)->[];  
getClausesTypeInfo([NIn|NIns],[{TC,_,{RetType,ArgsTypes},_}|InfoType])->
   	case lists:suffix("CLAUSE",atom_to_list(TC)) of
        	true -> [{NIn,RetType,ArgsTypes}|getClausesTypeInfo(NIns,InfoType)];
        	_ -> getClausesTypeInfo([NIn|NIns],InfoType)
   	end.


%%%%%%%%%%%%%%%%%%%%%%%%  removeDuplicates  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
-spec removeDuplicates(list()) -> list().
removeDuplicates(List) -> sets:to_list(sets:from_list(List)).


%%%%%%%%%%%%%%%%%%%%%%%%  termEquality  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
termEquality({integer,_,T},{integer,_,T})->true;
termEquality({atom,_,T},{atom,_,T})->true;
termEquality({float,_,T},{float,_,T})->true;
termEquality({string,_,T},{string,_,T})->true;
termEquality(_,_)->false.


%%%%%%%%%%%%%%%%%%%%%%%%  getParentControl  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
getParentControl(Node,Edges) ->
	[Parent|_]=[Parent_ || {edge,Parent_,Node_,control}<-Edges, Node_==Node],
	Parent.


%%%%%%%%%%%%%%%%%%%%%%%%  existVarDict  %%%%%%%%%%%%%%%%%%%%%%%%%%%%

existVarDict(V,[{V,_,_} | _]) -> true;
existVarDict(V,[_ | Dict]) -> existVarDict(V,Dict);
existVarDict(_,[])->false.


%%%%%%%%%%%%%%%%%%%%%%%%  existVarDictGM  %%%%%%%%%%%%%%%%%%%%%%%%%%%%

existVarDictGM(V,[{V,ND,undef} | _],NP) -> not lists:member(NP,ND);
existVarDictGM(V,[{V,_,_} | _],_) -> true;
existVarDictGM(V,[_ | Dict],NP) -> existVarDictGM(V,Dict,NP);
existVarDictGM(_,[],_)->false.

%%%%%%%%%%%%%%%%%%%%%%%%  existVarDictUndef  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
existVarDictUndef(V,[{V,_,undef} | _]) -> false;
existVarDictUndef(V,[{V,_,_} | _]) -> true;
existVarDictUndef(V,[_ | Dict]) -> existVarDictUndef(V,Dict);
existVarDictUndef(_,[])->false.


%%%%%%%%%%%%%%%%%%%%%%%%  getNumNodes  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
getNumNodes([])->[];
getNumNodes([{node,Num,_}|Nodes])->[Num]++getNumNodes(Nodes).


%%%%%%%%%%%%%%%%%%%%%%%%  findPMVar  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
findPMVar(V,Dict)-> 	
	case [{NodePM,NodeDecl} || {Var,NodeDecl,NodePM} <-Dict,Var==V,NodePM/='undef'] of
		[Head|_] -> Head;
		_ -> {[],[]}
	end.


%%%%%%%%%%%%%%%%%%%%%%%%  lasts  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
lasts({function_in,_,_,_,Lasts}) -> Lasts;
lasts({clause_in,_,Lasts}) -> Lasts;
lasts({'case',_,_,Lasts}) -> Lasts;
lasts({'if',_,_,Lasts}) -> Lasts;
lasts({block,_,_,Lasts}) -> Lasts;
lasts({call,Return}) -> [Return];
lasts({pm,_,Lasts}) -> Lasts;
lasts({op,_,_,_,Lasts}) -> Lasts.


%%%%%%%%%%%%%%%%%%%%%%%%  firstsLasts  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
firstsLasts({function_in,_,_,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({clause_in,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({'case',_,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({'if',_,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({block,_,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({call,Return}) -> [Return];
firstsLasts({pm,FirstsLasts,_}) -> FirstsLasts;
firstsLasts({op,_,_,FirstsLasts,_}) -> FirstsLasts.


%%%%%%%%%%%%%%%%%%%%%%%%  changeEdgeType  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
changeEdgeType([],_,_)->[];
changeEdgeType([{edge,NS,NT,OldType}|Es],OldType,NewType)->
	[{edge,NS,NT,NewType}|changeEdgeType(Es,OldType,NewType)];
changeEdgeType([E|Es],OldType,NewType)->
	[E|changeEdgeType(Es,OldType,NewType)].
    
    
%%%%%%%%%%%%%%%%%%%%%%%%  changeEdgeTypeNotAcum  %%%%%%%%%%%%%%%%%%%%%%%%%%%%    
%changeEdgeTypeNotAcum([],_,_)->[];
%changeEdgeTypeNotAcum([{edge,NS,NT,OldType}|Es],OldType,NewType)->
%	[{edge,NS,NT,NewType}]++changeEdgeTypeNotAcum(Es,OldType,NewType);
%changeEdgeTypeNotAcum([E|Es],OldType,NewType)->
%	[E]++changeEdgeTypeNotAcum(Es,OldType,NewType).    
    
 
%%%%%%%%%%%%%%%%%%%%%%%%  allArgsHold  %%%%%%%%%%%%%%%%%%%%%%%%%%%%   
allArgsHold(_,[],[])->true;
allArgsHold(F,[TCa|TCas],[TCl|TCls])->
  	F(TCa,TCl) and allArgsHold(F,TCas,TCls).
  	
  	
%%%%%%%%%%%%%%%%%%%%%%%%  hasValue  %%%%%%%%%%%%%%%%%%%%%%%%%%%% 
hasValue(_,[],_) -> false;
hasValue(Node,[{node,NumNode,Type}|_],Dict) when Node==NumNode ->
	 case Type of
	     {term,TermNC} -> 
	 	case TermNC of
	 	    {var,_,V} -> 
	 	        case V of
	 	            '_' -> true;
	 	            _ -> existVarDictUndef(V,Dict)
	 	        end;
	 	    _ -> true
	 	end;
	     _ -> true
	 end;
hasValue(Node,[_|Nodes],Dict) -> hasValue(Node,Nodes,Dict).	    
	     
	 	       	 	            
	 	


%%%%%%%%%%%%%%%%%%%%%%%%  leaves  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%leaves(N,Ns,Es) ->
%	Children=getChildren(N,Ns,Es),
%	Leaves=[N_||N_<-Children,getChildren(N_,Ns,Es)==[]],
%	NonLeaves=[N_||N_<-Children,getChildren(N_,Ns,Es)/=[]],
%	Leaves++[Leaf||NonLeaf<-NonLeaves,Leaf<-leaves(NonLeaf,Ns,Es)].
%

%%%%%%%%%%%%%%%%%%%%%%%%  getChildren  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%getChildren(N,Ns,Es)->[N_||{node,N_,_}<-Ns,{edge,NS,NT,control}<-Es,NS==N,NT==N_].


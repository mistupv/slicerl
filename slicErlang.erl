%c(slicErlang),c(slicErlangDot),slicErlang:start(0),slicErlangDot:start(0).
%c(slicErlang),c(slicErlangDot),c(slicErlangSlice),slicErlang:start(0),slicErlangDot:start(0),slicErlangSlice:start(0).

-module(slicErlang).

-export([start/1,graphForms/4]).


start(_) ->
    {ok,Abstract} = smerl:for_file("temp.erl"),
    Forms_=lists:reverse(smerl:get_forms(Abstract)),
    Exports = smerl:get_exports(Abstract),
    ModName = smerl:get_module(Abstract),
    {ok, DeviceNE} = file:open("modname_exports", [write]),
    ok=io:write(DeviceNE,{ModName,Exports}),
    ok = file:close(DeviceNE),
    Forms = [Form||Form={function,_,_,_,_}<-Forms_],
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
    io:format("\n\n\n\n\n\n\n***************\n\n\n\n\n\n"),
    io:format("DICTIONARY: ~w ~n",[get()]),
	    {Summary_input_Edges,Summary_output_Edges}=buildSummaryINOUT(Nodes,Edges++InputOutputEdges),
   
    ReachablePatterns = getReachablePatterns(Nodes,Edges,ClausesInfoWithTypes),
    SummaryEdges = buildSummaryEdges(Edges++InputOutputEdges,ReachablePatterns,CallsInfo),
    NewSummaryEdges = buildNewSummaryEdges(Edges++InputOutputEdges++ Summary_input_Edges ++ Summary_output_Edges,Nodes),
    
    io:format("DICTIONARY FINAL: ~w ~n",[get()]),
    
    NEdges = removeDuplicates(Edges++InputOutputEdges++SummaryEdges++ Summary_input_Edges ++ Summary_output_Edges ++ NewSummaryEdges),
    %io:format("get(pending) ~w~n",[ get(pending)]),
    {ok, DeviceSerial} = file:open("temp.serial", [write]),
    io:write(DeviceSerial,{Nodes,NEdges}),
    erase(),
    ok = file:close(DeviceSerial).








%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GRAPH FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
graphForms([],Free,_,NodesAcum)->{[],[],Free,NodesAcum};
graphForms([{function,_,Name,Arity,Clauses}|Funs],Free,VarsDict,NodesAcum) ->
    {NodesClauses,EdgesClauses,NFree,DictClauses,Firsts,Lasts,FLasts,_,NodesAcumN,_} = 
	                               graphClauses(Clauses,Free+1, VarsDict, NodesAcum, func,[]),
    put(Free,DictClauses),%Guardamos el diccionario en el diccionario del proceso
    %io:format("DictCLAUSES: ~w ~n",[get(Free)]),
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

    io:format("VD0: ~w ~n",[VD0]),
    Type =
        case From of
    	    func -> pat;
    	    _ -> patArg
        end,
    {N1,E1,Free1,VD1,F1,_,_,NodesAcumN} = graphExpressions(Patterns,Free0+1,VD0,Type,NodesAcum),
    io:format("VD1: ~w ~n",[VD1]),
    DiccGuardsClause = lists:subtract(VD1,VD0),
    io:format("DiccGuardsClause: ~w ~n",[DiccGuardsClause]),
    
    %'VD1,%++[{Var,NodesDecl,NodesPM} ||
       		%	{Var,NodesDecl,NodesPM}<-VD0,[Var1||{Var1,_,_}<-VD1,Var1==Var]==[]],
    {N2,E2,Free2,NodesAcumNN} = graphGuards(Guards,Free1,VD1,NodesAcumN),
    {N3,E3,Free3,VD3,F2,L2,FL2,NodesAcumNNN}=graphExpressionsLast(Body,Free2+1,VD1,exp,NodesAcumNN),
    io:format("VD3: ~w ~n",[VD3]),
    
    VDFinal= 
        case From of
    	    exp_case -> lists:subtract(VD3, DiccGuardsClause);
    	    _ -> VD3
        end,
    io:format("VDFinal: ~w ~n",[VDFinal]),
    N_body=[{node,Free2,{body,Body}}],
    EdgeBody=[{edge,Free1,Free2,control}], %del node guarda al node body
    EdgesBody_Body=[{edge,Free2,NE,control}||NE<-F2],%del node body als first del body	
    {N4,E4,Free4,VD4,F3,L3,FL3,FC3,NodesAcumNNNN,ClausesAcumN} = 
    		graphClauses(Clauses,Free3,VD0,NodesAcumNNN,From,ClausesAcum++[{Free0,getNumNodes(N1)}]),
    N_in = {node,Free0,{clause_in,FL2,L2}},
    EdgesLinkClauses = 
        case From of
    	    func -> edgesLinkClauses(
    			getNumNodes(N_body),getNumNodes(N1),ClausesAcum,VD3,NodesAcumNNNN++[N_in]);
    	    exp_case -> edgesLinkClauses(
    			getNumNodes(N_body),getNumNodes(N1),ClausesAcum,VD3,NodesAcumNNNN++[N_in]);
    	    exp_if -> edgesClausesAll(getNumNodes(N_body),getNumNodes(N1),ClausesAcum)
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
        removeDuplicates(VDFinal++VD4),
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
    {Res,_,_}=graphMatchingListAllLinkClauses(Patterns,PatternsAcum,Dict,NodesAcum,false,[]),
    case Res of
        true -> [{edge,N_in,N_body,data}]
                  ++ edgesLinkClauses([N_body],Patterns,ClausesAcum,Dict,NodesAcum);
        _ -> edgesLinkClauses([N_body],Patterns,ClausesAcum,Dict,NodesAcum)
    end.

%%%%%%%%%%%%%%%%%%%%%%%%  edgesClausesAll  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
edgesClausesAll([],_,_) -> [];
edgesClausesAll(_,_,[]) -> [];
edgesClausesAll([N_body],Patterns,[{N_in,_}|ClausesAcum]) ->
   [{edge,N_in,N_body,data}]++edgesClausesAll([N_body],Patterns,ClausesAcum).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GRAPH GUARDS & TERMS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
graphGuards(Guards,Free,VarsDict,NodesAcum) -> 
    Vars = removeDuplicates(lists:flatten([Var ||
    						Guard <- Guards,
    				   		Var<-lists:map(fun varsExpression/1,Guard)])),
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
		_ -> 
		    NewDict=
    		        case V of
    	    		    '_' -> VarsDict;
    	    		    _ -> VarsDict++[{V,[Free],undef}]
    			end,
		    {[],NewDict}
	    end
	end,
    {Ns,EdgeUse,NFree,NVarsDict,First,Lasts,NodesAcumN};
graphExpression(Term={var,_,V},Free,VarsDict,patArg,NodesAcum)->
    {Ns,_,NFree,_,First,Lasts,NodesAcumN}=graphTerm(Term,Free,VarsDict,NodesAcum),
    NewDict=
    	case V of
    	    '_' -> VarsDict;
    	    _ -> VarsDict++[{V,[Free],undefIO}]
    	end,
    {Ns,[],NFree, NewDict,First,Lasts,NodesAcumN};
graphExpression(Term={var,_,V},Free,VarsDict,exp,NodesAcum)->
    {Ns,_,NFree,_,First,Lasts,NodesAcumN}=graphTerm(Term,Free,VarsDict,NodesAcum),
    {Ns,[{edge,NodeDecl,Free,data}||{VarD,NodesDecl,_} <- VarsDict,NodeDecl<-NodesDecl,V==VarD],
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
    {NodesClauses,EdgesClauses,NNFree,NNVarsDict_,FirstsClauses,LastsClauses,FLasts,FPat,NodesAcumNN,_}=
		graphClauses(Cs0,NFree, VarsDict,NodesAcumN,exp_case,[]),
    NNVarsDict = linkEntrysDict(NNVarsDict_),
    		    %io:format("case NNVarsDict ~w ~n",[NNVarsDict]),
    N_case = {node,Free,{'case',Term,FLasts,LastsClauses}},
    NodesAcumNNN = NodesAcumNN++[N_case],
    {_,EdgesPM,_}=graphMatchingListPatternOr(FPat,Free+1,NVarsDict,NodesAcumNNN, case_,[]),
    {
     	[N_case]++NodesE++NodesClauses,
      	EdgesE
      		++EdgesClauses
      		++EdgesPM
       		++[{edge,Free,First,control}||First <- FirstsE]
       		++[{edge,Free,FirstC,control}||FirstC <- FirstsClauses],
      	NNFree,
      	NNVarsDict,
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
io:format("call VarsDict ~w ~n",[VarsDict]),
    {NodesE,EdgesE,NFree,NVarsDict,FirstsE,_,NodesAcumN}=
    graphExpression(F0,Free+1,VarsDict,exp,NodesAcum),
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
    	    exp -> graphMatching(Free+1,NFree,NNVarsDict,NodesAcumNNN,PatExp,[],[]);
    	    _ -> {true,[], NNVarsDict}
    	end,
    {EdgesPM,NNNNVarsDict}=
    	case Res of
	    true -> {EdgesPMAux,NNNVarsDict};
	    _ -> {[],NNVarsDict}
    	end,
       % io:format("match2 NNNVarsDict ~w ~n",[NNNNVarsDict]),
    {
        [N_match]
      		++NodesP
      		++NodesE,
      	EdgesP
      		++EdgesE
      		++EdgesPM
      		++[{edge,Free,First,control}||First <- (FirstsP++FirstsE)],
      	NNFree,
      	NNNNVarsDict,
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
    LastsGens2Exp =
    	case LastsGens2ExpAux of
	    [] -> [{edge,Free,First,control}||First <- FirstsExpLC];
	    _ -> LastsGens2ExpAux
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
graphMatching(NP,NE,Dict,NodesAcum,From,Stack,Edges)->
    [{node,NP,TypeNP}|_] = [Node||Node={node,NP_,_}<-NodesAcum,NP_==NP],
    [{node,NE,TypeNE}|_] = [Node||Node={node,NE_,_}<-NodesAcum,NE_==NE],
    io:format("~ngraphMatching: ~w~n ~w~n ~w~n ~w~n DICT: ~w~n~w~n",[NP,NE,TypeNP,TypeNE,get(), From]),

	case {TypeNP,TypeNE} of      
	    {{term,TermP},{term,TermE}} ->    %Los dos son términos
	    	case From of 		%Es unua llamada desde la construcción de las IO edges
                    input -> {true,[{edge,NE,NP,data}],Dict};
                    _ ->
                        case TermE of
		            {var,_,VExp} ->
		                case findPMVar(VExp,Dict) of
	                    		[{{undef_output,_}, NodesD} |_] -> 
	                    			updateVarsPattern(output, NodesAcum,Edges,TypeNP,NP,Stack),
	                    			updateGMDict(Dict,VExp,NE,NP,From,NodesAcum,Edges),
          	 	        		addEntryDictPendings(pending_output, NP, NodesD,Stack);
		            		[{undef_input, NodesD}|_] -> 
		            			updateVarsPattern(input, NodesAcum,Edges,TypeNP,NP,[]),
		            			updateGMDict(Dict,VExp,NE,NP,From,NodesAcum,Edges),
	               	 	        	addEntryDictPendings(pending_input, NP, NodesD,Stack);
			 	    	_ -> true
		                 end;
		             _ -> true
		        end,      
                        case termEquality(TermP,TermE) of      %iguales?
		            true -> %{true,[{edge,NE,NP,data}],Dict};
				    {true,[],Dict};
		            _ ->
		                case TermP of
		                    {var,_,V} ->      %No son iguales i PM es var
		                        case V of
		                            '_' ->  
						{true,[],Dict};
		                       	    _ ->
		                       	        	
		                       		case existVarDictGM(V,Dict,NP) of
		                       		    true -> %Variable definida
		                       		    	{NodesPM,_}=findPMVar(V,Dict),
		                       			
		                       			%io:format("DictTemp VELL!!! ~w ~n",[Dict]),
		                       			DictTemp= updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges),
							%io:format("DictTemp NOU!!! ~w ~n",[DictTemp]),

		                       			EdgeUse=
		                       		            case lists:member(From,[summary_input,summary_output]) of
		                       		    		true -> [{edge,NE,NP,data}]; 
		                       		    		_ -> case From of
		                       		    	    		case_ -> [{edge,NE,NP,data}]; 
		                       		    	    		_->[]
		                       		    	    	     end
		                       		            end,	                       			
		                       			{true, EdgeUse, DictTemp};
		                       		    _ ->     %Se esta definiendo aqui
		                       			%io:format("DictTemp VELL2!!! ~w ~n",[Dict]),
		                       			DictTemp= updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges),
							%io:format("DictTemp NOU2!!! ~w ~n",[DictTemp]),
		                       		    	EdgeUse=[{edge,NE,NP,data}], 
		                       		    	%io:format("EdgeUse2 ~p~n",[EdgeUse]),
		                     			%DictTemp=Dict++[{V,[NP],[NE]}],
		                     			{true,EdgeUse,DictTemp}
		                       		end
		                       	end;	
		                    _ -> 
		                        case TermE of  
		                            {var,_,V} ->    %No son iguales, PM NO es var i PE es var 
		                            			%---> a=X   (X tiene que estar definida)
		                            	{NodesPM,_}=findPMVar(V,Dict),
		                            	%io:format("NodesPM ~p~n",[NodesPM]),
		                            	case NodesPM of
		                            	    [] -> {true,[{edge,NE,NP,data}], Dict};
		                            	    _ ->
		                            	        {Return,_,DictTemp}=
		                            	                graphMatchingList(NP,NodesPM,Dict,NodesAcum,From,Stack,Edges),

						        case From of
						            case_ ->{true,[{edge,NE,NP,data}],DictTemp};
						    	    _ -> {Return,[],DictTemp}
						        end
						end;
		                            _ -> {false,[],Dict}
		                        end
		                end
		        end

                end;
            {{term,TermP},_} ->  %El PM es un termino i PE no.	
	        case TermP of
	            {var,_,V}-> 
	            	case V of  %PM es var
	                    '_' -> 
	                    	case From of
	                      	    input -> {true,[{edge,NE,NP,data}],Dict};
	                            _ -> {true,[],Dict}
	                       	end;
	                    _ -> 
%	                    	case TypeNE of
%	                    	    {call,Return} ->
%	                    	        ListPendingAux =erase(pending),
%                	 	    	ListPending= 
%                	 	            case ListPendingAux of
%                	 	    	    	undefined -> [];
%                	 	   	   	_ -> ListPendingAux
%                	 	            end,
%                	 	        put(pending,ListPending++[{NP,NE,From}]);
%                	 	    _ -> true
%                	 	end,
                	 	%io:format("pending: ~w~n",[ListPending++[{NP,NE}]]),
	                       	case existVarDictGM(V,Dict,NP) of   
	                            true ->  		%Variable ya declarada
	                       		%EdgeUse=[{edge,NodeDecl,NP,data} ||
	                       		%		{VarD,[NodeDecl|_],_}<-Dict,
	                       		%		V==VarD],
	                       		EdgeUse=
	                       		    case lists:member(From,[summary_data,summary_input,summary_output]) of
	                       		    	true -> [{edge,Last,NP,data}||Last <- lasts(TypeNE)]; 
	                       		    	_ -> []
	                       		    end,
	                       		%[], 
	                       		%io:format("EdgeUse5 ~p~n",[EdgeUse]),
	                       			%io:format("DictTemp VELL3!!! ~w ~n",[Dict]),
	                       			DictTemp= updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges);
						%io:format("DictTemp NOU3!!! ~w ~n",[DictTemp]);
	                       	    _ ->    		%Se esta declarando la variable
	                       		
	                       		EdgeUse=[{edge,Last,NP,data}||Last <- lasts(TypeNE)],%++[{edge,NP,NE,data}],
	                       		%io:format("EdgeUse4 ~p~n",[EdgeUse]),
	                       		
%	                       		case TypeNE  of
%	                       		    {call,_} ->
	                       		        %Gestion Pila
						%StackOutput=get(stack_output),
						%erase(stack_output),
						%put(stack_output, [NE]++StackOutput),
	                       		        
%	                       		        ListPendingAux=erase(pending),
%                	 	    		ListPending= 
%                	 	        	    case ListPendingAux of
%                	 	    	    		undefined -> [];
%                	 	   	   	        _ -> ListPendingAux
%                	 	        	    end,
%                	 	        	%io:format("pending: ~w~n",[ListPending++[{NP,NE}]]),
%                	 	    	        put(pending,ListPending++[{NP,NE,From}]),
	                       		        
%	                       		        ListPendingOutAux=erase(pending_output),
%                	 	    		ListPendingOut= 
%                	 	        	    case ListPendingOutAux of
%                	 	    	    		undefined -> [];
%                	 	   	   	        _ -> ListPendingOutAux
%                	 	        	    end,
%                	 	        	    %io:format("ListPendingOut: ~w~n",[ListPendingOut++[{NP,NE}]]),
%                	 	    	        put(pending_output,ListPendingOut++[{NP,NE,[NE]++Stack}]);
%                	 	    	    _ -> true
%	                       		end,
					%io:format("EdgeUse4 ~p~n",[Dict]), 
	                       		%io:format("EdgeUse4 ~p~n",[[{V_,DV,[NE]}||{V_,DV,undef}<-Dict,V_==V]
	                       		        %++[DE||DE={V_,_,_}<-Dict,V_/=V]]),    	
                       			%io:format("DictTemp VELL4!!! ~w ~n",[Dict]),
                       			DictTemp= updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges)
					%io:format("DictTemp NOU4!!! ~w ~n",[DictTemp])
	                       		     
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
                       	    {call,Return} -> 
%                                ListPendingAux =erase(pending),
%               	 	    	ListPending= 
%               	 	            case ListPendingAux of
%               	 	    	    	undefined -> [];
%               	 	   	   	_ -> ListPendingAux
%               	 	            end,
%               	 	        %io:format("pending: ~w~n",[ListPending++[{NP,NE}]]),
%               	 	    	put(pending,ListPending++[{NP,NE,From}]),
                            
           	 	        addEntryDictPendings(pending_output, NP, NE,[NE]++Stack),
           	 	         
           	 	            
%           	 	        VarsPM= varsTypeNode(TypeNP),
%           	 	        io:format("VarsPM ~w~n",[VarsPM]),
%           	 	        DictOthers=[Entry||Entry={Var_,_,_}<-Dict,not lists:member(Var_,VarsPM)],
%           	 	        DictThis=[Entry||Entry={Var_,_,_}<-Dict,lists:member(Var_,VarsPM)],
%           	 	        NewDict= DictOthers++
%           	 	         	  [Entry || Entry={_,_,PM}<-DictThis,PM/=undef]++
%           	 	         	  [{Var,DV,{undef_output,Stack}} || {Var,DV,PM}<-DictThis,PM==undef],
%           	 	        io:format("NewDict ~w~n",[NewDict]),
           	 	        updateVarsPattern(output, NodesAcum,Edges,TypeNP,NP,Stack),
	                       	%updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges),
                       	        {true,[{edge,Return,NP,data}], Dict};
                       	    _ ->  
                       	        graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum,From,Stack,Edges)
	               end
	        end;
	    {_,{term,TermE}} -> %P no es termino pero PE si
		case TermE of
		    {var,_,V} -> %PE es var
		        case findPMVar(V,Dict) of
	                    [{{undef_output,_}, NodesD} |_] -> 
	                    	updateVarsPattern(output, NodesAcum,Edges,TypeNP,NP,Stack),
	                    	updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges),
          	 	        addEntryDictPendings(pending_output, NP, NodesD, Stack);
		 	    _ -> true
	                 end,
			 {NodesPM,NodesDecl}=findPMVar(V,Dict),
			 %io:format("NodesPM,NodesDecl~p~n",[{V,NodesPM,NodesDecl}]),
                	 {Return,EdgesAux,DictTemp}=
                	     case NodesPM of
                	 	[] ->
                	 	    
                	 	    NewStack= 
                	 	        case Stack of
                	 	    	    [] -> [];
                	 	    	    _ ->lists:nthtail(1,Stack)
                	 	        end,
                	 	    
                	 	    addEntryDictPendings(pending_input, NP, NodesDecl, NewStack),
                	 	    
                	 	    %io:format("pending_input ~w~n",[get(pending_input)]),
                	 	    
%                	 	    VarsPM= varsTypeNode(TypeNP),
%                	 	    io:format("VarsPM ~w~n",[VarsPM]),
%           	 	            DictOthers=[Entry||Entry={Var_,_,_}<-Dict,not lists:member(Var_,VarsPM)],
%           	 	            DictThis=[Entry||Entry={Var_,_,_}<-Dict,lists:member(Var_,VarsPM)],
%           	 	            NewDict= DictOthers++
%           	 	         	  [Entry || Entry={_,_,PM}<-DictThis,PM/=undef]++
%           	 	         	  [{Var,DV,undef_input} || {Var,DV,PM}<-DictThis,PM==undef],
%           	 	    	    io:format("NewDict ~w~n",[NewDict]),
				    updateVarsPattern(input, NodesAcum,Edges,TypeNP,NP,[]),
                	 	    updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges),
                	 	    {true,[], Dict};
                	 	_ -> graphMatchingList(NP,NodesPM,Dict,NodesAcum,From,Stack,Edges)
                	     end,
                	%io:format("{Edges} ~w~n",[EdgesAux]),
                	%io:format("lasts(TypeNP) ~w~n",[lasts(TypeNP)]),
                	    
	                 {
	                     Return,
	                     [{edge,NodeDecl,Last,summary_data} ||  
	                     		NodeDecl<-NodesDecl,
	                     		Last<-lasts(TypeNP),
	                     		not hasValue(Last,NodesAcum, Dict)]
	                     	 ++[{edge,NodeDecl,NP,summary_data} || NodeDecl<-NodesDecl]
	                         ++[{edge,NE,NP,summary_data}]
	                         ++[{edge,NE,Last,summary_data} || 
	                         	Last<-lasts(TypeNP),
	                         	not hasValue(Last,NodesAcum, Dict)]
	                         ++ EdgesAux,	
	                         %%++changeEdgeTypeNotAcum(Edges,data,summary_data)
	                         DictTemp
	                 };
		    	%end;
		    _ ->     %PE no es Var
	             	case TypeNP of
	                    {op,'{}',_,_,_} -> {false,[],Dict};
	                    {op,'[]',_,_,_} -> {false,[],Dict};
	                    _ -> 
			        graphMatchingListPattern(firstsLasts(TypeNP),NE,Dict,NodesAcum,From,Stack,Edges)
	                end
		end;
            _ ->    %Ni PM es var ni PE tampoco --> Son listas, tuplas o PM
	        case TypeNP of
		    {op,'{}',_,_,_} ->    
	                case TypeNE  of 
	      		    {op,'[]',_,_,_} -> {false,[],Dict};
	              	    {function_in,_,_,_,_} -> {false,[],Dict};
			    {call,Return} ->			    
           	 	    	 addEntryDictPendings(pending_output, NP, NE, [NE]++Stack),
           	 	    	 
           	 	    	 
           	 	    	 VarsPM= varsTypeNode(TypeNP),
%           	 	    	 io:format("VarsPM ~w~n",[VarsPM]),
%           	 	    	 DictOthers=[Entry||Entry={Var_,_,_}<-Dict,not lists:member(Var_,VarsPM)],
%           	 	         DictThis=[Entry||Entry={Var_,_,_}<-Dict,lists:member(Var_,VarsPM)],
%           	 	         NewDict= DictOthers++
%           	 	         	  [Entry || Entry={_,_,PM}<-DictThis,PM/=undef]++
%           	 	         	  [{Var,DV,{undef_output,Stack}} || {Var,DV,PM}<-DictThis,PM==undef],
%           	 	    	 io:format("NewDict ~w~n",[NewDict]),
				 updateVarsPattern(output, NodesAcum,Edges,TypeNP,NP,Stack),
				 %updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges), PETABA
           	 	    	 {true,[{edge,NE,NP,data}], Dict};
			    {op,'{}',_,_,_} ->
			        FLastsNP=firstsLasts(TypeNP),
				FLastsNE=firstsLasts(TypeNE),
				ResGM=graphMatchingListAll(FLastsNP, FLastsNE,Dict,NodesAcum,From,Stack,Edges),
				case ResGM of
				    {true,DEdges,DictTemp} ->{true,DEdges++[{edge,NE,NP,data}],DictTemp};
				    			     %{true,DEdges,DictTemp};
				    _ -> {false,[],Dict}
				end;
			    _ -> graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum,From,Stack,Edges)
			end;
		    {op,'[]',_,_,_} -> 
	               	case TypeNE  of 
	                    {function_in,_,_,_,_} -> {false,[],Dict};
			    {call,Return} ->			    
           	 	    	 addEntryDictPendings(pending_output, NP, NE, [NE]++Stack),
           	 	    	 
%           	 	    	 VarsPM= varsTypeNode(TypeNP),
%           	 	    	 io:format("VarsPM ~w~n",[VarsPM]),
%           	 	         DictOthers=[Entry||Entry={Var_,_,_}<-Dict,not lists:member(Var_,VarsPM)],
%           	 	         DictThis=[Entry||Entry={Var_,_,_}<-Dict,lists:member(Var_,VarsPM)],
%           	 	         NewDict= DictOthers++
%           	 	         	  [Entry || Entry={_,_,PM}<-DictThis,PM/=undef]++
%           	 	         	  [{Var,DV,{undef_output,Stack}} || {Var,DV,PM}<-DictThis,PM==undef],
%           	 	    	 io:format("NewDict ~w~n",[NewDict]),
				 updateVarsPattern(output, NodesAcum,Edges,TypeNP,NP,Stack),
				 %updateGMDict(Dict,V,NE,NP,From,NodesAcum,Edges), PETABA
           	 	    	 {true,[{edge,Return,NP,data},{edge,NE,NP,data}], Dict};
	                    {op,'[]',_,_,_} -> 
			        FLastsNP=firstsLasts(TypeNP),
			        FLastsNE=firstsLasts(TypeNE),
		                ResGM=graphMatchingListAll(FLastsNP, FLastsNE,Dict,NodesAcum,From,Stack,Edges),
			        case ResGM of
				    {true,DEdges,DictTemp} -> {true,DEdges++[{edge,NE,NP,data}],DictTemp};
				    _ -> {false,[],Dict}
			        end;
			    _ -> graphMatchingList(NP,firstsLasts(TypeNE),Dict,NodesAcum,From,Stack,Edges)
			end;
		    {pm,_,_} -> 
		        graphMatchingListPattern(firstsLasts(TypeNP),NE,Dict,NodesAcum,From,Stack,Edges);
		    _ -> {false,[],Dict}
		end
	end.

	            
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingList  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	           
graphMatchingList(_,[],Dict,_,_,_,_) -> {false,[],Dict};
graphMatchingList(NP,[NE|NEs],Dict,NodesAcum,FromIO,Stack,Edges)->	
    %io:format("GML: ~w~n",[{NP,NE}]),
    {Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum,FromIO,Stack,Edges),
    {Bool2,DataArcs2,Dict3}=graphMatchingList(NP,NEs,Dict,NodesAcum,FromIO,Stack,Edges),
    NDict=[ Entry || Entry={Var2,Decl2,PM2}<-Dict2, {Var3,Decl3,PM3}<-Dict3, Var2==Var3, Decl2==Decl3, PM2==PM3]
            ++ [{Var2,removeDuplicates(Decl2++Decl3),removeDuplicates(PM2++PM3)} || 
            					{Var2,Decl2,PM2}<-Dict2, 
            					{Var3,Decl3,PM3}<-Dict3, 
            					Var2==Var3, 
            					(Decl2/=Decl3) or (PM2/=PM3),
            					    case PM2 of
            					    	{undef_output,_} -> false;
            					    	undef ->false;
            					    	undef_input ->false;
            					    	_ -> true	
            					    end
            					and	
            					    case PM3 of
            					    	{undef_output,_} -> false;
            					    	undef ->false;
            					    	undef_input ->false;
            					    	_ -> true	
            					    end
						]
            ++ [{Var2,removeDuplicates(Decl2++Decl3),PM3} || 
            					{Var2,Decl2,PM2}<-Dict2, 
            					{Var3,Decl3,PM3}<-Dict3, 
            					Var2==Var3, 
            					(Decl2/=Decl3) or (PM2/=PM3),
            					    case PM2 of
            					    	{undef_output,_} -> false;
            					    	undef ->false;
            					    	undef_input ->false;
            					    	_ -> true	
            					    end
            					and	
            					    case PM3 of
            					    	{undef_output,_} -> false;
            					    	undef ->false;
            					    	undef_input ->false;
            					    	_ -> true	
            					    end
            					]
            ++ [{Var2,removeDuplicates(Decl2++Decl3),PM2} || 
            					{Var2,Decl2,PM2}<-Dict2, 
            					{Var3,Decl3,PM3}<-Dict3, 
            					Var2==Var3, 
            					(Decl2/=Decl3) or (PM2/=PM3),
            					    case PM2 of
            					    	{undef_output,_} -> false;
            					    	undef ->false;
            					    	undef_input ->false;
            					    	_ -> true	
            					    end
            					and	
            					    case PM3 of
            					    	{undef_output,_} -> false;
            					    	undef ->false;
            					    	undef_input ->false;
            					    	_ -> true	
            					    end
            					],
    {Bool1 or Bool2,DataArcs1++DataArcs2,removeDuplicates(NDict)}.
    
    
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListDicts  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	    
graphMatchingListDicts(_,[],_,_,_,_,_)->[];
graphMatchingListDicts(NP,[NE|NEs],NodesAcum,Edges,FromIO,Stack,Edges)->
    NodesIn = [NFIn||{node,NFIn,{function_in,_,_,_,_}}<-NodesAcum],
    NI=giveMeNodeIn(NE, NodesIn,Edges),
    Dict=get(NI),
    
    {Res,DataArcs1,Dict1}=graphMatching(NP,NE,Dict,NodesAcum,FromIO,Stack,Edges),

    erase(NI),
    put(NI,Dict1),
    
    DataArcsAux=
    case Res of
    	true -> DataArcs1;
    	_ -> []
    end, 
    DataArcs2= graphMatchingListDicts(NP,NEs,NodesAcum, Edges ,FromIO,Stack,Edges),
    DataArcsAux++DataArcs2.
	
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListPattern  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	
graphMatchingListPattern([],_,Dict,_,_,_,_) -> {true,[],Dict};
graphMatchingListPattern([NP|NPs],NE,Dict,NodesAcum,FromIO,Stack,Edges)->	
    %io:format("GMLP: ~w~n",[{NP,NE}]),
    {Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum,FromIO,Stack,Edges),
    {Bool2,DataArcs2,Dict3}=graphMatchingListPattern(NPs,NE,Dict2,NodesAcum,FromIO,Stack,Edges),
    {Bool1 and Bool2,DataArcs1++DataArcs2,Dict3}.
    
    
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListPattern  %%%%%%%%%%%%%%%%%%%%%%%%%%%%   
graphMatchingListPatternOr([],_,Dict,_,_,_) -> {true,[],Dict};
graphMatchingListPatternOr([NP|NPs],NE,Dict,NodesAcum,From,Edges)->	
    %io:format("GMLPO: ~w~n",[{NP,NE}]),
    {Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum, From,[],Edges),
    %io:format("GMLPO2: ~w~n",[{Bool1,DataArcs1}]),
    DataArcs1Aux=
     case Bool1 of
     	true -> DataArcs1;
     	_ -> []
     end,
    {Bool2,DataArcs2,Dict3}= graphMatchingListPatternOr(NPs,NE,Dict2,NodesAcum, From,Edges),
    %io:format("GMLPO3: ~w~n",[{Bool2,DataArcs1Aux ++DataArcs2}]),
    {Bool1 or Bool2, DataArcs1Aux ++DataArcs2,Dict3}.
	
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListAll  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphMatchingListAll([],[],Dict,_,_,_,_) -> {true,[],Dict};	
graphMatchingListAll([],_,Dict,_,_,_,_) -> {false,[],Dict};	
graphMatchingListAll(_,[],Dict,_,_,_,_) -> {false,[],Dict};
graphMatchingListAll([NP|NPs],[NE|NEs],Dict,NodesAcum,FromIO,Stack,Edges)->	
    %io:format("GMLA: ~w~n",[{NP,NE}]),
    {Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum,FromIO,Stack,Edges),
    %io:format("GMLA Results: ~w~n",[{Bool1,NPs,NEs}]),
    case Bool1 of 
        true -> 
            {Bool2,DataArcs2,Dict3}=graphMatchingListAll(NPs,NEs,Dict2,NodesAcum,FromIO,Stack,Edges),
	    {Bool2,DataArcs1++DataArcs2,Dict3};
	false-> {false,[],Dict}
    end.  


%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListAllIO  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphMatchingListAllIO([],[],_,_,_,_,_) -> {true,[],[]};	
graphMatchingListAllIO([],_,_,_,_,_,_) -> {false,[],[]};	
graphMatchingListAllIO(_,[],_,_,_,_,_) -> {false,[]};
graphMatchingListAllIO([NP|NPs],[NE|NEs],Dict,Edges,NodesAcum,FromIO,Edges)->
    {_,DataArcs1,_}=graphMatching(NP,NE, Dict,NodesAcum,FromIO,[],Edges),
    {Bool2,DataArcs2,_}=graphMatchingListAllIO(NPs,NEs, Dict,Edges,NodesAcum,FromIO,Edges),
    {Bool2,DataArcs1++DataArcs2,[]}.
	
%%%%%%%%%%%%%%%%%%%%%%%%  graphMatchingListAllLinkClauses  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
graphMatchingListAllLinkClauses([],[],Dict,_,_,_) -> {true,[],Dict};	
graphMatchingListAllLinkClauses([],_,Dict,_,_,_) -> {true,[],Dict};	
graphMatchingListAllLinkClauses(_,[],Dict,_,_,_) -> {true,[],Dict};
graphMatchingListAllLinkClauses([NP|NPs],[NE|NEs],Dict,NodesAcum,FromIO,Edges)->	
    {Bool1,DataArcs1,Dict2}=graphMatching(NP,NE,Dict,NodesAcum,FromIO,[],Edges),
    case Bool1 of 
        true -> 
            {Bool2,DataArcs2,Dict3}=graphMatchingListAllLinkClauses(NPs,NEs,Dict2,NodesAcum,FromIO,Edges),
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
    
%    Dict= [],
   Dict=
        case NodesArgs of
            [] -> []; 
            [NodeArg|_] -> 
                %io:format(" NodeArg ~w ~n",[ NodeArg]),
                NodesIn = [NFIn||{node,NFIn,{function_in,_,_,_,_}}<-Nodes],
                %io:format(" NodesIn ~w ~n",[ NodesIn]),
                NI=giveMeNodeIn(NodeArg, NodesIn,Edges),
                %io:format("NI ~w ~n",[NI]),
    	        get(NI)
    	end,
                 %io:format("Dict ~w ~n",[Dict]),   
    if
	Strong -> 
	    {_,EdgesMatch,_}=graphMatchingListAllIO(NodesPatterns,NodesArgs, Dict,Edges,Nodes,input,Edges), 
	    {
	        [NodeClauseIn],
	        [{edge,getParentControl(CNode,Edges),NodeClauseIn,input}||CNode<-CalledNodes]
		%[{edge,CalledNode,NodeClauseIn,input}||CalledNode<-CalledNodes]
	    		++ changeEdgeType(changeEdgeType(EdgesMatch,summary_data,summary_data_input),data,input)
			%++ changeEdgeType(EdgesMatch,summary_data,summary_data_input)
		 	++[{edge,Last,NodeReturn,output}||Last<-Lasts]
	    };
	Weak -> 
	    {_,EdgesMatch,_}=graphMatchingListAllIO(NodesPatterns,NodesArgs, Dict,Edges,Nodes,input,Edges),
	    {MClauses,NewEdges}=inputOutputEdgesFunction(Nodes,Edges,InfoCall,CalledNodes,ClausesInfo),
	    {
	    	[NodeClauseIn| MClauses],
	  	[{edge,getParentControl(CalledNode,Edges),NodeClauseIn,input}||CalledNode<-CalledNodes]
		 	++ changeEdgeType(changeEdgeType(EdgesMatch,summary_data,summary_data_input),data,input)
		 	%++ changeEdgeType(EdgesMatch,summary_data, summary_data_input)
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
    %io:format("Reachables ~p ~n",[lists:sort(removeDuplicates(Reachables))]),
    [NodePattern||NodePattern<-NodesPatterns,lists:member(NodePattern,Reachables)]
    		++getReachablePatterns(Nodes,Edges,ClausesInfo).

%%%%%%%%%%%%%%%%%%%%%%%%  reachablesFrom  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
reachablesFrom(Node,Nodes,Edges,PreviouslyAnalyzed)->
    %io:format("reachablesFrom  Node ~w ~n",[Node]),
    Parents=[NodeO||{edge,NodeO,NodeD, Type_}<-Edges,NodeD==Node,Type <- [data,control,summary,summary_data], Type_== Type],
    ChildrenCall= 
        case [NodeCall||{node,NodeCall,{call,_}}<-Nodes,NodeCall==Node] of
	    []->[];
	    _-> [NodeD||{edge,NodeO,NodeD,Type_}<-Edges,NodeO==Node, Type <- [data,control,summary, summary_data], Type_== Type ]
	end,
    %io:format("reachablesFrom  ChildrenCall ~w ~n",[ChildrenCall]),
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
%io:format("buildSummaryEdgesArgs ~w ~n",[{NodeReturn,[NodeArg|NodesArgs], NeedPatterns}]),
    removeDuplicates([{edge,NodeArg_,NodeReturn,summary}||
			   {edge,NodeArg_,NodePattern,input}<-Edges,
			   NodeArg_==NodeArg,
			   lists:member(NodePattern,NeedPatterns)]
    ++buildSummaryEdgesArgs(Edges,NodeReturn,NeedPatterns,NodesArgs)).


%%%%%%%%%%%%%%%%%%%%%%%%  buildNewSummaryEdges  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildNewSummaryEdges(Edges, Nodes) ->
	Pending=get(pending),
	%io:format("Pending ~w ~n",[Pending]),
	case Pending of
	    [CurrentPend={NP,_}|RestPending] ->
	        %io:format("NodeCall_ ~w ~n",[{NCall, Nodes}]), 
		VarsPM=nodesVarsExpression([NP],Nodes,Edges),
	%	io:format("VarsPM ~w ~n",[VarsPM]),
		
		ListSummarys=buildNewSummaryEdgesAux(VarsPM,Edges,Nodes, CurrentPend),
	        
	        erase(pending),
		put(pending,RestPending),
	       
%	        [{edge,Orig, NP, NewTypeEdges}||{edge,Orig,_,summary}<-ListSummarys]++
	        %[{edge,Orig, Dest, From}||{edge,Orig,Dest,summary}<-ListSummarys]++
		ListSummarys++
	        buildNewSummaryEdges(Edges,Nodes);		
	    _ -> []
	end.

%%%%%%%%%%%%%%%%%%%%%%%%  buildNewSummaryEdgesAux  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildNewSummaryEdgesAux([],_,_,_)->[];
buildNewSummaryEdgesAux([VarPM|VarsPM],Edges,Nodes, {NP,Ncall}) ->
	FinalsPM=[Orig||
		   {edge,Orig, VarPM_,output}<-Edges, VarPM == VarPM_],
	       %io:format("FinalsPM ~w ~n",[FinalsPM]),
	ListFinals=groupByClause3(
	    [{
	    	giveMeNodeClauseIn(FinalPM,Nodes,Edges),
	        FinalPM,
	        nodesPatternsClause(giveMeNodeClauseIn(FinalPM,Nodes,Edges),Edges)
	     }
	                ||FinalPM<-FinalsPM]),		
	       %io:format("ListFinals ~w ~n",[ListFinals]),
	       ReachablePatterns=getReachablePatterns(
	       	Nodes,
	       	Edges,
	       	[{0,ListPatterns,0,ListFinal,0}|| 
	       	       {_, ListFinal, ListPatterns} <-ListFinals]),
	       %io:format("ReachablePatterns ~w ~n",[ReachablePatterns]),
	       [{_,_,Args,_}]=buildCallsInfo(Nodes,Edges, [Ncall]),
	       %io:format("Args ~w ~n",[Args]),	       
	       ListSummarys=buildSummaryEdges(Edges, ReachablePatterns,[{0,0, Args, VarPM}]),
	       %io:format("ListSummarys ~w ~n",[ListSummarys]),
	       ListSummarys ++ 
	       buildNewSummaryEdgesAux(VarsPM,Edges,Nodes, {NP, Ncall}).







%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%      SUMMARY_INOUT           %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildSummaryINOUT(Nodes,Edges) ->
    io:format("pendings1 ~w ~n",[{get(pending_input), get(pending_output)}]),
    Summary_input_Edges = 
      case get(pending_input) of
           undefined -> [];
           Pend -> buildSummaryInputEdges(Pend,Nodes,Edges,[])
       end,
       
    io:format("\n\n\n\n\n\n\n***************\n\n\n\n\n\n"),
    Summary_output_Edges = 
      case get(pending_output) of
           undefined -> [];
           PendOut -> buildSummaryOutputEdges(PendOut,Nodes,Edges,[])
       end,
    io:format("pendings2 ~w ~n",[{get(pending_input), get(pending_output)}]),
    case {get(pending_input), get(pending_output)}  of
    	{[],[]} -> {Summary_input_Edges, Summary_output_Edges};
    	{undefined,_} -> {Summary_input_Edges, Summary_output_Edges};
    	{_,undefined} -> {Summary_input_Edges, Summary_output_Edges};
    	_ -> 
    	    {Summary_input_EdgesAcum, Summary_output_EdgesAcum} = buildSummaryINOUT(Nodes,Edges++ Summary_input_Edges++ Summary_output_Edges),
    	    {Summary_input_EdgesAcum ++ Summary_input_Edges, Summary_output_EdgesAcum ++ Summary_output_Edges}  
    end.    


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%      SUMMARY_INPUT_EDGES           %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildSummaryInputEdges([],_,_,_) -> [];
buildSummaryInputEdges([{NodePM,NodesPending,Stack}| _],Nodes,Edges,PendingsDone) -> 
	NewPendingsDone =[{NodePM,NodesPending,Stack}| PendingsDone],
	%io:format("NewPendingsInputDone: ~w~n",[NewPendingsDone]),
        io:format("DICTINARY_ IN _ 1: ~w~n",[get()]),
	
	%io:format("Before: ~w~n",[Edges]),
	%io:format("findClauseIn(NodePending,Edges, Nodes): ~w~n",[[findClauseIn(NodePending,Edges, Nodes)|| NodePending<-NodesPending]]),
	
	NodesClauseInAux=removeDuplicates(lists:flatten([findClauseIn(NodePending,Edges, Nodes)|| NodePending<-NodesPending])),
	%io:format("NodesClauseInAux: ~w~n",[NodesClauseInAux]),
	%COMPROVAMOS QUE SEA CLAUSE_IN DE FUNCION -> solo tiene padre, no abuelo
	NodesClauseIn = removeDuplicates([NodeClause ||{edge,Parent,NodeClause,control}<-Edges,
					NodeClause<-NodesClauseInAux,
					not hasParent(Parent,Edges)]),	
	
	%io:format("NodesClauseIn: ~w~n",[NodesClauseIn]),
	%io:format("NodesClauseIn: ~w~n",[NodesClauseIn]),
	ListCallsClauseIn=
	    case Stack of
		[] -> [Call ||  
			{edge,Call, NodeClauseIn_,input} <- Edges,
			NodeClauseIn <-NodesClauseIn,
			NodeClauseIn_== NodeClauseIn];
		[Head|_] -> [Head]
	    end,
	%io:format("ListCallsClauseIn: ~w~n",[ListCallsClauseIn]),
	%io:format("InputEdges: ~w~n",[InputEdges]),
	%io:format("NodesPendingIN: ~w~n",[NodesPending]),		
        Origs=[Orig ||{edge,Orig, NodePending_,input} <- Edges,NodePending<-NodesPending,NodePending_==NodePending],
	NodesIn = [NFIn||{node,NFIn,{function_in,_,_,_,_}}<-Nodes],
	
	%io:format("Origs: ~w~n",[Origs]),
	NodesGMOrigsAux=removeDuplicates(
	                      lists:flatten(
	                             [findChildrenOfCall(Orig,ListCallsClauseIn,Edges,Nodes)
	                                      || Orig <- Origs])),
	%io:format("NodesGMOrigsAux: ~w~n",[NodesGMOrigsAux]),	                                      
	NodesGMOrigs =
	    case NodesGMOrigsAux of
	        [] ->
	           Dicts = 
		           [case giveMeNodeIn(Orig, NodesIn, Edges) of
		             -1 -> [];
		             NI -> get(NI)
		           end||Orig<-Origs],
		
		
		   OrigsByClauses=[{giveMeNodeClauseIn(Orig,Nodes,Edges),Orig} || Orig<-Origs],
		   %io:format("OrigsByClauses: ~w~n",[OrigsByClauses]),
		   GroupOrigsByClauses= groupByClause2(OrigsByClauses),
		   %io:format("GroupOrigsByClauses: ~w~n",[GroupOrigsByClauses]),
		   IntersectionsOrigs=findIntersectionsOrigs(GroupOrigsByClauses,Nodes,Edges),
		   %io:format("findIntersectionsOrigs: ~w~n",[IntersectionsOrigs]),
		   IntersectionsOrigs;

	        _ -> NodesGMOrigsAux
	    end,
	%io:format("NodesGMOrigs: ~w~n",[NodesGMOrigs]),
	
	NewNodesOrigs=[NodeGMOrigs || NodeGMOrigs <-NodesGMOrigs, 
				not lists:member(NodeGMOrigs,[undef,undef_input]),
				not is_tuple(NodeGMOrigs)],
	
	%io:format("NewNodesOrigs: ~w~n",[NewNodesOrigs]),
	
	EdgesSD= graphMatchingListDicts(NodePM, NewNodesOrigs,Nodes, Edges ,summary_input,Stack,Edges),
	
	
	NewPendingNodes_ = get(pending_input),
	%io:format("NewPendingNodesINPUTBefore: ~w~n",[NewPendingNodes_]),
	%io:format("EL PROBLEMA ESTA ASI?????? NO SEL DEURIA DE CARREGAR!!!!! ~n"),	 
%	NewPendingNodes = 
%	    case NewNodesOrigs of
%	    	[] -> NewPendingNodes_;
%	    	_ -> sets:to_list(
%	                     sets:subtract(sets:from_list(NewPendingNodes_),
%	                                   sets:from_list(NewPendingsDone)))
%	    end,
	NewPendingNodes = sets:to_list(
	                     sets:subtract(sets:from_list(NewPendingNodes_),
	                                   sets:from_list(NewPendingsDone))),

	%io:format("NewPendingNodesINPUTAfter: ~w~n",[NewPendingNodes]),                                  
		%ListPendingAux=
	erase(pending_input),
%        ListPending= 
%       	        case ListPendingAux of
%          	    undefined -> [];
%          	    _ -> RestPendings
%          	end,
%        io:format("ListPendingOut: ~w~n",[ListPending]),
        put(pending_input, NewPendingNodes),
        
        io:format("DICTINARY _ IN _ 2: ~w~n",[get()]),	                                   
	                                   
	%io:format("Before: ~w~n",[Edges]),
	%io:format("After: ~w~n",[changeEdgeType(changeEdgeType(Edges,data,input),summary_data,summary_data_input)]), 
	FinalEdges=changeEdgeType(changeEdgeType(EdgesSD,data,input),summary_data,summary_data_input),
	
	FinalEdges ++ buildSummaryInputEdges(NewPendingNodes,Nodes, Edges++FinalEdges, NewPendingsDone).
	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%      SUMMARY_OUTPUT_EDGES           %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
buildSummaryOutputEdges([],_,_,_) -> [];
buildSummaryOutputEdges([{NodePM,NodeCall,Stack}| _],Nodes,Edges,PendingsDone) -> 
	NewPendingsDone =[{NodePM,NodeCall,Stack}| PendingsDone],
	
	NewPendingsDoneAdapted=[{NodePM,Entry}||{NodePM,NodeCall,Stack} <-NewPendingsDone,Entry<-Stack],
	erase(pending),
        put(pending, removeDuplicates(NewPendingsDoneAdapted)),	       
	
	io:format("DICTINARY_ OUT _ 1: ~w~n",[get()]),
	
	%1. Buscar el return del call
	%2. Seguir les output en ordre invers --> Last de la definicio
	%3. Tirar cap a dalt hasta arribar al clause_in
	%4. Traure els firsts dels lasts
	%5. Llançar GraphMatching entre NodePM y el first del last
	%6. Canviar datos x output y summary per summary_output
	%io:format("NodeCall: ~w~n",[NodeCall]),
	ChildrenNCall=[NodeChildren || 
	                    {edge,NodeCall_,NodeChildren,control}<-Edges, NodeCall_== NodeCall],
	%io:format("ChildrenNCall: ~w~n",[ChildrenNCall]),
	NodeAux=                    
	    case ChildrenNCall of
		[] -> NodeCall;
		_ -> lists:nth(1,[NodeChildren || 
	                    {edge,NodeCall_,NodeChildren,control}<-Edges,
	                    {_,NodeChildren_,return}<-Nodes,
	                    NodeCall_==NodeCall,
	                    NodeChildren_==NodeChildren])
	    end,

	%io:format("NodeAux: ~w~n",[NodeAux]),
	
	case [Last || {edge,Last, NodeAux_,output} <- Edges, NodeAux_== NodeAux] of
		[] -> FisrstLastsFunction=[],NodeIn =-1, Dict=[];
		A -> LastFunction=lists:nth(1,A), 	
	 	     %Last || {edge,Last, NodeAux_,output} <- Edges, NodeAux_== NodeAux]),
		     %io:format("LastFunction: ~w~n",[LastFunction]),
			ClauseIN = giveMeNodeClauseIn(LastFunction,Nodes,Edges),
			%io:format("ClauseIN: ~w~n",[ClauseIN]),
			FisrstLastsFunction= lists:flatten([ FL || 
						{node, ClauseIN_,{clause_in,FL,_}} <-Nodes, 
						ClauseIN_ == ClauseIN]),
			%io:format("FisrstLastsFunction: ~w~n",[FisrstLastsFunction]),		
			NodesIn = [NFIn||{node,NFIn,{function_in,_,_,_,_}}<-Nodes],
			NodeIn=giveMeNodeIn(lists:nth(1, FisrstLastsFunction), NodesIn, Edges),
			Dict = case NodeIn of
			             -1 -> [];
			             NI -> get(NI)
			         end
	end,
	
	%io:format("DictBefore: ~w~n",[Dict]),
	
	{_,EdgesSDOut,NewDict}= graphMatchingList(NodePM,FisrstLastsFunction,Dict,Nodes, summary_output,Stack,Edges),
	%	io:format("EdgesSDOut: ~w~n",[EdgesSDOut]),
	%io:format("DictAfter: ~w~n",[NewDict]),
	
	
	case NodeIn of
		-1 -> true;
		_ -> 
			erase(NodeIn),
			put(NodeIn, NewDict)
	end,
	
	
	%Gestión Pendings
	NewPendingNodes_ = get(pending_output),
	%io:format("pending_output Before: ~w~n",[NewPendingNodes_]),
	%io:format("NewPendingNodes_: ~w~n",[NewPendingNodes_]),
	NewPendingNodes = sets:to_list(
	                     sets:subtract(sets:from_list(NewPendingNodes_),
	                                   sets:from_list(NewPendingsDone))),
	
	%ListPendingAux=
	erase(pending_output),
%        ListPending= 
%       	        case ListPendingAux of
%          	    undefined -> [];
%          	    _ -> RestPendings
%          	end,
%        io:format("ListPendingOut: ~w~n",[ListPending]),
        put(pending_output, NewPendingNodes),
        
        io:format("DICTINARY_ OUT _ 2: ~w~n",[get()]),
        
	%io:format("pending_output After: ~w~n",[NewPendingNodes]),                      
	changeEdgeType(changeEdgeType(EdgesSDOut,data,output),summary_data,summary_data_output)
		++ buildSummaryOutputEdges(NewPendingNodes,Nodes, Edges, NewPendingsDone).








%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%      AUXILIAR FUNCTIONS           %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

%%%%%%%%%%%%%%%%%%%%%%%%  varsExpression  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
varsExpression({var,_,'_'})-> [];                                                          
varsExpression({var,_,Name})-> [Name];
varsExpression({term,{var,_,Name}})->[Name];
varsExpression({match,_,E1,E2})-> removeDuplicates(varsExpression(E1)++varsExpression(E2));
varsExpression({tuple,_,Es}) -> removeDuplicates([Var||E<-Es,Var<-varsExpression(E)]);
varsExpression({cons,_,EH,ET}) -> removeDuplicates(varsExpression(EH)++varsExpression(ET));
varsExpression({op,_,_,E1,E2})-> removeDuplicates(varsExpression(E1)++varsExpression(E2));
varsExpression({op,_,_,E})-> varsExpression(E);
varsExpression(_)-> [].


%%%%%%%%%%%%%%%%%%%%%%%%  varsTypeNode  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
varsTypeNode({term,{var,_,'_'}}) -> [];
varsTypeNode({term,{var,_,V}}) -> [V];
varsTypeNode({var,_,V}) -> [V];
varsTypeNode({block,E,_,_}) -> removeDuplicates(varsTypeNode(E));
varsTypeNode({pm,E1,E2}) -> removeDuplicates(varsTypeNode(E1)++ varsTypeNode(E2));
varsTypeNode({op,_,E,_,_}) -> removeDuplicates(varsTypeNode(E));
varsTypeNode({tuple,_,Es}) -> removeDuplicates([Var||E<-Es,Var<-varsTypeNode(E)]);
varsTypeNode({cons,_,EH,ET}) -> removeDuplicates(varsTypeNode(EH)++ varsTypeNode(ET));
varsTypeNode(_)-> [].

%%%%%%%%%%%%%%%%%%%%%%%%  nodesVarsExpression  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
nodesVarsExpression([],_,_)->[];
nodesVarsExpression(NodesVars,Nodes,Edges) ->
    Children=[Dest||{_,Node_,Dest,control}<-Edges,Node<-NodesVars,Node_==Node],
    NodesAct=[N__||{node,N__,{term,{var,_,_}}}<-Nodes,N_<-NodesVars,N__==N_],
    NodesAct ++ nodesVarsExpression(Children,Nodes,Edges).
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
existVarDictGM(V,[{V,ND,undefIO} | _],NP) -> not lists:member(NP,ND);
existVarDictGM(V,[{V,ND,[]} | _],NP) -> not lists:member(NP,ND);
existVarDictGM(V,[{V,ND,undef_input} | _],NP) -> not lists:member(NP,ND);
existVarDictGM(V,[{V,ND,{undef_output,_}} | _],NP) -> not lists:member(NP,ND);
existVarDictGM(V,[{V,_,_} | _],_) -> true;
existVarDictGM(V,[_ | Dict],NP) -> existVarDictGM(V,Dict,NP);
existVarDictGM(_,[],_)->false.

%%%%%%%%%%%%%%%%%%%%%%%%  existVarDictUndef  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
existVarDictUndef(V,[{V,_,undef} | _]) -> false;
existVarDictUndef(V,[{V,_,undefIO} | _]) -> false;
existVarDictUndef(V,[{V,_, undef_input} | _]) -> false;
existVarDictUndef(V,[{V,_,{undef_output,_}} | _]) -> false;
existVarDictUndef(V,[{V,_,_} | _]) -> true;
existVarDictUndef(V,[_ | Dict]) -> existVarDictUndef(V,Dict);
existVarDictUndef(_,[])->false.


%%%%%%%%%%%%%%%%%%%%%%%%  getNumNodes  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
getNumNodes([])->[];
getNumNodes([{node,Num,_}|Nodes])->[Num]++getNumNodes(Nodes).


%%%%%%%%%%%%%%%%%%%%%%%%  findPMVar  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
findPMVar(V,Dict)-> 	
    case [{NodePM,NodeDecl} || {Var,NodeDecl,NodePM} <-Dict,Var==V] of
        [{undef,NodeDecl}|_] -> {[],NodeDecl};
        [{undefIO,NodeDecl}|_] -> {[],NodeDecl};
        [{undefined,NodeDecl}|_] -> {[],NodeDecl};
        [{undef_input,NodeDecl}|_] -> {[],NodeDecl};
        [{{undef_output,_},NodeDecl}|_] -> {[],NodeDecl};
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
lasts({op,_,_,_,Lasts}) -> Lasts;
lasts(_)-> [].

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
changeEdgeTypeNotAcum([],_,_)->[];
changeEdgeTypeNotAcum([{edge,NS,NT,OldType}|Es],OldType,NewType)->
	[{edge,NS,NT,NewType}]++changeEdgeTypeNotAcum(Es,OldType,NewType);
changeEdgeTypeNotAcum([E|Es],OldType,NewType)->
	changeEdgeTypeNotAcum(Es,OldType,NewType).    
    
 
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
	     
	     
	     
%%%%%%%%%%%%%%%%%%%%%%%%  linkEntrysDict  %%%%%%%%%%%%%%%%%%%%%%%%%%%% 	 	       	 	            
linkEntrysDict([]) -> [];
linkEntrysDict([{V,ND,PM}|List]) -> 
    NDAll= getNDEntryDict(V,List),
    PMAll= getPMEntryDict(V,List),
    %io:format("linkEntrysDict {NDAll, PMAll,ND,PM} :~p~n",[{NDAll, PMAll,ND,PM}]),
    NewDict=[Entry||Entry={V_,_,_}<-List,V_ /=V],
    PMAux=
        case PM of
            undefIO -> undefIO;
            undef -> undef;
            Rest -> Rest++PMAll
        end,
    [{V,ND++NDAll, PMAux}]++linkEntrysDict(NewDict).
				    

%%%%%%%%%%%%%%%%%%%%%%%%  getNDEntryDict  %%%%%%%%%%%%%%%%%%%%%%%%%%%% 
getNDEntryDict(_,[]) -> [];
getNDEntryDict(V,[{V,ND,_}|List]) -> ND++getNDEntryDict(V,List);
getNDEntryDict(V,[{_,_,_}|List]) -> getNDEntryDict(V,List).


%%%%%%%%%%%%%%%%%%%%%%%%  getPMEntryDict  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
getPMEntryDict(_,[]) -> [];
getPMEntryDict(V,[{V,_,NP}|List]) when NP/=undef -> NP++getPMEntryDict(V,List);
getPMEntryDict(V,[{_,_,_}|List]) -> getPMEntryDict(V,List).			
		 	


%%%%%%%%%%%%%%%%%%%%%%%%  leaves  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%leaves(N,Ns,Es) ->
%	Children=getChildren(N,Ns,Es),
%	Leaves=[N_||N_<-Children,getChildren(N_,Ns,Es)==[]],
%	NonLeaves=[N_||N_<-Children,getChildren(N_,Ns,Es)/=[]],
%	Leaves++[Leaf||NonLeaf<-NonLeaves,Leaf<-leaves(NonLeaf,Ns,Es)].
%

%%%%%%%%%%%%%%%%%%%%%%%%  getChildren  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%getChildren(N,Ns,Es)->[N_||{node,N_,_}<-Ns,{edge,NS,NT,control}<-Es,NS==N,NT==N_].


%%%%%%%%%%%%%%%%%%%%%%%%  giveMeNodeIn  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
giveMeNodeIn(Node,NodesIn,Edges) ->
   % io:format("Edges ~w ~n",[[||{edge,Parent,Node_,control}<-Edges]]),

    case lists:member(Node, NodesIn) of
         true -> Node;
         false -> case [Parent||{edge,Parent,Node_,control}<-Edges,Node==Node_] of
                       [] -> -1;
                       [Head|_] -> giveMeNodeIn(Head, NodesIn,Edges) 
                   end
    end.
    
%%%%%%%%%%%%%%%%%%%%%%%%  giveMeNodeClauseIn  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
giveMeNodeClauseIn(Node,Nodes,Edges) ->
   [NodeParent|_]=[Parent || {edge,Parent,Node_,control} <- Edges, Node_== Node],
      %io:format("NodeParent ~w ~n",[NodeParent]),
   NodeClauseIn=[NodeParent_ || {node, NodeParent_,{clause_in,_,_}}<-Nodes, NodeParent_== NodeParent],
   case NodeClauseIn of
   	[] -> giveMeNodeClauseIn(NodeParent,Nodes,Edges);
   	_ -> lists:nth(1,NodeClauseIn)
   end.

%%%%%%%%%%%%%%%%%%%%%%%%  findClauseIn  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
findClauseIn(Node,Edges,Nodes) ->  
	[ParentControl|_]=[Orig||{edge,Orig,Node_,control}<-Edges,Node_==Node],
	ParentsClauseIn=[Orig_ ||{node, Orig_,{clause_in,_,_}}<-Nodes,Orig_==ParentControl],
	case ParentsClauseIn of
	    [] -> findClauseIn(ParentControl,Edges,Nodes);
	    _ -> lists:nth(1,ParentsClauseIn)
	end.
 
		
%%%%%%%%%%%%%%%%%%%%%%%%  findChildrenOfCall  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
findChildrenOfCall(_,[],_,_) -> [];
findChildrenOfCall(Orig,ListCallsClauseIn,Edges,Nodes) ->
    ParentsCall=[Orig_||{edge,PreOrig,Orig_,control}<-Edges,
                           Orig_== Orig,
                           lists:member(PreOrig,ListCallsClauseIn)],
    case ParentsCall of
    	[] -> Parents= [PreOrig|| {edge,PreOrig,Orig_,control}<-Edges,
    						Orig_==Orig],
    	      case Parents of
    	          [] ->[]; 
    	          _  ->findChildrenOfCall(lists:nth(1,Parents),
    		       ListCallsClauseIn,Edges,Nodes)
    	      end;
    	_ -> lists:nth(1,ParentsCall)
    end.


%%%%%%%%%%%%%%%%%%%%%%%%  combineDuplicatesDeclDic  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
combineDuplicatesDeclDic([]) -> [];
combineDuplicatesDeclDic(List=[{Var1,_,_}|Dic]) ->
    ListEntrys=[Entry || Entry={Var1_,_,_}<-List, Var1_==Var1],
    ListDeclCombined=lists:flatten([Decl||{_,Decl,_}<-ListEntrys]),
    ListPMCombined=lists:flatten([PM||{_,_,PM}<-ListEntrys]),
    NewEntry=[{Var1,ListDeclCombined,ListPMCombined}],
    RestList=[Entry || Entry={Var1_,_,_}<-List, Var1_/=Var1],
    NewEntry++combineDuplicatesDeclDic(RestList).
    


%%%%%%%%%%%%%%%%%%%%%%%%  groupByClause3  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
groupByClause3([]) -> [];
groupByClause3(CompleteList=[{Clause_In,NodeFinal,NodesPatterns}|RestClauses]) ->
	[{Clause_In,
	 removeDuplicates(lists:flatten([List||{Clause,List,_}<-CompleteList,Clause==Clause_In])),
	 NodesPatterns}]
	++ groupByClause3([RestClause||RestClause={Clause,_,_}<-RestClauses,Clause/=Clause_In]).
	
%%%%%%%%%%%%%%%%%%%%%%%%  groupByClause2  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
groupByClause2([]) -> [];
groupByClause2(CompleteList=[{Clause_In,NodeFinal}|RestClauses]) ->
	[{Clause_In,
	 removeDuplicates(lists:flatten([List||{Clause,List}<-CompleteList,Clause==Clause_In]))}]
	++ groupByClause2([RestClause||RestClause={Clause,_}<-RestClauses,Clause/=Clause_In]).
	
	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%  nodesPatternsClause  %%%%%%%%%%%%%%%%%%%%%%%%%%%%	
nodesPatternsClause(Clause,Edges)->
   [NGuard|NsPat_]=
       lists:reverse(
           lists:sort(
               [Child||
                   {edge,NClause_,Child,control}<-Edges,
                   Clause==NClause_])),
   NodesPatterns=lists:reverse(NsPat_).	
   

%%%%%%%%%%%%%%%%%%%%%%%%  nodesPatternsClause  %%%%%%%%%%%%%%%%%%%%%%%%%%%%   
addEntryDictPendings(Type,First,Second,Stack) ->
    ListPendingOutAux=erase(Type),
    ListPendingOut= 
        case ListPendingOutAux of
            undefined -> [];
            _ -> ListPendingOutAux
        end,
        put(Type,ListPendingOut++[{First, Second,Stack}]).
        
        
        
%%%%%%%%%%%%%%%%%%%%%%%%  updateGMDict  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
updateGMDict(Dict,V,NE,NP,From, Nodes,Edges) ->
    NodesIn = [NFIn||{node,NFIn,{function_in,_,_,_,_}}<-Nodes],
    NodeIn=giveMeNodeIn(NP, NodesIn, Edges),
    DictAux=
        case From of
            summary_input -> 
    		case NodeIn of
             	    -1 -> [];
                    NI_In -> get(NI_In)
        	end;
    	    summary_output -> 
    		case NodeIn of
             	    -1 -> [];
                    NI_Out -> get(NI_Out)
        	end;
    	    _ -> Dict
    	end,
    	
    NewDict=removeDuplicates([{V_,DV,[NE]}||{V_,DV,undef}<-DictAux,V_==V]
     	++[{V_,DV,[NE]}||{V_,DV,undef_input}<-DictAux,V_==V]
        ++[{V_,DV,[NE]}||{V_,DV,{undef_output,_}}<-DictAux,V_==V]
        ++[{V_,DV,[NE]}||{V_,DV,[]}<-DictAux,V_==V]
        ++[{V_,DV,PM}||{V_,DV,PM}<-DictAux,V_==V,not lists:member(PM,[undef_input, undef,[]]),not is_tuple(PM)]
        ++[DE||DE={V_,_,_}<-DictAux,V_/=V]),
        
    case From of
    	summary_input -> 
            case NodeIn of
             	    -1 -> true;
                    NI_In_Final -> 
                        erase(NI_In_Final),
    	    		put(NI_In_Final, NewDict)
            end,
    	    Dict;
    	summary_output -> 
            case NodeIn of
             	    -1 -> true;
                    NI_Out_Final -> 
                        erase(NI_Out_Final),
    	    		put(NI_Out_Final, NewDict)
            end,
    	    Dict;
    	_ -> NewDict
    end.
        
        
%%%%%%%%%%%%%%%%%%%%%%%%  updateVarsPattern  %%%%%%%%%%%%%%%%%%%%%%%%%%%%        
updateVarsPattern(Type, Nodes,Edges,TypeNP,NP,Stack) ->
    NodesIn = [NFIn||{node,NFIn,{function_in,_,_,_,_}}<-Nodes],
    NodeIn=giveMeNodeIn(NP, NodesIn, Edges),
    Dict = case NodeIn of
             -1 -> [];
             NI -> get(NI)
        end,   
    VarsPM= varsTypeNode(TypeNP),
    DictOthers=[Entry||Entry={Var_,_,_}<-Dict,not lists:member(Var_,VarsPM)],
    DictThis=[Entry||Entry={Var_,_,_}<-Dict,lists:member(Var_,VarsPM)],
    
    NewDict=
        case Type of
    	    input -> 
    	        DictOthers++
                [Entry || Entry={_,_,PM}<-DictThis,PM/=undef]++
                [{Var,DV,undef_input} || {Var,DV,PM}<-DictThis,PM==undef];
    	    output ->
	        DictOthers++
                [Entry || Entry={_,_,PM}<-DictThis,PM/=undef]++
                [{Var,DV,{undef_output,Stack}} || {Var,DV,PM}<- DictThis,PM==undef]	
        end,
    
    case NodeIn of
        -1 -> true;
        NIFinal -> erase(NIFinal),put(NIFinal, NewDict)
    end.



%%%%%%%%%%%%%%%%%%%%%%%%  findIntersectionsOrigs  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
findIntersectionsOrigs([],_,_)->[];
findIntersectionsOrigs([{Clause,ListFinals}|RestClauses],Nodes,Edges) ->
	io:format("findIntersectionsOrigs ~w~n",[{[{Clause,ListFinals}|RestClauses]}]),
	ListReachablesClauses=[sets:from_list(removeDuplicates(reachablesBackwardControl(Final, Edges))) || Final<-ListFinals],
	io:format("ListReachablesClauses ~w~n",[ListReachablesClauses]),
	io:format("intersection ~w~n",[sets:to_list(sets:intersection(ListReachablesClauses))]),
	[lists:max(sets:to_list(sets:intersection(ListReachablesClauses)))]
		++findIntersectionsOrigs(RestClauses,Nodes,Edges).




%%%%%%%%%%%%%%%%%%%%%%%%  reachablesBackwardControl  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
reachablesBackwardControl(Node,Edges) -> 
	Parent=[Parent||{edge,Parent,Node_,control}<-Edges,Node_==Node],
	[Node |
		case Parent of
			[] -> [];
			[NodeParent|_] -> [NodeParent| reachablesBackwardControl(NodeParent,Edges)]
		end].


%%%%%%%%%%%%%%%%%%%%%%%%  intersection  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
intersection(L1,L2) -> lists:filter(fun(X) -> lists:member(X,L1) end, L2).



%%%%%%%%%%%%%%%%%%%%%%%%  hasParent  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
hasParent(Parent,Edges) ->
	[Orig || {edge,Orig,Parent_,control} <- Edges,Parent_==Parent]/=[].

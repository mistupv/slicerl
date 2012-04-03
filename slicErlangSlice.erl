-module(slicErlangSlice).

-export([start/1]).

start(_) ->
	{ok, DeviceSerialR} = file:open("temp.serial", [read]),
    	Graph=io:get_line(DeviceSerialR,""),
    	ok=file:close(DeviceSerialR),
    	{ok,Tokens,_EndLine} = erl_scan:string(Graph++"."),
	{ok,AbsForm} = erl_parse:parse_exprs(Tokens),
	{value,{Nodes,Edges},_Bs} = erl_eval:exprs(AbsForm, erl_eval:new_bindings()),
	
	
	
	
%   	{ok, DeviceStart} = file:open("start.txt", [read]),
%   	StartPosition=list_to_integer(lists:subtract(io:get_line(DeviceStart,""),"\n"))+1,
%    	ok=file:close(DeviceStart),
%    	{ok, DeviceEnd} = file:open("end.txt", [read]),
%    	EndPosition=list_to_integer(lists:subtract(io:get_line(DeviceEnd,""),"\n"))+1,
%    	ok=file:close(DeviceEnd),
    	{ok, DeviceS} = file:open("shows.txt", [read]),
    	Shows={list_to_atom(lists:subtract(io:get_line(DeviceS,""),"\n")),list_to_atom(lists:subtract(io:get_line(DeviceS,""),"\n")),
           list_to_atom(lists:subtract(io:get_line(DeviceS,""),"\n")),list_to_atom(lists:subtract(io:get_line(DeviceS,""),"\n"))
           ,list_to_atom(lists:subtract(io:get_line(DeviceS,""),"\n")),list_to_atom(lists:subtract(io:get_line(DeviceS,""),"\n"))
           ,list_to_atom(lists:subtract(io:get_line(DeviceS,""),"\n"))},
    	ok=file:close(DeviceS),
%    	{ok,FileContentBin}=file:read_file("temp.erl"),
%    	FileContent=binary_to_list(FileContentBin),
%    	Selected=string:substr(FileContent,StartPosition,EndPosition-StartPosition),
%    	%io:format("~p~n",[Selected++"."]),
%    	Exp=
%    	case erl_scan:string(Selected++".") of
%       	{ok,Tok,_}->	case erl_parse:parse_exprs(Tok) of
%               			{ok,[Exp_]}->Exp_;
%               			_->{}
%      				end;
%       	_->{}
%    	end,
%    	NFileContent=string:substr(FileContent,1,StartPosition-1)
%                 ++"slicing_criterion"
%                 ++string:substr(FileContent,EndPosition,(length(FileContent)-EndPosition)+1),
%    	ok=file:write_file("temp_aux.erl",list_to_binary(NFileContent)),
%    	{ok,Abstract} = smerl:for_file("temp_aux.erl"),
%    	{NodesAux,EdgesAux,_}=slicErlang:graphForms(lists:reverse(smerl:get_forms(Abstract)),0,[]),
%    	%io:format("~w~n",[{NodesAux}]),
%    	IdSC=searchSlicingCriterion(NodesAux,EdgesAux,Edges),
%    	IdSC=[IdSC_||{node,IdSC_,{expression,{atom,_,slicing_criterion}}}<-NodesAux]
%            ++[IdSC_||{node,IdSC_,{pattern,{atom,_,slicing_criterion}}}<-NodesAux],
	[_|IdSC_]=lists:reverse(io:get_line("CS? :")),
	IdSC=[list_to_integer(lists:reverse(IdSC_))],
	io:format("IdSC~p~n",[IdSC]),
    	case IdSC of
               [] -> io:format("Selected code is not valid to perform slicing~n");
               _ ->  %[NodeSlice|_]=IdSC,
                       io:format("Slice from nodes ~w~n",[IdSC]),
                       Slice=sliceFromList(Nodes,Edges,removeDuplicates(IdSC)),
                       slicErlangDot:dotGraph(Nodes,Edges,"temp_slice.dot",Shows,Slice),
                       {ok, DeviceSerialME} = file:open("modname_exports", [read]),
                       ME=io:get_line(DeviceSerialME,""),
                       ok=file:close(DeviceSerialME),
                       {ok,Tokens_,_EndLine_} = erl_scan:string(ME++"."),
                       {ok,AbsForm_} = erl_parse:parse_exprs(Tokens_),
                       {value,{ModName,Exports},_Bs_} = erl_eval:exprs(AbsForm_,
erl_eval:new_bindings()),
                       {ok, DeviceErl} = file:open("tempSliced.erl", [write]),
                       ok=file:write(DeviceErl,restore(Nodes,Edges,ModName,Exports,Slice)),
                       file:close(DeviceErl)
       end.
       
       
    
removeDuplicates(List) -> sets:to_list(sets:from_list(List)).
   
searchSlicingCriterion(Nodes,_,_,"slicing_criterion")->
	 [IdSC_||{node,IdSC_,{term,{atom,_,slicing_criterion}}}<-Nodes]++
	 [IdSC_||{node,IdSC_,{guards,Guards}}<-Nodes,Guard<-Guards,{atom,_,slicing_criterion}<-Guard].
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SLICING FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	

sliceFromList(_,_,[])->[];
sliceFromList(Nodes,Edges,SC)->
    	%io:format("*************~n INPUTS ~n*************~n",[]),
	FollowingInput= sliceFrom(Nodes,Edges,SC,[],input,true),
	%io:format("*************~n OUTPUTS ~n*************~n",[]),
	FollowingOutput= sliceFrom(Nodes,Edges,FollowingInput,[],output,false),
	FollowingOutput.
	

sliceFrom(_,_,[],AccSlices,_,_)-> AccSlices;	
sliceFrom(Nodes,Edges,Slices,AccSlices,Followed,Follow_data)->
    	io:format("\nFollow_data: ~p Slices: ~w~n",[Follow_data ,lists:sort(sets:to_list(sets:from_list(Slices)))]),
    	TypesFollowed = 
    	  case Follow_data of
    	       true -> [data,control,summary,Followed];
    	       false ->case Followed of
    	       		   input -> [control,summary];
    	       		   _ -> [control,summary,Followed]
    	       	       end
    	  end,
    	io:format("Tipes followed: ~p ~n",[ TypesFollowed]),      
	Parents = [N_||N__<-Slices,Type<-TypesFollowed,
	       		{edge,N_,N,Type_}<-Edges,N==N__,Type_==Type],
	
	io:format("Parents: ~w ~n ",[ [{N_, N , Type_ }||N__<-Slices,Type<-TypesFollowed,
	       		{edge,N_,N,Type_}<-Edges,N==N__,Type_==Type]]),
        ParentsSD = [N_||N__<-Slices,{edge,N_,N,Type_}<-Edges,N==N__,Type_==summary_data],
        io:format("ParentsSD: ~w ~n ",[removeDuplicates(ParentsSD)]),
        StopCondSummaryInput =  
            case Followed of
        	input -> ParentsSDInput=[N_||N__<-Slices,{edge,N_,N,Type_}<-Edges,N==N__,Type_==summary_data_input],
        		 (sets:subtract(sets:from_list(ParentsSDInput),sets:from_list(AccSlices++Slices)) == sets:from_list([]));
        	_ -> ParentsSDInput=[],
        	     true
            end,
        
         StopCondSummaryOutput =  
            case Followed of
        	output -> ParentsSDOutput=[N_||N__<-Slices,{edge,N_,N,Type_}<-Edges,N==N__,Type_==summary_data_output],
        		 (sets:subtract(sets:from_list(ParentsSDOutput),sets:from_list(AccSlices++Slices)) == sets:from_list([]));
        	_ -> ParentsSDOutput =[],
        	     true
            end,

%	FollowingSummaries =
%	  [N2 || {edge,N2,N1_,summary}<-Edges,{edge,N2_,N3_,input}<-Edges,
%	         N3 <- Slices, N1 <- Slices, N1_==N1, N2_==N2, N3_==N3],
	%NSlices=removeDuplicates(Slices++Parents++FollowingSummaries),
	%NSlices=removeDuplicates(Slices++Parents),
	%New = sets:to_list(sets:subtract(sets:from_list(AccSlices++Slice),sets:from_list(Parents))),
	%io:format("\nParents: ~w   ParentsSD: ~w~n",[Parents, ParentsSD]),
	%io:format("\nBool1: ~w   Bool2: ~w~n",[(sets:subtract(sets:from_list(Parents),sets:from_list(AccSlices++Slices)) == sets:from_list([])), (sets:subtract(sets:from_list(ParentsSD),sets:from_list(AccSlices++Slices)) == sets:from_list([]))]),
	StopCond = (sets:subtract(sets:from_list(Parents),sets:from_list(AccSlices++Slices)) == sets:from_list([])) 
	  and (sets:subtract(sets:from_list(ParentsSD),sets:from_list(AccSlices++Slices)) == sets:from_list([]))
	  and StopCondSummaryInput and StopCondSummaryOutput,
	 io:format("\ StopCond: ~w   ~n",[StopCond]), 
	case StopCond of
		true -> AccSlices++Slices;
	     	_ -> SlicesSD = sliceFrom(Nodes,
	     	                          Edges,
	     	                          removeDuplicates(ParentsSD),
	     	                          removeDuplicates(AccSlices++Slices),
	     	                          Followed,false),
	     	     %io:format("ParentsSD: ~w ~n ",[removeDuplicates(ParentsSD)]),
	     	     SlicesSDIn = sliceFrom(Nodes,
	     	     			  Edges,
	     	     			  removeDuplicates(ParentsSDInput),
	     	     			  removeDuplicates(AccSlices++Slices++SlicesSD),
	     	     			  Followed,false),
	     	     %io:format("ParentsSDIn: ~w ~n ",[removeDuplicates(ParentsSDInput)]),
	     	     SlicesSDOut = sliceFrom(Nodes,
	     	     			  Edges,
	     	     			  removeDuplicates(ParentsSDOutput),
	     	     			  removeDuplicates(AccSlices++Slices++SlicesSD++ SlicesSDIn),
	     	     			  Followed,false),
	     	     io:format("ParentsSDOut: ~w ~n ",[removeDuplicates(ParentsSDOutput)]),
	     	     io:format("XXXXXXXXXX ~n "),
		     io:format("AccSlices: ~w ~n Slices: ~w ~n SlicesSD: ~w ~n  SlicesSDIn: ~w~n SlicesSDOut: ~w ~n~n~n~n~n",[lists:sort(AccSlices) ,lists:sort(Slices), lists:sort(SlicesSD), lists:sort(SlicesSDIn), lists:sort(SlicesSDOut)]),
	     	     sliceFrom(Nodes,
	     	     		Edges,
	     	     		removeDuplicates(Parents),
	     	     		removeDuplicates(AccSlices++Slices++SlicesSD++SlicesSDIn++SlicesSDOut),
	     	     		Followed,true)
	end.


%sliceFrom(Nodes,Edges,Slices,AccSlices,Followed)->
%    	io:format("Slices: ~w~n",[{lists:sort(sets:to_list(sets:from_list(Slices)))}]),
%	Parents = [N_||N__<-Slices,Type<-Followed,
%	       		{edge,N_,N,Type_}<-Edges,N==N__,Type_==Type],
%        ParentsSD = [N_||N__<-Slices,{edge,N_,N,Type_}<-Edges,N==N__,Type_==summary_data],
%%	FollowingSummaries =
%%	  [N2 || {edge,N2,N1_,summary}<-Edges,{edge,N2_,N3_,input}<-Edges,
%%	         N3 <- Slices, N1 <- Slices, N1_==N1, N2_==N2, N3_==N3],
%	%NSlices=removeDuplicates(Slices++Parents++FollowingSummaries),
%	NSlices=removeDuplicates(Slices++Parents),
%	io:format("Diferences: ~w~n",[sets:to_list(sets:subtract(sets:from_list(NSlices),sets:from_list(Slices)))]),
%	case NSlices==Slices of
%		true -> {NSlices,AccSlices++ParentsSD};
%	     	_ -> sliceFrom(Nodes,Edges,NSlices,AccSlices++ParentsSD,Followed)
%	end.


%sliceFrom(Nodes,Edges,Node)->
%	SliceInput=sliceFollowingInputs(Nodes,Edges,[Node],[]),
%	%io:format("~w~n",[lists:sort(SliceInput)]),
%	%io:format("Returns: ~w~n",[[NodeRet||{node,NodeRet,return}<-Nodes,lists:member(NodeRet,SliceInput)]]),
%	ClausesOut=[NodeO||{edge,NodeO,NodeD,output}<-Edges,lists:member(NodeD,[NodeRet||{node,NodeRet,return}<-Nodes]),
%	                   lists:member(NodeD,SliceInput),not lists:member(NodeO,SliceInput)],
%	sliceFollowingOutputs(Nodes,Edges,ClausesOut,SliceInput).
%	%sliceFollowingOutputs(Nodes,Edges,[NodeRet||{node,NodeRet,return}<-Nodes,lists:member(NodeRet,SliceInput)],SliceInput).
%	
%sliceFollowingInputs(_,_,[],Slice)->Slice;
%sliceFollowingInputs(Nodes,Edges,[Node|SC],Slice)->
%	Slice_=sliceFollowingConDatStrSum(Nodes,Edges,[input,output],[Node],Slice),
%	NSlice_=removeDuplicates(Slice++Slice_),
%	Returns=[NodeO||{edge,NodeO,NodeD,input}<-Edges,lists:member(NodeD,NSlice_),not lists:member(NodeO,NSlice_),
%	                lists:member(NodeO,[NodeRet||{node,NodeRet,return}<-Nodes])],
%	ArgsInput=[NodeO||{edge,NodeO,NodeD,input}<-Edges,lists:member(NodeD,NSlice_),
%	                  not lists:member(NodeO,[NodeRet||{node,NodeRet,return}<-Nodes])],
%	FuncsCalls = [NodeO||{edge,NodeO,NodeD,data}<-Edges,lists:member(NodeD,Returns)],
%	%io:format("NSC: ~w~n",[{Returns,ArgsInput,FuncsCalls}]),
%    NSlice=removeDuplicates(NSlice_++Returns),
%	NSC=[N||N<-removeDuplicates(SC++ArgsInput++FuncsCalls),not lists:member(N,NSlice)],
%	%io:format("OUTTER WHILE: ~w~n",[{lists:sort(NSC),lists:sort(NSlice)}]),
%	sliceFollowingInputs(Nodes,Edges,NSC,NSlice).
%
%sliceFollowingOutputs(_,_,[],Slice)->Slice;
%sliceFollowingOutputs(Nodes,Edges,[Node|SC],Slice)->
%	Slice_=sliceFollowingConDatStrSum(Nodes,Edges,[input],[Node],Slice),
%	%Slice_=sliceFollowingConDatStrSum(Nodes,Edges,[],[Node],Slice),
%	NSlice=removeDuplicates(Slice_++Slice),
%	sliceFollowingOutputs(Nodes,Edges,SC,NSlice).
%	
%
%sliceFollowingConDatStrSum(_,_,_,[],Slice)->Slice;
%sliceFollowingConDatStrSum(Nodes,Edges,NotFollowed,[Node|SC],Slice)->
%	Parents=[NodeO||{edge,NodeO,NodeD,Type}<-Edges,NodeD==Node,
%	                not lists:member(Type,NotFollowed),Type/=structural],
%	Structural=[NodeO||{edge,NodeO,NodeD,structural}<-Edges,NodeD==Node],
%	ControlParentsOfStructural=[NodeO||{edge,NodeO,NodeD,control}<-Edges,lists:member(NodeD,Structural)],
%%	DataParentsOfStructural=[NodeO||{edge,NodeO,NodeD,data}<-Edges,lists:member(NodeD,Structural),
%%	                                not lists:member(NodeO,reachablesForward(Edges,NodeD))],
%	NSlice=removeDuplicates(Slice++[Node|Structural]),
%%	NSC_=[N||N<-removeDuplicates(SC++Parents++ControlParentsOfStructural++DataParentsOfStructural),not lists:member(N,NSlice)],
%	NSC_=[N||N<-removeDuplicates(SC++Parents++ControlParentsOfStructural),not lists:member(N,NSlice)],
%	NSC=case NotFollowed of
%	         [input] -> removeDuplicates(NSC_++[NodeO||{edge,NodeO,NodeD,input}<-Edges,NodeD==Node,
%	                                                   [NodeO_||{edge,NodeO_,NodeD_,summary}<-Edges,NodeO_==NodeO,lists:member(NodeD_,NSlice)]/=[]]);
%	         _->NSC_
%	    end,
%	%io:format("~w~n",[{Node,lists:sort(NSC),lists:sort(NSlice)}]),
%	sliceFollowingConDatStrSum(Nodes,Edges,NotFollowed,NSC,NSlice).
%
%
reachablesForward(Edges,Node)->
	Chidren=[NodeD||{edge,NodeO,NodeD,Type}<-Edges,NodeO==Node,Type/=input,Type/=output,Type/=summary,Type/=data],
	lists:flatten(Chidren++[reachablesForward(Edges,Node_)||Node_<-Chidren]).
%
%sliceFromList(_,_,[],_,_,PreviouslyAnalyzed)->PreviouslyAnalyzed;
%sliceFromList(Nodes,Edges,[Node|RNodes],NotFollowed,FirstTime,PreviouslyAnalyzed)->
%	io:format("Node and rest of nodes: ~w~n",[{Node,lists:sort(RNodes)}]),
%	Slice=sliceFrom(Nodes,Edges,Node,NotFollowed,FirstTime,PreviouslyAnalyzed),
%	io:format("Node and produced slice: ~w~n",[{Node,lists:sort(Slice)}]),
%	sliceFromList(Nodes,Edges,RNodes,NotFollowed,FirstTime,Slice).
%
%sliceFrom(Nodes,Edges,Node,NotFollowed,FirstTime,PreviouslyAnalyzed)->
%	SliceNodes=sliceFromCDSS(Nodes,Edges,Node,NotFollowed,FirstTime,PreviouslyAnalyzed),
%	io:format("~w~n",[{NotFollowed,Node,lists:sort(SliceNodes--PreviouslyAnalyzed)}]),
%	removeDuplicates(
%	 SliceNodes++
%	 sliceFromList(Nodes,Edges,[NodeO||
%	                NodePA<-SliceNodes,{edge,NodeO,NodeD,Type}<-Edges,
%	         	    NodeD==NodePA,Type/=data,Type/=control,Type/=summary,Type/=structural,Type/=NotFollowed,
%	         	    not lists:member(NodeO,SliceNodes)],NotFollowed,false,removeDuplicates(SliceNodes++[Node]))).
%	
%	
%
%sliceFromCDSS(Nodes,Edges,Node,NotFollowed,FirstTime,PreviouslyAnalyzed)->
%	Parents=
%	case NotFollowed of
%		 output-> case FirstTime of
%		 			   true -> [NodeO||{edge,NodeO,NodeD,Type}<-Edges,NodeD==Node,Type/=input,Type/=output,Type/=structural];
%		 			   _-> FollowingSummary=[NodeO||{edge,NodeO,NodeD,summary}<-Edges,NodeD==Node],
%		                   %io:format("SUMMARY: ~w~n",[{Node,FollowingSummary}]),
%		                   %io:read(" "),
%			 	           removeDuplicates(
%			 	            [NodeS||NodeS<-FollowingSummary,{edge,NodeO,NodeD,input}<-Edges,NodeO==NodeS,lists:member(NodeD,PreviouslyAnalyzed)]++
%			                [NodeO||{edge,NodeO,NodeD,Type}<-Edges,NodeD==Node,Type/=input,Type/=output,Type/=summary,Type/=structural])
%			       end;
%		 _-> %[NodeO||{edge,NodeO,NodeD,Type}<-Edges,NodeD==Node,Type/=input,Type/=output,Type/=structural]
%		                   FollowingSummary=[NodeO||{edge,NodeO,NodeD,summary}<-Edges,NodeD==Node],
%		                   %io:format("SUMMARY: ~w~n",[{Node,FollowingSummary,lists:sort(PreviouslyAnalyzed)}]),
%		                   %io:read(" "),
%			 	           removeDuplicates(
%			 	            [NodeS||NodeS<-FollowingSummary,{edge,NodeO,NodeD,input}<-Edges,NodeO==NodeS,lists:member(NodeD,PreviouslyAnalyzed)]++
%			                [NodeO||{edge,NodeO,NodeD,Type}<-Edges,NodeD==Node,Type/=input,Type/=output,Type/=summary,Type/=structural])
%	end,
%	Structural=[NodeO||{edge,NodeO,NodeD,structural}<-Edges,NodeD==Node],
%	ParentsStructural=[NodeO||{edge,NodeO,NodeD,Type}<-Edges,Type/=data,Type/=input,Type/=output,lists:member(NodeD,Structural)],
%	DataParentsStructural=[NodeO||{edge,NodeO,NodeD,data}<-Edges,lists:member(NodeD,Structural),not lists:member(NodeO,reachablesForward(Edges,NodeD))],
%	%io:format("~w~n",[{Node,Structural,ParentsStructural,DataParentsStructural}]),
%	NewNodes=removeDuplicates(Parents++ParentsStructural++DataParentsStructural),
%	%io:format("~w~n",[{Node,NewNodes,[sliceFromCDSS(Nodes,Edges,NodeN,NotFollowed,FirstTime,removeDuplicates(PreviouslyAnalyzed++NewNodes++[Node]))||
%	%               NodeN<-NewNodes,(not lists:member(NodeN,PreviouslyAnalyzed) or ([ND||{edge,NO,ND,structural}<-Edges,NO==NodeN]/=[]))]}]),
%	removeDuplicates(PreviouslyAnalyzed++Structural++
%	lists:flatten([sliceFromCDSS(Nodes,Edges,NodeN,NotFollowed,FirstTime,removeDuplicates(PreviouslyAnalyzed++NewNodes++[Node]))||
%	               NodeN<-NewNodes,(not lists:member(NodeN,PreviouslyAnalyzed))])). %or ([ND||{edge,NO,ND,structural}<-Edges,NO==NodeN]/=[]))])).
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% RESTORE FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	
restore(Nodes,Edges,ModName,Exports,Slice)->
       SortedFuncs= sortAnonimous([{NIn,reachablesForward(Edges,NIn)}||NIn<-[NIn_||{node,NIn_,{function_in,'_',_,_,_}}<-Nodes]])
                    ++[{NIn,FName,FArity}||{node,NIn,{function_in,FName,FArity,_,_}}<-Nodes,FName/='_'],
       %io:format("~w ~n",[{SortedFuncs}]),
       NFuncs=restoreFuncs(Nodes,Edges,Slice,[],SortedFuncs),
       Forms=[{attribute,1,module,ModName},{attribute,2,export,Exports}|NFuncs],
       lists:flatten([lists:flatten(erl_pp:form(Form))++"\n"||Form<-Forms]).

sortAnonimous([])->[];
sortAnonimous([{N,Reachables}|Rests])->
       case lists:any(fun (X)->X end,[lists:member(N_,Reachables)||{N_,_}<-Rests]) of
                true-> sortAnonimous(Rests++[{N,Reachables}]);
                false-> [{N,'_',0}|sortAnonimous(Rests)]
       end.


restoreFuncs(_,_,_,_,[])->"";
restoreFuncs(Nodes,Edges,Slice,FunsDict,[{N,Name,Arity}|Ns])->
       Clauses=lists:sort([ND||{edge,NO,ND,control}<-Edges,NO==N,lists:member(ND,Slice)]),
       NClauses=[restoreClause(Nodes,Edges,Slice,FunsDict,Clause)||Clause<-Clauses],
       case Name of
               '_'->restoreFuncs(Nodes,Edges,Slice,FunsDict++[{N,NClauses}],Ns);
               _-> case NClauses of
                       [] -> restoreFuncs(Nodes,Edges,Slice,FunsDict,Ns);
                       _ -> [{function,1,Name,Arity,NClauses}|restoreFuncs(Nodes,Edges,Slice,FunsDict,Ns)]
                   end
       end.


restoreClause(Nodes,Edges,Slice,FunsDict,N)->
       Children=lists:sort([ND||{edge,NO,ND,control}<-Edges,NO==N]),
       [{NGuard,Guards_}] =
[{Node,Guards_}||{node,Node,{guards,Guards_}}<-Nodes,lists:member(Node,Children)],
       NChildren = lists:sort([ND2||{edge,NO,ND,control}<-Edges,{edge,NO2,ND2,control}<-Edges,NO==NGuard,NO2==ND]),
       NChildrenWithout =
lists:sort([ND||{edge,NO,ND,control}<-Edges,NO==N,ND/=NGuard]),
%       io:format("Guards_: ~p ~n",[Guards_]),
%       io:format("NGuard: ~p\nSlice:~w\n",[NGuard,lists:sort(removeDuplicates(Slice))]),
       Guards =
       case lists:member(NGuard,Slice) of
            true->Guards_;
            _ ->[]
       end,
       Patterns=lists:sort([{Node,restoreExpression(Nodes,Edges,Slice,{var,1,'_'},FunsDict,Node)}||{node,Node,_}<-Nodes,lists:member(Node,NChildrenWithout)]),
       Expressions=lists:sort([{Node,restoreExpression(Nodes,Edges,Slice,{atom,1,undef},FunsDict,Node)}||

{node,Node,_}<-Nodes,lists:member(Node,Slice),lists:member(Node,NChildren)]),
       %io:format("Patterns: ~p\nExpressions: ~p\n",[Patterns,Expressions]),
       case Expressions of
               [] -> {clause,1,[Pat||{_,Pat}<-Patterns],Guards,[{atom,1,undef}]};
               _->{clause,1,[Pat||{_,Pat}<-Patterns],Guards,[Exp||{_,Exp}<-Expressions]}
       end.


restoreExpression(Nodes,Edges,Slice,VN,FunsDict,Node)->
   %io:format("Node ANTES:~p\n~p\n",[Node,lists:sort(removeDuplicates(Slice))]),
   %io:format("VN: ~p\n",[VN]),
   NotInSlice=[VN||{node,Node_,_}<-Nodes,not lists:member(Node_,Slice),Node_==Node],
   case NotInSlice of
        [V|_]->V;
        _ ->
            Exps = lists:sort([ND||{edge,NO,ND,control}<-Edges,NO==Node]),
            NExps = lists:map(fun(N)->restoreExpression(Nodes,Edges,Slice,VN,FunsDict,N) end,Exps),
            %io:format("Node: ~p\n",[Node]),
            [NType|_]=[Type||{node,Node_,Type}<-Nodes,Node_==Node],
            %io:format("NType: ~p\n",[NType]),
            case NType of
                {term,Term}->
                   Term;
                 {pm,_,_}->
                   [_,E]=NExps,
                   [P_,_] = Exps,
                   P = restoreExpression(Nodes,Edges,Slice,{var,1,'_'},FunsDict,P_),
                   {match,1,P,E};
                 {op,Op,_,_,_}->
                   case Op of
                        '[]' ->
                           [H,T]=NExps,
                           {cons,1,H,T};
                        '{}' ->
                           {tuple,1,NExps};
                         _ ->
                          case NExps of
                               [E1]->{op,1,Op,E1};
                               [E1,E2]->{op,1,Op,E1,E2}
                          end
                    end;
                  {'case',_,_,_}->
                    [E|_]=NExps,
                    [_|Clauses]=Exps,
                    NClauses =
lists:map(fun(N)->restoreClause(Nodes,Edges,Slice,FunsDict,N)
end,[C||C<-Clauses,lists:member(C,Slice)]),
                    {'case',1,E,NClauses};
                  {'if',_,_,_}->
                    NClauses =
lists:map(fun(N)->restoreClause(Nodes,Edges,Slice,FunsDict,N)
end,[C||C<-Exps,lists:member(C,Slice)]),
                    {'if',1,NClauses};
                  {call,_}->
                    [_|Sons] = lists:reverse(NExps),
                    [NE|NArgs] = lists:reverse(Sons),
                    {call,1,NE,NArgs};
                  {function_in,'_',_,_,_}->
                     [NClauses|_]=[Clauses||{N_,Clauses}<-FunsDict,N_==Node],
                     {'fun',1,{clauses,NClauses}};
                  _ -> {}
              end
    end.





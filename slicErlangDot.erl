-module(slicErlangDot).

-export([start/1,dotGraph/5]).

-define(DEBUG,true).

start(_) ->
	{ok, DeviceSerialR} = file:open("temp.serial", [read]),
    	Graph=io:get_line(DeviceSerialR,""),
    	ok = file:close(DeviceSerialR),
    	{ok,Tokens,_EndLine} = erl_scan:string(Graph++"."),
	{ok,AbsForm} = erl_parse:parse_exprs(Tokens),
	{value,{Nodes,Edges},_Bs} = erl_eval:exprs(AbsForm, erl_eval:new_bindings()),
    	{ok, Device} = file:open("shows.txt", [read]),
    	Shows={list_to_atom(lists:subtract(io:get_line(Device,""),"\n")),list_to_atom(lists:subtract(io:get_line(Device,""),"\n")),
              list_to_atom(lists:subtract(io:get_line(Device,""),"\n")),list_to_atom(lists:subtract(io:get_line(Device,""),"\n"))},
    	ok=file:close(Device),
    	dotGraph(Nodes,Edges,"temp.dot",Shows).
    
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DOT FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	

dotGraph(Nodes,Edges,Name,Shows,Slice)->
	ok=file:write_file(Name, list_to_binary("digraph PDG {\n"++dotNodes(Nodes,Slice)++dotEdges(Edges,Shows)++"}")).

dotGraph(Nodes,Edges,Name,Shows)->
	file:write_file(Name, list_to_binary("digraph PDG {\n"++dotNodes(Nodes)++dotEdges(Edges,Shows)++"}")).

dotNodes([])->"";
dotNodes([{node,Id,Type}|Ns])->
    	"\t"++integer_to_list(Id)++" "++dotNodeType(Type,Id)++"\n"++dotNodes(Ns).
    
dotNodes([],_)->"";
dotNodes([{node,Id,Type}|Ns],Slice)->
    	"\t"++integer_to_list(Id)++" "++dotNodeType(Type,Id,Slice)++"\n"++dotNodes(Ns,Slice).

-ifdef(DEBUG).
-define(SHOW(ID), integer_to_list(ID)++".- ").
-else.
-define(SHOW(_), "").
-endif.

dotNodeInfo(Type, _Id) ->
    	NodeId = ?SHOW(_Id),
	DotType=
	case Type of
		{function_in,NomFunc,Arity,_,_} -> "(function_in)  "++atom_to_list(NomFunc)++"/"++integer_to_list(Arity);
		%{function_out,NomFunc,Arity,_} -> "(function_out)  "++atom_to_list(NomFunc)++"/"++integer_to_list(Arity);
		{clause_in,_,_} -> "clause_in";
		%{clause_out,_} -> "clause_out";
		%{pattern,Pat} -> "(pattern)  "++addNewLine(Pat)++replace(lists:flatten(erl_pp:expr(Pat)));
		%{expression,Exp} ->"(exp)  "++addNewLine(Exp)++replace(lists:flatten(erl_pp:expr(Exp)));
		{guards,Guards} -> case Guards of
					[] -> "(guards) []";
		                        _ -> "(guards)  "++addNewLine(Guards)++replace(lists:flatten(erl_pp:guard(Guards)))
		                   end;
		{'case',_,_,_} -> "case";
		{'if',_,_,_} -> "if";
		{block,_,_,_}-> "block";
		{lc,_}-> "list_compr";
		{gen,_}->"gen";
		{call,_} -> "call";
		return -> "return";
		{term,Term} -> "(term)  "++addNewLine(Term)++replace(lists:flatten(erl_pp:expr(Term)));
		{pm,_,_} -> "pm";
		{op,Op,_,_,_} -> "(op) " ++ atom_to_list(Op);
		_ -> io:format("peta: ~p~n",[Type]),"potosi"
	end,
	{NodeId,DotType}.

dotNodeType(Type,Id)-> 
	ShowInfo = true,
   	{NodeId,DotType}=dotNodeInfo(Type,Id),
   	"[shape=ellipse"++
		(case ShowInfo of
			true -> ", label=\""++ NodeId++DotType++"\""%;
			%		_ -> ""
		end)++"];".
		
		
dotNodeType(Type,Id,Slice)-> 
	ShowInfo = true,
	{NodeId,DotType}=dotNodeInfo(Type,Id),
	"[shape=ellipse"++
	(case ShowInfo of
		true -> ", label=\""++ NodeId++DotType++"\""%;
%			_ -> ""
	end)++
	(case [Id_||Id_<-Slice,Id_==Id] of
		[]-> "";
	      	_-> " color=\"purple\" fontcolor=\"purple\""
	 end)
	 ++"];".



dotEdges([],_)->"";
dotEdges([{edge,S,T,Type}|Es],Shows={ShowData,ShowInput,ShowOutput,ShowSummary})->
	%io:format("~p~n",[{edge,S,T,Type}]),
   	%"\t"++integer_to_list(S)++" -> "++integer_to_list(T)++" "++dotEdgesType(Type)++"\n"++dotEdges(Es).
   	case Type of
    		data when (not ShowData)-> dotEdges(Es,Shows);
    	 	_-> case Type of
    	 	    	input when (not ShowInput)-> dotEdges(Es,Shows);
    	 	      	_ -> case Type of
    	 	      			output when (not ShowOutput)-> dotEdges(Es,Shows);
    	 	      	        	_-> case Type of 
    	 	      	                	summary when (not ShowSummary)-> dotEdges(Es,Shows); 
    	 	      	                 	_ -> "\t"++integer_to_list(S)++" -> "++integer_to_list(T)++" "++dotEdgesType(Type)++"\n"++dotEdges(Es,Shows)
    	 	      	             	    end
    	 	      	    end
    	 	 end
    	end.
	


dotEdgesType(Type) ->
	case Type of
		control -> "[color=black, penwidth=3];";
		data -> "[color=red, constraint=false, style=\"dotted\"];";
		input -> "[color=green3, penwidth=3,constraint=false, style=\"dashed\"];";
		output -> "[color=green3, penwidth=6,constraint=false, style=\"dashed\"];";
		summary -> "[color=brown, penwidth=7, constraint=false];";
		summary_data -> "[color=brown, penwidth=4, constraint=false];";
		%structural -> "[color=blue, penwidth=3, style=\"dashed\"];"
		_->""
	end.



replace("")->"\\"++"l";
replace("\n"++Rest)->"\\"++"l"++replace(Rest);
replace([34|Rest])->"\\"++"\""++replace(Rest);
replace("when "++Rest) -> replace(Rest);
replace([C|Rest])->[C|replace(Rest)].



addNewLine(_) ->"\\"++"l".

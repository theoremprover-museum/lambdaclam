/*

File: prettify.mod
Author: Alan Smaill / James Brotherston
Description:  Mark up syntax for the pretty printer
Last Modified: 14th August 2002.

*/

module prettify.

accumulate pretty_print.

local prettify_term_list list osyn -> thing -> o.
local prettify_emb_list list etree -> thing -> o.
%% local prettify_list (X -> string -> o) -> (list X) -> string -> o.

prettify_term X (str XX) :-
	headvar_osyn X, !, % what to do with meta-variables?
        term_to_string X S,  % need to call this with fresh output var,
        S = XX.              % and then do the unification.
prettify_term (app F Args) (blo 0 [FF, str " ", (blo 1 [str "(", AA , str ")"] ) ]) :-
	headvar_osyn F,
	!, prettify_term F FF, prettify_term_list Args AA.   
prettify_term X Str:-
	prettify_special X Str.
prettify_term  (otype_of X Y) (blo 0 [XX, str ":", YY]) :- !,
                 prettify_term X XX, prettify_term Y YY.
prettify_term  (hyp Y _) YY :- !,
                 prettify_term Y YY.
prettify_term  (user_object S) (str S) :- !.
prettify_term (app F Args) (blo 0 [FF, str " ", (blo 1 [str "(", AA , str ")"] )]) :-
	!, prettify_term F FF, prettify_term_list Args AA.   


prettify_term (abs F Type) (abstr 1 (a\ [ lvar a, str ":", PType, str "\\.", Body a ] )) :- !, 
	      prettify_term Type PType,
          pi z\ ( prettify_term (F z) (Body z) ).



prettify_term obj (str "obj").
prettify_term V (lvar V).
prettify_term_list [T] (blo 0 [PT]) :- !,  prettify_term T PT.
prettify_term_list [H|Rest] (blo 0 [PH, str ",", brk 1| PRest]) :- !,
                  prettify_term H PH,
                  prettify_term_list Rest (blo _ PRest).


prettify_emb X (str XX) :-
	not(not (X = (leaf _ _ _))),
	not(not (X = (sink _ _ _))),
        !, % what to do with meta-variables?
        term_to_string X S,  % need to call this with fresh output var,
        S = XX.              % and then do the unification.
prettify_emb (node Dir Pos F Args) (blo 0 [str "app(", str DirS, str ",", str RPosS, str ",", FF, str " ", (blo 1 [str "(", AA , str ")"] ), str ")" ]) :-
	term_to_string Dir DirK,
	DirS = DirK,
	reverse Pos RPos,
	term_to_string RPos RPosSK,
	RPosS = RPosSK,
	!, prettify_emb F FF, prettify_emb_list Args AA.   
prettify_emb (absnode E) (abstr 1 (a\ [lvar a, str "\\.", Body a])):-!,
	pi z\ (prettify_emb (E z) (Body z)).
prettify_emb  (leaf Dir Pos Osyn) (blo 0 [str "(", str DirS, str ",", str RPosS, str ",", OsynP, str ")" ]) :- 
	      term_to_string Dir DirK,
	DirS = DirK,
	reverse Pos RPos,
	term_to_string RPos RPosSK, 
	RPosSK = RPosS,
	prettify_term Osyn OsynP, !.
prettify_emb  (sink Dir Pos Osyn) (blo 0 [str "[", str DirS, str ",", str RPosS, str ",", OsynP, str "]" ]) :- 
	      term_to_string Dir DirK,
	DirS = DirK,
	reverse Pos RPos,
	term_to_string RPos RPosSK, 
	RPosS = RPosSK,
	prettify_term Osyn OsynP, !.
prettify_emb_list [T] (blo 0 [PT]) :- !,  prettify_emb T PT.
prettify_emb_list [H|Rest] (blo 0 [PH, str ",", brk 1| PRest]) :- !,
                  prettify_emb H PH,
                  prettify_emb_list Rest (blo _ PRest).

local pretty_show_hyp  osyn -> o.

pretty_show_hyp H :- pretty_show_term H, print "\n".

pretty_show_term  T :- prettify_term T PT,
                       pr std_out PT 78.

% better to deal with pretty_show_goal via prettify
% than directly as below

pretty_show_goal  (seqGoal (Hyps >>> Conc) Context) :- 
%%			not (member (embedding_context _ _) Context),
			!,
                       for_each Hyps pretty_show_hyp,
                       prettify_term Conc PConc,
                       pr std_out (blo 0 [str ">>> ", PConc]) 78,
                       print "\n",
		       printstdout "Context:", printstdout Context.
pretty_show_goal  trueGoal  :- !, print "trueGoal!\n".
pretty_show_goal  falseGoal  :- !, print "Warning: falseGoal!\n".
pretty_show_goal  (seqGoal Seq Context) :- !,
		memb_and_rest (embedding_context EList _) Context Rest,
                     pretty_show_goal (seqGoal Seq Rest).
/*		      ((verbose off, !), (print "Embeddings:\n",
		      mappred EList prettify_emb PEList,
		      for_each_cut PEList 
                          (X\ (pr std_out (blo 0 [X]) 78, 
                          print "\n")))).
*/
pretty_show_goal (G1 ** G2) :-
                      print "andGoal\n",
                      pretty_show_goal G1,
                      print "   **\n",
                      pretty_show_goal G2,
                      print "\n".
pretty_show_goal (allGoal X F) :-
                      print "allGoal (",
                      pi z\ ( printterm std_out z,
                              print "\\\n",
                              pretty_show_goal (F z),
                              print ")\n"
                            ).

pretty_show_goal G :-
	pretty_show_goal_special G, !.
pretty_show_goal G :- print "Don't know how to display goal:\n",
                      printterm std_out G,
                      print "\n".

/*
prettify_list F nil "]".
prettify_list F (H::T) [Out,T] :-
	F H Out,
	prettify_list F T String.
*/

end

/*

File: embed.mod
Author: Louise Dennis / James Brotherston
Description:  Embeddings (as used by rippling)
Last Modified: 20th August 2002

*/

module embed.

accumulate logic_eq_constants.


% ***************************************************************************
%                                                                           *
%                           AUXILIARY SYMBOLS                               *
%                                                                           *
% ***************************************************************************

local merge_weights  (list int) -> (list (list int)) -> (list int) -> o.

local get_weight  etree -> (list int) -> (list int) -> o.
local get_wt etree -> dir -> (list int) -> int -> o.

/*
localkind embedding_status.

local nu embedding_status.
%% no unaccounted for wave fronts
local nwfo embedding_status.
%% no new or missing wave fronts
local si embedding_status.
%% surplus inward wave front.
local do embedding_status.
%% deficit outward wave front.
*/

/*
%% Needed to control inward rewriting.
%% icT7 with lemma calculation in place requires this to succeed.
localkind branch_var_status.
local so branch_var_status.
%% wave fronts are only above sinks.
local ind_var branch_var_status.
%% There are wave fronts above bound variables.
local ind_var_nowf branch_var_status.
%% There are bound variables but no wave fronts.
*/
local tweak_directions etree -> etree -> etree -> dir -> int -> o.
local label_wave_front int -> int -> int -> int -> dir -> dir -> dir -> int -> int -> o.
local wave_front_directions etree -> etree -> embedding_status -> dir -> branch_var_status -> dir -> o.
local balanced_list (list etree) -> (list etree) -> dir -> branch_var_status -> dir -> embedding_status -> o.
local do_list (list etree) -> (list etree) -> dir -> branch_var_status -> dir -> o.
local dob_list (list etree) -> (list etree) -> dir -> branch_var_status -> dir -> o.
local si_list (list etree) -> (list etree) -> dir -> branch_var_status -> o.
local sib_list (list etree) -> (list etree) -> dir -> branch_var_status -> o.

local find_moved_wave_fronts  etree -> etree -> etree -> int -> int -> int -> int -> o.

local measure_less dir -> (list int) -> (list int) -> (list int) -> (list
int) -> o.
local lexicographic_less (list int) -> (list int) -> o.
local reverse_lexicographic_less (list int) -> (list int) -> o.

local embedding     etree -> osyn -> osyn -> (list int) -> o.
local s_embedding     etree -> osyn -> (list int) -> o.

local mapcount_bktk (list A) -> (A -> B -> C -> int -> o) -> (list B) -> (list C) -> int -> o.





%***************************************************************************
/*  Embeds and Embedding 
    ====================

    This section of code deals with the creation of a new embedding from
    two terms.
*/
%***************************************************************************

%***************************************************************************
%
% embeds is the interface to embedding:
% NB.  We will set directions when we check the measure
%
%***************************************************************************

embeds X Y Z :- 
    embedding X Y Z nil.

% **************************************************************************
% 
%			  MAIN EMBEDDING CODE
%
% **************************************************************************
%

% embedding -Embedding +Skel +Waveterm +Address
%
% Embed the skeleton Skel in the wave term Waveterm. In any call to
% embedding/4, the Address argument is the position in the of Waveterm
% term in wave term which was given as the third argument to the outermost
% call of embedding/4 - each time we step down through the waveterm,
% address gets one longer. In order for the measure-calculation code
% to work correctly, we should not embed a function term f(t_1,...,t_n)
% in a term e, but should separately embed f, and then each of the t_i in
% e, so that the nodes in the embedding tree are only one functor thick.
%
%
% Should add sinkability condition so that a wave front can only become
% inwards directed if the term it is attached to, or on of its subterms,
% matches a sink in the induction hypothesis.
%
% Is there any way to merge embedding with measure calculation? 
%
% Embeddings are defined by the following rules:
%
%        t < u_i
%   ------------------
%   t < f(u_1,...,u_n) 
%
%       t_1 < u_1,..., t_n < u_n
%   ---------------------------------
%    f(t_1,...,t_n) < f(u_1,...,u_n)
%
%           (P v) < (Q v),   v fresh          Note that when this rule is
%   ---------------------------------         used, the rule immediately
%        (x\ P x) < (y\ Q y)                  below will also be used.
%      
%            P < (Q v),   v fresh
%   ---------------------------------
%          P  < (y\ Q y)
%
%        x ground, V meta-variable            Note that V is not bound
%   ----------------------------------        to x by this rule.
%                x < V
%   
%                x < x
%
%           wild_card < t                     A sink can embed in any term
%


%             V meta-variable                 Note that V is never bound
%   ----------------------------------        to x by this rule. x may
%                x < V                        also be a meta-variable.
%

/*
embedding T X Y Ad:-
  printstdout T,
  printstdout X,
  printstdout Y, 
	  fail.
*/


%% It the erasure is a meta-variable and the skeleton an atom then
%% embed.

%% final embedding may be below this address.

embedding (leaf outward Ad X) X Y Ad :-
    	headvar_osyn Y,
    	((headvar_osyn X); ((not (X = (wild_card _))), obj_atom X)).

%***************************************************************************
%
%                     Base case - any term embeds in itself
%     x < x
%
%% Placed this here so that variables introduced by removing foralls
%% in hyp embed in conclusion if it is a variable.

embedding  (leaf outward Ad X) X Y Ad :- 
	((headvar_osyn X); (obj_atom X,	(not (X = (wild_card _))))),
	(Y = X),
	(headvar_osyn X; obj_atom X).


%% A sink is a variable - this will have been given a type by the
%% embed theory not by a "real" theory.

embedding (sink outward Ad X) X Y Ad :-
	(not (headvar_osyn X)),
	X = (wild_card Type),
	not (headvar_osyn Y),
        obj_atom Y,
	(has_otype _ Y Type; not (has_otype _ Y _)).

%% distinguish between a sink which has expanded and one that hasn't.  
%% Distinction needed for less_double_mono among other thms.
embedding (sink outward Ad X) X Y Ad :-
	(not (headvar_osyn X)),
	X = (wild_card Type),
	headvar_osyn Y.

%% Prevent any further instantiation of meta-variables as complex terms.
embedding _ X Y _ :-
  (headvar_osyn Y),
  !, fail.

%***************************************************************************
%
%        Embed the first term in one of the arguments of the second term
%
%
%        t < u_i
%   ------------------
%   t < f(u_1,...,u_n) 
%

embedding E T (app F Y) Ad :-
    (headvar_osyn T),
    ((headvar_osyn F); (not (F = forall))),
    embedding E T F (1::Ad).
embedding E T (app forall [Type, (abs F Type)]) Ad :-
    (headvar_osyn T),
    pi z\ (has_otype embed z Type => embedding E T (F z) (3::Ad)).
embedding E T (app F Y) Ad :-
    (headvar_osyn T),
    ((headvar_osyn F); (not (F = forall))),
    nth Y Num X _Rest,
    N is Num + 1,
    embedding E T X (N::Ad).
embedding T X (abs Y Type) Ad :-
    (headvar_osyn X),
    pi z \ (has_otype embed z Type => embedding T X  (Y z) Ad).

%% Prevent any further instantiation of meta-variables as complex terms.
embedding _ X _ _ :-
  (headvar_osyn X),
  !, fail.

%***************************************************************************
%
%                 Descend into lambda abstractions.
%
%
%
%           (P v) < (Q v),   v fresh          Note that when this rule is
%   ---------------------------------         used, the rule immediately
%        (x\ P x) < (y\ Q y)                  below will also be used.
%      
embedding (absnode T) (abs X Type) (abs Y Type) Ad :-
    pi z \ (has_otype embed z Type => embedding (T z) (X z) (Y z) Ad).


%            P < (Q v),   v fresh
%   ---------------------------------
%          P  < (y\ Q y)
%
embedding T X (abs Y Type) Ad :-
    pi z \ (has_otype embed z Type => embedding T X  (Y z) Ad).

%***************************************************************************
%
%            Embed all the arguments of two identical functions.
%
% The directions of the wave fronts in the arguments of f are set to 
% be the same as the direction of the wave fronts of f if the embedding
% and embedded terms could unify. This seems to be a slight restriction of
% embeddings, but improves efficiency.
% 
%
%       t_1 < u_1,..., t_n < u_n
%   ---------------------------------
%    f(t_1,...,t_n) < f(u_1,...,u_n)
%


embedding (node outward Ad Ftree Etree) (app F X) (app Fout Y) Ad :-
    ((headvar_osyn F); (not (F = forall))),
     	embedding Ftree F Fout (1::Ad),
     	mapcount_bktk Etree 
          (H\ H1\ H2\ C\ (embedding H H1 H2 (C::Ad))) X Y 2.

%% Special case for forall in order to note types
embedding (node outward Ad (leaf outward (1::Ad) forall) [(leaf outward (2::Ad) Type), (absnode Z)]) (app F1 Y1) (app F2 Y2) Ad :-
	not (headvar_osyn F1),
	not (headvar_osyn F2),
	F1 = forall,
	F2 = forall,
	Y1 = [Type, (abs X Type)],
	Y2 = [Type, (abs Y Type)],
     pi z\ (has_otype embed z Type => embedding (Z z) (X z) (Y z) (3::Ad)).


%***************************************************************************
%
%        Embed the first term in one of the arguments of the second term
%
%
%        t < u_i
%   ------------------
%   t < f(u_1,...,u_n) 
%
embedding E T (app F Y) Ad :-
    ((headvar_osyn F); (not (F = forall))),
    embedding E T F (1::Ad).
embedding E T (app F1 Y1) Ad :-
	not (headvar_osyn F1),
	F1 = forall,
	Y1 = [Type, (abs F Type)],
    pi z\ (has_otype embed z Type => embedding E T (F z) (3::Ad)).
embedding E T (app F Y) Ad :-
    ((headvar_osyn F); (not (F = forall))),
    nth Y Num X _Rest,
    N is Num + 1,
    embedding E T X (N::Ad).


%***************************************************************************
/*  Set_Epos and S_Embedding 
    ========================

    This section of code deals with the modification of an existing
    embedding wrt. a new erasure.  Otherwise identical to embeds and 
    embedding.

    Set_Epos does not set the embedding direction.
*/
%***************************************************************************

%***************************************************************************
%
% embeds is the interface to embedding:
% NB.  We will set directions when we check the measure
%
%***************************************************************************

set_epos Y Z :- 
    s_embedding Y Z nil.

% **************************************************************************
% 
%			  MAIN EMBEDDING CODE
%
% **************************************************************************
%


%% It the erasure is a meta-variable and the skeleton an atom then
%% embed.
/*
s_embedding X Y Z:-
	    printstdout X,
	    printstdout Y,
	    printstdout Z,
	    fail.
*/
s_embedding  (leaf Dir Ad X) Y Ad :- 
	headvar_osyn X,
	headvar_osyn Y,
	X = Y.

s_embedding (leaf Dir Ad X) Y Ad :-
        not (headvar_osyn Y), 
        not (headvar_osyn X), 
	X = Y,
	obj_atom X.

s_embedding (leaf Dir Ad X) Y Ad :-
        not (headvar_osyn Y), 
        not (headvar_osyn X), 
	X = Y.

s_embedding (leaf Dir Ad X) Y Ad :-
	headvar_osyn Y.

%% A sink is a variable - this will have been given a type by the
%% embed theory not by a "real" theory.

s_embedding (sink Dir Ad (wild_card Type)) Y Ad :-
	not (headvar_osyn Y),
        obj_atom Y,
	(has_otype _ Y Type; not (has_otype _ Y _)).

%% distinguish between a sink which has expanded and one that hasn't.  
%% Distinction needed for less_double_mono among other thms.
s_embedding (sink Dir Ad X) Y Ad :-
	headvar_osyn Y.

%% s_embedding (sink Dir Ad X) Y Ad.
%% Prevent any further instantiation of meta-variables as complex terms.
s_embedding _ Y _ :-
  (headvar_osyn Y),
  !, fail.

s_embedding (absnode T) (abs Y Type) Ad :-
    pi z \ (has_otype embed z Type => s_embedding (T z) (Y z) Ad).

s_embedding T (abs Y Type) Ad :-
    pi z \ (has_otype embed z Type => s_embedding T (Y z) Ad).

s_embedding (node Dir Ad Ftree Etree) (app Fout Y) Ad :-
    ((headvar_osyn F); (not (headvar_osyn F), (not (F = forall)))),
     	s_embedding Ftree Fout (1::Ad),
     	mapcount Etree 
          (H\ H2\ H1\ C\ (s_embedding H H2 (C::Ad))) Y _ 2.
%% Special case for forall in order to note types
s_embedding (node outward Ad (leaf outward (1::Ad) forall) [(leaf outward (2::Ad) Type), (absnode Z)]) (app F2 [Type, (abs Y Type)]) Ad :-
	not (headvar_osyn F2),
	F2 = forall,
     pi z\ (has_otype embed z Type => s_embedding (Z z) (Y z) (3::Ad)).


s_embedding E (app F Y) Ad :-
    ((headvar_osyn F);
     ((not (headvar_osyn F)),
     (not (F = forall)))),
    s_embedding E F (1::Ad).
s_embedding E (app F [Type, (abs F1 Type)]) Ad :-
	(not (headvar_osyn F)),
	(F = forall),
    pi z\ (has_otype embed z Type => s_embedding E (F1 z) (3::Ad)).
s_embedding E (app F Y) Ad :-
    ((headvar_osyn F);(not (headvar_osyn F), (not (F = forall)))),
    nth Y Num X _Rest,
    N is Num + 1,
    s_embedding E X (N::Ad).  





%***************************************************************************
%
%	MEASURE CODE
%
%***************************************************************************
%
%               Now we define a measure on embeddings.
%
% The embeddings to be compared are first flattened into lists of
% weights (which are natural numbers).

% Outward weights are compared first and then inward weights.

%% Outward weights compared with reverse lexicographic order.
%% Inward weights compared with lexicographic order.

%% Directions start as variables and are instantiated to greatest possible.

/*check_measure_reducing outward NewEmbedding OldEmbedding _ NewEmbedding:-
	get_weight OldEmbedding OldOutward OldInward, 
	get_weight NewEmbedding NewOutward NewInward, 
	((verbose off, !); (verbose on,
	printstdout "Out Measures:",
	printstdout OldOutward,
	printstdout NewOutward)),
	reverse_lexicographic_less NewOutward OldOutward, 
	!.
*/
check_measure_reducing Dir NewEmbedding OldEmbedding TermPos EmbeddingOut RDir:-
	not (NewEmbedding = dummytree),
	get_weight OldEmbedding OldOutward OldInward,
	%% Get all possible directional annotations for Embedding
	%% Find all directional labels on wave fronts and sort in
	%% order of the measure - aim is to pick the greatest embedding
	%% which reduces wrt the old embedding.
	findall_sort
	     (E\ tweak_directions OldEmbedding NewEmbedding E Dir RDir) Es
	     (E2\ E1\ (sigma NO1\ sigma NO2\ sigma NI1\ sigma NI2\
		       get_weight E1 NO1 NI1, 
		       get_weight E2 NO2 NI2,
		       measure_less Dir NO1 NO2 NI1 NI2)), !,	
	memb EmbeddingOut Es,
	get_weight EmbeddingOut NewOutward NewInward,
	((verbose off, !); (verbose on,
	printstdout "In Out Measures", 
	printstdout OldOutward,
	printstdout NewOutward,
	printstdout OldInward,
	printstdout NewInward)),
	((((not (wnm NewOutward OldOutward); not (wnm NewInward OldInward)),
	measure_less Dir NewOutward OldOutward NewInward OldInward); 
	 (%% not (measure_less Dir NewOutward OldOutward NewInward OldInward), 
	  wnm NewOutward OldOutward, wnm NewInward OldInward, RDir = 1));
	  (RDir = 2, measure_less Dir NewOutward OldOutward NewInward OldInward)).



local wnm (list int) -> (list int) -> o.
wnm [] [].
wnm (0::T1) (0::T2):-
    wnm T1 T2.
wnm (H1::T1) (H2::T2):-
    not (H1 = 0),
    not (H2 = 0),
    wnm T1 T2.

%% Weight comparison code.
measure_less inout Out Out NewIn OldIn:-
	!,
	lexicographic_less NewIn OldIn, !.
measure_less _ NewOut OldOut S S:-
	reverse_lexicographic_less NewOut OldOut, !.
measure_less inout NewOut OldOut _ _:-
	reverse_lexicographic_less NewOut OldOut, !.

lexicographic_less (H::_) (H1::_) :-
	H < H1, !.
lexicographic_less (H::T) (H::T1):-
	!,
	lexicographic_less T T1.

reverse_lexicographic_less L1 L2:-
	length L1 L,
	length L2 L, !,
	reverse L1 L1R,
	reverse L2 L2R,
	lexicographic_less L1R L2R.
reverse_lexicographic_less L1 L2:-
	length L1 Len1,
	length L2 Len2, 
	Len1 < Len2, !.

%% Weight calculation code
get_weight Embedding Outward Inward:-
	get_wt Embedding outward Outward 0,
	get_wt Embedding inward Inward 0, !.

%% According to TpHOls paper (Smaill & Green, Higher Annotated Terms for
%% proof search) the weight of an embedding node is the difference between
%% the length of the address at that node (Pos below) and the depth
%% in the tree.  I think they mean by this the Depth in the skeleton _but_
%% to get the measure that is analogous to Basin & Walsh's measure we
%% need a subtler notion.  

%% Once a wave front has appeared in the term _everything_ below it
%% that appears in the skeleton will be out by some amount (the extra
%% depth created by the wave front.  In fact we only want the first 
%% skeleton term to be out and everything under it to be out by
%% zero until the next wave front appears.  Therefore we actually 
%% need to keep an artificial count of "TermDepth" which increments
%% everywhere except where a wave front appears and use that for
%% our comparison.  In fact we can take this term Depth to be the
%% Length of the position for the parent embedding node.


get_wt (leaf Dir Pos _) Dir (X::nil) TermDepth:-
	!, length Pos Len,
	X is (Len - TermDepth).
%% Directions don't match
get_wt (leaf _Dir _Pos _) _Dir2 (0::nil) _.
get_wt (sink Dir Pos _) Dir (X::nil) TermDepth:-
	!, length Pos Len,
	X is (Len - TermDepth).
get_wt (sink _Dir _Pos _) _Dir2 (0::nil) _.
get_wt (node Dir Pos Ftree Tree) Dir (X::Measure) TermDepth:-
	!, length Pos Len,
	X is (Len - TermDepth),
	NewTermDepth is (Len + 1),
	(not (Ftree = dummytree)),
	mappred Tree (X\ Y\ ((not (X = dummytree)), 
                          get_wt X Dir Y NewTermDepth)) MeasureList,
	get_wt Ftree Dir MF NewTermDepth,
	merge_weights nil (MF::MeasureList) Measure.
get_wt (node _Dir2 Pos Ftree Tree) Dir (0::Measure) _TermDepth:-
	(not (Ftree = dummytree)),
	length Pos Len,
	NewTermDepth is (Len + 1),
	get_wt Ftree Dir MF NewTermDepth,
	mappred Tree (X\ Y\ ((not (X = dummytree)), get_wt X Dir Y NewTermDepth)) MeasureList,
	merge_weights nil (MF::MeasureList) Measure, !.
get_wt (absnode E) Dir Measure TermDepth:-
	pi x\ (get_wt (E x) Dir Measure TermDepth).

merge_weights nil (H::T) Y:-
	merge_weights H T Y.
merge_weights X nil X.
merge_weights W1 (W2::R2) R :-
	((pi mw_aux\
		(pi Y\ mw_aux  nil Y Y,
		 pi X\ mw_aux X nil X,
		 pi X\ pi Y\ pi W\ pi R1\ pi R2\ pi R\
			(mw_aux ((X:int)::R1) ((Y:int)::R2) ((W:int)::R) :-
      				W is X + Y, mw_aux R1 R2 R)) =>
	 mw_aux W1 W2 W)),
      	merge_weights W R2 R.
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Wave Front Direction Setting Code
%%

tweak_directions OldEmbedding NewEmbedding DirectionEmbedding Dir RDir:-
        %% Flag indicates the presence of new (or turned) wave fronts
	%% Flag is uninstantiated if there are no new wfs
	find_moved_wave_fronts OldEmbedding NewEmbedding TmpEmbedding 0 0 Flag RDir, 
%	printstdout TmpEmbedding,
%	branch_exclusion TmpEmbedding TmpEmbedding2 0,
	!,
%%	(S = nu; S = do),
	(S = nu; (Flag = 0, S = do)),
	wave_front_directions TmpEmbedding DirectionEmbedding S outward _ Dir.


label_wave_front OldDepth NewDepth OldParentDepth NewParentDepth OldDir _ nwf _ _:-
	K is (OldDepth - OldParentDepth),
	K is (NewDepth - NewParentDepth), K = 1, !.
label_wave_front 0 0 0 0 OldDir _ nwf _ _.
%% NewDir is blank if this area was altered by rewrite
%% not(NewDir = inward) checks blank.
label_wave_front OD ND OPD NPD outward NewDir uowf _ RDir:-
	not(NewDir = inward),
	N is OD - OPD,
	N1 is ND - NPD,
	not (N = 1),
	N = N1.
label_wave_front OD ND OPD NPD _ _ uowf _ RDir:-
	not (RDir = 2),
	N is OD - OPD,
	N1 is ND - NPD,
	N1 > N,
	not (N = 1).
%% This wave front could have been altered somehow
%% even though it appears not to have moved - its a candidate for
%% a direction change.
%% inward instantiates the blank NewDir
label_wave_front OD ND OPD NPD outward inward pnew 1 _:-
	N is OD - OPD,
	N1 is ND - NPD,
	not (N = 1),
	N = N1.
label_wave_front OD ND OPD NPD inward _ uiwf _ RDir:-
	N is OD - OPD,
	N1 is ND - NPD,
	not (N = 1),
	(N = N1; not(RDir = 2)).
label_wave_front OD ND OPD NPD inward _ uiwf _ RDir:-
	not (RDir = 2),
	N is OD - OPD,
	N1 is ND - NPD,
	N1 > N,
	not (N = 1).
label_wave_front OD ND OPD NPD outward _ lo 0 _:-
	N is OD - OPD,
	N1 is ND - NPD,
	N > N1.
label_wave_front OD ND OPD NPD inward _ li _ _:-
	N is OD - OPD,
	N1 is ND - NPD,
	N > N1.
label_wave_front OD ND OPD NPD _ _ new 1 RDir:-
	N is OD - OPD,
	N1 is ND - NPD,
	N1 > N,
	%% Doesn't count as new if widenend in unblocking rippling.
	(RDir = 2; N = 1).


%%
%% ------------------------------------
%% This ignores one situation exemplified by the following static wave rule
%% f(wfout(g(wh(x))), wfout(h(wh(y)))) => f(x, wfin(k(wh(y))))
%%
%% A straightforward analysis of k would flag it as an unmoved outward wave front
%% for the time being the wave front round K is marked as NEW
%% ------------------------------------

%% We now label each branch of a goal tree as
%% 1) No Unaccounted Wave Front
%% 2) Surplas Inward Wave Front(s)
%% 3) Deficit Outward Wave Front(s)

%% We need to distinguish between leaf nodes that contain constants
%% and those that contain bound variables.
%% In the first case an outward wave front can come back in since it
%% has effectively switched branch.

/*wave_front_directions A _ B C _ _:-
		      printstdout A,
		      printstdout B,
		      printstdout C,
		      fail.
*/

wave_front_directions (leaf nwfb NewPos Syn) (leaf DefaultDir NewPos Syn) nwfo DefaultDir BVStatus _:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var_nowf)).
wave_front_directions (leaf nwf NewPos Syn) (leaf DefaultDir NewPos Syn) nwfo DefaultDir BVStatus _:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var_nowf)).
wave_front_directions (leaf uowf NewPos Syn) (leaf outward NewPos Syn) nu _ BVStatus _:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var_nowf)).	
wave_front_directions (leaf pnew NewPos Syn) (leaf outward NewPos Syn) nu _ BVStatus _:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var_nowf)).	
wave_front_directions (leaf uiwf NewPos Syn) (leaf inward NewPos Syn) nu _ BVStatus inout:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var_nowf)).

wave_front_directions (leaf new NewPos Syn) (leaf inward NewPos Syn) si _ BVStatus inout:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var)).
wave_front_directions (leaf pnew NewPos Syn) (leaf inward NewPos Syn) si _ BVStatus inout:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var)).

wave_front_directions (leaf lo NewPos Syn) (leaf DefaultDir NewPos Syn) do DefaultDir BVStatus _:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var_nowf)).

%% Needed for wf cancellation.
wave_front_directions (leaf li NewPos Syn) (leaf DefaultDir NewPos Syn) do DefaultDir BVStatus _:-
	((constant Syn _, !, BVStatus = so);
	 (not (constant Syn _), !, BVStatus = ind_var_nowf)).

wave_front_directions (sink nwfb NewPos Syn) (sink DefaultDir  NewPos Syn) nwfo DefaultDir so _.
wave_front_directions (sink nwf NewPos Syn) (sink DefaultDir  NewPos Syn) nwfo DefaultDir so _.
wave_front_directions (sink uowf NewPos Syn) (sink outward NewPos Syn) nu _ so _.
wave_front_directions (sink pnew NewPos Syn) (sink outward NewPos Syn) nu _ so _.
%% wave_front_directions (sink uowf NewPos Syn) (sink inward NewPos Syn) nu _ so.
wave_front_directions (sink uiwf NewPos Syn) (sink inward NewPos Syn) nu _ so inout.
 
wave_front_directions (sink new NewPos Syn) (sink inward NewPos Syn) si _ so inout.
wave_front_directions (sink pnew NewPos Syn) (sink inward NewPos Syn) si _ so inout.

wave_front_directions (sink lo NewPos Syn) (sink DefaultDir NewPos Syn) do DefaultDir so Dir.


%% Situations where lists below can be "balanced"
wave_front_directions (node nwf NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) nwfo DefaultDir BVStatus Dir:-
		      balanced_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus Dir nwfo, !.
wave_front_directions (node nwf NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) nu DefaultDir BVStatus Dir:-
		      balanced_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus Dir nu.
wave_front_directions (node nwfb NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) nwfo DefaultDir BVStatus Dir:- !,
		      balanced_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus Dir nwfo.
wave_front_directions (node uowf NewPos IRator IRand) 
		      (node outward NewPos NRator NRand) nu _ BVStatus Dir:-
		      balanced_list (IRator::IRand) (NRator::NRand) outward BVStatus Dir _.
wave_front_directions (node pnew NewPos IRator IRand) 
		      (node outward NewPos NRator NRand) nu _ BVStatus Dir:-
		      balanced_list (IRator::IRand) (NRator::NRand) outward BVStatus Dir _.
wave_front_directions (node uiwf NewPos IRator IRand) 
		      (node inward NewPos NRator NRand) nu _ BVStatus Dir:-
		      balanced_list (IRator::IRand) (NRator::NRand) inward BVStatus Dir _.

%% Situations where lists below need "extra" inward
wave_front_directions (node li NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) nu DefaultDir BVStatus inout:-
		      %% balanced if cancellation.
		      sib_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus.
wave_front_directions (node lo NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) nu DefaultDir BVStatus inout:-
		      si_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus,
			(BVStatus = so; BVStatus = ind_var_nowf).
wave_front_directions (node lo NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) si DefaultDir BVStatus inout:-
		      si_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus.
wave_front_directions (node nwf NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) si DefaultDir BVStatus inout:-
		      si_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus.
wave_front_directions (node uiwf NewPos IRator IRand) 
		      (node inward NewPos NRator NRand) si _ BVStatus inout:-
		      si_list (IRator::IRand) (NRator::NRand) inward BVStatus.
wave_front_directions (node li NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) si DefaultDir BVStatus inout:-
		      si_list (IRator::IRand) (NRator::NRand) inward BVStatus.
wave_front_directions (node uowf NewPos IRator IRand) 
		      (node inward NewPos NRator NRand) si _ BVStatus inout:-
		      sib_list (IRator::IRand) (NRator::NRand) inward BVStatus1,
		      ((BVStatus1 = ind_var_nowf, BVStatus = ind_var);
                       (not (BVStatus1 = ind_var_nowf), BVStatus = BVStatus1)).
wave_front_directions (node pnew NewPos IRator IRand) 
		      (node inward NewPos NRator NRand) si _ BVStatus inout:-
		      sib_list (IRator::IRand) (NRator::NRand) inward BVStatus1,
		      ((BVStatus1 = ind_var_nowf, BVStatus = ind_var);
                       (not (BVStatus1 = ind_var_nowf), BVStatus = BVStatus1)).
wave_front_directions (node new NewPos IRator IRand) 
		      (node inward NewPos NRator NRand) si DefaultDir BVStatus inout:-
		      sib_list (IRator::IRand) (NRator::NRand) inward BVStatus1,
		      ((BVStatus1 = ind_var_nowf, BVStatus = ind_var);
                       (not (BVStatus1 = ind_var_nowf), BVStatus = BVStatus1)).



%% Situations where lists below need "missing" outward
wave_front_directions (node new NewPos IRator IRand) 
		      (node outward NewPos NRator NRand) nu _ BVStatus Dir:-
		      do_list (IRator::IRand) (NRator::NRand) outward BVStatus1 Dir,
		      ((BVStatus1 = ind_var_nowf, BVStatus = ind_var);
                       (not (BVStatus1 = ind_var_nowf), BVStatus = BVStatus1)).
/*wave_front_directions (node new NewPos IRator IRand) 
		      (node outward NewPos NRator NRand) nu outward BVStatus Dir:-
		      %% balanced list in unblocking case.
		      balanced_list (IRator::IRand) (NRator::NRand) outward BVStatus1 Dir _,
		      ((BVStatus1 = ind_var_nowf, BVStatus = ind_var);
                       (not (BVStatus1 = ind_var_nowf), BVStatus = BVStatus1)).
*/
wave_front_directions (node nwf NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) do DefaultDir BVStatus Dir:-
		      do_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus Dir.
wave_front_directions (node uowf NewPos IRator IRand) 
		      (node outward NewPos NRator NRand) do DefaultDir BVStatus Dir:-
		      do_list (IRator::IRand) (NRator::NRand) outward BVStatus Dir.
wave_front_directions (node pnew NewPos IRator IRand) 
		      (node outward NewPos NRator NRand) do DefaultDir BVStatus Dir:-
		      do_list (IRator::IRand) (NRator::NRand) outward BVStatus Dir.
wave_front_directions (node lo NewPos IRator IRand) 
		      (node DefaultDir NewPos NRator NRand) do DefaultDir BVStatus Dir:-
		      dob_list (IRator::IRand) (NRator::NRand) DefaultDir BVStatus Dir.


wave_front_directions (absnode E) (absnode E2) Status DefaultDir BVStatus Dir:-
	pi x\ (wave_front_directions (E x) (E2 x) Status DefaultDir BVStatus) Dir.

balanced_list [] [] _ so Dir nwfo.
balanced_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir nwfo:-
	      wave_front_directions IH NH nwfo DefaultDir BVStatus1 Dir, 
	      balanced_list IT NT DefaultDir BVStatus2 Dir nwfo, !,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
balanced_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir nu:-
	      wave_front_directions IH NH nwfo DefaultDir BVStatus1 Dir, !,
	      balanced_list IT NT DefaultDir BVStatus2 Dir nu,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
balanced_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir nu:-
	      balanced_list IT NT DefaultDir BVStatus2 Dir nwfo, !,
	      wave_front_directions IH NH nu DefaultDir BVStatus1 Dir,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
balanced_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir nu:-
	      wave_front_directions IH NH nu DefaultDir BVStatus1 Dir,
	      balanced_list IT NT DefaultDir BVStatus2 Dir nu,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
balanced_list (IH::IT) (NH::NT) DefaultDir BVStatus inout nu:-
	      wave_front_directions IH NH si DefaultDir BVStatus1 inout,
	      do_list IT NT DefaultDir BVStatus2 inout,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
balanced_list (IH::IT) (NH::NT) DefaultDir BVStatus inout nu:-
	      wave_front_directions IH NH do DefaultDir BVStatus1 inout,
	      si_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.

%% A list which overall is missing an outward wavefront
do_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir:-
	wave_front_directions IH NH nwfo DefaultDir BVStatus1 Dir, !,
	do_list IT NT DefaultDir BVStatus2 Dir,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
do_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir:-
	wave_front_directions IH NH nu DefaultDir BVStatus1 Dir,
	do_list IT NT DefaultDir BVStatus2 Dir,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
do_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir:-
	wave_front_directions IH NH do DefaultDir BVStatus1 Dir,
	dob_list IT NT DefaultDir BVStatus2 Dir,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
do_list (IH::IT) (NH::NT) DefaultDir BVStatus inout:-
	wave_front_directions IH NH do DefaultDir BVStatus1 inout,
	si_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
do_list (IH::IT) (NH::NT) DefaultDir BVStatus inout:-
	wave_front_directions IH NH si DefaultDir BVStatus1 inout,
	do_list IT NT DefaultDir BVStatus2 inout,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.


%% A list which overall is missing an outward wavefront
%% or is balanced
dob_list [] [] _ so Dir.
dob_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir:-
	wave_front_directions IH NH nwfo DefaultDir BVStatus1 Dir, !,
	dob_list IT NT DefaultDir BVStatus2 Dir,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
dob_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir:-
	wave_front_directions IH NH nu DefaultDir BVStatus1 Dir,
	dob_list IT NT DefaultDir BVStatus2 Dir,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
dob_list (IH::IT) (NH::NT) DefaultDir BVStatus Dir:-
	wave_front_directions IH NH do DefaultDir BVStatus2 Dir,
	dob_list IT NT DefaultDir BVStatus1 Dir,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
dob_list (IH::IT) (NH::NT) DefaultDir BVStatus inout:-
	wave_front_directions IH NH si DefaultDir BVStatus1 inout,
	do_list IT NT DefaultDir BVStatus2 inout,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.

si_list (IH::IT) (NH::NT) DefaultDir BVStatus:-
	wave_front_directions IH NH nwfo DefaultDir BVStatus1 inout, !,
	si_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
si_list (IH::IT) (NH::NT) DefaultDir BVStatus:-
	wave_front_directions IH NH nu DefaultDir BVStatus1 inout,
	si_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
si_list (IH::IT) (NH::NT) DefaultDir BVStatus:-
	wave_front_directions IH NH si DefaultDir BVStatus1 inout,
	sib_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.

sib_list [] [] _ so.
sib_list (IH::IT) (NH::NT) DefaultDir BVStatus:-
	wave_front_directions IH NH nwfo DefaultDir BVStatus1 inout, !,
	sib_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
sib_list (IH::IT) (NH::NT) DefaultDir BVStatus:-
	wave_front_directions IH NH nu DefaultDir BVStatus1 inout,
	sib_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
sib_list (IH::IT) (NH::NT) DefaultDir BVStatus:-
	wave_front_directions IH NH si DefaultDir BVStatus1 inout,
	sib_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
/* sib_list (IH::IT) (NH::NT) DefaultDir BVStatus:-
	wave_front_directions IH NH si DefaultDir BVStatus1 inout,
	do_list IT NT DefaultDir BVStatus2 inout,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.
*/
sib_list (IH::IT) (NH::NT) DefaultDir BVStatus:-
	wave_front_directions IH NH do DefaultDir BVStatus1 inout,
	si_list IT NT DefaultDir BVStatus2,
	      decide_branch_var_status BVStatus1 BVStatus2 BVStatus.

local decide_branch_var_status branch_var_status -> branch_var_status -> branch_var_status -> o.
decide_branch_var_status X X X:- !.
decide_branch_var_status ind_var _ ind_var:- !.
decide_branch_var_status _ ind_var ind_var:- !.
decide_branch_var_status X so X:- !.
decide_branch_var_status so X X:- !.


%% find_moved_wave_fronts
%% embedding direction should not change
find_moved_wave_fronts (node OldDir Pos OFT OEtree) 
		       (node NewDir NewPos NFT NEtree)
		       (node TmpDir NewPos NNFT NNEtree) OldParentDepth NewParentDepth OutFlag RDir:-
	(not (NFT = dummytree)),
	length Pos ODepth,
	length NewPos NDepth,
	label_wave_front ODepth NDepth OldParentDepth NewParentDepth OldDir NewDir TmpDir Flag RDir,

	 mappred3 (OFT::OEtree) (OE\ NE\ NNE\ FL\
		((not (NE = dummytree)),
		find_moved_wave_fronts OE NE NNE ODepth NDepth FL RDir))
		 (NFT::NEtree) (NNFT::NNEtree) FlagList,
	((not (not (Flag = 1)), 
	  not (not (Flag = 0)),
	  process_flaglist FlagList OutFlag);
	  OutFlag = Flag),
%%	);

%%	 (mappred (OFT::OEtree) fix_directions (NFT::NEtree),
%%	  NNFT = NFT, NEtree = NNEtree)), 
	  !.


find_moved_wave_fronts (absnode E) (absnode E1) (absnode E2) OD ND Flag RDir:-
	pi x\ (find_moved_wave_fronts (E x) (E1 x) (E2 x) OD ND Flag RDir).
find_moved_wave_fronts (leaf OldDir Pos Osyn) (leaf NewDir NewPos Osyn) 
		(leaf TmpDir NewPos Osyn) OPD NPD Flag RDir:-
	length Pos ODepth,
	length NewPos NDepth,
	label_wave_front ODepth NDepth OPD NPD OldDir NewDir TmpDir Flag RDir.
find_moved_wave_fronts (sink OldDir Pos Osyn) (sink NewDir NewPos Osyn) 
		(sink TmpDir NewPos Osyn) OPD NPD Flag RDir:-
	length Pos ODepth,
	length NewPos NDepth,
	label_wave_front ODepth NDepth OPD NPD OldDir NewDir TmpDir Flag RDir.

local mappred3 (list A) -> (A -> B -> C -> D -> o) -> (list B) -> (list C) -> (list D) -> o.
mappred3 [] P [] [] [].
mappred3 (A::AL) P (B::BL) (C::CL) (D::DL):-
	 P A B C D, !,
	 mappred3 AL P BL CL DL.

local process_flaglist (list int) -> int -> o.
process_flaglist [] 0.
process_flaglist (0::AL) Flag:-
		!, process_flaglist AL Flag.
process_flaglist (1::AL) 1.
		 
		 

/*
local fix_directions etree -> etree -> o.
fix_directions (node Dir P F E) (node Dir P1 F1 E1):-
	       mappred (F::E) fix_directions (F1::E1).
fix_directions (absnode E) (absnode E1):-
	       pi x\ (fix_directions (E x) (E1 x)).
fix_directions (leaf Dir P S) (leaf Dir P1 S1).
fix_directions (sink Dir P S) (sink Dir P1 S1).
*/

mapcount_bktk nil _ nil nil _.
mapcount_bktk (H::T) P (H1::T1) (H2::T2) Counter:-
	P H H1 H2 Counter, 
	C is Counter + 1,
	mapcount_bktk T P T1 T2 C.

local branch_exclusion etree -> etree -> int -> o.
/*branch_exclusion A B C:-
		  printstdout A,
		  printstdout B,
		  printstdout C, fail.
*/
branch_exclusion (sink nwf NewPos Syn) (sink nwfb NewPos Syn) 1:-!.
branch_exclusion (sink Ann NewPos Syn) (sink Ann NewPos Syn) 0:-!.
branch_exclusion (leaf nwf NewPos Syn) (leaf nwfb NewPos Syn) 1:-!.
branch_exclusion (leaf Ann NewPos Syn) (leaf Ann NewPos Syn) 0:-!.
branch_exclusion (node nwf P F E) (node nwfb P F1 E1) 1:-
		 mappred (F::E) (X\ Y\ branch_exclusion X Y 1) (F1::E1), !.
branch_exclusion (node Ann P F E) (node Ann P F1 E1) 0:-
		 mappred (F::E) (X\ Y\ sigma Z\ (branch_exclusion X Y Z)) (F1::E1).
branch_exclusion (absnode E) (absnode E1) F:-
		 pi x\ (branch_exclusion (E x) (E1 x) F).


end

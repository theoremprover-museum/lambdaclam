module compound_tacs.
accumulate lists_.

% ------------------- compound tactics:
% ------------------- enforce conditional, exhaustive, ordered application
% ------------------- of tactics, both basic AND compound

% pick up random formula(e)
pre PreTac Ingoal Outgoal :- PreTac N Ingoal Outgoal.
pre2 PreTac Ingoal Outgoal :- PreTac N M Ingoal Outgoal.
pre2l PreTac Ingoal Outgoal :- PreTac N M Ingoal Outgoal.
pret PreTac Ingoal Outgoal :- PreTac N M Ingoal Outgoal.
pre2t PreTac Ingoal Outgoal :- PreTac N M Ingoal Outgoal.

% --- goalr ---
% Simplifies true_goal inside goal constructors
goalr_tac (and_goal true_goal Goal) OutGoal :- !, goalr_tac Goal OutGoal.
goalr_tac (and_goal Goal true_goal) OutGoal :- !, goalr_tac Goal OutGoal.
goalr_tac (forall_goal t\ true_goal) true_goal :- !.
goalr_tac Goal Goal.

% --- map ---
% enforce goal constructors
map_tac Tac true_goal true_goal.
% apply two different tactics to the two branches
map_tac (pair_tac Tac1 Tac2) (and_goal InGoal1 InGoal2) OutGoal :-
  map_tac Tac1 InGoal1 OutGoal1, map_tac Tac2 InGoal2 OutGoal2,
  goalr_tac (and_goal OutGoal1 OutGoal2) OutGoal.
% apply the same tactic to the two branches
map_tac Tac (and_goal InGoal1 InGoal2) OutGoal :-
  map_tac Tac InGoal1 OutGoal1, map_tac Tac InGoal2 OutGoal2,
  goalr_tac (and_goal OutGoal1 OutGoal2) OutGoal.
% metalevel generalisation
map_tac Tac (forall_goal InGoal) OutGoal :-
  pi t\ (map_tac Tac (InGoal t) (OutGoal1 t)),
  goalr_tac (forall_goal OutGoal1) OutGoal.
map_tac Tac InGoal OutGoal :- Tac InGoal OutGoal.

% --- id, close, fail ---
% id_tac always succeeds, returning what has been done
% fail_tac always fails
% close_tac forces closing the branch
id_tac Goal Goal.
fail_tac _ _ :- !, fail.
close_tac ((close_rule P) proves (Gamma --> Delta)) true_goal :- print_ "**** Closed by user proof.\n".

% --- then ---
% compose two tactics, i.e., apply them in cascade
then_tac Tac1 Tac2 InGoal OutGoal :- Tac1 InGoal MidGoal, map_tac Tac2 MidGoal OutGoal.

% --- orelse and orelse! ---
% disjunctive application of two tactics. the ! version does not allow backtracking.
orelse_tac Tac1 Tac2 InGoal OutGoal :- Tac1 InGoal OutGoal; Tac2 InGoal OutGoal.
orelse!_tac Tac1 Tac2 InGoal OutGoal :- Tac1 InGoal OutGoal, !; Tac2 InGoal OutGoal.

% --- repeat and repeat_go ---
% exhaustively apply Tac until it is no longer possible.
% repeat fails at the end (i.e., if the exhaustive application did not yield
% OutGoal), while repeat_go succeeds and yields what was done
repeat_tac Tac InGoal OutGoal :- orelse_tac (then_tac Tac (repeat_tac Tac)) fail_tac InGoal OutGoal.
repeat_go_tac Tac InGoal OutGoal :- orelse_tac (then_tac Tac (repeat_go_tac Tac)) id_tac InGoal OutGoal.

% --- try and complete ---
% try: apply Tac and, upon failure, restore initial situation
% complete: apply Tac and try to get true_goal out of it.
try_tac Tac InGoal OutGoal :- orelse_tac Tac id_tac InGoal OutGoal.
complete_tac Tac InGoal true_goal :- Tac InGoal OutGoal, goalr_tac OutGoal true_goal.

% --- app_list and app_list! ---
% app_list: apply a list of tactics. The ! version doesn't allow backtracking
app_list_tac (Head::Tail) InGoal OutGoal :- orelse_tac Head (app_list_tac Tail) InGoal OutGoal.
app_list!_tac (Head::Tail) InGoal OutGoal :- orelse!_tac Head (app_list!_tac Tail) InGoal OutGoal.

% --- exhaust and exhaust! ---
% exhaust: exhaustively apply a list of tactics.
exhaust_tac L InGoal OutGoal :- (complete_tac (repeat_tac (app_list_tac L))) InGoal OutGoal.
exhaust!_tac L InGoal OutGoal :- (complete_tac (repeat_tac (app_list!_tac L))) InGoal OutGoal.

% --- idfs_b and idfs_ub ---
% idfs_b andF idfs_ub: iterative deepening exhaustive application of a list
%                     of tactics (bounded andF unbounded)
idfs Bound N Tacs Ingoal Outgoal :-
  N =< Bound, app_list_tac Tacs Ingoal Midgoal,
  M is (N + 1), map_tac (idfs Bound M Tacs) Midgoal Outgoal.
idfs_b Bound Incr Upbnd Tacs Ingoal Outgoal :-
  print_ "--> Trying at depth ", write_ Bound, print_ "\n",
  map_tac (idfs Bound 1 Tacs) Ingoal Outgoal.
idfs_b Bound Incr Upbnd Tacs Ingoal Outgoal :-
  Bound1 is (Bound + Incr), Bound1 =< Upbnd,
  idfs_b Bound1 Incr Upbnd Tacs Ingoal Outgoal.
idfs_ub Bound Incr Tacs Ingoal Outgoal :-
  print_ "--> Trying at depth ", write_ Bound, print_ "\n",
  map_tac (idfs Bound 1 Tacs) Ingoal Outgoal.
idfs_ub Bound Incr Tacs Ingoal Outgoal :-
  Bound1 is (Bound + Incr),
  idfs_ub Bound1 Incr Tacs Ingoal Outgoal.

end

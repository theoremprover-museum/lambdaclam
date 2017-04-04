/*

File: method.sig
Author: Louise Dennis / James Brotherston
Description: Types for methods.
Last Modified: 13th August 2002

*/

sig method.

accum_sig basic_types.

type   atomic		 theory -> meth -> goal -> o -> o -> goal -> tactic -> o.
type   compound		 theory -> meth -> meth -> (list int) -> o -> o.

%%  For use if we ever introduce hierarchical plans.
type   nomethodyet	 meth.
%%  Placeholder tactic --- until we get a theorem prover
type   notacticyet       tactic.

%% For user methods in external libraries 
type   user_method       string -> meth.

%% The Methodicals
type    id_meth        meth.      % like idtac
type    fail_meth      meth.
type    triv_meth      meth.      % for trivial goal
type    triv_tf_meth   meth.      % for trivial goal
type    orelse_meth    meth -> meth -> meth.
                                  % first, which failing second
type    cond_meth      (goal -> o) -> meth -> meth -> meth.
                                  % if condition holds, then meth1, 
                                  % otherwise meth2
type    try_meth       meth -> meth.
                                  % either given method, or id_meth
type    repeat_meth    meth -> meth.
                                  % exhaustive recursion on subgoals --
                                  %  oblige to succeed at least once
type    repeat_until   (goal -> o) -> meth -> meth.
type    then_meth      meth -> meth -> meth.
                                  % chain second method to all subgoals
                                  %  of first
type    then_meths     meth -> meth -> meth.
                                  % apply compound method to subgoal from first
type    map_meth       meth -> meth.
                                  % map method over compound goal structure
type    complete_meth  meth -> meth.
                                  % only succeed if subgoals all trivial
type    cut_meth       meth -> meth.
                                  % only give first solution
type	pair_meth      meth -> meth -> meth.

type    best_meth      (list meth) -> meth.
                                  % pick best of list according to score_method

%% Stuff for control rule emulation.
type   controll (list control_rule) -> goal -> (list meth) -> (list meth) -> o.
type   strat_meth (list control_rule) -> (list meth) -> meth.
type    control_rule_for theory -> control_rule -> goal -> (list meth) -> (list meth) -> o.
type    prefer (list meth) -> (list meth) -> (list meth) -> o.
type    reject (list meth) -> (list meth) -> (list meth) -> o.
type    replace meth -> meth -> (list meth) -> (list meth) -> o.

% Methodicals which call critics

type	critic_meth	crit -> meth.
type 	patch_meth	meth -> crit -> meth.

%% New Predicate for use in "copying" methods

type change_method_vars meth -> meth -> o.
type keep_variables_free meth -> meth -> o.

end

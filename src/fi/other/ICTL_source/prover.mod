module prover.

accumulate basics.
accumulate syntax.
accumulate tactics.
accumulate examples.

%
% ------------------- interactive prover
%

type  interp            sformula -> o.
type  inter_tac         goal -> goal -> o.
type  process_input     (goal -> goal -> o) -> goal -> goal -> o.
type  do                o -> goal -> goal -> o.
type  stop              goal -> goal -> o.
type  backtrack         goal -> goal -> o.

interp SFormula :-
  inter_tac (Proof proves (nil --> ((SFormula @ z)::nil))) OutGoal, nl,
  (
    ( OutGoal = true_goal,
      print "Proof found!\n", write SFormula, print "\n\nis proved by:\n", write Proof, nl );
    ( print "Stopped. Proof so far:\n", write Proof, nl )
  ).

inter_tac (P proves (Gamma --> Delta)) NewGoal :-
  print "----- Premises: \n", print_list Gamma 1,
  print "----- Conclusions: \n", print_list Delta 1,
  print "*****\n***** Tactic? ", read Tac,
  process_input Tac (P proves (Gamma --> Delta)) NewGoal.

process_input backtrack _ _ :- !, fail.     % backtrack
process_input stop NewGoal NewGoal :- !.    % abandon
process_input (do G) OldGoal NewGoal :-     % execute goal G first
  G, inter_tac OldGoal NewGoal.
process_input Tac OldGoal NewGoal :-        % apply tactic to OldGoal, getting NewGoal
  Tac OldGoal MidGoal,
  map_tac inter_tac MidGoal NewGoal.
process_input _ OldGoal NewGoal :-          % if tactic fails, ask for another
  inter_tac OldGoal NewGoal.

%
% ------------------- automatic prover
%

type autop       sformula -> o.

autop SFormula :-
  Gamma = nil, Delta = ((SFormula @ z)::nil),
  print "**** Goal is: ", write (P proves (Gamma --> Delta)), nl,
  auto_tac (P proves (Gamma --> Delta)) OutGoal,
  print "----> Proof found!\n", write P, nl.

%
% ------------------- Terzo startup
%

% #load "start".
% #query prover name "manna12" F, autop F.

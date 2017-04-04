/*

File: real_trig.mod
Author: Alex Heneveld
Description: trig fns for the reals
Created: Nov 02 (based on work in Jan 00)

*/

module real_trig.

accumulate real_fns.

%
% -------------------- SETUP --------------------
%

% all trigs fns are in radians

has_otype real_fns r_pi reals.

%
% ------------------- SIN / COS -------------------
%

has_otype real_fns sin (reals arrow reals).
has_otype real_fns cos (reals arrow reals).

prettify_special (app sin A)
  (blo 1 [str "sin(", AA, str ")"]):-
  !, prettify_term A AA.
prettify_special (app cos A)
  (blo 1 [str "cos(", AA, str ")"]):-
  !, prettify_term A AA.

% sin 0 = 0
definition real_fns sin_zero trueP
  (app sin r_zero)
  r_zero.

% cos 0 = 1
definition real_fns cos_zero trueP
  (app cos r_zero)
  r_one.


% sin pi = 0
definition real_fns sin_pi trueP
  (app sin r_pi)
  r_zero.

% cos pi = -1
definition real_fns cos_pi trueP
  (app cos r_pi)
  neg_one.

% sin pi/2 = 1
definition real_fns sin_pi_over_two trueP
  (app sin (app div_by (tuple [r_pi, (app plus (tuple [r_one, r_one]))])))
  r_one.

% cos pi/2 = 0
definition real_fns cos_pi_over_two trueP
  (app cos (app div_by (tuple [r_pi, (app plus (tuple [r_one, r_one]))])))
  r_zero.

% sin -x = -sin x
definition real_fns sin_neg_1 trueP
  (app sin (app neg X))
  (app neg (app sin X)).

definition real_fns sin_neg_2 trueP
  (app sin (app times (tuple XA1)))
  (app neg (app sin (app times (tuple XA2)))) :-
    remove neg_one XA1 XA2.

% cos -x = cos x
definition real_fns cos_neg_1 trueP
  (app cos (app neg X))
  (app cos X).
definition real_fns cos_neg_2 trueP
  (app sin (app times (tuple X1)))
  (app cos (app times (tuple X2))) :-
    remove neg_one X1 X2.


% addition rules


% sin A+B = sin A cos B + cos A sin B
definition real_fns sin_plus trueP
  (app sin (app plus (tuple [A, B])))
  (app plus (tuple [
    (app times (tuple [(app sin A), (app cos B)])),
    (app times (tuple [(app cos A), (app sin B)])) ])).

% cos A+B = cos A cos B - sin A sin B
definition real_fns cos_plus trueP
  (app cos (app plus (tuple [A, B])))
  (app minus (tuple [
    (app times (tuple [(app cos A), (app cos B)])),
    (app times (tuple [(app sin A), (app sin B)])) ])).


end

module examples.

accumulate syntax.

% --------- associate a name with a formula

type name    string -> sformula -> o.

% --------- example predicates, constants, functions

type p                 i -> sformula.
type a                 i.
type w, w1, w2, w3, v  sformula.

% --------- example formulae

%
% Vademecum of Kripke frames:
%
% - basic, no properties                  K
% - reflexive                             T             (K + T, alias KT)
% - refl + transitive                     S4            (T + 4, alias KT4)
% - refl + trans + convergent             S4.2          (S4 + G1)
% - refl + trans + connected (linear)     S4.3          (S4 + D2)
% - refl + trans + conn + discrete        S4.3.1        (S4.3 + N1, alias D)
%
% various modal axioms:
%

name "ser"   ( (glob w) imp (evt w) ).                  % seriality (D)
name "refl"  ( (glob w) imp w ).                        % reflexivity (T)
name "trans" ( (glob w) imp (glob (glob w)) ).          % transitivity (4)
name "conv"  ( (evt (glob w)) imp (glob (evt w)) ).     % convergency (G1)
name "lin1"  ( (glob ((glob w) imp v)) or               % connectedness (D2)
               (glob ((glob v) imp w)) ).
name "lin2"  ( ((evt w) and (evt v)) imp                % connectedness (alternative)
               ( (evt (w and v)) or
                 (evt ((evt w) and v)) or
                 (evt (w and (evt v))) ) ).
name "discr" ( (glob ((glob (w imp (glob w))) imp w)) imp   % discreteness (N1)
               ( (evt (glob w)) imp w ) ).

%
% A repertoire of valid temporal statements, taken from
%    Verification of Concurrent Programs: The Temporal Framework
%       by Z. Manna and A. Pnueli
%

name "manna1"  ( (glob (neg w)) iff (neg (evt w)) ).
name "manna2"  ( (evt (neg w)) iff (neg (glob w)) ).
name "manna3"  ( (next (neg w)) iff (neg (next w)) ).

name "manna4"  ( w imp evt w ).
name "manna5"  ( (glob w) imp w ).
name "manna6"  ( (next w) imp (evt w) ).
name "manna7"  ( (glob w) imp (next w) ).
name "manna7'" ( (glob w) imp (evt w) ).
name "manna8"  ( (glob w) imp (next (glob w)) ).
name "manna10" ( (evt (glob w)) imp (glob (evt w)) ).

name "manna11" ( (glob w) iff (glob (glob w)) ).
name "manna12" ( (evt w) iff (evt (evt w)) ).

name "manna13" ( (glob (next w)) iff (next (glob w)) ).
name "manna14" ( (evt (next w)) iff (next (evt w)) ).

name "manna16" ( (glob (w1 and w2)) iff ((glob w1) and glob w2) ).
name "manna17" ( (evt (w1 or w2)) iff ((evt w1) or evt w2) ).
name "manna18" ( (next (w1 and w2)) iff ((next w1) and next w2) ).
name "manna19" ( (next (w1 or w2)) iff ((next w1) or next w2) ).
name "manna20" ( (next (w1 imp w2)) iff ((next w1) imp next w2) ).

name "manna23" ( ((glob w1) or (glob w2)) imp glob (w1 or w2) ).
name "manna24" ( (evt (w1 and w2)) imp ((evt w1) and (evt w2)) ).

name "manna27" ( (glob (w1 imp w2)) imp ((glob w1) imp (glob w2)) ).
name "manna28" ( (glob (w1 imp w2)) imp ((evt w1) imp (evt w2)) ).
name "manna29" ( (glob (w1 imp w2)) imp ((next w1) imp (next w2)) ).

name "manna32" ( ((glob w1) and (next w2)) imp (next (w1 and w2)) ).
name "manna33" ( ((glob w1) and (evt w2)) imp (evt (w1 and w2)) ).
name "manna34" ( (glob (w1 imp w2)) imp ((next w1) imp (next w2)) ).

name "manna46" ( (evt (exists x\ (p x))) iff (exists x\ (evt (p x))) ).
name "manna47" ( (glob (forall x\ (p x))) iff (forall x\ (glob (p x))) ).
name "manna48" ( (next (exists x\ (p x))) iff (exists x\ (next (p x))) ).
name "manna49" ( (next (forall x\ (p x))) iff (forall x\ (next (p x))) ).

%
% Set-Reset flip-flop
%
% taken from
% http://www.ics.ele.tue.nl/es/research/fv/research/research_ptl.html
%

type fP, fQ, fR, fS    sformula.

name "srff"
 ( ( (glob (fQ iff (neg (fP and fS)))) and
     (glob (fP iff (neg (fQ and fR)))) and
     (glob (fS or fR)) and
     fQ and
     (neg fP) )
   imp
   (glob (fP iff (neg fQ)))
 ).

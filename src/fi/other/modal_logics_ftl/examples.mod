module examples.

% The weakest modal logic is E, which satisfies
% |- (phi iff psi) implies |- (box phi) iff (box psi)
% Example: DeMorgan's Law

name "axE"  ( box_ ((phi and_ psi) iff_ not_ ((not_ phi) or_ (not_ psi))) ).

% Stronger modal logics, up to K:
%
% Properties     Name  Axioms
% ----------------------------
% monotonicity   M     E.M
% regularity     R     E.M.C
% normality      K     E.M.C.N

name "axM"   ( (box_ (phi and_ psi)) imp_ box_ phi ).
name "axC"   ( ((box_ phi) and_ (box_ psi)) imp_ (box_ (phi and_ psi)) ).
name "axN"   ( box_ (phi imp_ phi) ).

% K is the weakest normal modal logic. Cqk proves the E axioms and M,C,N.
% Adding properties to the Kripke frame gets to stronger normal modal logics:
%
% Properties                    Name    Axioms
% -------------------------------------------------
% none                          K       K
% seriality                     D       K.D
% reflexivity                   T       K.T
% refl, transitivity            S4      K.T.4
% refl, trans, directed         S4.2    K.T.4.2
% refl, trans, connected        S4.3    K.T.4.3

name "axD"   ( (box_ phi) imp_ (dia_ phi) ).                   % seriality
name "axT"   ( (box_ phi) imp_ phi ).                          % reflexivity
name "ax4"   ( (box_ phi) imp_ (box_ (box_ phi)) ).            % transitivity
name "ax2"   ( (dia_ (box_ phi)) imp_ (box_ (dia_ phi)) ).     % directedness
name "ax3"   ( ((dia_ phi) and_ (dia_ psi)) imp_
               ( ( (dia_ ((dia_ phi) and_ psi)) or_
                   (dia_ (phi and_ (dia_ psi))) ) or_
                   (dia_ (phi and_ psi)))).                    % connectedness
name "axMcK" ( (box_ (dia_ phi)) imp_ (dia_ (box_ phi)) ).     % finality (McKinsey)
name "axvB3" ( (dia_ phi) and_
               (box_ (phi imp_ (box_ phi))) imp_ phi).         % unnamed property (Fact 1.5, VanBenthem)

% examples taken from techrep and validated

name "fig1"  ( box_ phi and_ box_ (phi imp_ psi) imp_ box_ psi ).
name "fig2"  ( box_ (all_ (x\ p x)) imp_ all_ (x\ box_ (p x)) ).
name "fig4"  ( box_ phi imp_ box_ (box_ phi) ).
name "fig5"  ( dia_ (box_ phi) imp_ box_ (dia_ phi) ).
name "fig6"  ( dia_ (box_ phi) imp_ box_ (dia_ phi) ).
name "fig7"  ( box_ (dia_ phi) imp_ dia_ (box_ phi) ).

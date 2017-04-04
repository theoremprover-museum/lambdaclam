sig frame.
accum_sig compound_tacs.

type zero_    theta.
type succ_    theta -> theta.
type bef      theta -> theta -> formula.
infixr bef    3.
type eqdot    theta -> theta -> formula.
infixr eqdot  3.

type refleq    proof.
type subeq     int -> proof -> proof.
type subeql    int -> int -> proof -> proof.
type subeqr    int -> int -> proof -> proof.
type trefleq   goal_ -> goal_ -> o.
type tsubeq    int -> goal_ -> goal_ -> o.
type tsubeql   int -> int -> goal_ -> goal_ -> o.
type tsubeqr   int -> int -> goal_ -> goal_ -> o.

type subst_eqdot  theta -> theta -> formula -> formula -> o.

type lor     int -> proof -> proof -> proof.
type ror     int -> proof -> proof.
type tlor    int -> goal_ -> goal_ -> o.
type tror    int -> goal_ -> goal_ -> o.

type rbef   int -> proof -> proof.
type trbef  int -> goal_ -> goal_ -> o.
type lbef   int -> proof -> proof -> proof.
type tlbef  int -> goal_ -> goal_ -> o.

type tser    goal_ -> goal_ -> o.
type ser     proof -> proof.
type wit     theta -> theta.

type trefl   goal_ -> goal_ -> o.
type refl    proof -> proof.

type ttrans  goal_ -> goal_ -> o.
type trans   proof -> proof -> proof -> proof.

type twdir   goal_ -> goal_ -> o.
type wdir    proof -> proof -> proof -> proof.
type cv      theta -> theta -> theta -> theta.
type tsdir   goal_ -> goal_ -> o.
type sdir    proof -> proof.

type twconn  goal_ -> goal_ -> o.
type wconn   proof -> proof -> proof -> proof -> proof -> proof.
type tsconn  theta -> theta -> goal_ -> goal_ -> o.
type sconn   theta -> theta -> proof -> proof -> proof -> proof.

type tatom   goal_ -> goal_ -> o.
type atom    proof -> proof -> proof.
type la      theta -> theta.

% not yet implemented
type tirr      goal_ -> goal_ -> o.
type ttsymm    goal_ -> goal_ -> o.
type tasymm    goal_ -> goal_ -> o.
type tantisymm goal_ -> goal_ -> o.
type twdens    goal_ -> goal_ -> o.
type tsdens    goal_ -> goal_ -> o.

type entails   proof -> (list formula) -> (list formula) -> o.

end

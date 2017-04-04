sig basic_tacs.

accum_sig frame.

% rules & tactics of Cqk

type ax     int -> int -> proof.
type lnot   int -> proof -> proof.
type rnot   int -> proof -> proof.
type limp   int -> proof -> proof -> proof.
type rimp   int -> proof -> proof.
type lallU  int -> proof -> proof.
type rallU  int -> (user_ -> proof) -> proof.
type lallN  int -> proof -> proof.
type rallN  int -> (nat_ -> proof) -> proof.
type lbox   int -> proof -> proof -> proof.
type rbox   int -> (theta -> proof) -> proof.
type tax    int -> int -> goal_ -> goal_ -> o.
type tlnot  int -> goal_ -> goal_ -> o.
type trnot  int -> goal_ -> goal_ -> o.
type tlimp  int -> goal_ -> goal_ -> o.
type trimp  int -> goal_ -> goal_ -> o.
type tlall  int -> goal_ -> goal_ -> o.
type trall  int -> goal_ -> goal_ -> o.
type tlbox  int -> goal_ -> goal_ -> o.
type trbox  int -> goal_ -> goal_ -> o.
type trbox2 int -> theta -> goal_ -> goal_ -> o.

% derived

type liff    int -> proof -> proof.
type riff    int -> proof -> proof -> proof.
type land    int -> proof -> proof.
type rand    int -> proof -> proof -> proof.
type lor     int -> proof -> proof -> proof.
type ror     int -> proof -> proof.
type lsomeU  int -> (user_ -> proof) -> proof.
type rsomeU  int -> proof -> proof.
type lsomeN  int -> (nat_ -> proof) -> proof.
type rsomeN  int -> proof -> proof.
type ldia    int -> (theta -> proof) -> proof.
type rdia    int -> proof -> proof -> proof.
type tliff   int -> goal_ -> goal_ -> o.
type triff   int -> goal_ -> goal_ -> o.
type tland   int -> goal_ -> goal_ -> o.
type trand   int -> goal_ -> goal_ -> o.
type tlor    int -> goal_ -> goal_ -> o.
type tror    int -> goal_ -> goal_ -> o.
type tlsome  int -> goal_ -> goal_ -> o.
type trsome  int -> goal_ -> goal_ -> o.
type tldia   int -> goal_ -> goal_ -> o.
type tldia2  int -> theta -> goal_ -> goal_ -> o.
type trdia   int -> goal_ -> goal_ -> o.

% entailment

type ent   proof -> proof.
type tent  goal_ -> goal_ -> o.
type isol  (list int) -> (list int) -> proof -> proof.
type tisol (list int) -> (list int) -> goal_ -> goal_ -> o.

% automatic

type tauto      goal_ -> goal_ -> o.
type tautoall   goal_ -> goal_ -> o.
type tsauto_fo  goal_ -> goal_ -> o.

% FI

type luntil   int -> (theta -> proof) -> proof.
type runtil   int -> proof -> proof -> proof -> proof.
type lwuntil  int -> proof -> proof -> proof.
type rwuntil  int -> proof -> proof.
type lboxt    int -> proof -> proof -> proof -> proof.
type rboxt    int -> (theta -> proof) -> proof.
type lnext    int -> proof -> proof.
type rnext    int -> proof -> proof.
type tluntil  int -> goal_ -> goal_ -> o.
type tluntil2 int -> theta -> goal_ -> goal_ -> o.
type truntil  int -> goal_ -> goal_ -> o.
type tlwuntil int -> goal_ -> goal_ -> o.
type trwuntil int -> goal_ -> goal_ -> o.
type tlboxt   int -> goal_ -> goal_ -> o.
type trboxt   int -> goal_ -> goal_ -> o.
type trboxt2  int -> theta -> goal_ -> goal_ -> o.
type tlnext   int -> goal_ -> goal_ -> o.
type trnext   int -> goal_ -> goal_ -> o.

end

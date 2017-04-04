sig basic_tacs.

accum_sig frame.

% rules & tactics of Cqk

type ax     int -> int -> proof.
type lnot   int -> proof -> proof.
type rnot   int -> proof -> proof.
type limp   int -> proof -> proof -> proof.
type rimp   int -> proof -> proof.
type lall   int -> proof -> proof.
type rall   int -> (iota -> proof) -> proof.
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
type lsome   int -> (iota -> proof) -> proof.
type rsome   int -> proof -> proof.
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

% automatic

type tauto      goal_ -> goal_ -> o.
type tautoall   goal_ -> goal_ -> o.
type tsauto_fo  goal_ -> goal_ -> o.

end

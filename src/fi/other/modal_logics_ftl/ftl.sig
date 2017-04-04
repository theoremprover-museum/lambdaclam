sig ftl.

accum_sig basic_tacs.
accum_sig examples.

type  check_  proof -> formula -> o.
type  top     formula -> o.
type  trim    (goal_ -> goal_ -> o) -> (goal_ -> goal_ -> o) -> o.
type  tinter  (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type  tproc   (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type  tback   goal_ -> goal_ -> o.

type  y      int.

end

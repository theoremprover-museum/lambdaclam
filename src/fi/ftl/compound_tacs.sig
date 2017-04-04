sig compound_tacs.

accum_sig lists_.
accum_sig syntax_.

type pre           (int -> goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type pre2          (int -> int -> goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type pre2l         ((list int) -> (list int) -> goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type pret          (theta -> theta -> goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type pre2t         (int -> theta -> goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.

type pair_tac      (goal_ -> goal_ -> o) -> (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type goalr_tac     goal_ -> goal_ -> o.
type map_tac       (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.

type id_tac        goal_ -> goal_ -> o.
type fail_tac      goal_ -> goal_ -> o.
type close_tac     goal_ -> goal_ -> o.
type close_rule    (proof -> proof).
type then_tac      (goal_ -> goal_ -> o) -> (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type orelse_tac    (goal_ -> goal_ -> o) -> (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type orelse!_tac   (goal_ -> goal_ -> o) -> (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type repeat_tac    (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type repeat_go_tac (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type try_tac       (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type complete_tac  (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type app_list_tac  list (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type app_list!_tac list (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type exhaust_tac   list (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type exhaust!_tac  list (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type idfs          int -> int -> list (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type idfs_b        int -> int -> int -> list (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.
type idfs_ub       int -> int -> list (goal_ -> goal_ -> o) -> goal_ -> goal_ -> o.

end

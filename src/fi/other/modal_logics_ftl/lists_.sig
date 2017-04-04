sig lists_.

type memberN_  int -> A -> (list A) -> o.
type deleteN_  int -> (list A) -> (list A) -> o.
type append_   A -> (list A) -> (list A) -> o.
type reduce_   (list int) -> (list A) -> (list A) -> o.

type map_      (A -> B -> o) -> (list A) -> (list B) -> o.

type print_    A -> o.
type write_    A -> o.
type wlist_    (list A) -> int -> o.

end

module lists_.

% ------- list management

memberN_ 1 A (A::Tail).
memberN_ N A (B::Tail) :- !, memberN_ N' A Tail, N is N' + 1.

deleteN_ 1 (A::Tail) Tail.
deleteN_ N (Y::Tail) (Y::Tail') :- !, deleteN_ N' Tail Tail', N is N' + 1.

append_ A nil (A::nil) :- !.
append_ A (X::Tail) (X::Tail') :- !, append_ A Tail Tail'.

reduce_ nil L nil.
reduce_ (N::Tail) L (X::Tail') :- memberN_ N X L, reduce_ Tail L Tail'.

% apply P eagerly, on elements on which it succeeds
map_ _ nil nil.
map_ P (H::Tail) (H'::Tail') :- P H H', map_ P Tail Tail'.
map_ P (H::Tail) (H ::Tail') :- map_ P Tail Tail'.

% ------- printing

print_ A :- !, print A.
write_ A :- !, term_to_string A Str, print_ Str.
wlist_ [] _ :- !.
wlist_ [Phi|Tail] N :- !, print_ "(", write_ N, print_ ") ",
  write_ Phi, print_ "\n\n", (N1 is (N + 1)), wlist_ Tail N1.

end

module basics.

%
% ------- list management
%

type member   A -> (list A) -> o.
type nmember  int -> A -> (list A) -> o.
type delete   A -> (list A) -> (list A) -> o.
type ndelete  int -> (list A) -> (list A) -> o.
type rmember  A -> (list A) -> (list A) -> o.
type rnmember int -> A -> (list A) -> (list A) -> o.

member X (X::L).
member X (Y::L) :- member X L.

nmember 1 A (A::Tail).
nmember N A (B::Tail) :- nmember N' A Tail, N is N' + 1.

delete X (X::Tail) Tail.
delete X (Y::Tail) (Y::Tail') :- delete X Tail Tail'.

ndelete N L1 L2 :- nmember N X L1, delete X L1 L2.

rmember A (A::Rest) Rest.
rmember A (B::Tail) (B::Rest) :- rmember A Tail Rest.

rnmember 1 A (A::Rest) Rest.
rnmember N A (B::Tail) (B::Rest) :- rnmember N' A Tail Rest, N is N' + 1.

%
% ------- printing routines
%

type  print_list  (list A) -> int -> o.
type  nl          o.
type  write       A -> o.

print_list nil N.
print_list (Phi::Tail) N :- !,
  print "(", write N, print ") ", write Phi, nl,
  (N1 is (N + 1)), print_list Tail N1.

nl :- print "\n".
write A :- term_to_string A Str, print Str.

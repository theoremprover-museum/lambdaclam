%  for testing pretty printer

module test_pretty.

import prettify.

testf 1 (app eq (tuple [zero,zero])).
testf 2 (app and (tuple [zero,zero])).
testf 3 (app forall (tuple [nat, abs z\ (app eq (tuple [z,z]))])).
testf N (app and (tuple [F,F])) :- 3 < N, N < 6, M is N - 1,
           testf M F.
testf 7      (app forall (tuple [nat,
      (abs x\ (app forall (tuple [nat, 
       (abs y\ (app eq (tuple [(app plus (tuple [y, x])),
                               (app plus (tuple [x, y]))])))])))])).
testf 8      (app forall (tuple [nat,
      (abs x\ (app forall (tuple [nat, 
       (abs y\ (app forall (tuple [nat, 
       (abs z\ (app eq
   (tuple [(app plus (tuple [(app plus (tuple [z,y])), x])),
           (app plus (tuple [z, (app plus (tuple [y, x]))]))
          ])))])))])))])).

ptestf N X :- testf N F, prettify_term F X.

test N :- 8 < N, print "Only test for numbers 1 ... 8 supported".
test N :- testf N F, pretty_show_term F.

testord :-  F = (app lim (tuple [zero, (abs z\ z)])),
            prettify_term F X,
            print "prettified syntax is ",
            printterm std_out X, print "\n",
            pr std_out X 80.

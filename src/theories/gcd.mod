/*

File: gcd.mod
Author: Louise Dennis
Description: Ordinal Theory
Last Modified: 10th January 2001

*/

module gcd.

accumulate objlists.

definition gcd_theory gcd1 
	trueP
      (app gcd (tuple [X, X, X]))
      trueP.

definition gcd_theory gcd2  
	trueP
      (app gcd 
       (tuple [(app plus (tuple [X, Y])), Y, Z]))
      (app gcd (tuple [X, Y, Z])).

definition gcd_theory gcd3  
	trueP
      (app gcd 
        (tuple [X, (app plus (tuple [X, Y])), Z]))  
      (app gcd (tuple [X, Y, Z])).

has_otype gcd_theory gcd ((tuple_type [X, X, X]) arrow bool).

top_goal gcd_theory gcd_synth []
   (app forall (tuple [nat,
    (abs p\ (app forall (tuple [nat,
     (abs q\ (app exists (tuple [nat,
      (abs r\ (app gcd (tuple [p, q, r])))])))])))])).

end
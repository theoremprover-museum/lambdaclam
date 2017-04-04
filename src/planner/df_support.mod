 /*

File: Kdf_support.mod
Author: Louise Dennis
Description: Support for Depth First Planner
Last Modified: 17th November 2000

*/

module df_support.

accumulate plan_support.

map_expand _Exp trueGoal trueGoal (and_node trueGoal _ complete_status nomethodyet nomethodyet nil nil notacticyet nil):- !.
map_expand Exp (G1 ** G2) (H1 ** H2) (and_node _ _ partial_status nomethodyet nomethodyet nil [P1, P2] notacticyet nil) :- !,
          map_expand Exp G1 H1 P1,
          map_expand Exp G2 H2 P2.
map_expand M (allGoal Type G) (allGoal Type H) (forall_node _ Type (X\ [P X])):- !,
        pi x\ (map_expand M (G x) (H x) (P x)).
map_expand M (existsGoal Type G) (existsGoal Type H) (exists_node _ Type (X\ [P X])):- !,
        (map_expand M (G Wit) (H Wit) (P Wit)).
map_expand Exp In Out Plan :- Exp In Out Plan.

end
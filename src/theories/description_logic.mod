/*

File: description_logic.mod
Author: Louise Dennis 
Description: Tree model construction in description logic

*/

module description_logic.

local dl_zip dl_zipper -> dl_tree -> dl_tree -> o.

dl_zip end_zip Node Node.
dl_zip (dl_tree_zip CL N P Zipper Rest) Node (dl_node CL TL) :-
	 dl_zip Zipper Node DLTree,
	 nth N (dl_pair DLTree P) TL Rest.

atomic description_logic detect_clash
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip Zipper (dl_node CL Children) T,
        member (ann_class Class Ann) CL,
        member (ann_class (app dl_neg Class) Ann) CL)
	true
	trueGoal
	notacticyet.
	
atomic description_logic dl_imp_goal
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip Zipper (dl_node CL Children) T,
        member (ann_class Class Ann) CL,
	definition _ Class NewClass trueP,
	not (member (ann_class NewClass _) CL)
	dl_zip Zipper (dl_node ((ann_class NewClass Ann)::CL) Children) NewT)
	true
	(seqGoal (N >>> (app clashes NewT)) Context)
	notacticyet.
	

atomic description_logic dl_imp_goal2
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip Zipper (dl_node CL Children) T,
        member (ann_class (app dl_neg Class) Ann) CL,
	definition _ NewClass Class trueP,
	not (member (ann_class NewClass _) CL)
	dl_zip Zipper (dl_node ((dl_pari NewClass Ann)::CL) Children) NewT)
	true
	(seqGoal (N >>> (app clashes NewT)) Context)
	notacticyet.
	

atomic description_logic dl_and_goal
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip Zipper (dl_node CL Children) T,
        member (ann_class (app dl_and [C1, C2]) Ann) CL,
	not (member (ann_class C1 _) CL)
	not (member (ann_class C2 _) CL)
	dl_zip Zipper (dl_node ((ann_class C1 Ann)::((ann_class C2 Ann)::CL)) Children) NewT)
	true
	(seqGoal (N >>> (app clashes NewT)) Context)
	notacticyet.


atomic description_logic dl_or_goal
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip Zipper (dl_node CL Children) T,
        member (ann_class (app dl_or [C1, C2]) Ann) CL,
	not (member (ann_class C1 _) CL)
	not (member (ann_class C2 _) CL)
	dl_zip Zipper (dl_node ((ann_class C1 Ann)::CL) Children) NewT1,
	dl_zip Zipper (dl_node ((ann_class C2 Ann)::CL) Children) NewT2)
	true
	(andGoal ((seqGoal (N >>> (app clashes NewT1)) Context) **
	(seqGoal (N >>> (app clashes NewT2)) Context)))
	notacticyet.

atomic description_logic dl_exists_goal
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip Zipper (dl_node CL Children) T,
        member (ann_class (app dl_exists [P, C2]) Ann) CL,
	not ( member (dl_pair (dl_node CL2 _) P), member C2 CL2),
	dl_zip Zipper (dl_node CL ((dl_node [(ann_class C2 Ann)] [])::Children)) NewT)
	true
	(seqGoal (N >>> (app clashes NewT)) Context)
	notacticyet.


atomic description_logic dl_all_goal
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip Zipper (dl_node CL Children) T,
        member (ann_class (app dl_forall [P, C2]) Ann) CL,
	nth N (dl_pair (dl_node CL2 Ch2) P) Children Rest,
	not (member C2 CL2),
	nth N (dl_pair (dl_node ((ann_class C2 Ann)::CL2 Ch2) P) NewChildren Rest,
	dl_zip Zipper (dl_node CL NewChildren) NewT)
	true
	(seqGoal (N >>> (app clashes NewT)) Context)
	notacticyet.

atomic description_logic nec_suff
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip (dl_tree_zip CLP N P Zipper Rest) (dl_node CL Children) T,
       forall (member (ann_class _ X) CL, X = Ann) ,
       member (ann_class (app neg C2) Ann2) CLP,
       not (Ann2 = Ann),
       axiom _ C3 C2 trueP,
       subterm_of C3 (app dl_exists [P, C4]) _,
       member (ann_class C4 _) CL)
       (printstdout "necessary and sufficient?"
        printstdout (app C3 C2))
	trueGoal
	notacticyet.
       

atomic description_logic open_world
       (seqGoal (H >>> (app clashes T)) Context)
       (dl_zip (dl_tree_zip CLP N P Zipper Rest) (dl_node CL Children) T,
       forall (member (ann_class _ X) CL, X = Ann) ,
       member (ann_class C2 Ann2) CLP,
       not (Ann2 = Ann),
       axiom _ C2 C3 trueP,
       subterm_of C3 (app dl_exists [P, C4]) _,
       member (ann_class C4 _) CL)
       (printstdout "necessary and sufficient?"
        printstdout (app C3 C2))
	trueGoal
	notacticyet.
       

end

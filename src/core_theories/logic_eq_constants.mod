/*

File: logic_eq_constants.mod
Author: Louise Dennis
Description: Theory of logic with equality
Last Modified: 20th March 2001

*/

module logic_eq_constants.


%% Useful utilities 

replace_in_hyps (H::T) H L HH :- append L T HH.
replace_in_hyps (H::T) X L (H::TT) :- replace_in_hyps T X L TT.

forall_elim X T (G X) (app forall [T, (abs G T)]).


%% Pretty printing of logic connectives

prettify_special (app and [A,B]) 
  (blo 1 [str "(", AA, str " /\\", brk 1, BB, str ")"] )
   :- !, prettify_term A AA, prettify_term B BB.

prettify_special (app eq [A,B]) 
  (blo 1 [str "(", AA, str " =", brk 1, BB, str ")"] )
   :- !, prettify_term A AA, prettify_term B BB.

prettify_special (app or [A,B]) 
  (blo 1 [str "(", AA, str " \\/", brk 1, BB, str ")"] )
   :- !, prettify_term A AA, prettify_term B BB.

prettify_special (app imp [A,B]) 
  (blo 1 [str "(", AA, str " ->", brk 1, BB, str ")"] )
   :- !, prettify_term A AA, prettify_term B BB.

prettify_special (app iff [A,B]) 
  (blo 1 [str "(", AA, str " <->", brk 1, BB, str ")"] )
   :- !, prettify_term A AA, prettify_term B BB.

prettify_special (app forall [Type, (abs F Type)])
         (abstr 1 (a\ [ str "forall ", lvar a, str ":", PType,
                      brk 1, Rest a])) 
   :- !, prettify_term Type PType,
         pi z\ (prettify_term (F z) (Rest z)).  
        
prettify_special (app exists [Type, (abs F Type)])
         (abstr 1 (a\ [ str "exists ", lvar a, str ":", PType,
                      brk 1, Rest a])) 
   :- !, prettify_term Type PType,
         pi z\ (prettify_term (F z) (Rest z)).

prettify_special (app neg [A]) (blo 1 [str "~ ", AA ]) 
   :- !, prettify_term A AA.


end

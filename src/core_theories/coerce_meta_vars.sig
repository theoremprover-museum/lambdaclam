/*
 * File: coerce_meta_vars
 * Author: Louise Dennis
 * meta-variable coercion onto a project of arguments
 * in order to try and eagerly instantiate meta-vars
 */

sig coerce_meta_vars.

accum_sig conjecture_tester.


type coerce_meta_vars theory.

type coerce_vars meth.
type try_projection meth.

type newgen osyn -> osyn -> context.


%% Predicates which will be defined later.

end
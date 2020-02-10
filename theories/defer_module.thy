theory defer_module
imports electoral_modules

begin

(********************************)
(*** Definition: Defer Module ***)
(********************************)

(* The defer module is not concerned about the voter's ballots, and just defers all alternatives.
   It is primarily used as definition for an empty loop.
*)
fun Defer_module :: "'a Electoral_module" where
  "Defer_module A p = ({}, {}, A)"

(* Soundness: Defer Module *)
(* The defer module satisfies the electoral_module predicate. This ensures it can be used as
   electoral module in compositions.
*)
theorem defer_module_sound[simp]:
  shows "electoral_module Defer_module"
  by (simp add: electoral_module_def partition_of_def)

(**************************************)
(*** Properties of the Defer Module ***)
(**************************************)

lemma defer_module_non_electing:
  shows "non_electing Defer_module"
  by (simp add: non_electing_def)

lemma defer_module_defer_lift_invariant:
  shows "defer_lift_invariant Defer_module"
  by (simp add: defer_lift_invariant_def)

end

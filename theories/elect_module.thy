theory elect_module
imports electoral_modules

begin

(********************************)
(*** Definition: Elect Module ***)
(********************************)

(* The elect module is not concerned about the voter's ballots, and just elects all alternatives.
   It is primarily used in sequence after an electoral module that only defer alternatives to
   finalize the decision.
*)
fun Elect_module :: "'a Electoral_module" where
  "Elect_module A p = (A, {}, {})"

(* Soundness: Elect Module *)
(* The elect module satisfies the electoral_module predicate. This ensures it can be used as
   electoral module in compositions.
*)
lemma elect_module_sound[simp]:
  shows "electoral_module Elect_module"
  by (simp add: electoral_module_def partition_of_def)

(**************************************)
(*** Properties of the Elect Module ***)
(**************************************)

(* The elect module is electing. *)
lemma elect_module_electing[simp]:
  shows "electing Elect_module"
  by (simp add: electing_def)

end
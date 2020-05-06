theory defer_eq_condition
imports termination_conditions

begin

(*****************************************)
(*** Definition: Defer Equal Condition ***)
(*****************************************)

(* This is a family of termination conditions. For a natural number n the affiliated defer equal
   condition is true, iff the given result's defer set has exactly n elements.
*)
fun Defer_eq_condition :: "nat \<Rightarrow> 'a Termination_condition" where
  "Defer_eq_condition n result
    = (let (e, r, d) = result in
        card d = n)"

end

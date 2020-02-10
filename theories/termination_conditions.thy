theory termination_conditions
imports electoral_modules

begin

(*****************************************)
(*** Definition: Termination Condition ***)
(*****************************************)

(* Termination conditions are used in loops. They decide whether or not to terminate the loop after
   each iteration, depending on the current outcome of the loop. *)
type_synonym 'a Termination_condition = "'a Result \<Rightarrow> bool"

end
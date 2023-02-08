(*  File:       Termination_Condition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Termination Condition\<close>

theory Termination_Condition
  imports "Social_Choice_Types/Result"
begin

text \<open>
  The termination condition is used in loops. It decides whether or not to
  terminate the loop after each iteration, depending on the current state
  of the loop.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Termination_Condition = "'a Result \<Rightarrow> bool"

end

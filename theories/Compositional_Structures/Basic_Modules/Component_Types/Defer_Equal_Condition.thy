(*  File:       Defer_Equal_Condition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Defer Equal Condition\<close>

theory Defer_Equal_Condition
  imports Termination_Condition
begin

text \<open>
  This is a family of termination conditions. For a natural number n,
  the according defer-equal condition is true if and only if the given
  result's defer-set contains exactly n elements.
\<close>

subsection \<open>Definition\<close>

fun defer_equal_condition :: "nat \<Rightarrow> 'a Termination_Condition" where
  "defer_equal_condition n result = (let (e, r, d) = result in card d = n)"

end

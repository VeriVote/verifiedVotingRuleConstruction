(*  File:       Defer_One_Loop_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Defer One Loop Composition\<close>

theory Defer_One_Loop_Composition
  imports "Basic_Modules/Component_Types/Defer_Equal_Condition"
          Loop_Composition
          Elect_Composition
begin

text \<open>
  This is a family of loop compositions. It uses the same module in sequence
  until either no new decisions are made or only one alternative is remaining
  in the defer-set. The second family herein uses the above family and
  subsequently elects the remaining alternative.
\<close>

subsection \<open>Definition\<close>

fun iter :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "iter m =
    (let t = defer_equal_condition 1 in
      (m \<circlearrowleft>\<^sub>t))"

abbreviation defer_one_loop ::
  "'a Electoral_Module \<Rightarrow> 'a Electoral_Module"
    ("_\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d" 50) where
  "m \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d \<equiv> iter m"

fun iterelect :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "iterelect m = elector (m \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)"

end

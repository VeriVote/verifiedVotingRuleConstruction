(*  File:       Schwartz_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Schwartz Rule\<close>

theory Schwartz_Rule
  imports "Compositional_Structures/Basic_Modules/Borda_Module"
          "Compositional_Structures/Defer_One_Loop_Composition"
begin

text \<open>
  This is the Schwartz voting rule. Confusingly, it is sometimes also referred
  as Nanson's rule. The Schwartz rule proceeds as in the classic Nanson's rule,
  but excludes alternatives with a Borda score that is strictly less than the
  average Borda score.
\<close>

subsection \<open>Definition\<close>

fun schwartz_rule :: "('a, 'v, 'a Result) Electoral_Module" where
  "schwartz_rule V A p =
    ((less_average_eliminator borda_score) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) V A p"

subsection \<open>Soundness\<close>

theorem schwartz_rule_sound: 
"social_choice_result.electoral_module schwartz_rule"
  unfolding schwartz_rule.simps
  by (simp add: loop_comp_sound)

end

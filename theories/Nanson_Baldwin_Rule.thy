(*  File:       Nanson_Baldwin_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Nanson-Baldwin Rule\<close>

theory Nanson_Baldwin_Rule
  imports "Compositional_Structures/Basic_Modules/Borda_Module"
          "Compositional_Structures/Defer_One_Loop_Composition"
begin

text \<open>
  This is the Nanson-Baldwin voting rule. It excludes alternatives with the
  lowest Borda score from the set of possible winners and then adjusts the
  Borda score to the new (remaining) set of still eligible alternatives.
\<close>

subsection \<open>Definition\<close>

fun nanson_baldwin_rule :: "('a, 'v, 'a Result) Electoral_Module" where
  "nanson_baldwin_rule A p =
    ((min_eliminator borda_score) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"

subsection \<open>Soundness\<close>

theorem nanson_baldwin_rule_sound: "\<S>\<C>\<F>_result.electoral_module nanson_baldwin_rule"
  using min_elim_sound loop_comp_sound
  unfolding nanson_baldwin_rule.simps Defer_One_Loop_Composition.iter.simps
  by metis

end
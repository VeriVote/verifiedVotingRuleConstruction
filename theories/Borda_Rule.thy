(*  File:       Borda_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Borda Rule\<close>

theory Borda_Rule
  imports "Compositional_Structures/Basic_Modules/Borda_Module"
          "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance_Rationalization"
          "Compositional_Structures/Elect_Composition"
begin

text \<open>
  This is the Borda rule. On each ballot, each alternative is assigned a score
  that depends on how many alternatives are ranked below. The sum of all such
  scores for an alternative is hence called their Borda score. The alternative
  with the highest Borda score is elected.
\<close>

subsection \<open>Definition\<close>

fun borda_rule :: "('a, 'v, 'a Result) Electoral_Module" where
  "borda_rule V A p = elector borda V A p"

fun borda_rule\<^sub>\<R> :: "('a, 'v::wellorder, 'a Result) Electoral_Module" where
  "borda_rule\<^sub>\<R> V A p = swap_\<R> unanimity V A p"

subsection \<open>Soundness\<close>

theorem borda_rule_sound: "social_choice_result.electoral_module borda_rule"
  unfolding borda_rule.simps
  using elector_sound borda_sound
  by metis

theorem borda_rule\<^sub>\<R>_sound: "social_choice_result.electoral_module borda_rule\<^sub>\<R>"
  unfolding borda_rule\<^sub>\<R>.simps swap_\<R>.simps
  using social_choice_result.\<R>_sound
  by metis

subsection \<open>Anonymity Property\<close>

theorem borda_rule\<^sub>\<R>_anonymous: "social_choice_result.anonymity borda_rule\<^sub>\<R>"
proof (unfold borda_rule\<^sub>\<R>.simps swap_\<R>.simps)
  let ?swap_dist = "votewise_distance swap l_one"
  from l_one_is_sym
  have "distance_anonymity ?swap_dist"
    using symmetric_norm_imp_distance_anonymous[of l_one]
    by simp
  with unanimity_anonymous
  show "social_choice_result.anonymity 
          (social_choice_result.distance_\<R> ?swap_dist unanimity)"
    using social_choice_result.anonymous_distance_and_consensus_imp_rule_anonymity
    by metis
qed

end

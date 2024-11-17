(*  File:       Kemeny_Rule.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Kemeny Rule\<close>

theory Kemeny_Rule
  imports
    "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Distance_Rationalization_Symmetry"
begin

text \<open>
  This is the Kemeny rule. It creates a complete ordering of alternatives and
  evaluates each ordering of the alternatives in terms of the sum of preference
  reversals on each ballot that would have to be performed in order to produce
  that transitive ordering. The complete ordering which requires the fewest
  preference reversals is the final result of the method.
\<close>

subsection \<open>Definition\<close>

fun kemeny_rule :: "('a, 'v :: wellorder, 'a Result) Electoral_Module" where
  "kemeny_rule V A p = swap_\<R> strong_unanimity V A p"

subsection \<open>Soundness\<close>

theorem kemeny_rule_sound: "\<S>\<C>\<F>_result.electoral_module kemeny_rule"
  unfolding kemeny_rule.simps swap_\<R>.simps
  using \<S>\<C>\<F>_result.\<R>_sound
  by metis

subsection \<open>Anonymity\<close>

theorem kemeny_rule_anonymous: "\<S>\<C>\<F>_result.anonymity kemeny_rule"
proof (unfold kemeny_rule.simps swap_\<R>.simps)
  let ?swap_dist = "votewise_distance swap l_one"
  have "distance_anonymity ?swap_dist"
    using l_one_is_sym symmetric_norm_imp_distance_anonymous[of l_one]
    by simp
  thus "\<S>\<C>\<F>_result.anonymity
          (\<S>\<C>\<F>_result.distance_\<R> ?swap_dist strong_unanimity)"
    using strong_unanimity_anonymous
          \<S>\<C>\<F>_result.anonymous_distance_and_consensus_imp_rule_anonymity
    by metis
qed

subsection \<open>Neutrality\<close>

lemma swap_dist_neutral: "distance_neutrality well_formed_elections
                              (votewise_distance swap l_one)"
  using neutral_dist_imp_neutral_votewise_dist swap_neutral
  by blast

theorem kemeny_rule_neutral: "\<S>\<C>\<F>_properties.neutrality
        well_formed_elections kemeny_rule"
  using strong_unanimity_neutral' swap_dist_neutral strong_unanimity_closed_under_neutrality
        \<S>\<C>\<F>_properties.neutr_dist_and_cons_imp_neutr_dr
  unfolding kemeny_rule.simps swap_\<R>.simps
  by blast

end
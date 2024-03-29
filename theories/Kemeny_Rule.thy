(*  File:       Kemeny_Rule.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Kemeny Rule\<close>

theory Kemeny_Rule
  imports "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance_Rationalization"
begin

text \<open>
  This is the Kemeny rule. It creates a complete ordering of alternatives and
  evaluates each ordering of the alternatives in terms of the sum of preference
  reversals on each ballot that would have to be performed in order to produce
  that transitive ordering. The complete ordering which requires the fewest
  preference reversals is the final result of the method.
\<close>

subsection \<open>Definition\<close>

fun kemeny_rule :: "'a Electoral_Module" where
  "kemeny_rule A p = swap_\<R> strong_unanimity A p"

subsection \<open>Soundness\<close>

theorem kemeny_rule_sound: "electoral_module kemeny_rule"
  unfolding kemeny_rule.simps swap_\<R>.simps
  using \<R>_sound
  by metis

subsection \<open>Anonymity Property\<close>

theorem kemeny_rule_anonymous: "anonymity kemeny_rule"
proof (unfold kemeny_rule.simps swap_\<R>.simps)
  let ?swap_dist = "votewise_distance swap l_one"
  have "distance_anonymity ?swap_dist"
    using l_one_is_sym symmetric_norm_imp_distance_anonymous[of l_one]
    by simp
  thus "anonymity (distance_\<R> ?swap_dist strong_unanimity)"
    using strong_unanimity_anonymous anonymous_distance_and_consensus_imp_rule_anonymity
    by metis
qed

end

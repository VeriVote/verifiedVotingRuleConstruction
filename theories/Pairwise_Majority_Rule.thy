(*  File:       Pairwise_Majority_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Pairwise Majority Rule\<close>

theory Pairwise_Majority_Rule
  imports "Compositional_Structures/Basic_Modules/Condorcet_Module"
          "Compositional_Structures/Defer_One_Loop_Composition"
begin

text \<open>
  This is the pairwise majority rule, a voting rule that implements the
  Condorcet criterion, i.e., it elects the Condorcet winner if it exists,
  otherwise a tie remains between all alternatives.
\<close>

subsection \<open>Definition\<close>

fun pairwise_majority_rule :: "'a Electoral_Module" where
  "pairwise_majority_rule A p = elector condorcet A p"

fun condorcet' :: "'a Electoral_Module" where
"condorcet' A p =
  ((min_eliminator condorcet_score) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"

fun pairwise_majority_rule' :: "'a Electoral_Module" where
"pairwise_majority_rule' A p = iterelect condorcet' A p"

subsection \<open>Soundness\<close>

theorem pairwise_majority_rule_sound: "electoral_module pairwise_majority_rule"
  unfolding pairwise_majority_rule.simps
  using condorcet_sound elector_sound
  by metis

theorem condorcet'_rule_sound: "electoral_module condorcet'"
  unfolding condorcet'.simps
  by (simp add: loop_comp_sound)

theorem pairwise_majority_rule'_sound: "electoral_module pairwise_majority_rule'"
  unfolding pairwise_majority_rule'.simps
  using condorcet'_rule_sound elector_sound iter.simps iterelect.simps loop_comp_sound
  by metis

subsection \<open>Condorcet Consistency Property\<close>

theorem condorcet_condorcet: "condorcet_consistency pairwise_majority_rule"
proof (unfold pairwise_majority_rule.simps)
  show "condorcet_consistency (elector condorcet)"
    using condorcet_is_dcc dcc_imp_cc_elector
    by metis
qed

end

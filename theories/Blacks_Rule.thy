(*  File:       Blacks_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Black's Rule\<close>

theory Blacks_Rule
  imports Pairwise_Majority_Rule
          Borda_Rule
begin

text \<open>
  This is Black's voting rule. It is composed of a function that determines
  the Condorcet winner, i.e., the Pairwise Majority rule, and the Borda rule.
  Whenever there exists no Condorcet winner, it elects the choice made by the
  Borda rule, otherwise the Condorcet winner is elected.
\<close>

subsection \<open>Definition\<close>

declare seq_comp_alt_eq[simp]

fun black :: "'a Electoral_Module" where
  "black A p = (condorcet \<triangleright> borda) A p"

fun blacks_rule :: "'a Electoral_Module" where
  "blacks_rule A p = elector black A p"

declare seq_comp_alt_eq[simp del]

subsection \<open>Soundness\<close>

theorem blacks_sound: "electoral_module black"
  unfolding black.simps
  using seq_comp_sound condorcet_sound borda_sound
  by metis

theorem blacks_rule_sound: "electoral_module blacks_rule"
  unfolding blacks_rule.simps
  using blacks_sound elector_sound
  by metis

subsection \<open>Condorcet Consistency Property\<close>

theorem black_is_dcc: "defer_condorcet_consistency black"
  unfolding black.simps
  using condorcet_is_dcc borda_mod_non_blocking borda_mod_non_electing seq_comp_dcc
  by metis

theorem black_condorcet: "condorcet_consistency blacks_rule"
  unfolding blacks_rule.simps
  using black_is_dcc dcc_imp_cc_elector
  by metis

end

(*  File:       Condorcet_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Condorcet Rule\<close>

theory Condorcet_Rule
  imports Condorcet_Module Elect_Module Defer_One_Loop_Composition
begin

text
\<open>This is a voting rule that implements the Condorcet criterion, i.e., it elects
the Condorcet winner if it exists, otherwise a tie remains between all
alternatives.\<close>

subsection \<open>Definition\<close>

fun condorcet_rule :: "'a Electoral_Module" where
  "condorcet_rule A p = elector condorcet A p"

fun condorcet_rule_code :: "'a Electoral_Module" where
  "condorcet_rule_code A p = elector condorcet_code A p"

fun condorcet' :: "'a Electoral_Module" where
"condorcet' A p =
  ((min_eliminator condorcet_score) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"

fun condorcet_rule' :: "'a Electoral_Module" where
"condorcet_rule' A p = iterelect condorcet' A p"

subsection \<open>Property\<close>

theorem condorcet_condorcet: "condorcet_consistency condorcet_rule"
proof -
  have
    "defer_condorcet_consistency
      (\<lambda>A. max_eliminator condorcet_score (A::'a set)) \<longrightarrow>
        condorcet_consistency
          (condorcet_rule ::'a set \<Rightarrow> (_ \<times> _) set list \<Rightarrow>
            _ set \<times> _ set \<times> _ set)"
    using condorcet.simps condorcet_consistency_def
          defer_condorcet_consistency_def electoral_module_def
          condorcet_rule.simps dcc_imp_cc_elector
    by (smt (verit, ccfv_threshold))
  thus ?thesis
    using condorcet_score_is_condorcet_rating
          cr_eval_imp_dcc_max_elim
    by blast
qed

end

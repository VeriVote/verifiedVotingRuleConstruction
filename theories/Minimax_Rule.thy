(*  File:       Minimax_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Minimax Rule\<close>

theory Minimax_Rule
  imports Minimax_Module Elect_Module
begin

text
\<open>This is the Minimax voting rule. It elects the alternatives with the highest
Minimax score.\<close>

subsection \<open>Definition\<close>

fun minimax_rule :: "'a Electoral_Module" where
  "minimax_rule A p = elector minimax A p"

fun minimax_rule_code :: "'a Electoral_Module" where
  "minimax_rule_code A p = elector minimax_code A p"

subsection \<open>Property\<close>

theorem minimax_condorcet: "condorcet_consistency minimax_rule"
proof -
  have assm:
    "defer_condorcet_consistency
      (\<lambda>A. max_eliminator minimax_score (A::'a set)) \<longrightarrow>
      condorcet_consistency
        (minimax_rule ::'a set \<Rightarrow> (_ \<times> _) set list \<Rightarrow>
          _ set \<times> _ set \<times> _ set)"
    using minimax.simps condorcet_consistency_def
          defer_condorcet_consistency_def electoral_module_def
          minimax_rule.simps dcc_imp_cc_elector
    by (smt (verit, ccfv_threshold))
  thus ?thesis
  proof -
    have
      "defer_condorcet_consistency
        (\<lambda>A. max_eliminator minimax_score (A::'a set))"
      using cr_eval_imp_dcc_max_elim minimax_score_cond_rating
      by blast
    thus ?thesis
      using assm
      by linarith
  qed
qed

end

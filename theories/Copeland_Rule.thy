(*  File:       Copeland_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Copeland Rule\<close>

theory Copeland_Rule
  imports Copeland_Module Elect_Module
begin

text
\<open>This is the Copeland voting rule. The idea is to elect the alternatives with
the highest difference between the amount of simple-majority wins and the
amount of simple-majority losses.\<close>

subsection \<open>Definition\<close>

fun copeland_rule :: "'a Electoral_Module" where
  "copeland_rule A p = elector copeland A p"

fun copeland_rule_code :: "'a Electoral_Module" where
  "copeland_rule_code A p = elector copeland_code A p"

subsection \<open>Property\<close>

(*Copeland is Condorcet consistent.*)
theorem copeland_condorcet: "condorcet_consistency copeland_rule"
proof -
  have
    "defer_condorcet_consistency
      (\<lambda>A. max_eliminator copeland_score (A::'a set)) \<longrightarrow>
    condorcet_consistency (copeland_rule ::'a set \<Rightarrow> (_ \<times> _) set list \<Rightarrow>
      _ set \<times> _ set \<times> _ set)"
    using copeland.simps condorcet_consistency_def
          defer_condorcet_consistency_def electoral_module_def
          copeland_rule.simps dcc_imp_cc_elector
    by (smt (verit, ccfv_threshold))
  thus ?thesis
    using copeland_score_is_cr
          cr_eval_imp_dcc_max_elim
    by blast
qed

end

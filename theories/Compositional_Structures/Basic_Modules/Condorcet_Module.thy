(*  File:       Condorcet_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Condorcet Module\<close>

theory Condorcet_Module
  imports "Component_Types/Elimination_Module"
begin

context social_choice_result
begin

text \<open>
  This is the Condorcet module used by the Condorcet (voting) rule. The
  Condorcet rule is a voting rule that implements the Condorcet criterion,
  i.e., it elects the Condorcet winner if it exists, otherwise a tie remains
  between all alternatives. The module implemented herein only rejects the
  alternatives not elected by the voting rule, and defers the alternatives that
  would be elected by the full voting rule.
\<close>

subsection \<open>Definition\<close>

fun condorcet_score :: "('a, 'v) Evaluation_Function" where
  "condorcet_score V x A p =
    (if (condorcet_winner V A p x) then 1 else 0)"

fun condorcet :: "('a, 'v, 'a Result) Electoral_Module" where
  "condorcet V A p = (max_eliminator condorcet_score) V A p"

subsection \<open>Soundness\<close>

theorem condorcet_sound: "electoral_module condorcet"
  unfolding condorcet.simps
  using max_elim_sound
  by metis

subsection \<open>Property\<close>

(* Condorcet score is Condorcet rating. *)
theorem condorcet_score_is_condorcet_rating: "condorcet_rating condorcet_score"
proof (unfold condorcet_rating_def, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'a" and
    l :: "'a"
  assume
    c_win: "condorcet_winner V A p w" and
    l_neq_w: "l \<noteq> w"
  have "\<not> condorcet_winner V A p l"
    using cond_winner_unique c_win l_neq_w
    by (metis (no_types))
  hence zero_score: "condorcet_score V l A p = 0"
    by simp
  moreover have one_score: "condorcet_score V w A p = 1"
    using c_win
    by auto
  ultimately show "condorcet_score V l A p < condorcet_score V w A p"
    by (metis one_score zero_less_one zero_score)
qed

theorem condorcet_is_dcc: "defer_condorcet_consistency condorcet"
proof (unfold defer_condorcet_consistency_def electoral_module_def, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    "finite A" and
    "finite V" and
    "profile V A p"
  hence "well_formed A (max_eliminator condorcet_score V A p)"
    using max_elim_sound
    unfolding electoral_module_def
    by metis
  thus "well_formed A (condorcet V A p)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    c_win_w: "condorcet_winner V A p a" and
    fin_A: "finite A" and
    fin_V: "finite V"
  have "defer_condorcet_consistency (max_eliminator condorcet_score)"
    using cr_eval_imp_dcc_max_elim
    by (simp add: condorcet_score_is_condorcet_rating)
  hence "max_eliminator condorcet_score V A p =
          ({},
          A - defer V (max_eliminator condorcet_score) A p,
          {b \<in> A. condorcet_winner V A p b})"
    using c_win_w fin_A
    unfolding defer_condorcet_consistency_def
    by (metis (no_types))
  thus "condorcet V A p =
          ({},
          A - defer V condorcet A p,
          {d \<in> A. condorcet_winner V A p d})"
    by simp
qed

end
end

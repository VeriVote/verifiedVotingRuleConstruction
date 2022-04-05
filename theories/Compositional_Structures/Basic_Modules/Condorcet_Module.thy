(*  File:       Condorcet_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Condorcet Module\<close>

theory Condorcet_Module
  imports "Component_Types/Elimination_Module"
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

fun condorcet_score :: "'a Evaluation_Function" where
  "condorcet_score x A p =
    (if (condorcet_winner A p x) then 1 else 0)"

fun condorcet :: "'a Electoral_Module" where
  "condorcet A p = (max_eliminator condorcet_score) A p"

subsection \<open>Property\<close>

(* Condorcet score is Condorcet rating. *)
theorem condorcet_score_is_condorcet_rating: "condorcet_rating condorcet_score"
proof (unfold condorcet_rating_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    l :: "'a"
  assume
    c_win: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  have "\<not> condorcet_winner A p l"
    using c_win l_neq_w cond_winner_unique
    by (metis (no_types))
  thus "condorcet_score l A p < condorcet_score w A p"
    using c_win
    by simp
qed

theorem condorcet_is_dcc: "defer_condorcet_consistency condorcet"
proof (unfold defer_condorcet_consistency_def electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    finA: "finite A" and
    profA: "profile A p"
  have "well_formed A (max_eliminator condorcet_score A p)"
    using finA profA max_elim_sound
    unfolding electoral_module_def
    by metis
  thus "well_formed A (condorcet A p)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    cwin_w: "condorcet_winner A p w" and
    finA: "finite A"
  have max_cscore_dcc:
    "defer_condorcet_consistency (max_eliminator condorcet_score)"
    using cr_eval_imp_dcc_max_elim
    by (simp add: condorcet_score_is_condorcet_rating)
  have
    "max_eliminator condorcet_score A p =
  ({},
  A - defer (max_eliminator condorcet_score) A p,
  {a \<in> A. condorcet_winner A p a})"
    using cwin_w finA max_cscore_dcc
    unfolding defer_condorcet_consistency_def
    by (metis (no_types))
  thus
    "condorcet A p =
      ({},
       A - defer condorcet A p,
       {d \<in> A. condorcet_winner A p d})"
    by simp
qed

end

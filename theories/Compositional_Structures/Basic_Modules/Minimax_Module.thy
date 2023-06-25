(*  File:       Minimax_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Minimax Module\<close>

theory Minimax_Module
  imports "Component_Types/Elimination_Module"
begin

text \<open>
  This is the Minimax module used by the Minimax voting rule. The Minimax rule
  elects the alternatives with the highest Minimax score. The module implemented
  herein only rejects the alternatives not elected by the voting rule, and defers
  the alternatives that would be elected by the full voting rule.
\<close>

subsection \<open>Definition\<close>

fun minimax_score :: "'a Evaluation_Function" where
  "minimax_score x A p =
    Min {prefer_count p x y | y . y \<in> A - {x}}"

fun minimax :: "'a Electoral_Module" where
  "minimax A p = max_eliminator minimax_score A p"

subsection \<open>Soundness\<close>

theorem minimax_sound: "electoral_module minimax"
  unfolding minimax.simps
  using max_elim_sound
  by metis

subsection \<open>Lemma\<close>

lemma non_cond_winner_minimax_score:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    l :: "'a"
  assumes
    prof: "profile A p" and
    winner: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  shows "minimax_score l A p \<le> prefer_count p l w"
proof (simp)
  let
    ?set = "{prefer_count p l y | y . y \<in> A - {l}}" and
      ?lscore = "minimax_score l A p"
  have finite: "finite ?set"
    using prof winner finite_Diff
    by simp
  have w_not_l: "w \<in> A - {l}"
    using winner l_neq_w
    by simp
  hence not_empty: "?set \<noteq> {}"
    by blast
  have "?lscore = Min ?set"
    by simp
  hence "?lscore \<in> ?set \<and> (\<forall> p \<in> ?set. ?lscore \<le> p)"
    using finite not_empty Min_le Min_eq_iff
    by (metis (no_types, lifting))
  thus "Min {card {i. i < length p \<and> (y, l) \<in> p!i} | y. y \<in> A \<and> y \<noteq> l} \<le>
          card {i. i < length p \<and> (w, l) \<in> p!i}"
    using w_not_l
    by auto
qed

subsection \<open>Property\<close>

theorem minimax_score_cond_rating: "condorcet_rating minimax_score"
proof (unfold condorcet_rating_def minimax_score.simps prefer_count.simps, safe, rule ccontr)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    l :: "'a"
  assume
    winner: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w:"l \<noteq> w" and
    min_leq:
      "\<not> Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r l))} |
        y. y \<in> A - {l}} <
      Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r w))} |
          y. y \<in> A - {w}}"
  hence min_count_ineq:
    "Min {prefer_count p l y | y. y \<in> A - {l}} \<ge>
        Min {prefer_count p w y | y. y \<in> A - {w}}"
    by simp
  have pref_count_gte_min: "prefer_count p l w  \<ge> Min {prefer_count p l y | y . y \<in> A - {l}}"
    using l_in_A l_neq_w condorcet_winner.simps winner non_cond_winner_minimax_score
          minimax_score.simps
    by metis
  have l_in_A_without_w: "l \<in> A - {w}"
    using l_in_A
    by (simp add: l_neq_w)
  hence pref_counts_non_empty: "{prefer_count p w y | y . y \<in> A - {w}} \<noteq> {}"
    by blast
  have "finite (A - {w})"
    using condorcet_winner.simps winner finite_Diff
    by metis
  hence "finite {prefer_count p w y | y . y \<in> A - {w}}"
    by simp
  hence "\<exists> n \<in> A - {w} . prefer_count p w n =
            Min {prefer_count p w y | y . y \<in> A - {w}}"
    using pref_counts_non_empty Min_in
    by fastforce
  then obtain n where pref_count_eq_min:
    "prefer_count p w n =
        Min {prefer_count p w y | y . y \<in> A - {w}}" and
    n_not_w: "n \<in> A - {w}"
    by metis
  hence n_in_A: "n \<in> A"
    using DiffE
    by metis
  have n_neq_w: "n \<noteq> w"
    using n_not_w
    by simp
  have w_in_A: "w \<in> A"
    using winner
    by simp
  have pref_count_n_w_ineq: "prefer_count p w n > prefer_count p n w"
    using n_not_w winner
    by simp
  have pref_count_l_w_n_ineq: "prefer_count p l w \<ge> prefer_count p w n"
    using pref_count_gte_min min_count_ineq pref_count_eq_min
    by linarith
  hence "prefer_count p n w \<ge> prefer_count p w l"
    using n_in_A w_in_A l_in_A n_neq_w l_neq_w pref_count_sym condorcet_winner.simps winner
    by metis
  hence "prefer_count p l w > prefer_count p w l"
    using n_in_A w_in_A l_in_A n_neq_w l_neq_w pref_count_sym condorcet_winner.simps winner
    using pref_count_n_w_ineq pref_count_l_w_n_ineq
    by linarith
  hence "wins l p w"
    by simp
  thus False
    using l_in_A_without_w wins_antisym winner
    unfolding condorcet_winner.simps
    by metis
qed

theorem minimax_is_dcc: "defer_condorcet_consistency minimax"
proof (unfold defer_condorcet_consistency_def electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    finA: "finite A" and
    profA: "profile A p"
  have "well_formed A (max_eliminator minimax_score A p)"
    using finA max_elim_sound par_comp_result_sound profA
    by metis
  thus "well_formed A (minimax A p)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    cwin_w: "condorcet_winner A p w" and
    fin_A: "finite A"
  have max_mmaxscore_dcc:
    "defer_condorcet_consistency (max_eliminator minimax_score)"
    using cr_eval_imp_dcc_max_elim
    by (simp add: minimax_score_cond_rating)
  hence
    "max_eliminator minimax_score A p =
      ({},
       A - defer (max_eliminator minimax_score) A p,
       {a \<in> A. condorcet_winner A p a})"
    using cwin_w fin_A
    unfolding defer_condorcet_consistency_def
    by (metis (no_types))
  thus
    "minimax A p =
      ({},
       A - defer minimax A p,
       {d \<in> A. condorcet_winner A p d})"
    by simp
qed

end

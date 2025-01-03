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

fun minimax_score :: "('a, 'v) Evaluation_Function" where
  "minimax_score V x A p =
    Min {prefer_count V p x y | y . y \<in> A - {x}}"

fun minimax :: "('a, 'v, 'a Result) Electoral_Module" where
  "minimax A p = max_eliminator minimax_score A p"

subsection \<open>Soundness\<close>

theorem minimax_sound: "\<S>\<C>\<F>_result.electoral_module minimax"
  unfolding minimax.simps
  using max_elim_sound
  by metis

subsection \<open>Lemma\<close>

lemma non_cond_winner_minimax_score:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w l :: "'a"
  assumes
    prof: "profile V A p" and
    winner: "condorcet_winner V A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  shows "minimax_score V l A p \<le> prefer_count V p l w"
proof (unfold minimax_score.simps, intro Min_le)
  have "finite V"
    using winner
    by simp
  moreover have "\<forall> E n. infinite E \<longrightarrow> (\<exists> e. \<not> e \<le> enat n \<and> e \<in> E)"
    using finite_enat_bounded
    by blast
  ultimately show "finite {prefer_count V p l y | y. y \<in> A - {l}}"
    using pref_count_voter_set_card
    by fastforce
next
  have "w \<in> A"
    using winner
    by simp
  thus "prefer_count V p l w \<in> {prefer_count V p l y | y. y \<in> A - {l}}"
    using l_neq_w
    by blast
qed

subsection \<open>Property\<close>

theorem minimax_score_cond_rating: "condorcet_rating minimax_score"
proof (unfold condorcet_rating_def minimax_score.simps prefer_count.simps,
       safe, rule ccontr)
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile" and
    w l :: "'b"
  assume
    winner: "condorcet_winner V A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w:"l \<noteq> w" and
    min_leq:
      "\<not> Min {if finite V
            then enat (card {v \<in> V. let r = p v in y \<preceq>\<^sub>r l})
            else \<infinity> | y. y \<in> A - {l}}
       < Min {if finite V
            then enat (card {v \<in> V. let r = p v in y \<preceq>\<^sub>r w})
            else \<infinity> | y. y \<in> A - {w}}"
  hence min_count_ineq:
    "Min {prefer_count V p l y | y. y \<in> A - {l}} \<ge>
        Min {prefer_count V p w y | y. y \<in> A - {w}}"
    by simp
  have pref_count_gte_min:
    "prefer_count V p l w  \<ge> Min {prefer_count V p l y | y . y \<in> A - {l}}"
    using l_in_A l_neq_w condorcet_winner.simps winner non_cond_winner_minimax_score
          minimax_score.simps
    by metis
  have l_in_A_without_w: "l \<in> A - {w}"
    using l_in_A l_neq_w
    by simp
  hence pref_counts_non_empty: "{prefer_count V p w y | y . y \<in> A - {w}} \<noteq> {}"
    by blast
  have "finite (A - {w})"
    using condorcet_winner.simps winner finite_Diff
    by metis
  hence "finite {prefer_count V p w y | y . y \<in> A - {w}}"
    by simp
  hence "\<exists> n \<in> A - {w} . prefer_count V p w n =
            Min {prefer_count V p w y | y . y \<in> A - {w}}"
    using pref_counts_non_empty Min_in
    by fastforce
  then obtain n :: "'b" where
    pref_count_eq_min:
    "prefer_count V p w n =
        Min {prefer_count V p w y | y . y \<in> A - {w}}" and
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
  have pref_count_n_w_ineq: "prefer_count V p w n > prefer_count V p n w"
    using n_not_w winner
    by auto
  have pref_count_l_w_n_ineq: "prefer_count V p l w \<ge> prefer_count V p w n"
    using pref_count_gte_min min_count_ineq pref_count_eq_min
    by auto
  hence "prefer_count V p n w \<ge> prefer_count V p w l"
    using n_in_A w_in_A l_in_A n_neq_w l_neq_w pref_count_sym winner
    unfolding condorcet_winner.simps
    by metis
  hence "prefer_count V p l w > prefer_count V p w l"
    using n_in_A w_in_A l_in_A n_neq_w l_neq_w pref_count_sym winner
          pref_count_n_w_ineq pref_count_l_w_n_ineq
    unfolding condorcet_winner.simps
    by auto
  hence "wins V l p w"
    by simp
  thus False
    using l_in_A_without_w wins_antisym winner
    unfolding condorcet_winner.simps
    by metis
qed

theorem minimax_is_dcc: "defer_condorcet_consistency minimax"
proof (unfold defer_condorcet_consistency_def \<S>\<C>\<F>_result.electoral_module.simps,
        safe)
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile"
  assume "profile V A p"
  hence "well_formed_\<S>\<C>\<F> A (max_eliminator minimax_score V A p)"
    using max_elim_sound par_comp_result_sound
    by metis
  thus "well_formed_\<S>\<C>\<F> A (minimax V A p)"
    by simp
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile" and
    w :: "'b"
  assume cwin_w: "condorcet_winner V A p w"
  have max_mmaxscore_dcc:
    "defer_condorcet_consistency ((max_eliminator minimax_score)
                                    :: ('b, 'a, 'b Result) Electoral_Module)"
    using cr_eval_imp_dcc_max_elim minimax_score_cond_rating
    by metis
  hence
    "max_eliminator minimax_score V A p =
      ({},
       A - defer (max_eliminator minimax_score) V A p,
       {a \<in> A. condorcet_winner V A p a})"
    using cwin_w
    unfolding defer_condorcet_consistency_def
    by blast
  thus
    "minimax V A p =
      ({},
       A - defer minimax V A p,
       {d \<in> A. condorcet_winner V A p d})"
    by simp
qed

end
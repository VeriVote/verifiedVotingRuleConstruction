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

theorem minimax_sound: "social_choice_result.electoral_module minimax"
  unfolding minimax.simps
  using max_elim_sound
  by metis

subsection \<open>Lemma\<close>

lemma non_cond_winner_minimax_score:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'a" and
    l :: "'a"
  assumes
    prof: "profile V A p" and
    winner: "condorcet_winner V A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  shows "minimax_score V l A p \<le> prefer_count V p l w"
proof (simp, clarify)
  assume "finite V"
  have "w \<in> A" 
    using winner 
    by simp
  hence el: "card {v \<in> V. (w, l) \<in> p v} \<in> {(card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l}"
    using l_neq_w
    by auto
  moreover have fin: "finite {(card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l}"
  proof -
    have "\<forall> y \<in> A. card {v \<in> V. (y, l) \<in> p v} \<le> card V"
      by (simp add: \<open>finite V\<close> card_mono)
    hence "\<forall> y \<in> A. card {v \<in> V. (y, l) \<in> p v} \<in> {..card V}"
      by (simp add: less_Suc_eq_le)
    hence "{(card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l} \<subseteq> {0..card V}"
      by auto
    thus ?thesis
      by (simp add: finite_subset)
  qed
  ultimately have "Min {(card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l}
          \<le> card {v \<in> V. (w, l) \<in> p v}"
    using Min_le 
    by blast
  hence enat_leq: "enat (Min {(card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l})
                    \<le> enat (card {v \<in> V. (w, l) \<in> p v})"
    using enat_ord_simps
    by simp
  have "\<forall> S::(nat set). finite S \<longrightarrow> (\<forall>m. (\<forall>x \<in> S. m \<le> x) \<longrightarrow> (\<forall> x \<in> S. enat m \<le> enat x))"
    using enat_ord_simps 
    by simp
  hence "\<forall> S::(nat set). finite S \<and> S \<noteq> {} \<longrightarrow> (\<forall> x. x \<in> S \<longrightarrow> enat (Min S) \<le> enat x)"
    by simp
  hence "\<forall> S::(nat set). finite S \<and> S \<noteq> {} \<longrightarrow> 
          (\<forall> x. x \<in> {enat x | x. x \<in> S} \<longrightarrow> enat (Min S) \<le> x)"
    by auto
  moreover have "\<forall> S::(nat set). finite S \<and> S \<noteq> {} \<longrightarrow> enat (Min S) \<in> {enat x | x. x \<in> S}"
    by simp
  moreover have "\<forall> S::(nat set). finite S \<and> S \<noteq> {} \<longrightarrow> finite {enat x | x. x \<in> S} 
                                                        \<and> {enat x | x. x \<in> S} \<noteq> {}"
    by simp
  ultimately have "\<forall> S::(nat set). finite S \<and> S \<noteq> {} \<longrightarrow> 
                    enat (Min S) = Min {enat x | x. x \<in> S}"
    using Min_eqI
    by (metis (no_types, lifting))
  moreover have "{(card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l} \<noteq> {}"
    using el
    by auto
  moreover have "{enat x | x. x \<in> {(card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l}}
                    = {enat (card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l}"
    by auto
  ultimately have "enat (Min {(card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l}) =
                    Min {enat (card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l}"
    using fin
    by presburger
  thus "Min {enat (card {v \<in> V. (y, l) \<in> p v}) | y. y \<in> A \<and> y \<noteq> l}
          \<le> enat (card {v \<in> V. (w, l) \<in> p v})"
    using enat_leq
    by simp
qed

subsection \<open>Property\<close>

theorem minimax_score_cond_rating: "condorcet_rating minimax_score"
proof (unfold condorcet_rating_def minimax_score.simps prefer_count.simps,
       safe, rule ccontr)
  fix
    A :: "'b set" and 
    V :: "'a set" and 
    p :: "('b, 'a) Profile" and 
    w :: 'b and
    l :: 'b
  assume
    winner: "condorcet_winner V A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w:"l \<noteq> w" and
    min_leq:
      "\<not> Min {if finite V then enat (card {v \<in> V. let r = p v in y \<preceq>\<^sub>r l}) else \<infinity> |y. y \<in> A - {l}}
       < Min {if finite V then enat (card {v \<in> V. let r = p v in y \<preceq>\<^sub>r w}) else \<infinity> |y. y \<in> A - {w}}"
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
    using l_in_A
    by (simp add: l_neq_w)
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
  then obtain n where pref_count_eq_min:
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
proof (unfold defer_condorcet_consistency_def social_choice_result.electoral_module_def, safe)
  fix
    A :: "'b set" and 
    V :: "'a set" and 
    p :: "('b, 'a) Profile"
  assume
    finA: "finite A" and
    finV: "finite A" and
    profA: "profile V A p"
  have "well_formed_soc_choice A (
          ((max_eliminator minimax_score)::('b, 'a, 'b Result) Electoral_Module) V A p)"
    using finA finV max_elim_sound par_comp_result_sound profA
    by auto
  thus "well_formed_soc_choice A (minimax V A p)"
    by simp
next
  fix
    A :: "'b set" and 
    V :: "'a set" and 
    p :: "('b, 'a) Profile" and 
    w :: 'b
  assume
    cwin_w: "condorcet_winner V A p w" and
    fin_A: "finite A" and
    fin_V: "finite V"
  have max_mmaxscore_dcc:
    "defer_condorcet_consistency ((max_eliminator minimax_score)
                                    ::('b, 'a, 'b Result) Electoral_Module)"
    using cr_eval_imp_dcc_max_elim
    by (simp add: minimax_score_cond_rating)
  hence
    "max_eliminator minimax_score V A p =
      ({},
       A - defer V (max_eliminator minimax_score) A p,
       {a \<in> A. condorcet_winner V A p a})"
    using cwin_w fin_A fin_V
    unfolding defer_condorcet_consistency_def
    by blast
  thus
    "minimax V A p =
      ({},
       A - defer V minimax A p,
       {d \<in> A. condorcet_winner V A p d})"
    by simp
qed

end

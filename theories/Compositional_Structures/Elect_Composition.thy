(*  File:       Elect_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elect Composition\<close>

theory Elect_Composition
  imports "Basic_Modules/Elect_Module"
          Sequential_Composition
begin

text \<open>
  The elect composition sequences an electoral module and the elect
  module. It finalizes the module's decision as it simply elects all their
  non-rejected alternatives. Thereby, any such elect-composed module induces
  a proper voting rule in the social choice sense, as all alternatives are
  either rejected or elected.
\<close>

subsection \<open>Definition\<close>

fun elector :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "elector m = (m \<triangleright> elect_module)"

subsection \<open>Auxiliary Lemmas\<close>

lemma elector_seqcomp_assoc:
  fixes
    a :: "'a Electoral_Module" and
    b :: "'a Electoral_Module"
  shows "(a \<triangleright> (elector b)) = (elector (a \<triangleright> b))"
  unfolding elector.simps elect_module.simps sequential_composition.simps
  using boolean_algebra_cancel.sup2 fst_eqD snd_eqD sup_commute
  by (metis (no_types, opaque_lifting))

subsection \<open>Soundness\<close>

theorem elector_sound[simp]:
  fixes m :: "'a Electoral_Module"
  assumes "electoral_module m"
  shows "electoral_module (elector m)"
  using assms
  by simp

subsection \<open>Electing\<close>

theorem elector_electing[simp]:
  fixes m :: "'a Electoral_Module"
  assumes
    module_m: "electoral_module m" and
    non_block_m: "non_blocking m"
  shows "electing (elector m)"
proof -
  obtain
    A :: "'a Electoral_Module \<Rightarrow> 'a set" and
    p :: "'a Electoral_Module \<Rightarrow> 'a Profile" where
    "\<forall> m'.
      (\<not> electing m' \<and> electoral_module m' \<longrightarrow> elect m' (A m') (p m') = {})
      \<and> (electing m' \<longrightarrow> (\<forall> A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow> elect m' A p \<noteq> {}))"
    using electing_def
    by metis
  moreover have "electoral_module (elector m)"
    by (simp add: module_m)
  moreover from this have
    "\<not> electing (elector m) \<longrightarrow> elect (elector m) (A (elector m)) (p (elector m)) \<noteq> {}"
    using Un_empty_left boolean_algebra.disj_zero_right fst_conv non_block_m
          result_presv_alts seq_comp_def_then_elect_elec_set sup_bot.eq_neutr_iff
    unfolding elect_module.simps elector.simps electing_def non_blocking_def
    by (metis (no_types, lifting))
  ultimately show ?thesis
    using non_block_m
    unfolding elector.simps
    by metis
qed

subsection \<open>Composition Rule\<close>

text \<open>
  If m is defer-Condorcet-consistent, then elector(m) is Condorcet consistent.
\<close>

lemma dcc_imp_cc_elector:
  fixes m :: "'a Electoral_Module"
  assumes "defer_condorcet_consistency m"
  shows "condorcet_consistency (elector m)"
proof (unfold defer_condorcet_consistency_def condorcet_consistency_def, safe)
  show "electoral_module (elector m)"
    using assms elector_sound
    unfolding defer_condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume c_win: "condorcet_winner A p w"
  have fin_A: "finite A"
    using condorcet_winner.simps c_win
    by metis
  have prof_A: "profile A p"
    using c_win
    by simp
  have max_card_w: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
    using c_win
    by simp
  have rej_is_complement: "reject m A p = A - (elect m A p \<union> defer m A p)"
    using double_diff sup_bot.left_neutral Un_upper2 assms fin_A prof_A
          defer_condorcet_consistency_def elec_and_def_not_rej reject_in_alts
    by (metis (no_types, opaque_lifting))
  have subset_in_win_set: "elect m A p \<union> defer m A p \<subseteq>
      {e \<in> A. e \<in> A \<and> (\<forall> x \<in> A - {e}.
        card {i. i < length p \<and> (e, x) \<in> p!i} < card {i. i < length p \<and> (x, e) \<in> p!i})}"
  proof (safe_step)
    fix x :: "'a"
    assume x_in_elect_or_defer: "x \<in> elect m A p \<union> defer m A p"
    hence x_eq_w: "x = w"
      using Diff_empty Diff_iff assms cond_winner_unique c_win fin_A insert_iff
            prod.sel sup_bot.left_neutral
      unfolding defer_condorcet_consistency_def
      by (metis (mono_tags, lifting))
    have "\<forall> x. x \<in> elect m A p \<longrightarrow> x \<in> A"
      using fin_A prof_A assms elect_in_alts in_mono
      unfolding defer_condorcet_consistency_def
      by metis
    moreover have "\<forall> x. x \<in> defer m A p \<longrightarrow> x \<in> A"
      using fin_A prof_A assms defer_in_alts in_mono
      unfolding defer_condorcet_consistency_def
      by metis
    ultimately have "x \<in> A"
      using x_in_elect_or_defer
      by auto
    thus "x \<in> {e \<in> A. e \<in> A \<and>
            (\<forall> x \<in> A - {e}.
              card {i. i < length p \<and> (e, x) \<in> p!i} <
                card {i. i < length p \<and> (x, e) \<in> p!i})}"
      using x_eq_w max_card_w
      by auto
  qed
  moreover have
    "{e \<in> A. e \<in> A \<and>
        (\<forall> x \<in> A - {e}.
            card {i. i < length p \<and> (e, x) \<in> p!i} <
              card {i. i < length p \<and> (x, e) \<in> p!i})}
          \<subseteq> elect m A p \<union> defer m A p"
  proof (safe)
    fix x :: "'a"
    assume
      x_not_in_defer: "x \<notin> defer m A p" and
      "x \<in> A" and
      "\<forall> x' \<in> A - {x}.
        card {i. i < length p \<and> (x, x') \<in> p!i} <
          card {i. i < length p \<and> (x', x) \<in> p!i}"
    hence c_win_x: "condorcet_winner A p x"
      using fin_A prof_A
      by simp
    have "(electoral_module m \<and> \<not> defer_condorcet_consistency m \<longrightarrow>
          (\<exists> A rs a. condorcet_winner A rs a \<and>
            m A rs \<noteq> ({}, A - defer m A rs, {a \<in> A. condorcet_winner A rs a}))) \<and>
        (defer_condorcet_consistency m \<longrightarrow>
          (\<forall> A rs a. finite A \<longrightarrow> condorcet_winner A rs a \<longrightarrow>
            m A rs = ({}, A - defer m A rs, {a \<in> A. condorcet_winner A rs a})))"
      unfolding defer_condorcet_consistency_def
      by blast
    hence "m A p = ({}, A - defer m A p, {a \<in> A. condorcet_winner A p a})"
      using c_win_x assms fin_A
      by blast
    thus "x \<in> elect m A p"
      using assms x_not_in_defer fin_A cond_winner_unique defer_condorcet_consistency_def
            insertCI snd_conv c_win_x
      by (metis (no_types, lifting))
  qed
  ultimately have
    "elect m A p \<union> defer m A p =
      {e \<in> A. e \<in> A \<and>
        (\<forall> x \<in> A - {e}.
          card {i. i < length p \<and> (e, x) \<in> p!i} <
            card {i. i < length p \<and> (x, e) \<in> p!i})}"
    by blast
  thus "elector m A p =
          ({e \<in> A. condorcet_winner A p e}, A - elect (elector m) A p, {})"
    using fin_A prof_A rej_is_complement
    by simp
qed

end

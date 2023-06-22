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
  have non_block:
    "non_blocking
      (elect_module::'a set \<Rightarrow> _ Profile \<Rightarrow> _ Result)"
    by (simp add: electing_imp_non_blocking)
  obtain
    alts :: "'a Electoral_Module \<Rightarrow> 'a set" and
    prof :: "'a Electoral_Module \<Rightarrow> 'a Profile" where
    electing_func:
    "\<forall> f.
      (\<not> electing f \<and> electoral_module f \<longrightarrow>
        profile (alts f) (prof f) \<and> finite (alts f) \<and>
          {} = elect f (alts f) (prof f)  \<and> {} \<noteq> alts f) \<and>
      (electing f \<and> electoral_module f \<longrightarrow>
        (\<forall> A p. (A \<noteq> {} \<and> profile A p \<and> finite A) \<longrightarrow> elect f A p \<noteq> {}))"
    using electing_def
    by metis
  obtain
    ele :: "'a Result \<Rightarrow> 'a set" and
    rej :: "'a Result \<Rightarrow> 'a set" and
    def :: "'a Result \<Rightarrow> 'a set" where
    result: "\<forall> r. (ele r, rej r, def r) = r"
    using disjoint3.cases
    by (metis (no_types))
  hence r_func:
    "\<forall> r. (elect_r r, rej r, def r) = r"
    by simp
  hence def_empty:
    "profile (alts (elector m)) (prof (elector m)) \<and> finite (alts (elector m)) \<longrightarrow>
      def (elector m (alts (elector m)) (prof (elector m))) = {}"
    by simp
  have elec_mod:
    "electoral_module (elector m)"
    using elector_sound module_m
    by simp
  have
    "finite (alts (elector m)) \<and>
      profile (alts (elector m)) (prof (elector m)) \<and>
      elect (elector m) (alts (elector m)) (prof (elector m)) = {} \<and>
      def (elector m (alts (elector m)) (prof (elector m))) = {} \<and>
      reject (elector m) (alts (elector m)) (prof (elector m)) =
        rej (elector m (alts (elector m)) (prof (elector m))) \<longrightarrow>
            electing (elector m)"
    using result electing_func Diff_empty elector.simps non_block_m snd_conv
          non_blocking_def reject_not_elec_or_def non_block
          seq_comp_presv_non_blocking
    by metis
  thus ?thesis
    using r_func def_empty elec_mod electing_func fst_conv snd_conv
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
  have mod_m: "electoral_module m"
    using assms defer_condorcet_consistency_def
    by metis
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
  have subset_1: "elect m A p \<union> defer m A p \<subseteq>
      {e \<in> A. e \<in> A \<and> (\<forall> x \<in> A - {e}.
        card {i. i < length p \<and> (e, x) \<in> p!i} < card {i. i < length p \<and> (x, e) \<in> p!i})}"
  proof (safe_step)
    fix x :: "'a"
    assume x_in_elect_or_defer: "x \<in> elect m A p \<union> defer m A p"
    hence x_eq_w: "x = w"
      using Diff_empty Diff_iff assms cond_winner_unique_3 c_win defer_condorcet_consistency_def
            fin_A insert_iff snd_conv prod.sel(1) sup_bot.left_neutral
      by (metis (mono_tags, lifting))
    have elect_then_in_A: "\<And> x. x \<in> elect m A p \<Longrightarrow> x \<in> A"
      using fin_A prof_A assms defer_condorcet_consistency_def elect_in_alts in_mono
      by metis
    have defer_then_in_A: "\<And> x. x \<in> defer m A p \<Longrightarrow> x \<in> A"
      using fin_A prof_A assms defer_condorcet_consistency_def defer_in_alts in_mono
      by metis
    have "x \<in> A"
      using x_in_elect_or_defer defer_then_in_A elect_then_in_A
      by auto
    thus "x \<in> {e \<in> A. e \<in> A \<and>
            (\<forall> x \<in> A - {e}.
              card {i. i < length p \<and> (e, x) \<in> p!i} < card {i. i < length p \<and> (x, e) \<in> p!i})}"
      using x_eq_w max_card_w
      by auto
  qed
  have subset_2: "{e \<in> A. e \<in> A \<and>
          (\<forall> x \<in> A - {e}.
            card {i. i < length p \<and> (e, x) \<in> p!i} < card {i. i < length p \<and> (x, e) \<in> p!i})}
          \<subseteq> elect m A p \<union> defer m A p"
  proof (safe)
    fix x :: "'a"
    assume
      x_not_in_defer: "x \<notin> defer m A p" and
      "x \<in> A" and
      "\<forall> x' \<in> A - {x}.
        card {i. i < length p \<and> (x, x') \<in> p!i} < card {i. i < length p \<and> (x', x) \<in> p!i}"
    hence "condorcet_winner A p x"
      using fin_A prof_A
      by simp
    thus "x \<in> elect m A p"
      using assms x_not_in_defer fin_A cond_winner_unique_3 defer_condorcet_consistency_def
            insertCI prod.sel(2)
      by (metis (mono_tags, lifting))
  qed
  have
    "elect m A p \<union> defer m A p =
      {e \<in> A. e \<in> A \<and>
        (\<forall> x \<in> A - {e}.
          card {i. i < length p \<and> (e, x) \<in> p!i} < card {i. i < length p \<and> (x, e) \<in> p!i})}"
    using subset_1 subset_2
    by blast
  thus "elector m A p = ({e \<in> A. condorcet_winner A p e}, A - elect (elector m) A p, {})"
    using fin_A prof_A rej_is_complement
    by simp
qed

end

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
  assumes "electoral_module m"
  shows "electoral_module (elector m)"
  using assms
  by simp

subsection \<open>Electing\<close>

theorem elector_electing[simp]:
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
  assumes "defer_condorcet_consistency m"
  shows "condorcet_consistency (elector m)"
proof (unfold defer_condorcet_consistency_def
              condorcet_consistency_def, auto)
  show "electoral_module (m \<triangleright> elect_module)"
    using assms elect_mod_sound seq_comp_sound
    unfolding defer_condorcet_consistency_def
    by metis
next
  show
    "\<And> A p w x.
       finite A \<Longrightarrow> profile A p \<Longrightarrow> w \<in> A \<Longrightarrow>
         \<forall> x \<in> A - {w}. card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)} \<Longrightarrow>
        x \<in> elect m A p \<Longrightarrow> x \<in> A"
  proof -
    fix
      A :: "'a set" and
      p :: "'a Profile" and
      w :: "'a" and
      x :: "'a"
    assume
      finite: "finite A" and
      prof_A: "profile A p"
    show
      "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)} \<Longrightarrow>
             x \<in> elect m A p \<Longrightarrow> x \<in> A"
      using assms elect_in_alts subset_eq finite prof_A
      unfolding defer_condorcet_consistency_def
      by metis
  qed
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a" and
    xa :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    1: "x \<in> elect m A p" and
    2: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A 2
    by simp
  thus "xa = x"
    using condorcet_winner.simps assms fst_conv insert_Diff 1 insert_not_empty
    unfolding defer_condorcet_consistency_def
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    0: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    1: "x \<in> defer m A p"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A 0
    by simp
  thus "x \<in> A"
    using 0 1 condorcet_winner.simps assms defer_in_alts
          order_trans subset_Compl_singleton
    unfolding defer_condorcet_consistency_def
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a" and
    xa :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    1: "x \<in> defer m A p" and
    xa_in_A: "xa \<in> A" and
    2: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    3: "\<not> card {i. i < length p \<and> (x, xa) \<in> (p!i)} <
            card {i. i < length p \<and> (xa, x) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "xa = x"
    using 1 2 condorcet_winner.simps assms empty_iff xa_in_A
          defer_condorcet_consistency_def 3 DiffI
          cond_winner_unique3 insert_iff prod.sel(2)
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    x_in_A: "x \<in> A" and
    1: "x \<notin> defer m A p" and
    2: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    3: "\<forall> y \<in> A - {x}.
          card {i. i < length p \<and> (x, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, x) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  also have "condorcet_winner A p x"
    using finite prof_A x_in_A "3"
    by simp
  ultimately show "x \<in> elect m A p"
    using 1 condorcet_winner.simps assms
          defer_condorcet_consistency_def
          cond_winner_unique3 insert_iff eq_snd_iff
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    1: "x \<in> reject m A p" and
    2: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "x \<in> A"
    using 1 assms finite prof_A reject_in_alts subsetD
    unfolding defer_condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    0: "x \<in> reject m A p" and
    1: "x \<in> elect m A p" and
    2: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus False
    using 0 1 assms IntI empty_iff result_disj
    unfolding condorcet_winner.simps defer_condorcet_consistency_def
    by (metis (no_types, opaque_lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    0: "x \<in> reject m A p" and
    1: "x \<in> defer m A p" and
    2: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus False
    using 0 1 assms IntI Diff_empty Diff_iff finite prof_A result_disj
    unfolding defer_condorcet_consistency_def
    by (metis (no_types, opaque_lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    x_in_A: "x \<in> A" and
    0: "x \<notin> reject m A p" and
    1: "x \<notin> defer m A p" and
    2: "\<forall> y \<in> A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A 2
    by simp
  thus "x \<in> elect m A p"
    using 0 1 assms x_in_A electoral_mod_defer_elem
    unfolding condorcet_winner.simps defer_condorcet_consistency_def
    by (metis (no_types, lifting))
qed

end

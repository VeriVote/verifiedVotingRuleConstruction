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

text
\<open>The elect composition sequences an electoral module and the elect
module. It finalizes the module's decision as it simply elects all their
non-rejected alternatives. Thereby, any such elect-composed module induces
a proper voting rule in the social choice sense, as all alternatives are either
rejected or elected.\<close>

subsection \<open>Definition\<close>

fun elector :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "elector m = (m \<triangleright> elect_module)"

subsection \<open>Soundness\<close>

theorem elector_sound[simp]:
  assumes module_m: "electoral_module m"
  shows "electoral_module (elector m)"
  by (simp add: module_m)

subsection \<open>Electing\<close>

theorem elector_electing[simp]:
  assumes
    module_m: "electoral_module m" and
    non_block_m: "non_blocking m"
  shows "electing (elector m)"
proof -
  obtain
    AA :: "'a Electoral_Module \<Rightarrow> 'a set" and
    rrs :: "'a Electoral_Module \<Rightarrow> 'a Profile" where
    f1:
    "\<forall>f.
      (electing f \<or>
        {} = elect f (AA f) (rrs f) \<and> profile (AA f) (rrs f) \<and>
            finite (AA f) \<and> {} \<noteq> AA f \<or>
        \<not> electoral_module f) \<and>
            ((\<forall>A rs. {} \<noteq> elect f A rs \<or> \<not> profile A rs \<or>
                infinite A \<or> {} = A) \<and>
            electoral_module f \<or>
        \<not> electing f)"
    using electing_def
    by metis
  have non_block:
    "non_blocking
      (elect_module::'a set \<Rightarrow> _ Profile \<Rightarrow> _ Result)"
    by (simp add: electing_imp_non_blocking)
  thus ?thesis
    (* using f1 Diff_empty elect_module.elims elector.simps non_block_m
          non_blocking_def reject_not_elec_or_def seq_comp_defers_def_set
          seq_comp_presv_non_blocking snd_conv elect_mod_sound fst_conv
          elect_module.simps elector_sound module_m disjoint3.cases
          empty_iff ex_in_conv seq_comp_def_set_trans *)
  proof -
    obtain
      AAa :: "'a Electoral_Module \<Rightarrow> 'a set" and
      rrsa :: "'a Electoral_Module \<Rightarrow> 'a Profile" where
      f1:
      "\<forall>f.
        (electing f \<or>
          {} = elect f (AAa f) (rrsa f) \<and> profile (AAa f) (rrsa f) \<and>
              finite (AAa f) \<and> {} \<noteq> AAa f \<or>
        \<not> electoral_module f) \<and> ((\<forall>A rs. {} \<noteq> elect f A rs \<or>
        \<not> profile A rs \<or> infinite A \<or> {} = A) \<and> electoral_module f \<or>
        \<not> electing f)"
      using electing_def
      by metis
    obtain
      AAb :: "'a Result \<Rightarrow> 'a set" and
      AAc :: "'a Result \<Rightarrow> 'a set" and
      AAd :: "'a Result \<Rightarrow> 'a set" where
      f2:
      "\<forall>p. (AAb p, AAc p, AAd p) = p"
      using disjoint3.cases
      by (metis (no_types))
    have f3:
      "electoral_module (elector m)"
      using elector_sound module_m
      by simp
    have f4:
      "\<forall>p. (elect_r p, AAc p, AAd p) = p"
      using f2
      by simp
    have
      "finite (AAa (elector m)) \<and>
        profile (AAa (elector m)) (rrsa (elector m)) \<and>
        {} = elect (elector m) (AAa (elector m)) (rrsa (elector m)) \<and>
        {} = AAd (elector m (AAa (elector m)) (rrsa (elector m))) \<and>
        reject (elector m) (AAa (elector m)) (rrsa (elector m)) =
          AAc (elector m (AAa (elector m)) (rrsa (elector m))) \<longrightarrow>
              electing (elector m)"
      using f2 f1 Diff_empty elector.simps non_block_m snd_conv
            non_blocking_def reject_not_elec_or_def non_block
            seq_comp_presv_non_blocking
      by metis
    moreover
    {
      assume
        "{} \<noteq> AAd (elector m (AAa (elector m)) (rrsa (elector m)))"
      hence
        "\<not> profile (AAa (elector m)) (rrsa (elector m)) \<or>
          infinite (AAa (elector m))"
        using f4
        by simp
    }
    ultimately show ?thesis
      using f4 f3 f1 fst_conv snd_conv
      by metis
  qed
qed

subsection \<open>Composition Rule\<close>

(*If m is defer-Condorcet-consistent, then elector(m) is Condorcet consistent.*)
lemma dcc_imp_cc_elector:
  assumes dcc: "defer_condorcet_consistency m"
  shows "condorcet_consistency (elector m)"
proof (unfold defer_condorcet_consistency_def
              condorcet_consistency_def, auto)
  show "electoral_module (m \<triangleright> elect_module)"
    using dcc defer_condorcet_consistency_def
          elect_mod_sound seq_comp_sound
    by metis
next
  show
    "\<And>A p w x.
       finite A \<Longrightarrow> profile A p \<Longrightarrow> w \<in> A \<Longrightarrow>
         \<forall>x\<in>A - {w}. card {i. i < length p \<and> (w, x) \<in> (p!i)} <
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
      "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)} \<Longrightarrow>
             x \<in> elect m A p \<Longrightarrow> x \<in> A"
      using dcc defer_condorcet_consistency_def
            elect_in_alts subset_eq finite prof_A
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
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "xa = x"
    using condorcet_winner.simps dcc fst_conv insert_Diff "1"
          defer_condorcet_consistency_def insert_not_empty
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
    0: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    1: "x \<in> defer m A p"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "0"
    by simp
  thus "x \<in> A"
    using "0" "1" condorcet_winner.simps dcc defer_in_alts
          defer_condorcet_consistency_def order_trans
          subset_Compl_singleton
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
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    3: "\<not> card {i. i < length p \<and> (x, xa) \<in> (p!i)} <
            card {i. i < length p \<and> (xa, x) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "xa = x"
    using "1" "2" condorcet_winner.simps dcc empty_iff xa_in_A
          defer_condorcet_consistency_def "3" DiffI
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
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    3: "\<forall>y\<in>A - {x}.
          card {i. i < length p \<and> (x, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, x) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  also have "condorcet_winner A p x"
    using finite prof_A x_in_A "3"
    by simp
  ultimately show "x \<in> elect m A p"
    using "1" condorcet_winner.simps dcc
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
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "x \<in> A"
    using "1" dcc defer_condorcet_consistency_def finite
          prof_A reject_in_alts subsetD
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
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "False"
    using "0" "1" condorcet_winner.simps dcc IntI empty_iff
          defer_condorcet_consistency_def result_disj
    by (metis (no_types, hide_lams))
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
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "False"
    using "0" "1" dcc defer_condorcet_consistency_def IntI
          Diff_empty Diff_iff finite prof_A result_disj
    by (metis (no_types, hide_lams))
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
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "x \<in> elect m A p"
    using "0" "1" condorcet_winner.simps dcc x_in_A
          defer_condorcet_consistency_def electoral_mod_defer_elem
    by (metis (no_types, lifting))
qed

end

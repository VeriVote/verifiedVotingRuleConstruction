(*  File:       Revision_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Revision Composition\<close>

theory Revision_Composition
  imports "Basic_Modules/Component_Types/Electoral_Module"
begin

text
\<open>A revised electoral module rejects all originally rejected or deferred
alternatives, and defers the originally elected alternatives.
It does not elect any alternatives.\<close>

subsection \<open>Definition\<close>

fun revision_composition :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "revision_composition m A p = ({}, A - elect m A p, elect m A p)"

abbreviation rev ::
"'a Electoral_Module \<Rightarrow> 'a Electoral_Module" ("_\<down>" 50) where
  "m\<down> == revision_composition m"

subsection \<open>Soundness\<close>

theorem rev_comp_sound[simp]:
  assumes module: "electoral_module m"
  shows "electoral_module (revision_composition m)"
proof -
  from module have "\<forall>A p. finite_profile A p \<longrightarrow> elect m A p \<subseteq> A"
    using elect_in_alts
    by auto
  hence "\<forall>A p. finite_profile A p \<longrightarrow> (A - elect m A p) \<union> elect m A p = A"
    by blast
  hence unity:
    "\<forall>A p. finite_profile A p \<longrightarrow>
      set_equals_partition A (revision_composition m A p)"
    by simp
  have "\<forall>A p. finite_profile A p \<longrightarrow> (A - elect m A p) \<inter> elect m A p = {}"
    by blast
  hence disjoint:
    "\<forall>A p. finite_profile A p \<longrightarrow> disjoint3 (revision_composition m A p)"
    by simp
  from unity disjoint show ?thesis
    by (simp add: electoral_modI)
qed

subsection \<open>Composition Rules\<close>

(*An electoral module received by revision is never electing.*)
theorem rev_comp_non_electing[simp]:
  assumes "electoral_module m"
  shows "non_electing (m\<down>)"
  by (simp add: assms non_electing_def)

(*
   Revising an electing electoral module results in a
   non-blocking electoral module.
*)
theorem rev_comp_non_blocking[simp]:
  assumes "electing m"
  shows "non_blocking (m\<down>)"
  unfolding non_blocking_def
proof (safe, simp_all)
  show "electoral_module (m\<down>)"
    using assms electing_def rev_comp_sound
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    no_elect: "A - elect m A p = A" and
    x_in_A: "x \<in> A"
  from no_elect have non_elect:
    "non_electing m"
    using assms prof_A x_in_A fin_A electing_def empty_iff
          Diff_disjoint Int_absorb2 elect_in_alts
    by (metis (no_types, lifting))
  show "False"
    using non_elect assms electing_def empty_iff fin_A
          non_electing_def prof_A x_in_A
    by (metis (no_types, lifting))
qed

(*
   Revising an invariant monotone electoral module results in a
   defer-invariant-monotone electoral module.
*)
theorem rev_comp_def_inv_mono[simp]:
  assumes "invariant_monotonicity m"
  shows "defer_invariant_monotonicity (m\<down>)"
proof -
  have "\<forall>A p q w. (w \<in> defer (m\<down>) A p \<and> lifted A p q w) \<longrightarrow>
                  (defer (m\<down>) A q = defer (m\<down>) A p \<or> defer (m\<down>) A q = {w})"
    using assms
    by (simp add: invariant_monotonicity_def)
  moreover have "electoral_module (m\<down>)"
    using assms rev_comp_sound invariant_monotonicity_def
    by auto
  moreover have "non_electing (m\<down>)"
    using assms rev_comp_non_electing invariant_monotonicity_def
    by auto
  ultimately have "electoral_module (m\<down>) \<and> non_electing (m\<down>) \<and>
      (\<forall>A p q w. (w \<in> defer (m\<down>) A p \<and> lifted A p q w) \<longrightarrow>
                 (defer (m\<down>) A q = defer (m\<down>) A p \<or> defer (m\<down>) A q = {w}))"
    by blast
  thus ?thesis
    using defer_invariant_monotonicity_def
    by (simp add: defer_invariant_monotonicity_def)
qed

end

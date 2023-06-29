(*  File:       Result.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Result\<close>

theory Result
  imports Main
begin

text \<open>
  An electoral result is the principal result type of the composable modules
  voting framework, as it is a generalization of the set of winning
  alternatives from social choice functions. Electoral results are selections
  of the received (possibly empty) set of alternatives into the three disjoint
  groups of elected, rejected and deferred alternatives.
  Any of those sets, e.g., the set of winning (elected) alternatives, may also
  be left empty, as long as they collectively still hold all the received
  alternatives.
\<close>

subsection \<open>Definition\<close>

text \<open>
  A result contains three sets of alternatives:
  elected, rejected, and deferred alternatives.
\<close>

type_synonym 'a Result = "'a set * 'a set * 'a set"

subsection \<open>Auxiliary Functions\<close>

text \<open>
  A partition of a set A are pairwise disjoint sets that "set equals
  partition" A. For this specific predicate, we have three disjoint sets
  in a three-tuple.
\<close>

fun disjoint3 :: "'a Result \<Rightarrow> bool" where
  "disjoint3 (e, r, d) =
    ((e \<inter> r = {}) \<and>
      (e \<inter> d = {}) \<and>
      (r \<inter> d = {}))"

fun set_equals_partition :: "'a set \<Rightarrow>'a Result \<Rightarrow> bool" where
  "set_equals_partition A (e, r, d) = (e \<union> r \<union> d = A)"

fun well_formed :: "'a set \<Rightarrow> 'a Result \<Rightarrow> bool" where
  "well_formed A result = (disjoint3 result \<and> set_equals_partition A result)"

text \<open>
  These three functions return the elect, reject, or defer set of a result.
\<close>

abbreviation elect_r :: "'a Result \<Rightarrow> 'a set" where
  "elect_r r \<equiv> fst r"

abbreviation reject_r :: "'a Result \<Rightarrow> 'a set" where
  "reject_r r \<equiv> fst (snd r)"

abbreviation defer_r :: "'a Result \<Rightarrow> 'a set" where
  "defer_r r \<equiv> snd (snd r)"

subsection \<open>Auxiliary Lemmas\<close>

lemma result_imp_rej:
  fixes
    A :: "'a set" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assumes "well_formed A (e, r, d)"
  shows "A - (e \<union> d) = r"
proof (safe)
  fix a :: "'a"
  assume
    "a \<in> A" and
    "a \<notin> r" and
    "a \<notin> d"
  moreover have "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    using assms
    by simp
  ultimately show "a \<in> e"
    by auto
next
  fix a :: "'a"
  assume "a \<in> r"
  moreover have "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    using assms
    by simp
  ultimately show "a \<in> A"
    by auto
next
  fix a :: "'a"
  assume
    "a \<in> r" and
    "a \<in> e"
  moreover have "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    using assms
    by simp
  ultimately show False
    by auto
next
  fix a :: "'a"
  assume
    "a \<in> r" and
    "a \<in> d"
  moreover have "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    using assms
    by simp
  ultimately show False
    by auto
qed

lemma result_count:
  fixes
    A :: "'a set" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assumes
    wf_result: "well_formed A (e, r, d)" and
    fin_A: "finite A"
  shows "card A = card e + card r + card d"
proof -
  have "e \<union> r \<union> d = A"
    using wf_result
    by simp
  moreover have "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {})"
    using wf_result
    by simp
  ultimately show ?thesis
    using fin_A Int_Un_distrib2 finite_Un card_Un_disjoint sup_bot.right_neutral
    by metis
qed

lemma defer_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed A r"
  shows "defer_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> defer_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have "\<forall> p. \<exists> E R D. set_equals_partition A p \<longrightarrow> (E, R, D) = p \<and> E \<union> R \<union> D = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI snd_conv
    by metis
qed

lemma elect_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed A r"
  shows "elect_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> elect_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have "\<forall> p. \<exists> E R D. set_equals_partition A p \<longrightarrow> (E, R, D) = p \<and> E \<union> R \<union> D = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI assms fst_conv
    by metis
qed

lemma reject_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed A r"
  shows "reject_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> reject_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have "\<forall> p. \<exists> E R D. set_equals_partition A p \<longrightarrow> (E, R, D) = p \<and> E \<union> R \<union> D = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI assms fst_conv snd_conv disjoint3.cases
    by metis
qed

end

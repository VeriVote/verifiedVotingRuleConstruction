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

subsection \<open>Auxiliary Lemmata\<close>

lemma result_imp_rej:
  assumes "well_formed A (e, r, d)"
  shows "A - (e \<union> d) = r"
proof (safe)
  fix x :: "'a"
  assume
    x_in_A: "x \<in> A" and
    x_not_rej: "x \<notin> r" and
    x_not_def: "x \<notin> d"
  from assms have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and>
    (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    by simp
  thus "x \<in> e"
    using x_in_A x_not_rej x_not_def
    by auto
next
  fix x :: "'a"
  assume x_rej: "x \<in> r"
  from assms have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and>
    (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    by simp
  thus "x \<in> A"
    using x_rej
    by auto
next
  fix x :: "'a"
  assume
    x_rej:  "x \<in> r" and
    x_elec: "x \<in> e"
  from assms have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and>
    (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    by simp
  thus False
    using x_rej x_elec
    by auto
next
  fix x :: "'a"
  assume
    x_rej: "x \<in> r" and
    x_def: "x \<in> d"
  from assms have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and>
    (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    by simp
  thus False
    using x_rej x_def
    by auto
qed

lemma result_count:
  assumes
    wf: "well_formed A (e, r, d)" and
    fin_A: "finite A"
  shows "card A = card e + card r + card d"
proof -
  from wf have disj:
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {})"
    by simp
  from wf have set_partit:
    "e \<union> r \<union> d = A"
    by simp
  show ?thesis
    using fin_A disj set_partit Int_Un_distrib2 finite_Un
          card_Un_disjoint sup_bot.right_neutral
    by metis
qed

lemma defer_subset:
  assumes "well_formed A result"
  shows "defer_r result \<subseteq> A"
proof (safe)
  fix x :: "'a"
  assume def_x: "x \<in> defer_r result"
  obtain
    alts :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    res :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    wf: "A = alts result A \<and> result = res result A \<and> disjoint3 (res result A) \<and>
            set_equals_partition (alts result A) (res result A)"
    using assms
    by simp
  hence
    "\<forall> p A. \<exists> elec rej def.
      set_equals_partition (A::'a set) p \<longrightarrow> (elec, rej, def) = p \<and> elec \<union> rej \<union> def = A"
    by simp
  thus "x \<in> A"
    using UnCI def_x wf snd_conv
    by metis
qed

lemma elect_subset:
  assumes "well_formed A result"
  shows "elect_r result \<subseteq> A"
proof (safe)
  fix x :: "'a"
  assume elec_res: "x \<in> elect_r result"
  obtain
    alts :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    res :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    wf: "A = alts result A \<and> result = res result A \<and> disjoint3 (res result A) \<and>
            set_equals_partition (alts result A) (res result A)"
    using assms
    by simp
  hence
    "\<forall> p A. \<exists> elec rej def.
      set_equals_partition (A::'a set) p \<longrightarrow> (elec, rej, def) = p \<and> elec \<union> rej \<union> def = A"
    by simp
  thus "x \<in> A"
    using UnCI elec_res wf assms fst_conv
    by metis
qed

lemma reject_subset:
  assumes "well_formed A result"
  shows "reject_r result \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume rej_a: "a \<in> reject_r result"
  obtain
    alts :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    res :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    wf: "A = alts result A \<and> result = res result A \<and> disjoint3 (res result A) \<and>
            set_equals_partition (alts result A) (res result A)"
    using assms
    by simp
  hence
    "\<forall> p A. \<exists> elec rej def.
      set_equals_partition (A::'a set) p \<longrightarrow> (elec, rej, def) = p \<and> elec \<union> rej \<union> def = A"
    by simp
  thus "a \<in> A"
    using UnCI assms rej_a wf fst_conv snd_conv disjoint3.cases
    by metis
qed

end

(*  File:       Maximum_Aggregator.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Maximum Aggregator\<close>

theory Maximum_Aggregator
  imports Aggregator
begin

text \<open>
  The max(imum) aggregator takes two partitions of an alternative set A as
  input. It returns a partition where every alternative receives the maximum
  result of the two input partitions.
\<close>

subsection \<open>Definition\<close>

fun max_aggregator :: "'a Aggregator" where
  "max_aggregator A (e1, r1, d1) (e2, r2, d2) =
    (e1 \<union> e2,
     A - (e1 \<union> e2 \<union> d1 \<union> d2),
     (d1 \<union> d2) - (e1 \<union> e2))"

subsection \<open>Auxiliary Lemma\<close>

lemma max_agg_rej_set: "(well_formed A (e1, r1, d1) \<and>
                          well_formed A (e2, r2, d2)) \<longrightarrow>
           reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
proof (clarify)
  assume
    wf1: "well_formed A (e1, r1, d1)" and
    wf2: "well_formed A (e2, r2, d2)"
  have "A - (e1 \<union> d1) = r1"
    using wf1
    by (simp add: result_imp_rej)
  moreover have
    "A - (e2 \<union> d2) = r2"
    using wf2
    by (simp add: result_imp_rej)
  ultimately have
    "A - (e1 \<union> e2 \<union> d1 \<union> d2) = r1 \<inter> r2"
    by blast
  moreover have
    "{l \<in> A. l \<notin> e1 \<union> e2 \<union> d1 \<union> d2} = A - (e1 \<union> e2 \<union> d1 \<union> d2)"
    by (simp add: set_diff_eq)
  ultimately show "reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
    by simp
qed

subsection \<open>Soundness\<close>

theorem max_agg_sound[simp]: "aggregator max_aggregator"
proof (unfold aggregator_def, simp, safe)
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set" and
    x :: "'a"
  assume
    "e2 \<union> r2 \<union> d2 = e1 \<union> r1 \<union> d1" and
    "x \<notin> d1" and
    "x \<notin> r1" and
    "x \<in> e2"
  thus "x \<in> e1"
    by auto
next
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set" and
    x :: "'a"
  assume
    "e2 \<union> r2 \<union> d2 = e1 \<union> r1 \<union> d1" and
    "x \<notin> d1" and
    "x \<notin> r1" and
    "x \<in> d2"
  thus "x \<in> e1"
    by auto
qed

subsection \<open>Properties\<close>

text \<open>
  The max-aggregator is conservative.
\<close>

theorem max_agg_consv[simp]: "agg_conservative max_aggregator"
proof (unfold agg_conservative_def, safe)
  show "aggregator max_aggregator"
    using max_agg_sound
    by metis
next
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set" and
    x :: "'a"
  assume
    elect_x: "x \<in> elect_r (max_aggregator A (e1, r1, d1) (e2, r2, d2))" and
    x_not_in_e2: "x \<notin> e2"
  have "x \<in> e1 \<union> e2"
    using elect_x
    by simp
  hence "x \<in> e1 \<union> e2"
    by metis
  thus "x \<in> e1"
    using x_not_in_e2
    by simp
next
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set" and
    x :: "'a"
  assume
    wf2: "well_formed A (e2, r2, d2)" and
    reject_x: "x \<in> reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2))" and
    x_not_in_r2: "x \<notin> r2"
  have "x \<in> r1 \<union> r2"
    using wf2 reject_x
    by force
  hence "x \<in> r1 \<union> r2"
    by metis
  thus "x \<in> r1"
    using x_not_in_r2
    by simp
next
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set" and
    x :: "'a"
  assume
    wf2: "well_formed A (e2, r2, d2)" and
    defer_x: "x \<in> defer_r (max_aggregator A (e1, r1, d1) (e2, r2, d2))" and
    x_not_in_d2: "x \<notin> d2"
  have "x \<in> d1 \<union> d2"
    using wf2 defer_x
    by force
  hence "x \<in> d1 \<union> d2"
    by metis
  thus "x \<in> d1"
    using x_not_in_d2
    by simp
qed

text \<open>
  The max-aggregator is commutative.
\<close>

theorem max_agg_comm[simp]: "agg_commutative max_aggregator"
proof (unfold agg_commutative_def, safe, simp)
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set"
  show
    "max_aggregator A (e1, r1, d1) (e2, r2, d2) =
      max_aggregator A (e2, r2, d2) (e1, r1, d1)"
  by auto
qed

end

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

lemma max_agg_rej_set:
  fixes
    A :: "'a set" and
    e :: "'a set" and
    e' :: "'a set" and
    d :: "'a set" and
    d' :: "'a set" and
    r :: "'a set" and
    r' :: "'a set" and
    a :: "'a"
  assumes
    wf_first_mod: "well_formed A (e, r, d)" and
    wf_second_mod: "well_formed A (e', r', d')"
  shows "reject_r (max_aggregator A (e, r, d) (e', r', d')) = r \<inter> r'"
proof -
  have "A - (e \<union> d) = r"
    using wf_first_mod
    by (simp add: result_imp_rej)
  moreover have "A - (e' \<union> d') = r'"
    using wf_second_mod
    by (simp add: result_imp_rej)
  ultimately have "A - (e \<union> e' \<union> d \<union> d') = r \<inter> r'"
    by blast
  moreover have "{l \<in> A. l \<notin> e \<union> e' \<union> d \<union> d'} = A - (e \<union> e' \<union> d \<union> d')"
    unfolding set_diff_eq
    by simp
  ultimately show "reject_r (max_aggregator A (e, r, d) (e', r', d')) = r \<inter> r'"
    by simp
qed

subsection \<open>Soundness\<close>

theorem max_agg_sound[simp]: "aggregator max_aggregator"
proof (unfold aggregator_def, simp, safe)
  fix
    A :: "'a set" and
    e :: "'a set" and
    e' :: "'a set" and
    d :: "'a set" and
    d' :: "'a set" and
    r :: "'a set" and
    r' :: "'a set" and
    a :: "'a"
  assume
    "e' \<union> r' \<union> d' = e \<union> r \<union> d" and
    "a \<notin> d" and
    "a \<notin> r" and
    "a \<in> e'"
  thus "a \<in> e"
    by auto
next
  fix
    A :: "'a set" and
    e :: "'a set" and
    e' :: "'a set" and
    d :: "'a set" and
    d' :: "'a set" and
    r :: "'a set" and
    r' :: "'a set" and
    a :: "'a"
  assume
    "e' \<union> r' \<union> d' = e \<union> r \<union> d" and
    "a \<notin> d" and
    "a \<notin> r" and
    "a \<in> d'"
  thus "a \<in> e"
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
    e :: "'a set" and
    e' :: "'a set" and
    d :: "'a set" and
    d' :: "'a set" and
    r :: "'a set" and
    r' :: "'a set" and
    a :: "'a"
  assume
    elect_a: "a \<in> elect_r (max_aggregator A (e, r, d) (e', r', d'))" and
    a_not_in_e': "a \<notin> e'"
  have "a \<in> e \<union> e'"
    using elect_a
    by simp
  thus "a \<in> e"
    using a_not_in_e'
    by simp
next
  fix
    A :: "'a set" and
    e :: "'a set" and
    e' :: "'a set" and
    d :: "'a set" and
    d' :: "'a set" and
    r :: "'a set" and
    r' :: "'a set" and
    a :: "'a"
  assume
    wf_result: "well_formed A (e', r', d')" and
    reject_a: "a \<in> reject_r (max_aggregator A (e, r, d) (e', r', d'))" and
    a_not_in_r': "a \<notin> r'"
  have "a \<in> r \<union> r'"
    using wf_result reject_a
    by force
  thus "a \<in> r"
    using a_not_in_r'
    by simp
next
  fix
    A :: "'a set" and
    e :: "'a set" and
    e' :: "'a set" and
    d :: "'a set" and
    d' :: "'a set" and
    r :: "'a set" and
    r' :: "'a set" and
    a :: "'a"
  assume
    defer_a: "a \<in> defer_r (max_aggregator A (e, r, d) (e', r', d'))" and
    a_not_in_d': "a \<notin> d'"
  have "a \<in> d \<union> d'"
    using defer_a
    by force
  thus "a \<in> d"
    using a_not_in_d'
    by simp
qed

text \<open>
  The max-aggregator is commutative.
\<close>

theorem max_agg_comm[simp]: "agg_commutative max_aggregator"
  unfolding agg_commutative_def
  by auto

end

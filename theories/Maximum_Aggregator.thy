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

text
\<open>The max(imum) aggregator takes two partitions of an alternative set A as
input. It returns a partition where every alternative receives the maximum
result of the two input partitions.\<close>

subsection \<open>Definition\<close>

fun max_aggregator :: "'a Aggregator" where
  "max_aggregator A (e1, r1, d1) (e2, r2, d2) =
    (e1 \<union> e2,
     A - (e1 \<union> e2 \<union> d1 \<union> d2),
     (d1 \<union> d2) - (e1 \<union> e2))"

subsection \<open>Auxiliary Lemma\<close>

lemma max_agg_rej_set: "(partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
           reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
proof -
  have "partition A (e1, r1, d1) \<longrightarrow>  A - (e1 \<union> d1) = r1"
    by (simp add: result_imp_rej)
  moreover have
    "partition A (e2, r2, d2) \<longrightarrow>  A - (e2 \<union> d2) = r2"
    by (simp add: result_imp_rej)
  ultimately have
    "(partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
        A - (e1 \<union> e2 \<union> d1 \<union> d2) = r1 \<inter> r2"
    by blast
  moreover have
    "{l \<in> A. l \<notin> e1 \<union> e2 \<union> d1 \<union> d2} = A - (e1 \<union> e2 \<union> d1 \<union> d2)"
    by (simp add: set_diff_eq)
  ultimately show ?thesis
    by simp
qed

subsection \<open>Soundness\<close>

theorem max_agg_sound[simp]: "aggregator max_aggregator"
proof -
  have
    "\<forall>A e1 e2 d1 d2 r1 r2.
          (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
      set_equals_partition A (e1 \<union> e2,
                  A - (e1 \<union> e2 \<union> d1 \<union> d2),
                  (d1 \<union> d2) - (e1 \<union> e2))"
  proof -
    have
      "\<forall>B p. Electoral_Module.partition (B::'b set) p =
          (disjoint3 p \<and> set_equals_partition B p)"
      by simp
    thus ?thesis
      using Un_Diff_cancel result_imp_rej set_equals_partition.simps
            sup.left_commute sup_commute
      by auto
  qed
  hence unity:
    "\<forall>A res1 res2. (partition A res1 \<and> partition A res2) \<longrightarrow>
          set_equals_partition A (max_aggregator A res1 res2)"
    using max_aggregator.simps partition.simps set_equals_partition.elims(2)
    by (smt (z3))
  have
    "\<forall>A e1 e2 d1 d2 r1 r2.
          (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
      (e1 \<union> e2) \<inter> (A - (e1 \<union> e2 \<union> d1 \<union> d2)) = {}"
    by auto
  moreover have
    "\<forall>A e1 e2 d1 d2 r1 r2.
          (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
      (e1 \<union> e2) \<inter> ((d1 \<union> d2) - (e1 \<union> e2)) = {}"
    by auto
  moreover have
    "\<forall>A e1 e2 d1 d2 r1 r2.
          (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
      (A - (e1 \<union> e2 \<union> d1 \<union> d2)) \<inter> ((d1 \<union> d2) - (e1 \<union> e2)) = {}"
    by auto
  ultimately have disjoint:
      "\<forall>A res1 res2. (partition A res1 \<and> partition A res2) \<longrightarrow>
            disjoint3 (max_aggregator A res1 res2)"
    using disjoint3.simps
    by auto
  hence "\<forall>A res1 res2. (partition A res1 \<and> partition A res2) \<longrightarrow>
            partition A (max_aggregator A res1 res2)"
    by (simp add: disjoint unity)
    thus ?thesis
    using aggregator_def
    by blast
qed

subsection \<open>Properties\<close>

(*The max-aggregator is conservative.*)
theorem max_agg_consv[simp]: "agg_conservative max_aggregator"
proof -
  have
    "\<forall>A e1 e2 d1 d2 r1 r2.
          (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
      reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
    using max_agg_rej_set
    by blast
  hence
    "\<forall>A e1 e2 d1 d2 r1 r2.
            (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
        reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> r1 \<inter> r2"
    by blast
  moreover have
    "\<forall>A e1 e2 d1 d2 r1 r2.
        (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
            elect_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2)"
    by (simp add: subset_eq)
  ultimately have
    "\<forall>A e1 e2 d1 d2 r1 r2.
        (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
            (elect_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
             reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2))"
    by blast
  moreover have
    "\<forall>A e1 e2 d1 d2 r1 r2.
        (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
            defer_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2)"
    by auto
  ultimately have
    "\<forall>A e1 e2 d1 d2 r1 r2.
        (partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
            (elect_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
            reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2) \<and>
            defer_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2))"
    by blast
  thus ?thesis
    by (simp add: agg_conservative_def)
qed

(*The max-aggregator is commutative.*)
theorem max_agg_comm[simp]: "agg_commutative max_aggregator"
  using agg_commutative_def max_agg_sound max_aggregator.simps
        sup_assoc sup_commute
  by (smt (verit))

end

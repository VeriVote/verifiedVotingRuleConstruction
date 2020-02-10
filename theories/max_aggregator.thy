theory max_aggregator
imports aggregators

begin

(**********************************)
(*** Definition: Max Aggregator ***)
(**********************************)

(* The max aggregator takes 2 partitions of an alternative set A as input. It returns a partition
   where every alternative receives the maximum result of the 2 input partitions.
*)
fun Max_aggregator :: "'a Aggregator" where
  "Max_aggregator A (e1, r1, d1) (e2, r2, d2) =
    (e1 \<union> e2,
     A - (e1 \<union> e2 \<union> d1 \<union> d2),
     (d1 \<union> d2) - (e1 \<union> e2))"

(* Soundness: Max Aggregator *)
(* The max aggregator satisfies the aggregator predicate. This ensures it can be used in parallel
   compositions.
*)
theorem max_aggregator_sound[simp]:
  shows "aggregator Max_aggregator"
proof -
  have "\<forall>A e1 e2 d1 d2 r1 r2. (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
      unify_to A (e1 \<union> e2,
                  A - (e1 \<union> e2 \<union> d1 \<union> d2),
                  (d1 \<union> d2) - (e1 \<union> e2))"
    by (smt Un_Diff_cancel partition_of_def partition_reject sup.left_commute sup_commute
        unify_to.simps)
  hence unity: "\<forall>A res1 res2. (partition_of A res1 \<and> partition_of A res2) \<longrightarrow>
      unify_to A (Max_aggregator A res1 res2)"
    by (smt Max_aggregator.simps partition_of_def unify_to.elims(2))
  have "\<forall>A e1 e2 d1 d2 r1 r2. (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
      (e1 \<union> e2) \<inter> (A - (e1 \<union> e2 \<union> d1 \<union> d2)) = {}"
    by auto
  moreover have "\<forall>A e1 e2 d1 d2 r1 r2.
      (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
      (e1 \<union> e2) \<inter> ((d1 \<union> d2) - (e1 \<union> e2)) = {}"
    by auto
  moreover have "\<forall>A e1 e2 d1 d2 r1 r2.
      (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
      (A - (e1 \<union> e2 \<union> d1 \<union> d2)) \<inter> ((d1 \<union> d2) - (e1 \<union> e2)) = {}"
    by auto
  ultimately have disjoint: "\<forall>A res1 res2. (partition_of A res1 \<and> partition_of A res2) \<longrightarrow>
      disjoint3 (Max_aggregator A res1 res2)"
    using disjoint3.simps by auto
  hence "\<forall>A res1 res2. (partition_of A res1 \<and> partition_of A res2) \<longrightarrow>
      partition_of A (Max_aggregator A res1 res2)"
    by (metis partition_of_def unity)
  thus ?thesis
    using aggregator_def by blast
qed

(****************************************)
(*** Properties of the Max Aggregator ***)
(****************************************)

lemma max_aggregator_reject_set:
  shows "(partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
           reject_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
proof -
  have "partition_of A (e1, r1, d1) \<longrightarrow>  A - (e1 \<union> d1) = r1"
    by (simp add: partition_reject)
  moreover have "partition_of A (e2, r2, d2) \<longrightarrow>  A - (e2 \<union> d2) = r2"
    by (simp add: partition_reject)
  ultimately have "(partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
                     A - (e1 \<union> e2 \<union> d1 \<union> d2) = r1 \<inter> r2"
    by blast
  moreover have "{l \<in> A. l \<notin> e1 \<union> e2 \<union> d1 \<union> d2} = A - (e1 \<union> e2 \<union> d1 \<union> d2)"
    by (simp add: set_diff_eq)
  ultimately show ?thesis
    by simp
qed

(* The max aggregator is conservative. *)
theorem max_aggregator_conservative[simp]:
  shows "conservative Max_aggregator"
proof -
  have "\<forall>A e1 e2 d1 d2 r1 r2. (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
      reject_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
    using max_aggregator_reject_set by blast
  hence "\<forall>A e1 e2 d1 d2 r1 r2. (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
      reject_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> r1 \<inter> r2"
    by blast
  moreover have "\<forall>A e1 e2 d1 d2 r1 r2.
      (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
        elect_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2)"
    by (simp add: subset_eq)
  ultimately have "\<forall>A e1 e2 d1 d2 r1 r2.
      (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
        (elect_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
         reject_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2))"
    by blast
  moreover have "\<forall>A e1 e2 d1 d2 r1 r2.
      (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
        defer_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2)"
    by auto
  ultimately have "\<forall>A e1 e2 d1 d2 r1 r2.
      (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
        (elect_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
    reject_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2) \<and>
    defer_r (Max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2))"
    by blast
  thus ?thesis
    by (simp add: conservative_def)
qed

end

theory pass_module
imports electoral_modules

begin

(*******************************)
(*** Definition: Pass Module ***)
(*******************************)

(* This is a family of electoral modules. For a natural number n and a lexicon (linear order) r of
   all alternatives the affiliated pass module defers the lexicographically first n alternatives
   (from A) and reject the rest. It is primarily used as counterpart of the drop module in a
   parallel composition, to devide alternatives into two groups.
*)
fun Pass_module :: "nat \<Rightarrow> 'a rel \<Rightarrow> 'a Electoral_module" where
  "Pass_module n r A p = ({},
                          {a \<in> A. card(above (limit_to A r) a) > n},
                          {a \<in> A. card(above (limit_to A r) a) \<le> n})"

(* For any natural number and any linear order the affiliated pass module satisfies the
   electoral_module predicate. This ensures it can be used as electoral module in compositions.
*)
lemma pass_module_sound[simp]:
  assumes order: "linear_order r"
  shows "electoral_module (Pass_module n r)"
proof -
  let ?mod = "Pass_module n r"
  have "\<forall> A p. finite_profile A p \<longrightarrow> (\<forall>a \<in> A. a \<in> {x \<in> A. card(above (limit_to A r) x) > n} \<or>
                                               a \<in> {x \<in> A. card(above (limit_to A r) x) \<le> n})"
    by (metis CollectI not_less)
  hence "\<forall> A p. finite_profile A p \<longrightarrow>
      {a \<in> A. card(above (limit_to A r) a) > n} \<union> {a \<in> A. card(above (limit_to A r) a) \<le> n} = A"
    by blast
  hence 0: "\<forall> A p. finite_profile A p \<longrightarrow> unify_to A (Pass_module n r A p)"
    by (simp)
  have "\<forall> A p. finite_profile A p \<longrightarrow>
      (\<forall>a \<in> A. \<not>(a \<in> {x \<in> A. card(above (limit_to A r) x) > n} \<and>
                 a \<in> {x \<in> A. card(above (limit_to A r) x) \<le> n}))"
    by auto
  hence "\<forall> A p. finite_profile A p \<longrightarrow>
      {a \<in> A. card(above (limit_to A r) a) > n} \<inter> {a \<in> A. card(above (limit_to A r) a) \<le> n} = {}"
    by blast
  hence 1: "\<forall> A p. finite_profile A p \<longrightarrow> disjoint3 (?mod A p)"
    by (simp)
  from 0 1
  have "\<forall> A p. finite_profile A p \<longrightarrow> partition_of A (?mod A p)"
    by (simp add: partition_of_def)
  hence "\<forall> A p. finite_profile A p \<longrightarrow> partition_of A (?mod A p)"
    by simp
  thus ?thesis
    by blast
qed

(*************************************)
(*** Properties of the Pass Module ***)
(*************************************)

(* For any natural number and any linear order the affiliated pass module is non electing. *)
lemma pass_module_non_electing[simp]:
  assumes order: "linear_order r"
  shows "non_electing (Pass_module n r)"
  by (simp add: non_electing_def order)

(* For any natural number and any linear order, the affiliated pass module is strict defer monotone.
*)
lemma pass_module_defer_lift_invariant[simp]:
  assumes order: "linear_order r"
  shows "defer_lift_invariant (Pass_module n r)"
  by (simp add: order defer_lift_invariant_def)

(* For any natural number n and any linear order, the affiliated pass module defers n alternatives
   (if there are n alternatives).
*)
(* The induction proof is still missing. Following are the proofs for n=1 and n=2. *)
theorem pass_1_module_defers_1[simp]:
  assumes order: "linear_order r"
  shows "defers 1 (Pass_module 1 r)"
proof -
  { have "\<forall>A p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow> card (defer (Pass_module 1 r) A p) = 1"
    proof
      { fix A show "\<forall>p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
                          card (defer (Pass_module 1 r) A p) = 1"
        proof
          { fix p show "(card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
                          card (defer (Pass_module 1 r) A p) = 1"
            proof
              assume A_valid: "(card A \<ge> 1 \<and> finite_profile A p)"
              hence finite_A: "finite A"
                by simp
              moreover have "A \<noteq> {}"
                using A_valid
                by auto
              moreover have lin_ord_on_A: "linear_order_on A (limit_to A r)"
                using order
                using limit_preserves_linear_order
                by blast
              ultimately have winner_exists: "\<exists>a\<in>A. above (limit_to A r) a = {a}
                                                  \<and> (\<forall>x\<in>A. above (limit_to A r) x = {x} \<longrightarrow> x = a)"
                using linear_order_above_one_winner
                by (simp add: linear_order_above_one_winner)
              then obtain w where
                w_unique_top: "above (limit_to A r) w = {w}
                                \<and> (\<forall>x\<in>A. above (limit_to A r) x = {x} \<longrightarrow> x = w)"
                using linear_order_above_one_winner
                by auto
                { hence "{a \<in> A. card(above (limit_to A r) a) \<le> 1} = {w}"
                  proof
                    assume w_top: "above (limit_to A r) w = {w}"
                    assume w_unique: "\<forall>x\<in>A. above (limit_to A r) x = {x} \<longrightarrow> x = w"
                    have "card(above (limit_to A r) w) \<le> 1"
                      using w_top
                      by auto
                    hence "{w} \<subseteq> {a \<in> A. card(above (limit_to A r) a) \<le> 1}"
                      using winner_exists w_unique_top
                      by blast
                    moreover
                      { have "{a \<in> A. card(above (limit_to A r) a) \<le> 1} \<subseteq> {w}"
                        proof
                          fix x assume x_in_winner_set:
                            "x \<in> {a \<in> A. card (above (limit_to A r) a) \<le> 1}"
                          hence x_in_A: "x \<in> A"
                            by auto
                          hence "(x,x) \<in> limit_to A r"
                            by (meson lin_ord_on_A above_in_relation_equiv
                                linear_order_impl_connex self_in_above)
                          hence x_above_x: "x \<in> above (limit_to A r) x"
                            by (simp add: above_def)
                          have "above (limit_to A r) x \<subseteq> A"
                            using limited_above_subset order
                            by fastforce
                          hence above_finite: "finite (above (limit_to A r) x)"
                            by (simp add: A_valid finite_subset)
                          have "card (above (limit_to A r) x) \<le> 1"
                            using x_in_winner_set
                            by simp
                          moreover have "card (above (limit_to A r) x) \<ge> 1"
                            by (metis One_nat_def Suc_leI above_finite card_eq_0_iff equals0D
                                neq0_conv x_above_x)
                          ultimately have "card (above (limit_to A r) x) = 1"
                            by simp
                          hence "{x} = above (limit_to A r) x"
                            by (metis is_singletonE is_singleton_altdef singletonD x_above_x)
                          hence "x = w"
                            using w_unique
                            by (simp add: x_in_A)
                          thus "x \<in> {w}"
                            by simp
                        qed }
                    ultimately have "{w} = {a \<in> A. card(above (limit_to A r) a) \<le> 1}"
                      by auto
                    thus ?thesis
                      by simp
                  qed }
              hence "defer (Pass_module 1 r) A p = {w}"
                by simp
              thus "card (defer (Pass_module 1 r) A p) = 1"
                by simp
            qed }
        qed }
    qed }
  thus ?thesis
    using defers_def order pass_module_sound
    by blast
qed

theorem pass_2_module_defers_2:
  assumes order: "linear_order r"
  shows "defers 2 (Pass_module 2 r)"
proof -
  { have "\<forall>A p. (card A \<ge> 2 \<and> finite_profile A p) \<longrightarrow> card (defer (Pass_module 2 r) A p) = 2"
    proof
      { fix A show "\<forall>p. (card A \<ge> 2 \<and> finite_profile A p) \<longrightarrow>
                          card (defer (Pass_module 2 r) A p) = 2"
        proof
          { fix p show "(card A \<ge> 2 \<and> finite_profile A p) \<longrightarrow>
                          card (defer (Pass_module 2 r) A p) = 2"
            proof
              { assume A_ok: "card A \<ge> 2 \<and> finite_profile A p"
                hence finA: "finite A"
                  by simp
                moreover from A_ok
                have not_empty_A: "A \<noteq> {}"
                  by auto
                moreover have limitA_order: "linear_order_on A (limit_to A r)"
                  using limit_preserves_linear_order order
                  by auto
                ultimately obtain a where
                  a: "above (limit_to A r) a = {a}"
                  using linear_order_above_one_winner
                  by blast
                hence a_best: "\<forall>b \<in> A. (b, a) \<in> limit_to A r"
                  by (metis limitA_order above_in_relation_equiv empty_iff insert_iff insert_subset
                      limited_above_subset linear_order_on_def order total_on_def)
                hence a_above: "\<forall>b \<in> A. a \<in> above (limit_to A r) b"
                  by (simp add: above_def)
                from a
                have a_in_defer: "a \<in> defer (Pass_module 2 r) A p"
                  by (metis (no_types, lifting) CollectI Pass_module.simps Suc_leI not_empty_A
                      a_above card_UNIV_bool card_empty card_gt_0_iff card_insert_disjoint empty_iff
                      empty_not_UNIV finA finite.emptyI finite_UNIV insert_iff limitA_order
                      linear_order_above_one_winner sndI)
                have "finite (A-{a})"
                  by (simp add: finA)
                moreover have A_not_only_a: "A-{a} \<noteq> {}"
                  by (metis A_ok Diff_empty Diff_idemp Diff_insert0 One_nat_def not_empty_A
                      card.insert_remove card_empty finite.emptyI insert_Diff numeral_le_one_iff
                      semiring_norm(69))
                moreover have limitAa_order: "linear_order_on (A-{a}) (limit_to (A-{a}) r)"
                  using limit_preserves_linear_order order
                  by blast
                ultimately obtain b where
                  b: "above (limit_to (A-{a}) r) b = {b}"
                  using linear_order_above_one_winner
                  by blast
                hence b_in_limit: "\<forall>c \<in> A-{a}. (c, b) \<in> limit_to (A-{a}) r"
                  by (metis limitAa_order above_in_relation_equiv empty_iff insert_iff insert_subset
                      limited_above_subset linear_order_on_def order total_on_def)
                hence b_best: "\<forall>c \<in> A-{a}. (c, b) \<in> limit_to A r"
                  by auto
                hence c_not_above_b: "\<forall>c \<in> A-{a, b}. c \<notin> above (limit_to A r) b"
                  by (smt DiffD2 a_best above_def b insertCI insertE insert_Diff
                      limit_preserves_preferences1 limit_preserves_preferences2 limit_to_limits
                      limited_dest mem_Collect_eq)
                moreover have above_subset: "above (limit_to A r) b \<subseteq> A"
                  by (meson limited_above_subset order)
                moreover have b_above_b: "b \<in> above (limit_to A r) b"
                  by (metis above_def b b_best limited_above_subset mem_Collect_eq order
                      rev_subsetD singletonI)
                ultimately have above_b_eq_ab: "above (limit_to A r) b = {a, b}"
                  using a_above
                  by auto
                hence card_above_b_eq_2: "card (above (limit_to A r) b) = 2"
                  using A_not_only_a b_in_limit
                  by auto
                hence b_in_defer: "b \<in> defer (Pass_module 2 r) A p"
                  using b_above_b above_subset
                  by auto
                from b_best
                have b_above: "\<forall>c \<in> A-{a}. b \<in> above (limit_to A r) c"
                  by (meson above_in_relation_equiv)
                have "connex_on A (limit_to A r)"
                  using limitA_order linear_order_impl_connex
                  by auto
                hence "\<forall>c \<in> A. c \<in> above (limit_to A r) c"
                  by (simp add: self_in_above)
                hence "\<forall>c \<in> A-{a, b}. {a, b, c} \<subseteq> above (limit_to A r) c"
                  using a_above b_above
                  by auto
                moreover have "\<forall>c \<in> A-{a, b}. card{a, b, c} = 3"
                  by (metis DiffE One_nat_def Suc_1 above_b_eq_ab card_above_b_eq_2 above_subset
                      card_insert_disjoint finA finite_subset insert_commute numeral_3_eq_3)
                ultimately have "\<forall>c \<in> A-{a, b}. card (above (limit_to A r) c) \<ge> 3"
                  by (metis card_mono finA finite_subset limited_above_subset order)
                hence "\<forall>c \<in> A-{a, b}. card (above (limit_to A r) c) > 2"
                  by (meson less_le_trans numeral_less_iff order_refl semiring_norm(79))
                hence "\<forall>c \<in> A-{a, b}. c \<notin> defer (Pass_module 2 r) A p"
                  by (simp add: not_le)
                moreover have "defer (Pass_module 2 r) A p \<subseteq> A"
                  by auto
                ultimately have "defer (Pass_module 2 r) A p \<subseteq> {a, b}"
                  by blast
                from this a_in_defer b_in_defer
                have "defer (Pass_module 2 r) A p = {a, b}"
                  by blast
                thus "card (defer (Pass_module 2 r) A p) = 2"
                  using above_b_eq_ab card_above_b_eq_2
                  by auto
              }
            qed }
        qed }
    qed }
  thus ?thesis
    using defers_def order pass_module_sound
    by blast
qed

(* For any natural number and any linear order, the affiliated pass module is non blocking. *)
theorem pass_module_non_blocking[simp]:
  assumes order: "linear_order r" and
          g0_n:  "n > 0"
  shows "non_blocking (Pass_module n r)"
proof -
  { have "\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> reject (Pass_module n r) A p \<noteq> A"
    proof
      { fix A show "\<forall>p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> reject (Pass_module n r) A p \<noteq> A"
        proof
          { fix p show "(A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> reject (Pass_module n r) A p \<noteq> A"
            proof
              { assume input_fine: "A \<noteq> {} \<and> finite_profile A p"
                hence "finite A"
                  by simp
                moreover have "A \<noteq> {}"
                  by (simp add: input_fine)
                moreover have "linear_order_on A (limit_to A r)"
                  using limit_preserves_linear_order order
                  by auto
                ultimately have "\<exists>a\<in>A. above (limit_to A r) a = {a}
                                        \<and> (\<forall>x\<in>A. above (limit_to A r) x = {x} \<longrightarrow> x = a)"
                  using linear_order_above_one_winner
                  by (simp add: linear_order_above_one_winner)
                thus "reject (Pass_module n r) A p \<noteq> A"
                  by (metis (no_types, lifting) One_nat_def Pass_module.simps Suc_leI assms(2)
                      fst_conv is_singletonI is_singleton_altdef leD mem_Collect_eq snd_conv)
              }
            qed }
        qed }
    qed }
  thus ?thesis
    by (simp add: non_blocking_def order)
qed

end

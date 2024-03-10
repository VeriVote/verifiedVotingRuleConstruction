(*  File:       Drop_And Pass_Compatibility.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Compositional Structures\<close>

section \<open>Drop And Pass Compatibility\<close>

theory Drop_And_Pass_Compatibility
  imports "Basic_Modules/Drop_Module"
          "Basic_Modules/Pass_Module"
begin

text \<open>
  This is a collection of properties about the interplay and compatibility
  of both the drop module and the pass module.
\<close>

subsection \<open>Properties\<close>

theorem drop_zero_mod_rej_zero[simp]:
  fixes r :: "'a Preference_Relation"
  assumes "linear_order r"
  shows "rejects 0 (drop_module 0 r)"
proof (unfold rejects_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (drop_module 0 r)"
    using assms
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    fin_A: "finite A" and
    prof_A: "profile V A p"
  have "connex UNIV r"
    using assms lin_ord_imp_connex
    by auto
  hence connex: "connex A (limit A r)"
    using limit_presv_connex subset_UNIV
    by metis
  have "\<forall> B a. B \<noteq> {} \<or> (a::'a) \<notin> B"
    by simp
  hence "\<forall> a B. a \<in> A \<and> a \<in> B \<longrightarrow> connex B (limit A r) \<longrightarrow>
            \<not> card (above (limit A r) a) \<le> 0"
    using above_connex above_presv_limit card_eq_0_iff
          fin_A finite_subset le_0_eq assms
    by (metis (no_types))
  hence "{a \<in> A. card (above (limit A r) a) \<le> 0} = {}"
    using connex
    by auto
  hence "card {a \<in> A. card (above (limit A r) a) \<le> 0} = 0"
    using card.empty
    by (metis (full_types))
  thus "card (reject (drop_module 0 r) V A p) = 0"
    by simp
qed

text \<open>
  The drop module rejects n alternatives (if there are at least n alternatives).
\<close>

theorem drop_two_mod_rej_n[simp]:
  fixes r :: "'a Preference_Relation"
  assumes "linear_order r"
  shows "rejects n (drop_module n r)"
proof (unfold rejects_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (drop_module n r)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    card_n: "n \<le> card A" and
    fin_A: "finite A" and
    prof: "profile V A p"
  let ?inv_rank = "the_inv_into A (rank (limit A r))"
  have lin_ord_limit: "linear_order_on A (limit A r)"
    using assms limit_presv_lin_ord
    by auto
  hence "(limit A r) \<subseteq> A \<times> A"
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
    by simp
  hence "\<forall> a \<in> A. (above (limit A r) a) \<subseteq> A"
    unfolding above_def
    by auto
  hence leq: "\<forall> a \<in> A. rank (limit A r) a \<le> card A"
    using fin_A
    by (simp add: card_mono)
  have "\<forall> a \<in> A. {a} \<subseteq> (above (limit A r) a)"
    using lin_ord_limit
    unfolding linear_order_on_def partial_order_on_def 
              preorder_on_def refl_on_def above_def
    by auto
  hence "\<forall> a \<in> A. card {a} \<le> card (above (limit A r) a)"
    using card_mono fin_A rev_finite_subset above_presv_limit
    by metis
  hence geq_1: "\<forall> a \<in> A. 1 \<le> rank (limit A r) a"
    by simp
  with leq have "\<forall> a \<in> A. rank (limit A r) a \<in> {1 .. card A}"
    by simp
  hence "rank (limit A r) ` A \<subseteq> {1 .. card A}"
    by auto
  moreover have inj: "inj_on (rank (limit A r)) A"
    using fin_A inj_onI rank_unique lin_ord_limit
    by metis
  ultimately have bij: "bij_betw (rank (limit A r)) A {1 .. card A}"
    using bij_betw_def bij_betw_finite bij_betw_iff_card card_seteq
          dual_order.refl ex_bij_betw_nat_finite_1 fin_A
    by metis
  hence bij_inv: "bij_betw ?inv_rank {1 .. card A} A"
    using bij_betw_the_inv_into
    by blast
  hence "\<forall> S \<subseteq> {1..card A}. card (?inv_rank ` S) = card S"
    using fin_A bij_betw_same_card bij_betw_subset
    by metis
  moreover have subset: "{1 .. n} \<subseteq> {1 .. card A}"
    using card_n
    by simp
  ultimately have "card (?inv_rank ` {1 .. n}) = n"
    using numeral_One numeral_eq_iff semiring_norm(85) card_atLeastAtMost
    by presburger
  also have "?inv_rank ` {1..n} = {a \<in> A. rank (limit A r) a \<in> {1 .. n}}"
  proof
    show "?inv_rank ` {1..n} \<subseteq> {a \<in> A. rank (limit A r) a \<in> {1 .. n}}"
    proof
      fix a :: "'a"
      assume "a \<in> ?inv_rank ` {1..n}"
      then obtain b where b_img: "b \<in> {1 .. n} \<and> ?inv_rank b = a"
        by auto
      hence "rank (limit A r) a = b"
        using subset f_the_inv_into_f_bij_betw subsetD bij
        by metis
      hence "rank (limit A r) a \<in> {1 .. n}"
        using b_img
        by simp
      moreover have "a \<in> A"
        using b_img bij_inv bij_betwE subset
        by blast
      ultimately show "a \<in> {a \<in> A. rank (limit A r) a \<in> {1 .. n}}"
        by blast
    qed
  next
    show "{a \<in> A. rank (limit A r) a \<in> {1 .. n}} \<subseteq> the_inv_into A (rank (limit A r)) ` {1 .. n}"
    proof
      fix a :: "'a"
      assume el: "a \<in> {a \<in> A. rank (limit A r) a \<in> {1 .. n}}"
      then obtain b where b_img: "b \<in> {1..n} \<and> rank (limit A r) a = b"
        by auto
      moreover have "a \<in> A"
        using el
        by simp
      ultimately have "?inv_rank b = a"
        using inj the_inv_into_f_f
        by metis
      thus "a \<in> ?inv_rank ` {1 .. n}"
        using b_img
        by auto
    qed
  qed
  finally have "card {a \<in> A. rank (limit A r) a \<in> {1..n}} = n"
    by blast
  also have "{a \<in> A. rank (limit A r) a \<in> {1 .. n}} = {a \<in> A. rank (limit A r) a \<le> n}"
    using geq_1
    by auto
  also have "... = reject (drop_module n r) V A p"
    by simp
  finally show "card (reject (drop_module n r) V A p) = n"
    by blast
qed

text \<open>
  The pass and drop module are (disjoint-)compatible.
\<close>

theorem drop_pass_disj_compat[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: "nat"
  assumes "linear_order r"
  shows "disjoint_compatibility (drop_module n r) (pass_module n r)"
proof (unfold disjoint_compatibility_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (drop_module n r)"
    using assms
    by simp
next
  show "\<S>\<C>\<F>_result.electoral_module (pass_module n r)"
    using assms
    by simp
next
  fix
    A :: "'a set" and
    V :: "'b set"
  have "linear_order_on A (limit A r)"
    using assms limit_presv_lin_ord
    by blast
  hence "profile V A (\<lambda> v. (limit A r))"
    using profile_def
    by blast
  then obtain p :: "('a, 'b) Profile" where
    "profile V A p"
    by blast
  show "\<exists> B \<subseteq> A. (\<forall> a \<in> B. indep_of_alt (drop_module n r) V A a \<and>
                         (\<forall> p. profile V A p \<longrightarrow> a \<in> reject (drop_module n r) V A p)) \<and>
            (\<forall> a \<in> A - B. indep_of_alt (pass_module n r) V A a \<and>
                      (\<forall> p. profile V A p \<longrightarrow> a \<in> reject (pass_module n r) V A p))"
  proof
    have same_A:
      "\<forall> p q. (profile V A p \<and> profile V A q) \<longrightarrow>
        reject (drop_module n r) V A p = reject (drop_module n r) V A q"
      by auto
    let ?A = "reject (drop_module n r) V A p"
    have "?A \<subseteq> A"
      by auto
    moreover have "\<forall> a \<in> ?A. indep_of_alt (drop_module n r) V A a"
      using assms
      unfolding indep_of_alt_def
      by simp
    moreover have "\<forall> a \<in> ?A. \<forall> p. profile V A p \<longrightarrow> a \<in> reject (drop_module n r) V A p"
      by auto
    moreover have "\<forall> a \<in> A - ?A. indep_of_alt (pass_module n r) V A a"
      using assms
      unfolding indep_of_alt_def
      by simp
    moreover have "\<forall> a \<in> A - ?A. \<forall> p. profile V A p \<longrightarrow> a \<in> reject (pass_module n r) V A p"
      by auto
    ultimately show "?A \<subseteq> A \<and>
        (\<forall> a \<in> ?A. indep_of_alt (drop_module n r) V A a \<and>
          (\<forall> p. profile V A p \<longrightarrow> a \<in> reject (drop_module n r) V A p)) \<and>
        (\<forall> a \<in> A - ?A. indep_of_alt (pass_module n r) V A a \<and>
          (\<forall> p. profile V A p \<longrightarrow> a \<in> reject (pass_module n r) V A p))"
      by simp
  qed
qed

end
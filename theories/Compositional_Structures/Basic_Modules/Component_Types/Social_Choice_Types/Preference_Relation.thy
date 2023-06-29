(*  File:       Preference_Relation.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Social-Choice Types\<close>

section \<open>Preference Relation\<close>

theory Preference_Relation
  imports Main
begin

text \<open>
  The very core of the composable modules voting framework: types and
  functions, derivations, lemmas, operations on preference relations, etc.
\<close>

subsection \<open>Definition\<close>

text \<open>
  Each voter expresses pairwise relations between all alternatives,
  thereby inducing a linear order.
\<close>

type_synonym 'a Preference_Relation = "'a rel"

type_synonym 'a Vote = "'a set \<times> 'a Preference_Relation"

fun is_less_preferred_than ::
  "'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<preceq>\<^sub>_ _" [50, 1000, 51] 50) where
    "x \<preceq>\<^sub>r y = ((x, y) \<in> r)"

lemma lin_imp_antisym:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes "linear_order_on A r"
  shows "antisym r"
  using assms
  unfolding linear_order_on_def partial_order_on_def
  by simp

lemma lin_imp_trans:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes "linear_order_on A r"
  shows "trans r"
  using assms order_on_defs
  by blast

subsection \<open>Ranking\<close>

fun rank :: "'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank r x = card (above r x)"

lemma rank_gt_zero:
  fixes
    r :: "'a Preference_Relation" and
    x :: "'a"
  assumes
    refl: "x \<preceq>\<^sub>r x" and
    fin:  "finite r"
  shows "rank r x \<ge> 1"
proof -
  have "x \<in> {y \<in> Field r. (x, y) \<in> r}"
    using FieldI2 refl
    by fastforce
  hence "{y \<in> Field r. (x, y) \<in> r} \<noteq> {}"
    by blast
  hence "card {y \<in> Field r. (x, y) \<in> r} \<noteq> 0"
    by (simp add: fin finite_Field)
  moreover have "card {y \<in> Field r. (x, y) \<in> r} \<ge> 0"
    using fin
    by auto
  ultimately show ?thesis
    using Collect_cong FieldI2 above_def
          less_one not_le_imp_less rank.elims
    by (metis (no_types, lifting))
qed

subsection \<open>Limited Preference\<close>

definition limited :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "limited A r \<equiv> r \<subseteq> A \<times> A"

lemma limitedI:
  fixes
    r :: "'a Preference_Relation" and
    A :: "'a set"
  assumes "\<And> x y. x \<preceq>\<^sub>r y \<Longrightarrow> x \<in> A \<and> y \<in> A"
  shows "limited A r"
  using assms
  unfolding limited_def
  by auto

lemma limited_dest:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    x :: "'a" and
    y :: "'a"
  assumes
    "x \<preceq>\<^sub>r y" and
    "limited A r"
  shows "x \<preceq>\<^sub>r y \<Longrightarrow> limited A r \<Longrightarrow> x \<in> A \<and> y \<in> A"
  unfolding limited_def
  by auto

fun limit :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
  "limit A r = {(a, b) \<in> r. a \<in> A \<and> b \<in> A}"

definition connex :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "connex A r \<equiv> limited A r \<and> (\<forall> x \<in> A. \<forall> y \<in> A. x \<preceq>\<^sub>r y \<or> y \<preceq>\<^sub>r x)"

lemma connex_imp_refl:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes "connex A r"
  shows "refl_on A r"
proof
  from assms
  show "r \<subseteq> A \<times> A"
    unfolding connex_def limited_def
    by simp
next
  fix x :: "'a"
  assume "x \<in> A"
  with assms
  have "x \<preceq>\<^sub>r x"
    unfolding connex_def
    by metis
  thus "(x, x) \<in> r"
    by simp
qed

lemma lin_ord_imp_connex:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes "linear_order_on A r"
  shows "connex A r"
proof (unfold connex_def limited_def, safe)
  fix
    a :: "'a" and
    b :: "'a"
  assume "(a, b) \<in> r"
  with assms
  show "a \<in> A"
    using partial_order_onD(1) order_on_defs(3) refl_on_domain
    by metis
next
  fix
    a :: "'a" and
    b :: "'a"
  assume "(a, b) \<in> r"
  with assms
  show "b \<in> A"
    using partial_order_onD(1) order_on_defs(3) refl_on_domain
    by metis
next
  fix
    a :: "'a" and
    b :: "'a"
  assume
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    not_y_pref_r_x: "\<not> b \<preceq>\<^sub>r a"
  have "(b, a) \<notin> r"
    using not_y_pref_r_x
    by simp
  with a_in_A b_in_A
  have "(a, b) \<in> r"
    using assms partial_order_onD(1) refl_onD
    unfolding linear_order_on_def total_on_def
    by metis
  thus "a \<preceq>\<^sub>r b"
    by simp
qed

lemma connex_antsym_and_trans_imp_lin_ord:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes
    connex_r: "connex A r" and
    antisym_r: "antisym r" and
    trans_r: "trans r"
  shows "linear_order_on A r"
proof (unfold connex_def linear_order_on_def partial_order_on_def
              preorder_on_def refl_on_def total_on_def, safe)
  fix
    a :: "'a" and
    b :: "'a"
  assume "(a, b) \<in> r"
  thus "a \<in> A"
    using connex_r refl_on_domain connex_imp_refl
    by metis
next
  fix
    a :: "'a" and
    b :: "'a"
  assume "(a, b) \<in> r"
  thus "b \<in> A"
    using connex_r refl_on_domain connex_imp_refl
    by metis
next
  fix a :: "'a"
  assume "a \<in> A"
  thus "(a, a) \<in> r"
    using connex_r connex_imp_refl refl_onD
    by metis
next
  from trans_r
  show "trans r"
    by simp
next
  from antisym_r
  show "antisym r"
    by simp
next
  fix
    a :: "'a" and
    b :: "'a"
  assume
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    b_not_pref_r_a: "(b, a) \<notin> r"
  from a_in_A b_in_A
  have "a \<preceq>\<^sub>r b \<or> b \<preceq>\<^sub>r a"
    using connex_r
    unfolding connex_def
    by metis
  hence "(a, b) \<in> r \<or> (b, a) \<in> r"
    by simp
  thus "(a, b) \<in> r"
    using b_not_pref_r_a
    by metis
qed

lemma limit_to_limits:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  shows "limited A (limit A r)"
  unfolding limited_def
  by fastforce

lemma limit_presv_connex:
  fixes
    S :: "'a set" and
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes
    connex: "connex S r" and
    subset: "A \<subseteq> S"
  shows "connex A (limit A r)"
proof (unfold connex_def limited_def, simp, safe)
  let ?s = "{(a, b). (a, b) \<in> r \<and> a \<in> A \<and> b \<in> A}"
  fix
    x :: "'a" and
    y :: "'a" and
    a :: "'a" and
    b :: "'a"
  assume
    x_in_A: "x \<in> A" and
    y_in_A: "y \<in> A" and
    not_y_pref_r_x: "(y, x) \<notin> r"
  have "y \<preceq>\<^sub>r x \<or> x \<preceq>\<^sub>r y"
    using x_in_A y_in_A connex connex_def in_mono subset
    by metis
  hence "x \<preceq>\<^sub>?s y \<or> y \<preceq>\<^sub>?s x"
    using x_in_A y_in_A
    by auto
  hence "x \<preceq>\<^sub>?s y"
    using not_y_pref_r_x
    by simp
  thus "(x, y) \<in> r"
    by simp
qed

lemma limit_presv_antisym:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes "antisym r"
  shows "antisym (limit A r)"
  using assms
  unfolding antisym_def
  by simp

lemma limit_presv_trans:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes "trans r"
  shows "trans (limit A r)"
  unfolding trans_def
  using transE assms
  by auto

lemma limit_presv_lin_ord:
  fixes
    A :: "'a set" and
    S :: "'a set" and
    r :: "'a Preference_Relation"
  assumes
    "linear_order_on S r" and
      "A \<subseteq> S"
    shows "linear_order_on A (limit A r)"
  using assms connex_antsym_and_trans_imp_lin_ord limit_presv_antisym limit_presv_connex
        limit_presv_trans lin_ord_imp_connex order_on_defs(1, 2, 3)
  by metis

lemma limit_presv_prefs_1:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    x :: "'a" and
    y :: "'a"
  assumes
    "x \<preceq>\<^sub>r y" and
    "x \<in> A" and
    "y \<in> A"
  shows "let s = limit A r in x \<preceq>\<^sub>s y"
  using assms
  by simp

lemma limit_presv_prefs_2:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    x :: "'a" and
    y :: "'a"
  assumes "(x, y) \<in> limit A r"
  shows "x \<preceq>\<^sub>r y"
  using mem_Collect_eq assms
  by simp

lemma limit_trans:
  fixes
    B :: "'a set" and
    C :: "'a set" and
    r :: "'a Preference_Relation"
  assumes "C \<subseteq> B"
  shows "limit C r = limit C (limit B r)"
  using assms
  by auto

lemma lin_ord_not_empty:
  fixes r :: "'a Preference_Relation"
  assumes "r \<noteq> {}"
  shows "\<not> linear_order_on {} r"
  using assms connex_imp_refl lin_ord_imp_connex
        refl_on_domain subrelI
  by fastforce

lemma lin_ord_singleton:
  fixes a :: "'a"
  shows "\<forall> r. linear_order_on {a} r \<longrightarrow> r = {(a, a)}"
proof (clarify)
  fix r :: "'a Preference_Relation"
  assume lin_ord_r_a: "linear_order_on {a} r"
  hence "a \<preceq>\<^sub>r a"
    using lin_ord_imp_connex singletonI
    unfolding connex_def
    by metis
  moreover from lin_ord_r_a
  have "\<forall> (x, y) \<in> r. x = a \<and> y = a"
    using connex_imp_refl lin_ord_imp_connex
          refl_on_domain split_beta
    by fastforce
  ultimately show "r = {(a, a)}"
    by auto
qed

subsection \<open>Auxiliary Lemmas\<close>

lemma above_trans:
  fixes
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a"
  assumes
    "trans r" and
    "(a, b) \<in> r"
  shows "above r b \<subseteq> above r a"
  using Collect_mono assms transE
  unfolding above_def
  by metis

lemma above_refl:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    "refl_on A r" and
     "a \<in> A"
  shows "a \<in> above r a"
  using assms refl_onD
  unfolding above_def
  by simp

lemma above_subset_geq_one:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    "linear_order_on A r \<and> linear_order_on A s" and
    "above r a \<subseteq> above s a" and
    "above s a = {a}"
  shows "above r a = {a}"
  using assms connex_imp_refl above_refl insert_absorb
        lin_ord_imp_connex mem_Collect_eq refl_on_domain
        singletonI subset_singletonD
  unfolding above_def
  by metis

lemma above_connex:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    "connex A r" and
    "a \<in> A"
  shows "a \<in> above r a"
  using assms connex_imp_refl above_refl
  by metis

lemma pref_imp_in_above:
  fixes
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a"
  shows "a \<preceq>\<^sub>r b \<equiv> b \<in> above r a"
  unfolding above_def
  by simp

lemma limit_presv_above:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a"
  assumes
    "b \<in> above r a" and
    "a \<in> A" and
    "b \<in> A"
  shows "b \<in> above (limit A r) a"
  using assms pref_imp_in_above limit_presv_prefs_1
  by metis

lemma limit_presv_above_2:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a"
  assumes "b \<in> above (limit B r) a"
  shows "b \<in> above r a"
  using assms limit_presv_prefs_2
        mem_Collect_eq pref_imp_in_above
  unfolding above_def
  by metis

lemma above_one:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation"
  assumes
    lin_ord_r: "linear_order_on A r" and
    fin_ne_A: "finite A \<and> A \<noteq> {}"
  shows "\<exists> a \<in> A. above r a = {a} \<and> (\<forall> x \<in> A. above r x = {x} \<longrightarrow> x = a)"
proof -
  obtain n :: nat where
    len_n_plus_one: "n + 1 = card A"
    using Suc_eq_plus1 antisym_conv2 fin_ne_A card_eq_0_iff
          gr0_implies_Suc le0
    by metis
  have
    "(linear_order_on A r \<and> finite A \<and> A \<noteq> {} \<and> n + 1 = card A)
          \<longrightarrow> (\<exists> a. a \<in> A \<and> above r a = {a})"
  proof (induction n arbitrary: A r)
    case 0
    show ?case
    proof (clarify)
      assume
        lin_ord_r: "linear_order_on A r" and
        len_A_is_one: "0 + 1 = card A"
      then obtain a where "{a} = A"
        using card_1_singletonE add.left_neutral
        by metis
      hence "a \<in> A \<and> above r a = {a}"
        using above_def lin_ord_r connex_imp_refl above_refl
              lin_ord_imp_connex refl_on_domain
        by fastforce
      thus "\<exists> a. a \<in> A \<and> above r a = {a}"
        by metis
    qed
  next
    case (Suc n)
    show ?case
    proof (clarify)
      assume
        lin_ord_r: "linear_order_on A r" and
        fin_A: "finite A" and
        A_not_empty: "A \<noteq> {}" and
        len_A_n_plus_one: " Suc n + 1 = card A"
      then obtain B where
        subset_B_card: "card B = n + 1 \<and> B \<subseteq> A"
        using Suc_inject add_Suc card.insert_remove finite.cases
              insert_Diff_single subset_insertI
        by (metis (mono_tags, lifting))
      then obtain a where
        a: "{a} = A - B"
        using Suc_eq_plus1 add_diff_cancel_left' fin_A len_A_n_plus_one
              card_1_singletonE card_Diff_subset finite_subset
        by metis
      have "\<exists> b \<in> B. above (limit B r) b = {b}"
        using subset_B_card Suc.IH add_diff_cancel_left' lin_ord_r card_eq_0_iff
              diff_le_self leD lessI limit_presv_lin_ord
        unfolding One_nat_def
        by metis
      then obtain b where
        alt_b: "above (limit B r) b = {b}"
        by blast
      hence b_above: "{a. (b, a) \<in> limit B r} = {b}"
        unfolding above_def
        by metis
      hence b_pref_b: "b \<preceq>\<^sub>r b"
        using CollectD limit_presv_prefs_2 singletonI
        by (metis (lifting))
      show "\<exists> a. a \<in> A \<and> above r a = {a}"
      proof (cases)
        assume a_pref_r_b: "a \<preceq>\<^sub>r b"
        have refl_A:
          "\<forall> A r a a'. (refl_on A r \<and> (a::'a, a') \<in> r) \<longrightarrow> a \<in> A \<and> a' \<in> A"
          using refl_on_domain
          by metis
        have connex_refl:
          "\<forall> A r. connex (A::'a set) r \<longrightarrow> refl_on A r"
          using connex_imp_refl
          by metis
        have "\<forall> A r. linear_order_on (A::'a set) r \<longrightarrow> connex A r"
          by (simp add: lin_ord_imp_connex)
        hence "refl_on A r"
          using connex_refl lin_ord_r
          by metis
        hence "a \<in> A \<and> b \<in> A"
          using refl_A a_pref_r_b
          by simp
        hence b_in_r: "\<forall> a. a \<in> A \<longrightarrow> (b = a \<or> (b, a) \<in> r \<or> (a, b) \<in> r)"
          using lin_ord_r order_on_defs(3)
          unfolding total_on_def
          by metis
        have b_in_lim_B_r: "(b, b) \<in> limit B r"
          using alt_b mem_Collect_eq singletonI
          unfolding above_def
          by metis
        have b_wins: "{a. (b, a) \<in> limit B r} = {b}"
          using alt_b
          unfolding above_def
          by (metis (no_types))
        have b_refl: "(b, b) \<in> {(a', a). (a', a) \<in> r \<and> a' \<in> B \<and> a \<in> B}"
          using b_in_lim_B_r
          by simp
        moreover have b_wins_B: "\<forall> x \<in> B. b \<in> above r x"
          using subset_B_card b_in_r b_wins b_refl CollectI
                Product_Type.Collect_case_prodD
          unfolding above_def
          by fastforce
        moreover have "b \<in> above r a"
          using a_pref_r_b pref_imp_in_above
          by metis
        ultimately have b_wins: "\<forall> x \<in> A. b \<in> above r x"
          using Diff_iff a empty_iff insert_iff
          by (metis (no_types))
        hence "\<forall> x \<in> A. x \<in> above r b \<longrightarrow> x = b"
          using CollectD lin_ord_r lin_imp_antisym
          unfolding above_def antisym_def
          by metis
        hence "\<forall> x \<in> A. (x \<in> above r b) = (x = b)"
          using b_wins
          by blast
        moreover have above_b_in_A: "above r b \<subseteq> A"
          using lin_ord_r connex_imp_refl lin_ord_imp_connex
                mem_Collect_eq refl_on_domain subsetI
          unfolding above_def
          by metis
        ultimately have "above r b = {b}"
          using alt_b
          unfolding above_def
          by fastforce
        thus ?thesis
          using above_b_in_A
          by blast
      next
        assume "\<not> a \<preceq>\<^sub>r b"
        hence "b \<preceq>\<^sub>r a"
          using subset_B_card DiffE a lin_ord_r alt_b limit_to_limits
                limited_dest singletonI subset_iff
                lin_ord_imp_connex pref_imp_in_above
          unfolding connex_def
          by metis
        hence b_smaller_a: "(b, a) \<in> r"
          by simp
        have lin_ord_subset_A:
          "\<forall> A r A'.
            (linear_order_on (A::'a set) r \<and> A' \<subseteq> A) \<longrightarrow>
              linear_order_on A' (limit A' r)"
          using limit_presv_lin_ord
          by metis
        have "{a. (b, a) \<in> limit B r} = {b}"
          using alt_b
          unfolding above_def
          by metis
        hence b_in_B: "b \<in> B"
          by auto
        have limit_B:
          "partial_order_on B (limit B r) \<and> total_on B (limit B r)"
          using lin_ord_subset_A subset_B_card lin_ord_r
          unfolding order_on_defs(3)
          by metis
        have
          "\<forall> A r.
            total_on A r = (\<forall> a. (a::'a) \<notin> A \<or>
              (\<forall> a'. (a' \<notin> A \<or> a = a') \<or> (a, a') \<in> r \<or> (a', a) \<in> r))"
          unfolding total_on_def
          by metis
        hence "\<forall> a a'. a \<in> B \<longrightarrow> a' \<in> B \<longrightarrow>
                (a = a' \<or> (a, a') \<in> limit B r \<or> (a', a) \<in> limit B r)"
          using limit_B
          by simp
        hence "\<forall> x \<in> B. b \<in> above r x"
          using limit_presv_prefs_2 pref_imp_in_above singletonD mem_Collect_eq
                lin_ord_r alt_b b_above b_pref_b subset_B_card b_in_B
          by (metis (lifting))
        hence "\<forall> x \<in> B. x \<preceq>\<^sub>r b"
          unfolding above_def
          by simp
        hence b_wins: "\<forall> x \<in> B. (x, b) \<in> r"
          by simp
        have "trans r"
          using lin_ord_r lin_imp_trans
          by metis
        hence "\<forall> x \<in> B. (x, a) \<in> r"
          using transE b_smaller_a b_wins
          by metis
        hence "\<forall> x \<in> B. x \<preceq>\<^sub>r a"
          by simp
        hence nothing_above_a: "\<forall> x \<in> A. x \<preceq>\<^sub>r a"
          using a lin_ord_r lin_ord_imp_connex above_connex Diff_iff
                empty_iff insert_iff pref_imp_in_above
          by metis
        have "\<forall> x \<in> A.( x \<in> above r a) = (x = a)"
          using lin_ord_r lin_imp_antisym nothing_above_a pref_imp_in_above CollectD
          unfolding antisym_def above_def
          by metis
        moreover have above_a_in_A: "above r a \<subseteq> A"
          using lin_ord_r connex_imp_refl lin_ord_imp_connex
                mem_Collect_eq refl_on_domain
          unfolding above_def
          by fastforce
        ultimately have "above r a = {a}"
          using a
          unfolding above_def
          by blast
        thus ?thesis
          using above_a_in_A
          by blast
      qed
    qed
  qed
  hence "\<exists> a. a \<in> A \<and> above r a = {a}"
    using fin_ne_A lin_ord_r len_n_plus_one
    by blast
  thus ?thesis
    using assms lin_ord_imp_connex pref_imp_in_above singletonD
    unfolding connex_def
    by metis
qed

lemma above_one_2:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a"
  assumes
    lin_ord: "linear_order_on A r" and
    fin_not_emp: "finite A \<and> A \<noteq> {}" and
    above_a: "above r a = {a}" and
    above_b: "above r b = {b}"
  shows "a = b"
proof -
  have "a \<preceq>\<^sub>r a"
    using above_a singletonI pref_imp_in_above
    by metis
  also have "b \<preceq>\<^sub>r b"
    using above_b singletonI pref_imp_in_above
    by metis
  moreover have
    "\<exists> a \<in> A. above r a = {a} \<and>
      (\<forall> x \<in> A. above r x = {x} \<longrightarrow> x = a)"
    using lin_ord fin_not_emp
    by (simp add: above_one)
  moreover have "connex A r"
    using lin_ord
    by (simp add: lin_ord_imp_connex)
  ultimately show "a = b"
    using above_a above_b limited_dest
    unfolding connex_def
    by metis
qed

lemma rank_one_1:
  fixes
    r :: "'a Preference_Relation" and
    a :: "'a"
  assumes "above r a = {a}"
  shows "rank r a = 1"
  using assms
  by simp

lemma rank_one_2:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    lin_ord: "linear_order_on A r" and
    rank_one: "rank r a = 1"
  shows "above r a = {a}"
proof -
  from lin_ord
  have "refl_on A r"
    using linear_order_on_def partial_order_onD(1)
    by blast
  moreover from lin_ord rank_one
  have "a \<in> A"
    unfolding rank.simps above_def linear_order_on_def
    partial_order_on_def preorder_on_def total_on_def
    using card_1_singletonE insertI1 mem_Collect_eq refl_onD1
    by metis
  ultimately have "a \<in> above r a"
    using above_refl
    by fastforce
  with rank_one
  show "above r a = {a}"
    using card_1_singletonE rank.simps singletonD
    by metis
qed


theorem above_rank:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    a :: "'a"
  assumes "linear_order_on A r"
  shows "(above r a = {a}) = (rank r a = 1)"
  using assms rank_one_1 rank_one_2
  by metis

lemma rank_unique:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a"
  assumes
    lin_ord: "linear_order_on A r" and
    fin_A: "finite A" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    a_neq_b: "a \<noteq> b"
  shows "rank r a \<noteq> rank r b"
proof (unfold rank.simps above_def, clarify)
  assume card_eq: "card {b. (a, b) \<in> r} = card {ba. (b, ba) \<in> r}"
  have r_trans: "trans r"
    using lin_ord lin_imp_trans
    by metis
  have r_total: "\<forall> x \<in> A. \<forall> y \<in> A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
    using lin_ord
    unfolding linear_order_on_def total_on_def
    by metis
  have sets_eq: "{a'. (a, a') \<in> r} = {b'. (b, b') \<in> r}"
    using card_subset_eq connex_imp_refl lin_ord lin_ord_imp_connex mem_Collect_eq
          refl_on_domain rev_finite_subset subset_eq transE
    using card_eq fin_A r_trans r_total
    by (smt (verit, best))
  hence "(b, a) \<in> r"
    using a_in_A above_connex lin_ord lin_ord_imp_connex
    unfolding above_def
    by fastforce
  hence "(a, b) \<notin> r"
    using lin_ord lin_imp_antisym a_neq_b antisymD
    by metis
  hence "b \<notin> A"
    using lin_ord partial_order_onD(1) sets_eq
    unfolding linear_order_on_def refl_on_def
    by blast
  thus "False"
    using b_in_A
    by presburger
qed

lemma above_presv_limit:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    x :: "'a"
  shows "above (limit A r) x \<subseteq> A"
  unfolding above_def
  by auto

subsection \<open>Lifting Property\<close>

definition equiv_rel_except_a :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                                    'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv_rel_except_a A r s a \<equiv>
    linear_order_on A r \<and> linear_order_on A s \<and> a \<in> A \<and>
    (\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}. (x \<preceq>\<^sub>r y) = (x \<preceq>\<^sub>s y))"

definition lifted :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                        'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A r s a \<equiv>
    equiv_rel_except_a A r s a \<and> (\<exists> x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)"

lemma trivial_equiv_rel:
  fixes
    A :: "'a set" and
    p :: "'a Preference_Relation"
  assumes "linear_order_on A p"
  shows "\<forall> a \<in> A. equiv_rel_except_a A p p a"
  unfolding equiv_rel_except_a_def
  using assms
  by simp

lemma lifted_imp_equiv_rel_except_a:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes "lifted A r s a"
  shows "equiv_rel_except_a A r s a"
  using assms
  unfolding lifted_def equiv_rel_except_a_def
  by simp

lemma lifted_mono:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes "lifted A r s a"
  shows "\<forall> x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x)"
proof (safe)
  fix x :: "'a"
  assume
    x_in_A:   "x \<in> A" and
    x_exist:  "x \<notin> {}" and
    x_neq_a:  "x \<noteq> a" and
    x_pref_a: "x \<preceq>\<^sub>r a" and
    a_pref_x: "a \<preceq>\<^sub>s x"
  hence x_pref_a_rel: "(x, a) \<in> r"
    by simp
  have a_pref_x_rel: "(a, x) \<in> s"
    using a_pref_x
    by simp
  from assms
  have "antisym r"
    using lifted_imp_equiv_rel_except_a lin_imp_antisym
    unfolding equiv_rel_except_a_def
    by metis
  hence "(\<forall> x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y)"
    unfolding antisym_def
    by metis
  hence imp_x_eq_a: "\<lbrakk>(x, a) \<in> r; (a, x) \<in> r\<rbrakk> \<Longrightarrow> x = a"
    by simp
  from assms
  have "\<exists> x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a"
    unfolding lifted_def
    by metis
  then obtain y :: 'a where
    "y \<in> A - {a} \<and> a \<preceq>\<^sub>r y \<and> y \<preceq>\<^sub>s a"
    by metis
  hence y_eq_r_s_exc_a:
    "y \<in> A - {a} \<and> (a, y) \<in> r \<and> (y, a) \<in> s"
    by simp
  from assms
  have equiv_r_s_exc_a: "equiv_rel_except_a A r s a"
    unfolding lifted_def
    by metis
  hence "\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}. (x \<preceq>\<^sub>r y) = (x \<preceq>\<^sub>s y)"
    unfolding equiv_rel_except_a_def
    by metis
  hence equiv_r_s_exc_a_rel:
    "\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}. ((x, y) \<in> r) = ((x, y) \<in> s)"
    by simp
  from equiv_r_s_exc_a
  have "\<forall> x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
    unfolding equiv_rel_except_a_def linear_order_on_def
              partial_order_on_def preorder_on_def trans_def
    by metis
  with x_in_A x_neq_a x_pref_a_rel y_eq_r_s_exc_a equiv_r_s_exc_a equiv_r_s_exc_a_rel
  have "(x, y) \<in> s"
    using insertE insert_Diff
    unfolding equiv_rel_except_a_def
    by metis
  with a_pref_x_rel x_pref_a_rel imp_x_eq_a x_neq_a equiv_r_s_exc_a
  have "(a, y) \<in> s"
    using lin_imp_trans transE
    unfolding equiv_rel_except_a_def
    by metis
  with y_eq_r_s_exc_a equiv_r_s_exc_a
  show False
    using antisymD DiffD2 lin_imp_antisym singletonI
    unfolding equiv_rel_except_a_def
    by metis
qed

lemma lifted_mono2:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    lifted: "lifted A r s a" and
    x_pref_a: "x \<preceq>\<^sub>r a"
  shows "x \<preceq>\<^sub>s a"
proof (simp)
  have x_pref_a_rel: "(x, a) \<in> r"
    using x_pref_a
    by simp
  with lifted
  have x_in_A: "x \<in> A"
    using connex_imp_refl lin_ord_imp_connex refl_on_domain
    unfolding equiv_rel_except_a_def lifted_def
    by metis
  have "\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}. (x \<preceq>\<^sub>r y) = (x \<preceq>\<^sub>s y)"
    using lifted
    unfolding lifted_def equiv_rel_except_a_def
    by metis
  hence rest_eq:
    "\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}. ((x, y) \<in> r) = ((x, y) \<in> s)"
    by simp
  have "\<exists> x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a"
    using lifted
    unfolding lifted_def
    by metis
  hence ex_lifted: "\<exists> x \<in> A - {a}. (a, x) \<in> r \<and> (x, a) \<in> s"
    by simp
  show "(x, a) \<in> s"
  proof (cases "x = a")
    case True
    thus ?thesis
      using connex_imp_refl refl_onD lifted lin_ord_imp_connex
      unfolding equiv_rel_except_a_def lifted_def
      by metis
  next
    case False
    thus ?thesis
      using x_pref_a_rel x_in_A rest_eq ex_lifted insertE insert_Diff
            lifted lin_imp_trans lifted_imp_equiv_rel_except_a
      unfolding equiv_rel_except_a_def trans_def
      by metis
  qed
qed

lemma lifted_above:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes "lifted A r s a"
  shows "above s a \<subseteq> above r a"
proof (unfold above_def, safe)
  fix x :: "'a"
  assume a_pref_x: "(a, x) \<in> s"
  from assms
  have "\<exists> x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a"
    unfolding lifted_def
    by metis
  hence lifted_r: "\<exists> x \<in> A - {a}. (a, x) \<in> r \<and> (x, a) \<in> s"
    by simp
  from assms
  have "\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}. (x \<preceq>\<^sub>r y) = (x \<preceq>\<^sub>s y)"
    unfolding lifted_def equiv_rel_except_a_def
    by metis
  hence rest_eq: "\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}. ((x, y) \<in> r) = ((x, y) \<in> s)"
    by simp
  from assms
  have trans_r: "\<forall> x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
    using lin_imp_trans
    unfolding trans_def lifted_def equiv_rel_except_a_def
    by metis
  from assms
  have trans_s: "\<forall> x y z. (x, y) \<in> s \<longrightarrow> (y, z) \<in> s \<longrightarrow> (x, z) \<in> s"
    using lin_imp_trans
    unfolding trans_def lifted_def equiv_rel_except_a_def
    by metis
  from assms
  have refl_r: "(a, a) \<in> r"
    using connex_imp_refl lin_ord_imp_connex refl_onD
    unfolding equiv_rel_except_a_def lifted_def
    by metis
  from a_pref_x assms
  have "x \<in> A"
    using connex_imp_refl lin_ord_imp_connex refl_onD2
    unfolding equiv_rel_except_a_def lifted_def
    by metis
  with a_pref_x lifted_r rest_eq trans_r trans_s refl_r
  show "(a, x) \<in> r"
    using Diff_iff singletonD
    by (metis (full_types))
qed

lemma lifted_above_2:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a" and
    x :: "'a"
  assumes
    lifted_a: "lifted A r s a" and
    x_in_A_sub_a: "x \<in> A - {a}"
  shows "above r x \<subseteq> above s x \<union> {a}"
proof (safe, simp)
  fix y :: "'a"
  assume
    y_in_above_r: "y \<in> above r x" and
    y_not_in_above_s: "y \<notin> above s x"
  have "\<forall> z \<in> A - {a}. (x \<preceq>\<^sub>r z) = (x \<preceq>\<^sub>s z)"
    using x_in_A_sub_a lifted_a
    unfolding lifted_def equiv_rel_except_a_def
    by metis
  hence "\<forall> z \<in> A - {a}. (z \<in> above r x) = (z \<in> above s x)"
    unfolding above_def
    by simp
  hence "(y \<in> above r x) = (y \<in> above s x)"
    using lifted_a y_not_in_above_s lifted_mono2 limited_dest lifted_def
          lin_ord_imp_connex member_remove pref_imp_in_above
    unfolding equiv_rel_except_a_def remove_def connex_def
    by metis
  thus "y = a"
    using y_in_above_r y_not_in_above_s
    by simp
qed

lemma limit_lifted_imp_eq_or_lifted:
  fixes
    A :: "'a set" and
    S :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    lifted: "lifted S r s a" and
    subset: "A \<subseteq> S"
  shows "limit A r = limit A s \<or> lifted A (limit A r) (limit A s) a"
proof -
  have "\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}. (x \<preceq>\<^sub>r y) = (x \<preceq>\<^sub>s y)"
    using lifted subset
    unfolding lifted_def equiv_rel_except_a_def
    by auto
  hence eql_rs:
      "\<forall> x \<in> A - {a}. \<forall> y \<in> A - {a}.
      ((x, y) \<in> (limit A r)) = ((x, y) \<in> (limit A s))"
    using DiffD1 limit_presv_prefs_1 limit_presv_prefs_2
    by simp
  have lin_ord_r_s: "linear_order_on A (limit A r) \<and> linear_order_on A (limit A s)"
    using lifted subset lifted_def equiv_rel_except_a_def limit_presv_lin_ord
    by metis
  show ?thesis
  proof (cases)
    assume a_in_A: "a \<in> A"
    thus ?thesis
    proof (cases)
      assume "\<exists> x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a"
      hence
        "\<exists> x \<in> A - {a}. (let q = limit A r in a \<preceq>\<^sub>q x) \<and>
            (let u = limit A s in x \<preceq>\<^sub>u a)"
        using DiffD1 limit_presv_prefs_1 a_in_A
        by simp
      thus ?thesis
        using a_in_A eql_rs lin_ord_r_s
        unfolding lifted_def equiv_rel_except_a_def
        by simp
    next
      assume "\<not>(\<exists> x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)"
      hence strict_pref_to_a: "\<forall> x \<in> A - {a}. \<not>(a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)"
        by simp
      moreover have not_worse: "\<forall> x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x)"
        using lifted subset lifted_mono
        by fastforce
      moreover have connex: "connex A (limit A r) \<and> connex A (limit A s)"
        using lifted subset limit_presv_lin_ord lin_ord_imp_connex
        unfolding lifted_def equiv_rel_except_a_def
        by metis
      moreover have
        "\<forall> A r. connex A r =
          (limited A r \<and>
            (\<forall> a a'. (a::'a) \<in> A \<longrightarrow> a' \<in> A \<longrightarrow> (a \<preceq>\<^sub>r a' \<or> a' \<preceq>\<^sub>r a)))"
        unfolding connex_def
        by (simp add: Ball_def_raw)
      hence limit_rel_r:
        "limited A (limit A r) \<and>
          (\<forall> a a'. a \<in> A \<and> a' \<in> A \<longrightarrow> ((a, a') \<in> limit A r \<or> (a', a) \<in> limit A r))"
        using connex
        by simp
      have limit_imp_rel: "\<forall> a a' A r. (a::'a, a') \<in> limit A r \<longrightarrow> a \<preceq>\<^sub>r a'"
        using limit_presv_prefs_2
        by metis
      have limit_rel_s:
        "limited A (limit A s) \<and>
          (\<forall> a a'. a \<in> A \<and> a' \<in> A \<longrightarrow> ((a, a') \<in> limit A s \<or> (a', a) \<in> limit A s))"
        using connex
        unfolding connex_def
        by simp
      ultimately have "\<forall> x \<in> A - {a}. (a \<preceq>\<^sub>r x \<and> a \<preceq>\<^sub>s x) \<or> (x \<preceq>\<^sub>r a \<and> x \<preceq>\<^sub>s a)"
        using DiffD1 limit_rel_r limit_presv_prefs_2 a_in_A
        by metis
      have "\<forall> x \<in> A - {a}. ((a, x) \<in> (limit A r)) = ((a, x) \<in> (limit A s))"
        using DiffD1 limit_imp_rel limit_rel_r limit_rel_s a_in_A strict_pref_to_a not_worse
        by metis
      hence
        "\<forall> x \<in> A - {a}.
          (let q = limit A r in a \<preceq>\<^sub>q x) = (let q = limit A s in a \<preceq>\<^sub>q x)"
        by simp
      moreover have "\<forall> x \<in> A - {a}. ((x, a) \<in> (limit A r)) = ((x, a) \<in> (limit A s))"
        using a_in_A strict_pref_to_a not_worse DiffD1 limit_presv_prefs_2 limit_rel_s limit_rel_r
        by metis
      moreover have "(a, a) \<in> (limit A r) \<and> (a, a) \<in> (limit A s)"
        using a_in_A connex connex_imp_refl refl_onD
        by metis
      ultimately show ?thesis
        using eql_rs
        by auto
    qed
  next
    assume "a \<notin> A"
    thus ?thesis
      using limit_to_limits limited_dest subrelI subset_antisym eql_rs
      by auto
  qed
qed

lemma negl_diff_imp_eq_limit:
  fixes
    S :: "'a set" and
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    change: "equiv_rel_except_a S r s a" and
    subset: "A \<subseteq> S" and
    not_in_A: "a \<notin> A"
  shows "limit A r = limit A s"
proof -
  have "A \<subseteq> S - {a}"
    unfolding subset_Diff_insert
    using not_in_A subset
    by simp
  hence "\<forall> x \<in> A. \<forall> y \<in> A. (x \<preceq>\<^sub>r y) = (x \<preceq>\<^sub>s y)"
    using change in_mono
    unfolding equiv_rel_except_a_def
    by metis
  thus ?thesis
    by auto
qed

theorem lifted_above_winner:
  fixes
    X :: "'a set" and
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    lifted_a: "lifted A r s a" and
    above_x: "above r x = {x}" and
    fin_A: "finite A"
  shows "above s x = {x} \<or> above s a = {a}"
proof (cases)
  assume "x = a"
  thus ?thesis
    using above_subset_geq_one lifted_a above_x lifted_above
    unfolding lifted_def equiv_rel_except_a_def
    by metis
next
  assume x_neq_a: "x \<noteq> a"
  thus ?thesis
  proof (cases)
    assume "above s x = {x}"
    thus ?thesis
      by simp
  next
    assume x_not_above: "above s x \<noteq> {x}"
    have "\<forall> y \<in> A. y \<preceq>\<^sub>r x"
    proof (safe)
      fix y :: "'a"
      assume y_in_A: "y \<in> A"
      hence "A \<noteq> {}"
        by blast
      moreover have "linear_order_on A r"
        using lifted_a
        unfolding equiv_rel_except_a_def lifted_def
        by simp
      ultimately show "y \<preceq>\<^sub>r x"
        using fin_A y_in_A above_one above_one_2 above_x lin_ord_imp_connex
              pref_imp_in_above singletonD
        unfolding connex_def
        by (metis (no_types))
    qed
    moreover have "equiv_rel_except_a A r s a"
      using lifted_a
      unfolding lifted_def
      by metis
    moreover have "x \<in> A - {a}"
      using above_one above_one_2 x_neq_a assms calculation
            insert_not_empty member_remove insert_absorb
      unfolding equiv_rel_except_a_def remove_def
      by metis
    ultimately have "\<forall> y \<in> A - {a}. y \<preceq>\<^sub>s x"
      using DiffD1 lifted_a
      unfolding equiv_rel_except_a_def
      by metis
    hence "\<forall> y \<in> A - {a}. above s y \<noteq> {y}"
      using x_not_above empty_iff insert_iff pref_imp_in_above
      by metis
    hence "above s a = {a}"
      using Diff_iff all_not_in_conv lifted_a fin_A above_one singleton_iff
      unfolding lifted_def equiv_rel_except_a_def
      by metis
    thus "above s x = {x} \<or> above s a = {a}"
      by simp
  qed
qed

theorem lifted_above_winner_2:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a"
  assumes
    "lifted A r s a" and
    "above r a = {a}" and
    "finite A"
  shows "above s a = {a}"
  using assms lifted_above_winner
  by metis

theorem lifted_above_winner_3:
  fixes
    A :: "'a set" and
    r :: "'a Preference_Relation" and
    s :: "'a Preference_Relation" and
    a :: "'a" and
    x :: "'a"
  assumes
    lifted_a: "lifted A r s a" and
    above_x: "above s x = {x}" and
    fin_A: "finite A" and
    x_not_a: "x \<noteq> a"
  shows "above r x = {x}"
proof (rule ccontr)
  assume not_above_x: "above r x \<noteq> {x}"
  then obtain y where
    y: "above r y = {y}"
    using lifted_a fin_A insert_Diff insert_not_empty above_one
    unfolding lifted_def equiv_rel_except_a_def
    by metis
  hence "above s y = {y} \<or> above s a = {a}"
    using lifted_a fin_A lifted_above_winner
    by metis
  moreover have "\<forall> b. above s b = {b} \<longrightarrow> b = x"
    using all_not_in_conv lifted_a above_x fin_A above_one_2
    unfolding lifted_def equiv_rel_except_a_def
    by metis
  ultimately have "y = x"
    using x_not_a
    by presburger
  moreover have "y \<noteq> x"
    using not_above_x y
    by blast
  ultimately show False
    by simp
qed

end

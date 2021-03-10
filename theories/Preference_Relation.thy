(*  File:       Preference_Relation.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Preference Relation\<close>

theory Preference_Relation
  imports Main
begin

text
\<open>The very core of the composable modules voting framework:
Types and functions, derivations, lemmata, operations on profiles, etc.\<close>

subsection \<open>Definition\<close>

(*
  Each voter expresses pairwise relations between all alternatives,
  thereby inducing a linear order.
*)
type_synonym 'a Preference_Relation = "'a rel"

fun is_less_preferred_than ::
  "'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<preceq>\<^sub>_ _" [50, 1000, 51] 50) where
    "x \<preceq>\<^sub>r y \<longleftrightarrow> (x, y) \<in> r"

lemma lin_imp_antisym:
  assumes "linear_order_on A r"
  shows "antisym r"
  using assms linear_order_on_def partial_order_on_def
  by auto

lemma lin_imp_trans:
  assumes "linear_order_on A r"
  shows "trans r"
  using assms order_on_defs
  by blast

subsection \<open>Ranking\<close>

fun rank :: "'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank r x = card (above r x)"

lemma rank_gt_zero:
  assumes
    refl: "x \<preceq>\<^sub>r x" and
    fin:  "finite r"
  shows "rank r x \<ge> 1"
proof -
  have "x \<in> {y \<in> Field r. (x, y) \<in> r}"
    using FieldI2 local.refl
    by fastforce
  hence "{y \<in> Field r. (x, y) \<in> r} \<noteq> {}"
    by blast
  hence "card {y \<in> Field r. (x, y) \<in> r} \<noteq> 0"
    by (simp add: fin finite_Field)
  moreover have "card{y \<in> Field r. (x, y) \<in> r} \<ge> 0"
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
  "(\<And>x y. \<lbrakk> x \<preceq>\<^sub>r y \<rbrakk> \<Longrightarrow>  x \<in> A \<and> y \<in> A) \<Longrightarrow> limited A r"
  unfolding limited_def
  by auto

lemma limited_dest:
  "(\<And>x y. \<lbrakk> x \<preceq>\<^sub>r y; limited A r \<rbrakk> \<Longrightarrow>  x \<in> A \<and> y \<in> A)"
  unfolding limited_def
  by auto

fun limit :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
  "limit A r = {(a, b) \<in> r. a \<in> A \<and> b \<in> A}"

definition connex :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "connex A r \<equiv> limited A r \<and> (\<forall>x \<in> A. \<forall>y \<in> A. x \<preceq>\<^sub>r y \<or> y \<preceq>\<^sub>r x)"

lemma connex_imp_refl:
  assumes "connex A r"
  shows "refl_on A r"
  using assms connex_def limited_def refl_on_def
        is_less_preferred_than.simps
  by metis

lemma lin_ord_imp_connex:
  assumes "linear_order_on A r"
  shows "connex A r"
  using assms connex_def limited_def linear_order_on_def
        partial_order_on_def preorder_on_def refl_on_def
        total_on_def is_less_preferred_than.simps
  by (smt (verit, del_insts))

lemma connex_antsym_and_trans_imp_lin_ord:
  assumes
    "connex A r" and
    "antisym r" and
    "trans r"
  shows "linear_order_on A r"
  using assms connex_imp_refl connex_def order_on_defs(1)
        order_on_defs(2) order_on_defs(3) total_on_def
        is_less_preferred_than.simps
  by metis

lemma limit_to_limits: "limited A (limit A r)"
  using CollectD case_prodD limit.simps limitedI
        is_less_preferred_than.simps
  by (metis (no_types, lifting))

lemma limit_presv_connex:
  assumes
    connex: "connex S r" and
    subset: "A \<subseteq> S"
  shows "connex A (limit A r)"
  using CollectI Product_Type.Collect_case_prodD assms case_prod_conv
        connex_def limited_def fst_conv limit.simps mem_Sigma_iff snd_conv
        subrelI subset_eq mem_Collect_eq is_less_preferred_than.simps
  by (smt (verit, del_insts))

lemma limit_presv_antisym:
  assumes
    antisymmetric: "antisym r" and
    subset: "A \<subseteq> S"
  shows "antisym (limit A r)"
  using antisym_def antisymmetric
  by auto

lemma limit_presv_trans:
  assumes
    transitive: "trans r" and
    subset:     "A \<subseteq> S"
  shows "trans (limit A r)"
  using Product_Type.Collect_case_prodD case_prodI fst_conv
        limit.simps local.transitive mem_Collect_eq snd_conv
        trans_def
  by (smt (verit, ccfv_threshold))

lemma limit_presv_lin_ord:
  assumes
    "linear_order_on S r" and
      "A \<subseteq> S"
    shows "linear_order_on A (limit A r)"
  using assms connex_antsym_and_trans_imp_lin_ord
            limit_presv_antisym limit_presv_connex
            limit_presv_trans lin_ord_imp_connex
            order_on_defs(1) order_on_defs(2)
            order_on_defs(3)
  by metis

lemma limit_presv_prefs1:
  assumes
    x_less_y: "x \<preceq>\<^sub>r y" and
    x_in_A: "x \<in> A" and
    y_in_A: "y \<in> A"
  shows "let s = limit A r in x \<preceq>\<^sub>s y"
  using is_less_preferred_than.simps
        x_in_A x_less_y y_in_A
  by simp

lemma limit_presv_prefs2:
  assumes x_less_y: "(x, y) \<in> limit A r"
  shows "x \<preceq>\<^sub>r y"
  using limit.simps mem_Collect_eq x_less_y
  by auto

lemma limit_trans:
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B" and
    "linear_order_on A r"
  shows "limit C r = limit C (limit B r)"
  using assms
  by auto

lemma lin_ord_not_empty:
  assumes "r \<noteq> {}"
  shows "\<not> linear_order_on {} r"
  using assms connex_imp_refl lin_ord_imp_connex
        refl_on_domain subrelI
  by fastforce

lemma lin_ord_singleton:
  "\<forall>r. linear_order_on {a} r \<longrightarrow> r = {(a, a)}"
proof
  fix r
  show "linear_order_on {a} r \<longrightarrow> r = {(a, a)}"
  proof
    assume asm: "linear_order_on {a} r"
    hence "a \<preceq>\<^sub>r a"
      using connex_def lin_ord_imp_connex singletonI
      by metis
    moreover have "\<forall>(x, y) \<in> r. x = a \<and> y = a"
      using asm connex_imp_refl lin_ord_imp_connex
            refl_on_domain split_beta
      by fastforce
    ultimately show "r = {(a, a)}"
      using is_less_preferred_than.elims(2)
      by auto
  qed
qed

subsection \<open>Auxiliary Lemmata\<close>

lemma above_trans:
  assumes
    "trans r" and
    "(a, b) \<in> r"
  shows "above r b \<subseteq> above r a"
  using Collect_mono above_def assms transE
  by metis

lemma above_refl:
  assumes
    "refl_on A r" and
     "a \<in> A"
  shows "a \<in> above r a"
  using above_def assms refl_onD
  by fastforce

lemma above_subset_geq_one:
  assumes
    "linear_order_on A r \<and> linear_order_on A s" and
    "above r a \<subseteq> above s a" and
    "above s a = {a}"
  shows "above r a = {a}"
  using above_def assms connex_imp_refl above_refl insert_absorb
        lin_ord_imp_connex mem_Collect_eq refl_on_domain
        singletonI subset_singletonD
  by metis

lemma above_connex:
  assumes
    "connex A r" and
    "a \<in> A"
  shows "a \<in> above r a"
  using assms connex_imp_refl above_refl
  by metis

lemma pref_imp_in_above: "a \<preceq>\<^sub>r b \<longleftrightarrow> b \<in> above r a"
  by (simp add: above_def)

lemma limit_presv_above:
  assumes
    "b \<in> above r a" and
    (*"linear_order_on A r" and
    "B \<subseteq> A" and ??? *)
    "a \<in> B \<and> b \<in> B"
  shows "b \<in> above (limit B r) a"
  using pref_imp_in_above assms limit_presv_prefs1
  by metis

lemma limit_presv_above2:
  assumes
    "b \<in> above (limit B r) a" and
    "linear_order_on A r" and
    "B \<subseteq> A" and
    "a \<in> B" and 
    "b \<in> B"
  shows "b \<in> above r a"
  using above_def assms(1) limit_presv_prefs2
        mem_Collect_eq is_less_preferred_than.simps
  by metis

lemma above_one:
  assumes
    "linear_order_on A r" and
    "finite A \<and> A \<noteq> {}"
  shows "\<exists>a\<in>A. above r a = {a} \<and> (\<forall>x\<in>A. above r x = {x} \<longrightarrow> x = a)"
proof -
  obtain n::nat where n: "n+1 = card A"
    using Suc_eq_plus1 antisym_conv2 assms(2) card_eq_0_iff
          gr0_implies_Suc le0
    by metis
  have
    "(linear_order_on A r \<and> finite A \<and> A \<noteq> {} \<and> n+1 = card A)
          \<longrightarrow> (\<exists>a. a\<in>A \<and> above r a = {a})"
  proof (induction n arbitrary: A r)
    case 0
    show ?case
    proof
      assume asm: "linear_order_on A r \<and> finite A \<and> A \<noteq> {} \<and> 0+1 = card A"
      then obtain a where "{a} = A"
        using card_1_singletonE add.left_neutral
        by metis
      hence "a \<in> A \<and> above r a = {a}"
        using above_def asm connex_imp_refl above_refl
              lin_ord_imp_connex refl_on_domain
        by fastforce
      thus "\<exists>a. a\<in>A \<and> above r a = {a}"
        by auto
    qed
  next
    case (Suc n)
    show ?case
    proof
      assume asm:
        "linear_order_on A r \<and> finite A \<and> A \<noteq> {} \<and> Suc n+1 = card A"
      then obtain B where B: "card B = n+1 \<and> B \<subseteq> A"
        using Suc_inject add_Suc card.insert_remove finite.cases
              insert_Diff_single subset_insertI
        by (metis (mono_tags, lifting))
      then obtain a where a: "{a} = A - B"
        using Suc_eq_plus1 add_diff_cancel_left' asm card_1_singletonE
              card_Diff_subset finite_subset
        by metis
      have "\<exists>b\<in>B. above (limit B r) b = {b}"
        using B One_nat_def Suc.IH add_diff_cancel_left' asm
              card_eq_0_iff diff_le_self finite_subset leD lessI
              limit_presv_lin_ord
        by metis
      then obtain b where b: "above (limit B r) b = {b}"
        by blast
      show "\<exists>a. a \<in> A \<and> above r a = {a}"
      proof cases
        assume "a \<preceq>\<^sub>r b"
        moreover have "\<forall>x \<in> B. b \<in> above r x"
          using B pref_imp_in_above asm b connex_imp_refl
                limit_presv_lin_ord lin_ord_imp_connex
                order_on_defs(3) refl_on_domain singletonD singletonI
                total_on_def limit_presv_above2 is_less_preferred_than.simps
          by (smt (verit, ccfv_threshold))
        ultimately have b_wins: "\<forall>x \<in> A. b \<in> above r x"
          using a pref_imp_in_above Diff_iff empty_iff insert_iff
          by metis
        hence "\<forall>x \<in> A. x \<in> above r b \<longrightarrow> x = b"
          using CollectD above_def antisym_def asm lin_imp_antisym
          by metis
        hence "\<forall>x \<in> A. x \<in> above r b \<longleftrightarrow> x = b"
          using b_wins
          by blast
        moreover have above_b_in_A: "above r b \<subseteq> A"
          using above_def asm connex_imp_refl lin_ord_imp_connex
                mem_Collect_eq refl_on_domain subsetI
          by metis
        ultimately have "above r b = {b}"
          using above_def b
          by fastforce
        thus ?thesis
          using above_b_in_A
          by blast
      next
        assume "\<not>a \<preceq>\<^sub>r b"
        hence b_smaller_a: "b \<preceq>\<^sub>r a"
          using B DiffE a asm b limit_to_limits connex_def
                limited_dest singletonI subset_iff
                lin_ord_imp_connex pref_imp_in_above
          by metis
        have "\<forall>x \<in> B. b \<in> above r x"
          using limit_presv_above2 B pref_imp_in_above asm b
                connex_imp_refl limit_presv_lin_ord lin_ord_imp_connex
                order_on_defs(3) refl_on_domain singletonD singletonI
                total_on_def is_less_preferred_than.simps
          by (smt (verit, ccfv_threshold))
        hence "\<forall>x \<in> B. x \<preceq>\<^sub>r b"
          by (simp add: above_def)
        hence "\<forall>x \<in> B. x \<preceq>\<^sub>r a"
          using b_smaller_a lin_imp_trans asm transE
                is_less_preferred_than.elims(2)
                is_less_preferred_than.elims(3)
          by metis
        hence nothing_above_a: "\<forall>x \<in> A. x \<preceq>\<^sub>r a"
          using a asm lin_ord_imp_connex above_connex Diff_iff
                empty_iff insert_iff pref_imp_in_above
          by metis
        have "\<forall>x \<in> A. x \<in> above r a \<longleftrightarrow> x = a"
          using antisym_def asm lin_imp_antisym
                nothing_above_a pref_imp_in_above
                is_less_preferred_than.simps
          by metis
        moreover have above_a_in_A: "above r a \<subseteq> A"
          using above_def asm connex_imp_refl lin_ord_imp_connex
                mem_Collect_eq refl_on_domain
          by fastforce
        ultimately have "above r a = {a}"
          using above_def a
          by auto
        thus ?thesis
          using above_a_in_A
          by blast
      qed
    qed
  qed
  hence "\<exists>a. a\<in>A \<and> above r a = {a}"
    using assms n
    by blast
  thus ?thesis
    using Diff_eq_empty_iff above_trans assms(1) empty_Diff insertE
          insert_Diff_if insert_absorb insert_not_empty order_on_defs(1)
          order_on_defs(2) order_on_defs(3) total_on_def
    by (smt (verit, ccfv_SIG))
qed

lemma above_one2:
  assumes
    "linear_order_on A r" and
    "finite A \<and> A \<noteq> {}" and
    "above r a = {a} \<and> above r b = {b}"
  shows "a = b"
  using pref_imp_in_above assms(1) assms(2)
        assms(3) connex_imp_refl insert_iff above_one
        lin_ord_imp_connex refl_on_domain subsetI subset_antisym
        is_less_preferred_than.simps
  by (smt (verit, ccfv_SIG))

lemma above_presv_limit:
  assumes "linear_order r"
  shows "above (limit A r) x \<subseteq> A"
  using CollectD above_def assms subset_iff
        subsetI limit_to_limits limited_dest
        is_less_preferred_than.simps
  by (metis (mono_tags, lifting))

subsection \<open>Lifting Property\<close>

definition equiv_rel_except_a :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                                    'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv_rel_except_a A r s a \<equiv>
    linear_order_on A r \<and> linear_order_on A s \<and> a \<in> A \<and>
    (\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y)"

definition lifted :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                        'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A r s a \<equiv>
    equiv_rel_except_a A r s a \<and> (\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)"

lemma trivial_equiv_rel:
  assumes order: "linear_order_on A p"
  shows "\<forall>a \<in> A. equiv_rel_except_a A p p a"
  by (simp add: equiv_rel_except_a_def order)

lemma lifted_imp_equiv_rel_except_a:
  assumes lifted: "lifted A r s a"
  shows "equiv_rel_except_a A r s a"
proof -
  from lifted have
    "linear_order_on A r \<and> linear_order_on A s \<and> a \<in> A \<and>
      (\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y)"
    by (simp add: lifted_def equiv_rel_except_a_def)
  thus ?thesis
    by (simp add: equiv_rel_except_a_def)
qed

lemma lifted_mono:
  assumes lifted: "lifted A r s a"
  shows "\<forall>x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x)"
proof (rule ccontr)
  assume a_not: "\<not>(\<forall>x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x))"
  then obtain x::"'a" where x: "x \<in> A - {a} \<and> x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x"
    by blast
  from lifted obtain y::"'a" where y: "y \<in> A - {a} \<and> a \<preceq>\<^sub>r y \<and> y \<preceq>\<^sub>s a"
    using lifted_def
    by metis
  from x have "a \<preceq>\<^sub>s x"
    by auto
  moreover from lifted x y have "x \<preceq>\<^sub>s y"
    using lifted_def equiv_rel_except_a_def linear_order_on_def
          partial_order_on_def preorder_on_def transE
          is_less_preferred_than.simps
    by metis
  moreover from lifted have "trans s"
    by (simp add: lifted_def equiv_rel_except_a_def order_on_defs)
  ultimately have "a \<preceq>\<^sub>s y"
    using transE is_less_preferred_than.simps
    by metis
  moreover from y have "y \<noteq> a \<and> y \<preceq>\<^sub>s a"
    by auto
  moreover from lifted have "antisym s"
    by (simp add: lifted_def equiv_rel_except_a_def
                  linear_order_on_def partial_order_on_def)
  ultimately show "False"
    using antisymD is_less_preferred_than.simps
    by metis
qed

lemma lifted_mono2:
  assumes lifted: "lifted A r s a"
  shows "x \<preceq>\<^sub>r a \<longrightarrow> x \<preceq>\<^sub>s a"
proof -
  {
    assume "x \<noteq> a"
    moreover
    {
      assume "x \<in> A \<and> x \<noteq> a"
      moreover
      {
        assume "x \<in> A \<and> a \<preceq>\<^sub>s x \<and> x \<noteq> a"
        hence "x \<in> A - {a} \<and> a \<preceq>\<^sub>s x"
          using Diff_iff singleton_iff
          by blast
        hence ?thesis
          using lifted lifted_mono
          by metis
      }
      ultimately have ?thesis
        using lifted lifted_def equiv_rel_except_a_def
              linear_order_on_def total_on_def
              is_less_preferred_than.simps
        by metis
    }
    ultimately have ?thesis
      using lifted lifted_def equiv_rel_except_a_def linear_order_on_def
            order_on_defs(1) order_on_defs(2) order_on_defs(3)
            refl_on_domain is_less_preferred_than.simps
      by metis
  }
  thus ?thesis
    using lifted lifted_def equiv_rel_except_a_def
          linear_order_on_def order_on_defs(1)
          order_on_defs(2) order_on_defs(3)
          refl_onD is_less_preferred_than.simps
    by metis
qed

lemma lifted_above:
  assumes "lifted A r s a"
  shows "above s a \<subseteq> above r a"
proof -
  have "\<not>(\<exists>x \<in> A. x \<in> above s a \<and> x \<notin> above r a)"
  proof -
    {
      fix aa :: 'a
      {
        assume "aa \<noteq> a"
        moreover
        {
          assume "aa \<preceq>\<^sub>r a \<and> aa \<noteq> a"
          hence "(a, aa) \<notin> s"
            using antisym_def assms lifted_def equiv_rel_except_a_def
                  lifted_mono2 linear_order_on_def partial_order_on_def
                  is_less_preferred_than.simps
            by metis
          hence "aa \<notin> A \<or> aa \<notin> above s a \<or> aa \<in> above r a"
            by (simp add: above_def)
        }
        ultimately have "(aa \<notin> A \<or> aa \<notin> above s a \<or> aa \<in> above r a) \<or> a \<preceq>\<^sub>r aa"
          using assms lifted_def equiv_rel_except_a_def
                linear_order_on_def total_on_def
                is_less_preferred_than.simps
          by metis
      }
      hence "(aa \<notin> A \<or> aa \<notin> above s a \<or> aa \<in> above r a) \<or> a \<preceq>\<^sub>r aa"
        using assms lifted_def equiv_rel_except_a_def linear_order_on_def
              partial_order_on_def preorder_on_def refl_on_def
              is_less_preferred_than.simps
        by metis
      hence "aa \<notin> A \<or> aa \<notin> above s a \<or> aa \<in> above r a"
        by (simp add: above_def)
    }
    thus ?thesis
      by blast
  qed
  thus ?thesis
    using CollectD above_def assms lifted_def equiv_rel_except_a_def
          order_on_defs(1) order_on_defs(2)
          order_on_defs(3) refl_on_domain subsetI
    by metis
qed

lemma lifted_above2:
  assumes "lifted A r s a"
  shows "\<forall>x. x \<in> A-{a} \<longrightarrow> above r x \<subseteq> above s x \<union> {a}"
proof
  fix x
  show "x \<in> A-{a} \<longrightarrow> above r x \<subseteq> above s x \<union> {a}"
  proof
    assume "x \<in> A-{a}"
    hence "\<forall>y \<in> A-{a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
      using assms lifted_def equiv_rel_except_a_def
      by metis
    hence "\<forall>y \<in> A-{a}. y \<in> above r x \<longleftrightarrow> y \<in> above s x"
      by (simp add: above_def)
    moreover have "a \<in> above r x \<longrightarrow> a \<in> above s x"
      using CollectD CollectI above_def assms lifted_mono2
            is_less_preferred_than.simps
      by metis
    moreover have "above r x \<subseteq> A \<and> above s x \<subseteq> A"
      using CollectD above_def assms connex_imp_refl
            lifted_def equiv_rel_except_a_def
            lin_ord_imp_connex refl_on_domain subsetI
      by metis
    ultimately show "above r x \<subseteq> above s x \<union> {a}"
      using Diff_iff UnI1 UnI2 in_mono subsetI
      by blast
  qed
qed

lemma limit_lifted_imp_eq_or_lifted:
  assumes
    lifted: "lifted S r s a" and
    subset: "A \<subseteq> S"
  shows 
    "limit A r = limit A s \<or>
      lifted A (limit A r) (limit A s) a"
proof -
  from lifted have
    "\<forall>x \<in> S - {a}. \<forall>y \<in> S - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    by (simp add: lifted_def equiv_rel_except_a_def)
  with subset have temp:
    "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    by auto
  hence eql_rs:
      "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}.
      (x, y) \<in> (limit A r) \<longleftrightarrow> (x, y) \<in> (limit A s)"
    using DiffD1 limit_presv_prefs1 limit_presv_prefs2
    by auto
  show ?thesis
  proof cases
    assume a1: "a \<in> A"
    thus ?thesis
    proof cases
      (* (\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y) *)
      assume a1_1: "\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a" (* \<and> a1: "a \<in> A" *)
      from lifted subset have 
        "linear_order_on A (limit A r) \<and> linear_order_on A (limit A s)"
        using lifted_def equiv_rel_except_a_def limit_presv_lin_ord
        by metis
      moreover from a1 a1_1 have keep_lift:
        "\<exists>x \<in> A - {a}. (a, x) \<in> (limit A r) \<and>
            (x, a) \<in> (limit A s)"
        using DiffD1 limit_presv_prefs1
              is_less_preferred_than.simps
        by metis
      ultimately show ?thesis
        using a1 temp lifted_def equiv_rel_except_a_def
              is_less_preferred_than.simps
        by (simp add: lifted_def equiv_rel_except_a_def)
    next
      assume "\<not>(\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)" (* \<and> a1: "a \<in> A" *)
      hence a1_2: "\<forall>x \<in> A - {a}. \<not>(a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)"
        by auto
      moreover from lifted subset have not_worse:
        "\<forall>x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x)"
        using lifted_mono Diff_iff subset_eq
        by fastforce
      moreover from lifted subset have connex:
        "connex A (limit A r) \<and> connex A (limit A s)"
        using lifted_def equiv_rel_except_a_def limit_presv_lin_ord
              lin_ord_imp_connex
        by metis
      ultimately have r_eq_s_on_A:
          "\<forall>x \<in> A - {a}. (a \<preceq>\<^sub>r x \<and> a \<preceq>\<^sub>s x) \<or> (x \<preceq>\<^sub>r a \<and> x \<preceq>\<^sub>s a)"
        using DiffD1 a1 connex_def limit_presv_prefs2
              is_less_preferred_than.simps
        by (smt (verit, best))
      with a1 a1_2 not_worse have
        "\<forall>x \<in> A - {a}. (a, x) \<in> (limit A r) \<longleftrightarrow> (a, x) \<in> (limit A s)"
        using DiffD1 limit_presv_prefs1 limit_presv_prefs2
              is_less_preferred_than.simps
        by metis
      moreover from r_eq_s_on_A a1 a1_2 not_worse have
        "\<forall>x \<in> A - {a}. (x, a) \<in> (limit A r) \<longleftrightarrow> (x, a) \<in> (limit A s)"
        using DiffD1 limit_presv_prefs1 limit_presv_prefs2
              is_less_preferred_than.simps
        by metis
      moreover from lifted a1 have
        "(a, a) \<in> (limit A r) \<and> (a, a) \<in> (limit A s)"
        using connex connex_imp_refl refl_onD
        by metis
      moreover have
        "limited A (limit A r) \<and> limited A (limit A s)"
        using limit_to_limits
        by blast
      ultimately have
        "\<forall>x y. (x, y) \<in> limit A r \<longleftrightarrow> (x, y) \<in> limit A s"
        using eql_rs insertE insert_Diff limited_dest
        by auto
      thus ?thesis
        by (simp add: subset_antisym subset_iff)
    qed
  next
    assume a2: "a \<notin> A"
    with eql_rs have
      "\<forall>x \<in> A. \<forall>y \<in> A. (x, y) \<in> (limit A r) \<longleftrightarrow> (x, y) \<in> (limit A s)"
      by simp
    thus ?thesis
      using limit_to_limits limited_dest subrelI subset_antisym
      by auto
  qed
qed

lemma negl_diff_imp_eq_limit:
  assumes
    change: "equiv_rel_except_a S r s a" and
    subset: "A \<subseteq> S" and
    notInA: "a \<notin> A"
  shows "limit A r = limit A s"
proof -
  have "A \<subseteq> S-{a}"
    by (simp add: notInA subset subset_Diff_insert)
  hence "\<forall>x \<in> A. \<forall>y \<in> A. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    by (meson change equiv_rel_except_a_def in_mono)
  thus ?thesis
    by auto
qed

theorem lifted_above_winner:
  assumes
    "lifted A r s a" and
    "above r x = {x}" and
    "finite A"
  shows "above s x = {x} \<or> above s a = {a}"
proof cases
  assume "x = a"
  thus ?thesis
    using above_subset_geq_one assms(1) assms(2)
          lifted_above lifted_def equiv_rel_except_a_def
    by metis
next
  assume asm1: "x \<noteq> a"
  thus ?thesis
  proof cases
    assume "above s x = {x}"
    thus ?thesis
      by simp
  next
    assume asm2: "above s x \<noteq> {x}" (* \<and> asm1: x \<noteq> a *)
    have "\<forall>y \<in> A. y \<preceq>\<^sub>r x"
    proof -
      {
        fix aa :: 'a
        have "x \<preceq>\<^sub>r aa \<longrightarrow> aa \<notin> A \<or> aa \<preceq>\<^sub>r x"
          using singletonD pref_imp_in_above assms(2)
          by metis
        hence "aa \<notin> A \<or> aa \<preceq>\<^sub>r x"
          using pref_imp_in_above assms(1) assms(2)
                connex_imp_refl connex_def lifted_def
                equiv_rel_except_a_def lin_ord_imp_connex
                refl_on_domain singleton_iff assms(3)
                is_less_preferred_than.simps
          by metis
      }
      thus ?thesis
        by simp
    qed
    moreover have "x \<in> A-{a}"
      using asm1 assms(1) calculation connex_imp_refl lifted_def
            equiv_rel_except_a_def lin_ord_imp_connex member_remove
            refl_on_domain remove_def is_less_preferred_than.simps
      by metis
    ultimately have "\<forall>y \<in> A-{a}. y \<preceq>\<^sub>s x"
      using DiffD1 assms(1) lifted_def equiv_rel_except_a_def
      by metis
    hence not_others: "\<forall>y \<in> A-{a}. above s y \<noteq> {y}"
      using asm2 empty_iff insert_iff pref_imp_in_above
      by metis
    hence "above s a = {a}"
      using Diff_iff all_not_in_conv assms(1) assms(3) lifted_def
            equiv_rel_except_a_def above_one singleton_iff
      by metis
    thus ?thesis
      by simp
  qed
qed

theorem lifted_above_winner2:
  assumes
    "lifted A r s a" and
    "above r a = {a}" and
    "finite A"
  shows "above s a = {a}"
  using assms lifted_above_winner
  by metis

theorem lifted_above_winner3:
  assumes
    "lifted A r s a" and
    "above s x = {x}" and
    "finite A" and
    "x \<noteq> a"
  shows "above r x = {x}"
proof (rule ccontr)
  assume asm: "above r x \<noteq> {x}"
  then obtain y where y: "above r y = {y}"
    using assms(1) assms(3) insert_Diff insert_not_empty
          lifted_def equiv_rel_except_a_def above_one
    by metis
  hence "above s y = {y} \<or> above s a = {a}"
    using assms(1) assms(3) lifted_above_winner
    by metis
  moreover have "\<forall>b. above s b = {b} \<longrightarrow> b = x"
    using all_not_in_conv assms(1) assms(2) assms(3)
          lifted_def equiv_rel_except_a_def above_one2
    by metis
  ultimately have "y = x"
    using assms(4)
    by presburger
  moreover have "y \<noteq> x"
    using asm y
    by blast
  ultimately show "False"
    by simp
qed

end

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

text
\<open>The very core of the composable modules voting framework: types and
functions, derivations, lemmata, operations on preference relations, etc.\<close>

subsection \<open>Definition\<close>

(*
  Each voter expresses pairwise relations between all alternatives,
  thereby inducing a linear order.
*)
type_synonym 'a Preference_Relation = "'a rel"

fun is_less_preferred_than ::
  "'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<preceq>\<^sub>_ _" [50, 1000, 51] 50) where
    "x \<preceq>\<^sub>r y = ((x, y) \<in> r)"

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
    using FieldI2 refl
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
proof
  show "r \<subseteq> A \<times> A"
    using assms connex_def limited_def
    by metis
next
  fix
    x :: "'a"
  assume
    x_in_A: "x \<in> A"
  have "x \<preceq>\<^sub>r x"
    using assms connex_def x_in_A
    by metis
  thus "(x, x) \<in> r"
    by simp
qed

lemma lin_ord_imp_connex:
  assumes "linear_order_on A r"
  shows "connex A r"
  unfolding connex_def limited_def
proof (safe)
  fix
    a :: "'a" and
    b :: "'a"
  assume
    asm1: "(a, b) \<in> r"
  show "a \<in> A"
    using asm1 assms partial_order_onD(1)
          order_on_defs(3) refl_on_domain
    by metis
next
  fix
    a :: "'a" and
    b :: "'a"
  assume
    asm1: "(a, b) \<in> r"
  show "b \<in> A"
    using asm1 assms partial_order_onD(1)
          order_on_defs(3) refl_on_domain
    by metis
next
  fix
    x :: "'a" and
    y :: "'a"
  assume
    asm1: "x \<in> A" and
    asm2: "y \<in> A" and
    asm3: "\<not> y \<preceq>\<^sub>r x"
  have "(y, x) \<notin> r"
    using asm3
    by simp
  hence "(x, y) \<in> r"
    using asm1 asm2 assms partial_order_onD(1)
          linear_order_on_def refl_onD total_on_def
    by metis
  thus "x \<preceq>\<^sub>r y"
    by simp
qed

lemma connex_antsym_and_trans_imp_lin_ord:
  assumes
    connex_r: "connex A r" and
    antisym_r: "antisym r" and
    trans_r: "trans r"
  shows "linear_order_on A r"
  unfolding connex_def linear_order_on_def partial_order_on_def
            preorder_on_def refl_on_def total_on_def
proof (safe)
  fix
    a :: "'a" and
    b :: "'a"
  assume
    asm1: "(a, b) \<in> r"
  show "a \<in> A"
    using asm1 connex_r refl_on_domain connex_imp_refl
    by metis
next
  fix
    a :: "'a" and
    b :: "'a"
  assume
    asm1: "(a, b) \<in> r"
  show "b \<in> A"
    using asm1 connex_r refl_on_domain connex_imp_refl
    by metis
next
  fix
    x :: "'a"
  assume
    asm1: "x \<in> A"
  show "(x, x) \<in> r"
    using asm1 connex_r connex_imp_refl refl_onD
  by metis
next
  show "trans r"
    using trans_r
    by simp
next
  show "antisym r"
    using antisym_r
    by simp
next
  fix
    x :: "'a" and
    y :: "'a"
  assume
    asm1: "x \<in> A" and
    asm2: "y \<in> A" and
    asm3: "x \<noteq> y" and
    asm4: "(y, x) \<notin> r"
  have "x \<preceq>\<^sub>r y \<or> y \<preceq>\<^sub>r x"
    using asm1 asm2 connex_r connex_def
    by metis
  hence "(x, y) \<in> r \<or> (y, x) \<in> r"
    by simp
  thus "(x, y) \<in> r"
    using asm4
    by metis
qed

lemma limit_to_limits: "limited A (limit A r)"
  unfolding limited_def
  by auto

lemma limit_presv_connex:
  assumes
    connex: "connex S r" and
    subset: "A \<subseteq> S"
  shows "connex A (limit A r)"
  unfolding connex_def limited_def
proof (simp, safe)
  let ?s = "{(a, b). (a, b) \<in> r \<and> a \<in> A \<and> b \<in> A}"
  fix
    x :: "'a" and
    y :: "'a" and
    a :: "'a" and
    b :: "'a"
  assume
    asm1: "x \<in> A" and
    asm2: "y \<in> A" and
    asm3: "(y, x) \<notin> r"
  have "y \<preceq>\<^sub>r x \<or> x \<preceq>\<^sub>r y"
    using asm1 asm2 connex connex_def in_mono subset
    by metis
  hence
    "x \<preceq>\<^sub>?s y \<or> y \<preceq>\<^sub>?s x"
    using asm1 asm2
    by auto
  hence "x \<preceq>\<^sub>?s y"
    using asm3
    by simp
  thus "(x, y) \<in> r"
    by simp
qed

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
  unfolding trans_def
proof (simp, safe)
  fix
    x :: "'a" and
    y :: "'a" and
    z :: "'a"
  assume
    asm1: "(x, y) \<in> r" and
    asm2: "x \<in> A" and
    asm3: "y \<in> A" and
    asm4: "(y, z) \<in> r" and
    asm5: "z \<in> A"
  show  "(x, z) \<in> r"
    using asm1 asm4 transE transitive
    by metis
qed

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
  using x_in_A x_less_y y_in_A
  by simp

lemma limit_presv_prefs2:
  assumes x_less_y: "(x, y) \<in> limit A r"
  shows "x \<preceq>\<^sub>r y"
  using mem_Collect_eq x_less_y
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
  fix r :: "'a Preference_Relation"
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
  unfolding above_def
  using above_def assms(1) limit_presv_prefs2
        mem_Collect_eq pref_imp_in_above
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
      hence b1: "{a. (b, a) \<in> limit B r} = {b}"
        using above_def
        by metis
      hence b2: "b \<preceq>\<^sub>r b"
        using CollectD limit_presv_prefs2 singletonI
        by (metis (lifting))
      show "\<exists>a. a \<in> A \<and> above r a = {a}"
      proof cases
        assume
          asm1: "a \<preceq>\<^sub>r b"
        have f1:
          "\<forall>A r a aa.
            \<not> refl_on A r \<or> (a::'a, aa) \<notin> r \<or> a \<in> A \<and> aa \<in> A"
          using refl_on_domain
          by metis
        have f2:
          "\<forall>A r. \<not> connex (A::'a set) r \<or> refl_on A r"
          using connex_imp_refl
          by metis
        have f3:
          "\<forall>A r. \<not> linear_order_on (A::'a set) r \<or> connex A r"
          by (simp add: lin_ord_imp_connex)
        hence "refl_on A r"
          using f2 asm
          by metis
        hence "a \<in> A \<and> b \<in> A"
          using f1 asm1
          by simp
        hence f4:
          "\<forall>a. a \<notin> A \<or> b = a \<or> (b, a) \<in> r \<or> (a, b) \<in> r"
          using asm order_on_defs(3) total_on_def
          by metis
        have f5:
          "(b, b) \<in> limit B r"
          using above_def b mem_Collect_eq singletonI
          by metis
        have f6:
          "\<forall>a A Aa. (a::'a) \<notin> A - Aa \<or> a \<in> A \<and> a \<notin> Aa"
          by simp
        have ff1:
          "{a. (b, a) \<in> limit B r} = {b}"
          using above_def b
          by (metis (no_types))
        have ff2:
          "(b, b) \<in> {(aa, a). (aa, a) \<in> r \<and> aa \<in> B \<and> a \<in> B}"
          using f5
          by simp
        moreover have b_wins_B:
          "\<forall>x \<in> B. b \<in> above r x"
          using B above_def f4 ff1 ff2 CollectI
                Product_Type.Collect_case_prodD
          by fastforce
        moreover have "b \<in> above r a"
          using asm1 pref_imp_in_above
          by metis
        ultimately have b_wins:
          "\<forall>x \<in> A. b \<in> above r x"
          using Diff_iff a empty_iff insert_iff
          by (metis (no_types))
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
        hence b_smaller_a_0: "(b, a) \<in> r"
          by simp
        have g1:
          "\<forall>A r Aa.
            \<not> linear_order_on (A::'a set) r \<or>
              \<not> Aa \<subseteq> A \<or>
              linear_order_on Aa (limit Aa r)"
          using limit_presv_lin_ord
          by metis
        have
          "{a. (b, a) \<in> limit B r} = {b}"
          using above_def b
          by metis
        hence g2: "b \<in> B"
          by auto
        have g3:
          "partial_order_on B (limit B r) \<and> total_on B (limit B r)"
          using g1 B asm order_on_defs(3)
          by metis
        have
          "\<forall>A r.
            total_on A r = (\<forall>a. (a::'a) \<notin> A \<or>
              (\<forall>aa. (aa \<notin> A \<or> a = aa) \<or> (a, aa) \<in> r \<or> (aa, a) \<in> r))"
          using total_on_def
          by metis
        hence
          "\<forall>a. a \<notin> B \<or>
            (\<forall>aa. aa \<notin> B \<or> a = aa \<or>
                (a, aa) \<in> limit B r \<or> (aa, a) \<in> limit B r)"
          using g3
          by simp
        hence "\<forall>x \<in> B. b \<in> above r x"
          using limit_presv_prefs2 pref_imp_in_above singletonD mem_Collect_eq
                asm b b1 b2 B g2
          by (metis (lifting))
        hence
          "\<forall>x \<in> B. x \<preceq>\<^sub>r b"
          by (simp add: above_def)
        hence b_wins2:
          "\<forall>x \<in> B. (x, b) \<in> r"
          by simp
        have "trans r"
          using asm lin_imp_trans
          by metis
        hence "\<forall>x \<in> B. (x, a) \<in> r"
          using transE b_smaller_a_0 b_wins2
          by metis
        hence "\<forall>x \<in> B. x \<preceq>\<^sub>r a"
          by simp
        hence nothing_above_a: "\<forall>x \<in> A. x \<preceq>\<^sub>r a"
          using a asm lin_ord_imp_connex above_connex Diff_iff
                empty_iff insert_iff pref_imp_in_above
          by metis
        have "\<forall>x \<in> A. x \<in> above r a \<longleftrightarrow> x = a"
          using antisym_def asm lin_imp_antisym
                nothing_above_a pref_imp_in_above
                CollectD above_def
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
    using assms connex_def lin_ord_imp_connex
          pref_imp_in_above singletonD
    by metis
qed

lemma above_one2:
  assumes
    lin_ord: "linear_order_on A r" and
    fin_not_emp: "finite A \<and> A \<noteq> {}" and
    above1: "above r a = {a} \<and> above r b = {b}"
  shows "a = b"
proof -
  have "a \<preceq>\<^sub>r a \<and> b \<preceq>\<^sub>r b"
    using above1 singletonI pref_imp_in_above
    by metis
  also have
    "\<exists>a\<in>A. above r a = {a} \<and>
      (\<forall>x\<in>A. above r x = {x} \<longrightarrow> x = a)"
    using lin_ord fin_not_emp
    by (simp add: above_one)
  moreover have "connex A r"
    using lin_ord
    by (simp add: lin_ord_imp_connex)
  ultimately show "a = b"
    using above1 connex_def limited_dest
    by metis
qed

lemma above_presv_limit:
  assumes "linear_order r"
  shows "above (limit A r) x \<subseteq> A"
  unfolding above_def
  by auto

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
proof (safe)
  fix
    x :: "'a"
  assume
    x_in_A:   "x \<in> A" and
    x_exist:  "x \<notin> {}" and
    x_neq_a:  "x \<noteq> a" and
    x_pref_a: "x \<preceq>\<^sub>r a" and
    a_pref_x: "a \<preceq>\<^sub>s x"
  from x_pref_a
  have x_pref_a_0: "(x, a) \<in> r"
    by simp
  from a_pref_x
  have a_pref_x_0: "(a, x) \<in> s"
    by simp
  have "antisym r"
    using equiv_rel_except_a_def lifted
          lifted_imp_equiv_rel_except_a
          lin_imp_antisym
    by metis
  hence antisym_r:
    "(\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y)"
    using antisym_def
    by metis
  hence imp_x_eq_a_0:
    "\<lbrakk>(x, a) \<in> r; (a, x) \<in> r\<rbrakk> \<Longrightarrow> x = a"
    by simp
  have lift_ex: "\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a"
    using lifted lifted_def
    by metis
  from lift_ex obtain y :: 'a where
    f1: "y \<in> A - {a} \<and> a \<preceq>\<^sub>r y \<and> y \<preceq>\<^sub>s a"
    by metis
  hence f1_0:
    "y \<in> A - {a} \<and> (a, y) \<in> r \<and> (y, a) \<in> s"
    by simp
  have f2:
    "equiv_rel_except_a A r s a"
    using lifted lifted_def
    by metis
  hence f2_0:
    "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    using equiv_rel_except_a_def
    by metis
  hence f2_1:
    "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. (x, y) \<in> r \<longleftrightarrow> (x, y) \<in> s"
    by simp
  have trans: "\<forall>x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
    using f2 equiv_rel_except_a_def linear_order_on_def
          partial_order_on_def preorder_on_def trans_def
    by metis
  have x_pref_y_0: "(x, y) \<in> s"
    using equiv_rel_except_a_def f1_0 f2 f2_1 insertE
          insert_Diff x_in_A x_neq_a x_pref_a_0 trans
    by metis
  have a_pref_y_0: "(a, y) \<in> s"
    using a_pref_x_0 imp_x_eq_a_0 x_neq_a x_pref_a_0
          equiv_rel_except_a_def f2 lin_imp_trans
          transE x_pref_y_0
    by metis
  show "False"
    using a_pref_y_0 antisymD equiv_rel_except_a_def
          DiffD2 f1_0 f2 lin_imp_antisym singletonI
    by metis
qed

lemma lifted_mono2:
  assumes
    lifted: "lifted A r s a" and
    x_pref_a: "x \<preceq>\<^sub>r a"
  shows "x \<preceq>\<^sub>s a"
proof (simp)
  have x_pref_a_0: "(x, a) \<in> r"
    using x_pref_a
    by simp
  have x_in_A: "x \<in> A"
    using connex_imp_refl equiv_rel_except_a_def
          lifted lifted_def lin_ord_imp_connex
          refl_on_domain x_pref_a_0
    by metis
  have "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    using lifted lifted_def equiv_rel_except_a_def
    by metis
  hence rest_eq:
    "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. (x, y) \<in> r \<longleftrightarrow> (x, y) \<in> s"
    by simp
  have "\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a"
    using lifted lifted_def
    by metis
  hence ex_lifted:
    "\<exists>x \<in> A - {a}. (a, x) \<in> r \<and> (x, a) \<in> s"
    by simp
  show "(x, a) \<in> s"
  proof (cases "x = a")
    case True
    thus ?thesis
      using connex_imp_refl equiv_rel_except_a_def refl_onD
            lifted lifted_def lin_ord_imp_connex
      by metis
  next
    case False
    thus ?thesis
      using equiv_rel_except_a_def insertE insert_Diff
            lifted lifted_imp_equiv_rel_except_a x_in_A
            x_pref_a_0 ex_lifted lin_imp_trans rest_eq
            trans_def
      by metis
  qed
qed

lemma lifted_above:
  assumes "lifted A r s a"
  shows "above s a \<subseteq> above r a"
  unfolding above_def
proof (safe)
  fix
    x :: "'a"
  assume
    a_pref_x: "(a, x) \<in> s"
  have "\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a"
    using assms lifted_def
    by metis
  hence lifted_r:
    "\<exists>x \<in> A - {a}. (a, x) \<in> r \<and> (x, a) \<in> s"
    by simp
  have "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    using assms lifted_def equiv_rel_except_a_def
    by metis
  hence rest_eq:
    "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. (x, y) \<in> r \<longleftrightarrow> (x, y) \<in> s"
    by simp
  have trans_r:
    "\<forall>x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
    using trans_def lifted_def lin_imp_trans
          equiv_rel_except_a_def assms
    by metis
  have trans_s:
    "\<forall>x y z. (x, y) \<in> s \<longrightarrow> (y, z) \<in> s \<longrightarrow> (x, z) \<in> s"
    using trans_def lifted_def lin_imp_trans
          equiv_rel_except_a_def assms
    by metis
  have refl_r:
    "(a, a) \<in> r"
    using assms connex_imp_refl equiv_rel_except_a_def
          lifted_def lin_ord_imp_connex refl_onD
    by metis
  have x_in_A: "x \<in> A"
    using a_pref_x assms connex_imp_refl equiv_rel_except_a_def
          lifted_def lin_ord_imp_connex refl_onD2
    by metis
  show "(a, x) \<in> r"
    using Diff_iff a_pref_x lifted_r rest_eq singletonD
          trans_r trans_s x_in_A refl_r
    by (metis (full_types))
qed

lemma lifted_above2:
  assumes
    "lifted A r s a" and
    "x \<in> A-{a}"
  shows "above r x \<subseteq> above s x \<union> {a}"
proof (safe, simp)
  fix y :: "'a"
  assume
    y_in_above_r: "y \<in> above r x" and
    y_not_in_above_s: "y \<notin> above s x"
  have "\<forall>z \<in> A-{a}. x \<preceq>\<^sub>r z \<longleftrightarrow> x \<preceq>\<^sub>s z"
    using assms lifted_def equiv_rel_except_a_def
    by metis
  hence "\<forall>z \<in> A-{a}. (x, z) \<in> r \<longleftrightarrow> (x, z) \<in> s"
    by simp
  hence "\<forall>z \<in> A-{a}. z \<in> above r x \<longleftrightarrow> z \<in> above s x"
    by (simp add: above_def)
  hence "y \<in> above r x \<longleftrightarrow> y \<in> above s x"
    using y_not_in_above_s assms(1) connex_def
          equiv_rel_except_a_def lifted_def lifted_mono2
          limited_dest lin_ord_imp_connex member_remove
          pref_imp_in_above remove_def
    by metis
  thus "y = a"
    using y_in_above_r y_not_in_above_s
    by simp
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
        "\<exists>x \<in> A - {a}. (let q = limit A r in a \<preceq>\<^sub>q x) \<and>
            (let u = limit A s in x \<preceq>\<^sub>u a)"
        using DiffD1 limit_presv_prefs1
        by simp
      ultimately show ?thesis
        using a1 temp
        by (simp add: lifted_def equiv_rel_except_a_def)
    next
      assume
        "\<not>(\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)" (* \<and> a1: "a \<in> A" *)
      hence a1_2:
        "\<forall>x \<in> A - {a}. \<not>(a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)"
        by auto
      moreover have not_worse:
        "\<forall>x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x)"
        using lifted subset lifted_mono
        by fastforce
      moreover have connex:
        "connex A (limit A r) \<and> connex A (limit A s)"
        using lifted subset lifted_def equiv_rel_except_a_def
              limit_presv_lin_ord lin_ord_imp_connex
        by metis
      moreover have connex1:
        "\<forall>A r. connex A r =
          (limited A r \<and> (\<forall>a. (a::'a) \<in> A \<longrightarrow>
            (\<forall>aa. aa \<in> A \<longrightarrow> a \<preceq>\<^sub>r aa \<or> aa \<preceq>\<^sub>r a)))"
        by (simp add: Ball_def_raw connex_def)
      hence limit1:
        "limited A (limit A r) \<and>
          (\<forall>a. a \<notin> A \<or>
            (\<forall>aa.
              aa \<notin> A \<or> (a, aa) \<in> limit A r \<or>
                (aa, a) \<in> limit A r ))"
        using connex connex1
        by simp
      have limit2:
        "\<forall>a aa A r. (a::'a, aa) \<notin> limit A r \<or> a \<preceq>\<^sub>r aa"
        using limit_presv_prefs2
        by metis
      have
        "limited A (limit A s) \<and>
          (\<forall>a. a \<notin> A \<or>
            (\<forall>aa. aa \<notin> A \<or>
              (let q = limit A s in a \<preceq>\<^sub>q aa \<or> aa \<preceq>\<^sub>q a)))"
        using connex connex_def
        by metis
      hence connex2:
        "limited A (limit A s) \<and>
          (\<forall>a. a \<notin> A \<or>
            (\<forall>aa. aa \<notin> A \<or>
              ((a, aa) \<in> limit A s \<or> (aa, a) \<in> limit A s)))"
        by simp
      ultimately have
          "\<forall>x \<in> A - {a}. (a \<preceq>\<^sub>r x \<and> a \<preceq>\<^sub>s x) \<or> (x \<preceq>\<^sub>r a \<and> x \<preceq>\<^sub>s a)"
        using DiffD1 limit1 limit_presv_prefs2 a1
        by metis
      hence r_eq_s_on_A_0:
        "\<forall>x \<in> A - {a}. ((a, x) \<in> r \<and> (a, x) \<in> s) \<or> ((x, a) \<in> r \<and> (x, a) \<in> s)"
        by simp
      have
        "\<forall>x \<in> A - {a}. (a, x) \<in> (limit A r) \<longleftrightarrow> (a, x) \<in> (limit A s)"
        using DiffD1 limit2 limit1 connex2 a1 a1_2 not_worse
        by metis
      hence
        "\<forall>x \<in> A - {a}.
          (let q = limit A r in a \<preceq>\<^sub>q x) \<longleftrightarrow> (let q = limit A s in a \<preceq>\<^sub>q x)"
        by simp
      moreover have
        "\<forall>x \<in> A - {a}. (x, a) \<in> (limit A r) \<longleftrightarrow> (x, a) \<in> (limit A s)"
        using a1 a1_2 not_worse DiffD1 limit_presv_prefs2 connex2 limit1
        by metis
      moreover have
        "(a, a) \<in> (limit A r) \<and> (a, a) \<in> (limit A s)"
        using a1 connex connex_imp_refl refl_onD
        by metis
      moreover have
        "limited A (limit A r) \<and> limited A (limit A s)"
        using limit_to_limits
        by metis
      ultimately have
        "\<forall>x y. (x, y) \<in> limit A r \<longleftrightarrow> (x, y) \<in> limit A s"
        using eql_rs
        by auto
      thus ?thesis
        by simp
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
    lifted_a: "lifted A r s a" and
    above_x: "above r x = {x}" and
    fin_A: "finite A"
  shows "above s x = {x} \<or> above s a = {a}"
proof cases
  assume "x = a"
  thus ?thesis
    using above_subset_geq_one lifted_a above_x
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
      fix aa :: 'a
      have imp_a: "x \<preceq>\<^sub>r aa \<longrightarrow> aa \<notin> A \<or> aa \<preceq>\<^sub>r x"
        using singletonD pref_imp_in_above above_x
        by metis
      also have f1:
        "\<forall>A r.
          (connex A r \<or>
            (\<exists>a. (\<exists>aa. \<not> (aa::'a) \<preceq>\<^sub>r a \<and> \<not> a \<preceq>\<^sub>r aa \<and> aa \<in> A) \<and> a \<in> A) \<or>
              \<not> limited A r) \<and>
            ((\<forall>a. (\<forall>aa. aa \<preceq>\<^sub>r a \<or> a \<preceq>\<^sub>r aa \<or> aa \<notin> A) \<or> a \<notin> A) \<and> limited A r \<or>
              \<not> connex A r)"
        using connex_def
        by metis
      moreover have eq_exc_a:
        "equiv_rel_except_a A r s a"
        using lifted_def lifted_a
        by metis
      ultimately have "aa \<notin> A \<or> aa \<preceq>\<^sub>r x"
        using pref_imp_in_above above_x equiv_rel_except_a_def
              lin_ord_imp_connex limited_dest insertCI
        by metis
      thus ?thesis
        using f1 eq_exc_a above_one above_one2 above_x fin_A
              equiv_rel_except_a_def insert_not_empty pref_imp_in_above
              lin_ord_imp_connex mk_disjoint_insert insertE
        by metis
    qed
    moreover have "equiv_rel_except_a A r s a"
      using lifted_a lifted_def
      by metis
    moreover have "x \<in> A-{a}"
      using above_one above_one2 asm1 assms calculation
            equiv_rel_except_a_def insert_not_empty
            member_remove remove_def insert_absorb
      by metis
    ultimately have "\<forall>y \<in> A-{a}. y \<preceq>\<^sub>s x"
      using DiffD1 lifted_a equiv_rel_except_a_def
      by metis
    hence not_others: "\<forall>y \<in> A-{a}. above s y \<noteq> {y}"
      using asm2 empty_iff insert_iff pref_imp_in_above
      by metis
    hence "above s a = {a}"
      using Diff_iff all_not_in_conv lifted_a fin_A lifted_def
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
    lifted_a: "lifted A r s a" and
    above_x: "above s x = {x}" and
    fin_A: "finite A" and
    x_not_a: "x \<noteq> a"
  shows "above r x = {x}"
proof (rule ccontr)
  assume asm: "above r x \<noteq> {x}"
  then obtain y where y: "above r y = {y}"
    using lifted_a fin_A insert_Diff insert_not_empty
          lifted_def equiv_rel_except_a_def above_one
    by metis
  hence "above s y = {y} \<or> above s a = {a}"
    using lifted_a fin_A lifted_above_winner
    by metis
  moreover have "\<forall>b. above s b = {b} \<longrightarrow> b = x"
    using all_not_in_conv lifted_a above_x lifted_def
          fin_A equiv_rel_except_a_def above_one2
    by metis
  ultimately have "y = x"
    using x_not_a
    by presburger
  moreover have "y \<noteq> x"
    using asm y
    by blast
  ultimately show "False"
    by simp
qed

end

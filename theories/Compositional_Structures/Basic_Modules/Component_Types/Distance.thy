(*  File:       Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance\<close>

theory Distance
  imports "HOL-Library.Extended_Real"
          "Social_Choice_Types/Profile"
          "HOL-Combinatorics.List_Permutation"
begin

text \<open>
  A general distance on a set X is a mapping d : X x X to R union {+infty} such
  that for every x, y, z in X the following four conditions are satisfied:
  - d(x, y) >= 0 (nonnegativity);
  - d(x, y) = 0 if and only if x = y (identity of indiscernibles);
  - d(x, y) = d(y, x) (symmetry);
  - d(x, y) <= d(x, z) + d(z, y) (triangle inequality).
  Moreover, a mapping that satisfies all but the second conditions is called
  a pseudodistance, whereas a quasidistance needs to satisfy the first three
  conditions (and not necessarily the last one).
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Distance = "'a \<Rightarrow> 'a \<Rightarrow> ereal"

definition distance :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "distance S d \<equiv> \<forall> x y. (x \<in> S \<and> y \<in> S) \<longrightarrow> (d x x = 0 \<and> 0 \<le> d x y)"

subsection \<open>TODO\<close>

definition symmetric :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "symmetric S d \<equiv> \<forall> x y. (x \<in> S \<and> y \<in> S) \<longrightarrow> d x y = d y x"

definition triangle_ineq :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "triangle_ineq S d \<equiv> \<forall> x y z. (x \<in> S \<and> y \<in> S \<and> z \<in> S) \<longrightarrow> d x z \<le> d x y + d y z"

definition eq_if_zero :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "eq_if_zero S d \<equiv> \<forall> x y. (x \<in> S \<and> y \<in> S) \<longrightarrow> d x y = 0 \<longrightarrow> x = y"

abbreviation vote_distance_property :: "('a Vote set \<Rightarrow> 'a Vote Distance \<Rightarrow> bool)
                                     \<Rightarrow> 'a Vote Distance \<Rightarrow> bool" where
  "vote_distance_property p d \<equiv> p {(A, v). linear_order_on A v \<and> finite A} d"

abbreviation election_distance_property :: "('a Election set
                                           \<Rightarrow> 'a Election Distance \<Rightarrow> bool)
                                           \<Rightarrow> 'a Election Distance
                                           \<Rightarrow> bool" where
  "election_distance_property p d \<equiv> p {(A, p). finite_profile A p} d"

definition el_distance_anonymity :: "'a Election Distance \<Rightarrow> bool" where
  "el_distance_anonymity d \<equiv>
    \<forall> C B pi p q. (\<forall> n. (pi n) permutes {..< n}) \<longrightarrow>
    d (C, p) (B, q) = d (C, permute_list (pi (length p)) p) (B, permute_list (pi (length q)) q)"

definition standard :: "'a Election Distance \<Rightarrow> bool" where
 "standard d \<equiv> \<forall> C B p q. length p \<noteq> length q \<or> C \<noteq> B \<longrightarrow> d (C, p) (B, q) = \<infinity>"

lemma sum_mon:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> int" and
    g :: "'a \<Rightarrow> int"
  assumes "\<forall> a \<in> A. (f a :: int) \<le> g a"
  shows "(\<Sum> a \<in> A. f a) \<le> (\<Sum> a \<in> A. g a)"
  using assms
  by (induction A rule: infinite_finite_induct, auto)

subsection \<open>Swap Distance\<close>

fun neq_ord :: "'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "neq_ord x y u v = (u \<preceq>\<^sub>x v \<and> v \<preceq>\<^sub>x u)"

definition pairwise_disagreements :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                                      ('a \<times> 'a) set" where
  "pairwise_disagreements A x y = {(u, v) \<in> A \<times> A. u \<noteq> v \<and> neq_ord x y u v}"

definition pairwise_disagreements' :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                                      ('a \<times> 'a) set" where
  "pairwise_disagreements' A x y = Set.filter (\<lambda> (u, v). u \<noteq> v \<and> neq_ord x y u v) (A \<times> A)"

lemma set_eq_filter:
  fixes
    X :: "'a set" and
    P :: "'a \<Rightarrow> bool"
  shows "{x \<in> X. P x} = Set.filter P X"
  by auto

lemma pairwise_disagreements_eq[code]: "pairwise_disagreements = pairwise_disagreements'"
  unfolding pairwise_disagreements_def pairwise_disagreements'_def
  by fastforce

fun swap :: "'a Vote Distance" where
  "swap (A, x) (A', y) =
    (if A = A'
    then card (pairwise_disagreements A x y)
    else \<infinity>)"

lemma swap_case_inf:
  fixes
    x :: "'a Vote" and
    y :: "'a Vote"
  assumes "(fst x) \<noteq> (fst y)"
  shows "swap x y = \<infinity>"
  using assms
  by (induction rule: swap.induct, simp)

lemma swap_case_fin:
  fixes
    x :: "'a Vote" and
    y :: "'a Vote"
  assumes "(fst x) = (fst y)"
  shows "swap x y = card (pairwise_disagreements (fst x) (snd x) (snd y))"
  using assms
  by (induction rule: swap.induct, simp)

subsection \<open>Spearman Distance\<close>

fun spearman :: "'a Vote Distance" where
  "spearman (A, x) (A', y) =
    (if A = A'
    then (\<Sum> a \<in> A. abs (int (rank x a) - int (rank y a)))
    else \<infinity>)"

lemma spearman_case_inf:
  fixes
    x :: "'a Vote" and
    y :: "'a Vote"
  assumes "(fst x) \<noteq> (fst y)"
  shows "spearman x y = \<infinity>"
  using assms
  by (induction rule: spearman.induct, simp)

lemma spearman_case_fin:
  fixes
    x :: "'a Vote" and
    y :: "'a Vote"
  assumes "(fst x) = (fst y)"
  shows "spearman x y = (\<Sum> a \<in> (fst x). abs (int (rank (snd x) a) - int (rank (snd y) a)))"
  using assms
  by (induction rule: spearman.induct, simp)

lemma distrib:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> int" and
    g :: "'a \<Rightarrow> int"
  shows "(\<Sum> a \<in> A. (f::'a \<Rightarrow> int) a) + (\<Sum> a \<in> A. g a) = (\<Sum> a \<in> A. (f a) + (g a))"
  using sum.distrib
  by metis

lemma distrib_ereal:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> int" and
    g :: "'a \<Rightarrow> int"
  shows "ereal (real_of_int ((\<Sum> a \<in> A. (f::'a \<Rightarrow> int) a) + (\<Sum> a \<in> A. g a)))
          = ereal (real_of_int ((\<Sum> a \<in> A. (f a) + (g a))))"
  using distrib[of f]
  by simp

lemma uneq_ereal:
  fixes
    x :: int and
    y :: int
  assumes "x \<le> y"
  shows "ereal (real_of_int x) \<le> ereal (real_of_int y)"
  using assms
  by simp

end

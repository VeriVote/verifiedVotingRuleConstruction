(*  File:       Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance\<close>

theory Distance
  imports "HOL-Library.Extended_Real"
          "HOL-Combinatorics.List_Permutation"
          "Social_Choice_Types/Profile"
begin

text \<open>
  A general distance on a set X is a mapping d : X x X to R union {+\<infinity>} such
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

subsection \<open>Conditions\<close>

definition symmetric :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "symmetric S d \<equiv> \<forall> x y. (x \<in> S \<and> y \<in> S) \<longrightarrow> d x y = d y x"

definition triangle_ineq :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "triangle_ineq S d \<equiv> \<forall> x y z. (x \<in> S \<and> y \<in> S \<and> z \<in> S) \<longrightarrow> d x z \<le> d x y + d y z"

definition eq_if_zero :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "eq_if_zero S d \<equiv> \<forall> x y. (x \<in> S \<and> y \<in> S) \<longrightarrow> d x y = 0 \<longrightarrow> x = y"

definition vote_distance :: "('a Vote set \<Rightarrow> 'a Vote Distance \<Rightarrow> bool) \<Rightarrow>
                                          'a Vote Distance \<Rightarrow> bool" where
  "vote_distance \<pi> d \<equiv> \<pi> {(A, p). linear_order_on A p \<and> finite A} d"

definition election_distance :: 
  "(('a, 'v) Election set \<Rightarrow> ('a, 'v) Election Distance \<Rightarrow> bool) \<Rightarrow>
      ('a, 'v) Election Distance \<Rightarrow> bool" where
  "election_distance \<pi> d \<equiv> \<pi> {(A, V, p). finite_profile V A p} d"

subsection \<open>Standard Distance Property\<close>

definition standard :: "('a, 'v) Election Distance \<Rightarrow> bool" where
 "standard d \<equiv> \<forall> A A' V V' p p'. A \<noteq> A' \<or> V \<noteq> V' \<longrightarrow> d (A, V, p) (A', V', p') = \<infinity>"

subsection \<open>Auxiliary Lemmas\<close>

fun arg_min_set :: "('b \<Rightarrow> 'a :: ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "arg_min_set f A = Collect (is_arg_min f (\<lambda> a. a \<in> A))"
(* fun arg_min_set' :: "('b \<Rightarrow> 'a::ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
   "arg_min_set_' f A = Set.filter (is_arg_min f (\<lambda> a. a \<in> A)) A" *)

lemma arg_min_subset: 
  fixes 
    B :: "'b set" and
    f :: "('b \<Rightarrow> 'a :: ord)"
  shows 
    "arg_min_set f B \<subseteq> B"
proof (auto, unfold is_arg_min_def, simp) 
qed

lemma sum_monotone:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> int" and
    g :: "'a \<Rightarrow> int"
  assumes "\<forall> a \<in> A. (f a :: int) \<le> g a"
  shows "(\<Sum> a \<in> A. f a) \<le> (\<Sum> a \<in> A. g a)"
  using assms
  by (induction A rule: infinite_finite_induct, simp_all)

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

subsection \<open>Swap Distance\<close>

fun neq_ord :: "'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "neq_ord r s a b = ((a \<preceq>\<^sub>r b \<and> b \<preceq>\<^sub>s a) \<or> (b \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s b))"

fun pairwise_disagreements :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                                      ('a \<times> 'a) set" where
  "pairwise_disagreements A r s = {(a, b) \<in> A \<times> A. a \<noteq> b \<and> neq_ord r s a b}"

fun pairwise_disagreements' :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                                      ('a \<times> 'a) set" where
  "pairwise_disagreements' A r s = Set.filter (\<lambda> (a, b). a \<noteq> b \<and> neq_ord r s a b) (A \<times> A)"

lemma set_eq_filter:
  fixes
    X :: "'a set" and
    P :: "'a \<Rightarrow> bool"
  shows "{x \<in> X. P x} = Set.filter P X"
  by auto

lemma pairwise_disagreements_eq[code]: "pairwise_disagreements = pairwise_disagreements'"
  unfolding pairwise_disagreements.simps pairwise_disagreements'.simps
  by fastforce

fun swap :: "'a Vote Distance" where
  "swap (A, r) (A', r') =
    (if A = A'
    then card (pairwise_disagreements A r r')
    else \<infinity>)"

lemma swap_case_infinity:
  fixes
    x :: "'a Vote" and
    y :: "'a Vote"
  assumes "alts_\<V> x \<noteq> alts_\<V> y"
  shows "swap x y = \<infinity>"
  using assms
  by (induction rule: swap.induct, simp)

lemma swap_case_fin:
  fixes
    x :: "'a Vote" and
    y :: "'a Vote"
  assumes "alts_\<V> x = alts_\<V> y"
  shows "swap x y = card (pairwise_disagreements (alts_\<V> x) (pref_\<V> x) (pref_\<V> y))"
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
  assumes "alts_\<V> x \<noteq> alts_\<V> y"
  shows "spearman x y = \<infinity>"
  using assms
  by (induction rule: spearman.induct, simp)

lemma spearman_case_fin:
  fixes
    x :: "'a Vote" and
    y :: "'a Vote"
  assumes "alts_\<V> x = alts_\<V> y"
  shows "spearman x y = (\<Sum> a \<in> alts_\<V> x. abs (int (rank (pref_\<V> x) a) - int (rank (pref_\<V> y) a)))"
  using assms
  by (induction rule: spearman.induct, simp)

section \<open>Properties\<close>

definition distance_anonymity :: "('a, 'v) Election Distance \<Rightarrow> bool" where
  "distance_anonymity d \<equiv>
    \<forall> A A' V V' p p' \<pi>::('v \<Rightarrow> 'v).
      (bij \<pi> \<longrightarrow>
        (d (A, V, p) (A', V', p')) =
          (d (rename \<pi> (A, V, p))) (rename \<pi> (A', V', p')))"

end

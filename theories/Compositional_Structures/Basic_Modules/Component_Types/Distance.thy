(*  File:       Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance\<close>

theory Distance
  imports "HOL-Library.Extended_Real"
          "Social_Choice_Types/Profile"
          "Social_Choice_Types/Tools/List_Permutation_2"
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
  "distance S d \<equiv> (\<forall> x y. (x \<in> S \<and> y \<in> S) \<longrightarrow> (d x x = 0 \<and> d x y \<ge> 0))"

type_synonym 'a Vote = "('a set \<times> 'a Preference_Relation)"

subsection \<open>TODO\<close>

definition symmetric :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "symmetric S d \<equiv> (\<forall> x y. (x \<in> S \<and> y \<in> S) \<longrightarrow> d x y = d y x)"

definition triangle_ineq :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "triangle_ineq S d \<equiv> (\<forall> x y z. (x \<in> S \<and> y \<in> S \<and> z \<in> S) \<longrightarrow> d x z \<le> d x y + d y z)"

definition eq_if_zero :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "eq_if_zero S d \<equiv> (\<forall> x y. (x \<in> S \<and> y \<in> S) \<longrightarrow> d x y = 0 \<longrightarrow> x = y)"

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
    (\<forall> C B pi p q. (\<forall>n::nat. is_perm pi \<longrightarrow> d (C,p) (B,q) = d (C,build_perm pi p) (B,build_perm pi q)))"

definition standard :: "'a Election Distance \<Rightarrow> bool" where
 "standard d \<equiv> (\<forall> C B p q. length p \<noteq> length q \<or> C \<noteq> B \<longrightarrow> d (C,p) (B,q) = \<infinity>)"

lemma sum_mon: "(\<forall> a \<in> A. (f a :: int) \<le> g a) \<longrightarrow> (\<Sum> a \<in> A. f a) \<le> (\<Sum> a \<in> A. g a)"
  by (induction A rule: infinite_finite_induct, auto)

subsection \<open>Swap Distance\<close>

definition neq_ord :: "'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "neq_ord x y u v \<equiv> (is_less_preferred_than u x v \<and> is_less_preferred_than v y u)"

definition pairwise_disagreements :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                                      ('a \<times> 'a) set" where
  "pairwise_disagreements A x y = {(u, v) \<in> A \<times> A. u \<noteq> v \<and> neq_ord x y u v}"

definition pairwise_disagreements_2 :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow>
                                      ('a \<times> 'a) set" where
  "pairwise_disagreements_2 A x y = Set.filter (\<lambda> (u, v). u \<noteq> v \<and> neq_ord x y u v) (A \<times> A)"

lemma x: "{x \<in> X. P x} = Set.filter P X"
  by auto

lemma [code]: "pairwise_disagreements = pairwise_disagreements_2"
  unfolding pairwise_disagreements_def pairwise_disagreements_2_def
  by fastforce

fun swap :: "'a Vote Distance" where
  "swap (A, x) (A', y) =
    (if A = A'
    then card (pairwise_disagreements A x y)
    else \<infinity>)"

lemma swap_case_inf: "(fst x) \<noteq> (fst y) \<longrightarrow> swap x y = \<infinity>"
  by (induction rule: swap.induct, simp)

lemma swap_case_fin: "(fst x) = (fst y)
    \<longrightarrow> swap x y = card (pairwise_disagreements (fst x) (snd x) (snd y))"
  by (induction rule: swap.induct, simp)

subsection \<open>Spearman Distance\<close>

fun spearman :: "'a Vote Distance" where
  "spearman (A, x) (A', y) =
    (if A = A'
    then (\<Sum> a \<in> A. abs (int (rank x a) - int (rank y a)))
    else \<infinity>)"

lemma spearman_case_inf: "(fst x) \<noteq> (fst y) \<longrightarrow> spearman x y = \<infinity>"
  by (induction rule: spearman.induct, simp)

lemma spearman_case_fin: "(fst x) = (fst y)
    \<longrightarrow> spearman x y = (\<Sum> a \<in> (fst x). abs (int (rank (snd x) a) - int (rank (snd y) a)))"
  by (induction rule: spearman.induct, simp)

lemma distrib: "(\<Sum> a \<in> A. (f::'a \<Rightarrow> int) a) + (\<Sum> a \<in> A. g a) = (\<Sum> a \<in> A. (f a) + (g a))"
  using sum.distrib
  by metis

lemma distrib_ereal: "ereal (real_of_int ((\<Sum> a \<in> A. (f::'a \<Rightarrow> int) a) + (\<Sum> a \<in> A. g a)))
                    = ereal (real_of_int ((\<Sum> a \<in> A. (f a) + (g a))))"
  using distrib[of f A]
  by simp

lemma uneq_ereal: "x \<le> y \<Longrightarrow> ereal (real_of_int x) \<le> ereal (real_of_int y)"
  by simp

end

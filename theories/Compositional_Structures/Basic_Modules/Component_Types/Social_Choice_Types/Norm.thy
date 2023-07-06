(*  File:       Norm.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Norm\<close>

theory Norm
  imports "HOL-Library.Extended_Real"
          "HOL-Combinatorics.List_Permutation"
begin

text \<open>
  A norm on R to n is a mapping N: R to n on R that has the following properties:
  - positive scalability: N(a * u) = |a| * N(u) for all u in R to n and all a in R;
  - positive semidefiniteness: N(u) >= 0 for all u in R to n, and N(u) = 0 if and
    only if u = (0, 0, . . . , 0);
  - triangle inequality: N(u + v) <= N(u) + N(v) for all u,v in R to n.
\<close>

subsection \<open>Definition\<close>

type_synonym Norm = "ereal list \<Rightarrow> ereal"

definition norm :: "Norm \<Rightarrow> bool" where
  "norm n \<equiv> \<forall> (x::ereal list). n x \<ge> 0 \<and> (\<forall> i < length x. (x!i = 0) \<longrightarrow> n x = 0)"

subsection \<open>Auxiliary Lemmas\<close>

lemma sum_over_image_of_bijection:
  fixes
    A :: "'a set" and
    A' :: "'b set" and
    f :: "'a \<Rightarrow> 'b" and
    g :: "'a \<Rightarrow> ereal"
  assumes "bij_betw f A A'"
  shows "(\<Sum> a \<in> A. g a) = (\<Sum> a' \<in> A'. g (the_inv_into A f a'))"
  using assms
proof (induction "card A" arbitrary: A A')
  case 0
  hence "card A' = 0"
    using bij_betw_same_card assms
    by metis
  hence "(\<Sum> a \<in> A. g a) = 0 \<and> (\<Sum> a' \<in> A'. g (the_inv_into A f a')) = 0"
    using 0 card_0_eq sum.empty sum.infinite
    by metis
  thus ?case
    by simp
next
  case (Suc x)
  fix
    A :: "'a set" and
    A' :: "'b set" and
    x :: nat
  assume
    IH: "\<And> A A'. x = card A \<Longrightarrow>
            bij_betw f A A' \<Longrightarrow> sum g A = (\<Sum> a \<in> A'. g (the_inv_into A f a))" and
    suc: "Suc x = card A" and
    bij_A_A': "bij_betw f A A'"
  obtain a where
    a_in_A: "a \<in> A"
    using suc card_eq_SucD insertI1
    by metis
  have a_compl_A: "insert a (A - {a}) = A"
    using a_in_A
    by blast
  have inj_on_A_A': "inj_on f A \<and> A' = f ` A"
    using bij_A_A'
    unfolding bij_betw_def
    by simp
  hence inj_on_A: "inj_on f A"
    by simp
  have img_of_A: "A' = f ` A"
    using inj_on_A_A'
    by simp
  have "inj_on f (insert a A)"
    using inj_on_A a_compl_A
    by simp
  hence A'_sub_fa: "A' - {f a} = f ` (A - {a})"
    using img_of_A
    by blast
  hence bij_without_a: "bij_betw f (A - {a}) (A' - {f a})"
    using inj_on_A a_compl_A inj_on_insert
    unfolding bij_betw_def
    by (metis (no_types))
  have "\<forall> f A A'. bij_betw f (A::'a set) (A'::'b set) = (inj_on f A \<and> f ` A = A')"
    unfolding bij_betw_def
    by simp
  hence inv_without_a: "\<forall> a' \<in> (A' - {f a}). the_inv_into (A - {a}) f a' = the_inv_into A f a'"
    using inj_on_A A'_sub_fa
    by (simp add: inj_on_diff the_inv_into_f_eq)
  have card_without_a: "card (A - {a}) = x"
    using suc a_in_A Diff_empty card_Diff_insert diff_Suc_1 empty_iff
    by simp
  hence card_A'_from_x: "card A' = Suc x \<and> card (A' - {f a}) = x"
    using suc bij_A_A' bij_without_a
    by (simp add: bij_betw_same_card)
  hence "(\<Sum> a \<in> A. g a) = (\<Sum> a \<in> (A - {a}). g a) + g a"
    using suc add.commute card_Diff1_less_iff insert_Diff insert_Diff_single lessI
          sum.insert_remove card_without_a
    by metis
  also have "\<dots> = (\<Sum> a' \<in> (A' - {f a}). g (the_inv_into (A - {a}) f a')) + g a"
    using IH bij_without_a card_without_a
    by simp
  also have "\<dots> = (\<Sum> a' \<in> (A' - {f a}). g (the_inv_into A f a')) + g a"
    using inv_without_a
    by simp
  also have "\<dots> = (\<Sum> a' \<in> (A' - {f a}). g (the_inv_into A f a')) + g (the_inv_into A f (f a))"
    using a_in_A bij_A_A'
    by (simp add: bij_betw_imp_inj_on the_inv_into_f_f)
  also have "\<dots> = (\<Sum> a' \<in> A'. g (the_inv_into A f a'))"
    using add.commute card_Diff1_less_iff insert_Diff insert_Diff_single lessI
          sum.insert_remove card_A'_from_x
    by metis
  finally show "(\<Sum> a \<in> A. g a) = (\<Sum> a' \<in> A'. g (the_inv_into A f a'))"
    by simp
qed

subsection \<open>Common Norms\<close>

fun l_one :: "Norm" where
  "l_one x = (\<Sum> i < length x. \<bar>x!i\<bar>)"

subsection \<open>Properties\<close>

definition symmetry :: "Norm \<Rightarrow> bool" where
  "symmetry n \<equiv> \<forall> x y. x <~~> y \<longrightarrow> n x = n y"

subsection \<open>Theorems\<close>

theorem l_one_is_symm: "symmetry l_one"
proof (unfold symmetry_def, safe)
  fix
    xs :: "ereal list" and
    ys :: "ereal list"
  assume perm: "xs <~~> ys"
  from perm obtain pi
    where
      pi_perm: "pi permutes {..< length xs}" and
      pi_xs_ys: "permute_list pi xs = ys"
    using mset_eq_permutation
    by metis
  hence "(\<Sum> i < length xs. \<bar>ys!i\<bar>) = (\<Sum> i < length xs. \<bar>xs!(pi i)\<bar>)"
    using permute_list_nth
    by fastforce
  also have "\<dots> = (\<Sum> i < length xs. \<bar>xs!(pi (inv pi i))\<bar>)"
    using pi_perm permutes_inv_eq f_the_inv_into_f_bij_betw permutes_imp_bij sum.cong
          sum_over_image_of_bijection
    by (smt (verit, ccfv_SIG))
  also have "\<dots> = (\<Sum> i < length xs. \<bar>xs!i\<bar>)"
    using pi_perm permutes_inv_eq
    by metis
  finally have "(\<Sum> i < length xs. \<bar>ys!i\<bar>) = (\<Sum> i < length xs. \<bar>xs!i\<bar>)"
    by simp
  moreover have "length xs = length ys"
    using perm perm_length
    by metis
  ultimately show "l_one xs = l_one ys"
    using l_one.elims
    by metis
qed

end

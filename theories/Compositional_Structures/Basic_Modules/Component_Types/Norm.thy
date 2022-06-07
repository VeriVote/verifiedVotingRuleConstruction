(*  File:       Norm.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Norm\<close>

theory Norm
  imports "HOL-Library.Extended_Real"
          "Social_Choice_Types/Tools/List_Permutation_2"
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

type_synonym Norm = "ereal list  \<Rightarrow> ereal"

definition norm :: "Norm \<Rightarrow> bool" where
  "norm n \<equiv> (\<forall> (x::ereal list). n x \<ge> 0 \<and> (\<forall> i < length x. (x!i = 0) \<longrightarrow> n x = 0))"

subsection \<open>TODO\<close>

definition symmetry :: "Norm \<Rightarrow> bool" where
  "symmetry n \<equiv> \<forall> xs ys. xs <~~> ys \<longrightarrow> n xs = n ys"

fun l_one :: "Norm" where
  "l_one xs = (\<Sum> i < length xs. \<bar>xs!i\<bar>)"

lemma sum_over_image_of_bijection:
  "bij_betw f A A' \<longrightarrow> (\<Sum> a \<in> A. g a) = (\<Sum> a' \<in> A'. g (the_inv_into A f a'))"
proof (safe, induction "card A" arbitrary: A A')
  case 0
  assume "bij_betw f A A'"
  with 0 have "card A' = 0"
    using bij_betw_same_card
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
    A' :: "'b set"
  assume
    IH: "\<And> A A'. x = card A \<Longrightarrow>
            bij_betw f A A' \<Longrightarrow> sum g A = (\<Sum> a \<in> A'. g (the_inv_into A f a))" and
    suc: "Suc x = card A" and
    bij_A_A': "bij_betw f A A'"
  from suc have "\<exists> a. a \<in> A"
    using card_eq_SucD insertI1
    by metis
  then obtain a where
    a_in_A: "a \<in> A"
    by blast
  have a_compl_A: "insert a (A - {a}) = A"
    using a_in_A
    by fastforce
  from bij_A_A' have inj_on_A_A':
    "inj_on f A \<and> A' = f ` A"
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
  have card_without_a: "card (A - {a}) = x"
    using suc a_in_A Diff_empty card_Diff_insert diff_Suc_1 empty_iff
    by simp
  hence "(\<Sum> a \<in> A. g a) = (\<Sum> a \<in> (A - {a}). g a) + g a"
    using suc add.commute card_Diff1_less_iff insert_Diff
          insert_Diff_single lessI sum.insert_remove
    by metis
  also have "\<dots> = (\<Sum> a' \<in> (A' - {f a}). g (the_inv_into (A - {a}) f a')) + g a"
    using IH[of "(A - {a})" "(A' - {f a})"] bij_without_a card_without_a
    by simp
  also have "\<dots> = (\<Sum> a' \<in> (A' - {f a}). g (the_inv_into A f a')) + g a"
  proof -
    have "\<forall> f A A'. bij_betw f (A::'a set) (A'::'b set) = (inj_on f A \<and> f ` A = A')"
      unfolding bij_betw_def
      by simp
    hence "\<forall> a' \<in> (A' - {f a}). the_inv_into (A - {a}) f a' = the_inv_into A f a'"
      using inj_on_A A'_sub_fa
      by (simp add: inj_on_diff the_inv_into_f_eq)
    thus ?thesis
      by simp
  qed
  also have "\<dots> = (\<Sum> a' \<in> (A' - {f a}). g (the_inv_into A f a')) + g (the_inv_into A f (f a))"
    using a_in_A bij_A_A'
    by (simp add: bij_betw_imp_inj_on the_inv_into_f_f)
  also have "\<dots> = (\<Sum> a' \<in> A'. g (the_inv_into A f a'))"
  proof -
    have "card A' = Suc x \<and> card (A' - {f a}) = x"
      using suc bij_A_A' card_without_a bij_without_a
      by (simp add: bij_betw_same_card)
    thus ?thesis
      using add.commute card_Diff1_less_iff insert_Diff
            insert_Diff_single lessI sum.insert_remove
      by metis
  qed
  finally show "(\<Sum> a \<in> A. g a) = (\<Sum> a' \<in> A'. g (the_inv_into A f a'))"
    by simp
qed

subsection \<open>Property\<close>

lemma l_one_is_symm: "symmetry l_one"
proof (unfold symmetry_def, safe)
  fix
    xs :: "ereal list" and
    ys :: "ereal list"
  assume perm: "xs <~~> ys"
  from perm obtain pi 
    where pi_perm: "pi permutes {..<length xs}" and pi_xs_ys: "permute_list pi xs = ys"
    using mset_eq_permutation
    by metis
  from pi_xs_ys pi_perm have
    "(\<Sum> i < length xs. \<bar>ys!i\<bar>) = (\<Sum> i < length xs. \<bar>xs!(pi i)\<bar>)"
    using permute_list_nth 
    by fastforce
  also from pi_perm have "\<dots> = (\<Sum> i < length xs. \<bar>xs!(pi (inv pi i))\<bar>)"
    using permutes_imp_bij sum_over_image_of_bijection[of pi "{..<length xs}" "{..<length xs}" 
            "\<lambda>i. \<bar>xs ! (pi i)\<bar>"]
    by (smt (verit, ccfv_SIG) bijection.inv_left bijection_def f_the_inv_into_f_bij_betw permutes_bij sum.cong)
  also from pi_perm have "\<dots> = (\<Sum> i < length xs. \<bar>xs!i\<bar>)"
    by (metis permutes_inv_eq)
  finally have "(\<Sum> i < length xs. \<bar>ys!i\<bar>) = (\<Sum> i < length xs. \<bar>xs!i\<bar>)"
    by simp
  moreover from pi_perm pi_xs_ys have "length xs = length ys"
    by auto
  ultimately show "l_one xs = l_one ys"
    by (metis l_one.elims)
qed

end

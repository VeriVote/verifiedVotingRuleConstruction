(*  File:       Auxiliary_Lemmas.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Social-Choice Types\<close>

section \<open>Auxiliary Lemmas\<close>

theory Auxiliary_Lemmas
  imports Main
begin

lemma sum_comp:
  fixes
    f :: "'x \<Rightarrow> 'z :: comm_monoid_add" and
    g :: "'y \<Rightarrow> 'x" and
    X :: "'x set" and
    Y :: "'y set"
  assumes "bij_betw g Y X"
  shows "sum f X = sum (f \<circ> g) Y"
  using assms
proof (induction "card X" arbitrary: X Y f g)
  case 0
  hence "card Y = 0"
    using bij_betw_same_card
    unfolding 0
    by simp
  hence
    "sum f X = 0" and
    "sum (f \<circ> g) Y = 0"
    using 0 card_0_eq sum.empty sum.infinite
    by (metis, metis)
  thus ?case
    by simp
next
  case (Suc n)
  assume
    card_X: "Suc n = card X" and
    bij_g: "bij_betw g Y X"
  obtain x :: "'x"
    where x_in_X: "x \<in> X"
    using card_X
    by fastforce
  hence "bij_betw g (Y - {the_inv_into Y g x}) (X - {x})"
    using bij_g bij_betw_DiffI bij_betw_apply bij_betw_singletonI empty_subsetI
          bij_betw_the_inv_into f_the_inv_into_f_bij_betw insert_subsetI
    by (metis (mono_tags, lifting))
  moreover have "n = card (X - {x})"
    using card_X x_in_X
    by fastforce
  ultimately have "sum f (X - {x}) = sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using Suc
    by metis
  moreover from this have
    "sum (f \<circ> g) Y =
        f (g (the_inv_into Y g x)) + sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using Suc x_in_X bij_g card.infinite f_the_inv_into_f_bij_betw
          nat.discI sum.reindex sum.remove
    unfolding bij_betw_def
    by metis
  moreover have
    "f (g (the_inv_into Y g x)) + sum (f \<circ> g) (Y - {the_inv_into Y g x}) =
      f x + sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using x_in_X bij_g f_the_inv_into_f_bij_betw
    by metis
  moreover have "sum f X = f x + sum f (X - {x})"
    using Suc x_in_X Zero_neq_Suc card.infinite sum.remove
    by metis
  ultimately show ?case
    by simp
qed

lemma the_inv_comp:
  fixes
    f :: "'y \<Rightarrow> 'z" and
    g :: "'x \<Rightarrow> 'y" and
    s :: "'x set" and
    t :: "'y set" and
    u :: "'z set" and
    x :: "'z"
  assumes
    "bij_betw f t u" and
    "bij_betw g s t" and
    "x \<in> u"
  shows "the_inv_into s (f \<circ> g) x = ((the_inv_into s g) \<circ> (the_inv_into t f)) x"
proof (unfold comp_def)
  have el_Y: "the_inv_into t f x \<in> t"
    using assms bij_betw_apply bij_betw_the_inv_into
    by metis
  hence "g (the_inv_into s g (the_inv_into t f x)) = the_inv_into t f x"
    using assms f_the_inv_into_f_bij_betw
    by metis
  moreover have "f (the_inv_into t f x) = x"
    using el_Y assms f_the_inv_into_f_bij_betw
    by metis
  ultimately have "(f \<circ> g) (the_inv_into s g (the_inv_into t f x)) = x"
    by simp
  hence "the_inv_into s (f \<circ> g) x =
      the_inv_into s (f \<circ> g) ((f \<circ> g) (the_inv_into s g (the_inv_into t f x)))"
    by presburger
  also have
    "the_inv_into s (f \<circ> g) ((f \<circ> g) (the_inv_into s g (the_inv_into t f x))) =
      the_inv_into s g (the_inv_into t f x)"
    using assms bij_betw_apply bij_betw_imp_inj_on bij_betw_the_inv_into
          bij_betw_trans the_inv_into_f_eq
    by (metis (no_types, lifting))
  also have "the_inv_into s (f \<circ> g) x = the_inv_into s (\<lambda> x. f (g x)) x"
    using o_apply
    by metis
  finally show "the_inv_into s (\<lambda> x. f (g x)) x = the_inv_into s g (the_inv_into t f x)"
    by presburger
qed

end
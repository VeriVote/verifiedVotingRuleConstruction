section \<open>Auxiliary Results\<close>

theory Auxiliary_Results
  imports Main

begin

lemma sum_comp:
  fixes
    f :: "'x \<Rightarrow> 'z::comm_monoid_add" and
    g :: "'y \<Rightarrow> 'x" and
    X :: "'x set" and
    Y :: "'y set"
  assumes "bij_betw g Y X"
  shows "sum f X = sum (f \<circ> g) Y"
  using assms
proof (induction "card X" arbitrary: X Y f g)
  case 0
  assume "bij_betw g Y X"
  hence "card Y = 0"
    using bij_betw_same_card "0.hyps"
    unfolding "0.hyps"
    by simp
  hence "sum f X = 0 \<and> sum (f \<circ> g) Y = 0"
    using assms 0 card_0_eq sum.empty sum.infinite
    by metis
  thus ?case
    by simp
next
  case (Suc n)
  assume
    card_X: "Suc n = card X" and
    bij: "bij_betw g Y X" and
    hyp: "\<And> X Y f g. n = card X \<Longrightarrow> bij_betw g Y X \<Longrightarrow> sum f X = sum (f \<circ> g) Y"
  then obtain x :: "'x"
    where x_in_X: "x \<in> X"
    by fastforce
  with bij have "bij_betw g (Y - {the_inv_into Y g x}) (X - {x})"
    using bij_betw_DiffI bij_betw_apply bij_betw_singletonI bij_betw_the_inv_into
          empty_subsetI f_the_inv_into_f_bij_betw insert_subsetI
    by (metis (mono_tags, lifting))
  moreover have "n = card (X - {x})"
    using card_X x_in_X
    by fastforce
  ultimately have "sum f (X - {x}) = sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using hyp Suc
    by blast
  moreover have
    "sum (f \<circ> g) Y = f (g (the_inv_into Y g x)) + sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using Suc.hyps(2) x_in_X bij bij_betw_def calculation card.infinite
          f_the_inv_into_f_bij_betw nat.discI sum.reindex sum.remove
    by metis
  moreover have "f (g (the_inv_into Y g x)) + sum (f \<circ> g) (Y - {the_inv_into Y g x}) =
    f x + sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using x_in_X bij f_the_inv_into_f_bij_betw
    by metis
  moreover have "sum f X = f x + sum f (X - {x})"
    using Suc.hyps(2) Zero_neq_Suc x_in_X card.infinite sum.remove
    by metis
  ultimately show ?case
    by simp
qed

end
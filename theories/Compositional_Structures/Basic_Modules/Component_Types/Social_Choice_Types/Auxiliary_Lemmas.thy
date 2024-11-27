(*  File:       Auxiliary_Lemmas.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Social-Choice Types\<close>

section \<open>Auxiliary Lemmas\<close>

theory Auxiliary_Lemmas
  imports Main
begin

text \<open>
  Summation function is invariant under application of a (bijective) permutation on the elements.
\<close>

lemma sum_comp:
  fixes
    f :: "'x \<Rightarrow> ('z :: comm_monoid_add)" and
    g :: "'y \<Rightarrow> 'x" and
    X :: "'x set" and
    Y :: "'y set"
  assumes "bij_betw g Y X"
  shows "(\<Sum> x \<in> X. f x) = (\<Sum> x \<in> Y. (f \<circ> g) x)"
  using assms sum.reindex
  unfolding bij_betw_def
  by (metis (no_types))

text \<open>
  The inversion of a composition of injective functions is equivalent to the composition of the
  two individual inverted functions.
\<close>

lemma the_inv_comp:
  fixes
    X :: "'x set" and
    Y :: "'y set" and
    Z :: "'z set" and
    f :: "'y \<Rightarrow> 'x" and
    g :: "'z \<Rightarrow> 'y" and
    x :: "'x"
  assumes
    "bij_betw f Y X" and
    "bij_betw g Z Y" and
    "x \<in> X"
  shows "the_inv_into Z (f \<circ> g) x = ((the_inv_into Z g) \<circ> (the_inv_into Y f)) x"
  using assms the_inv_into_comp
  unfolding bij_betw_def
  by metis

end
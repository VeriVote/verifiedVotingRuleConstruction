(*  File:       Zip_With.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Zip With\<close>

theory Zip_With
  imports List_Permutation_2
begin

text \<open>
  TODO.
\<close>

subsection \<open>Definition\<close>

fun zip_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zip_with f xs ys = map (case_prod f) (zip xs ys)"

subsection \<open>Auxiliary Lemmata\<close>

lemma zip_with_length:
  fixes
    f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" and
    xs :: "'a list" and
    ys :: "'b list"
  shows "length (zip_with f xs ys) = min (length xs) (length ys)"
  by simp

lemma zip_with_element:
  fixes
    f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" and
    xs :: "'a list" and
    ys :: "'b list"
  shows "\<forall> i < min (length xs) (length ys).
          (zip_with f xs ys)!i = f (xs!i) (ys!i)"
  by simp

subsection \<open>Property\<close>

lemma zipwith_perm_comm:
  fixes
    b :: "nat \<Rightarrow> nat" and
    f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" and
    xs :: "'a list" and
    ys :: "'b list"
  assumes
    bij: "bij_betw b {..< length xs} {..< length xs}" and
    length_eq: "length xs = length ys"
  shows "perm b (zip_with f xs ys) = zip_with f (perm b xs) (perm b ys)"
proof -
  let ?zs = "zip_with f xs ys :: 'c list"
  from length_eq have len_eq: "length ?zs = length xs"
    by simp
  have "\<forall> i < length ?zs. (perm b ?zs)!i = ?zs!(b i)"
    by simp
  moreover have "\<forall> i < length ?zs. ?zs!(b i) = f (xs!(b i)) (ys!(b i))"
  proof (safe)
    fix i :: nat
    assume "i < length (zip_with f xs ys)"
    with len_eq have "i < length xs"
      by presburger
    with len_eq have "(b i) < length ?zs"
      using bij bij_betw_apply lessThan_iff
      by (metis (no_types))
    thus "zip_with f xs ys!b i = f (xs!b i) (ys!b i)"
      by simp
  qed
  moreover have
    "\<forall> i < length ?zs. f (xs!(b i)) (ys!(b i)) = f (perm b xs!i) (perm b ys!i)"
  proof (safe)
    fix i :: nat
    assume i_ok: "i < length (zip_with f xs ys)"
    hence "i < length xs \<and> i < length ys"
      by simp
    hence "xs!(b i) = perm b xs!i"
      using bij
      by simp
    moreover have "ys!(b i) = perm b ys!i"
      using bij i_ok
      by simp
    ultimately show "f (xs!b i) (ys!b i) = f (perm b xs!i) (perm b ys!i)"
      by simp
  qed
  moreover have
    "\<forall> i < length ?zs.
      f (perm b xs!i) (perm b ys!i) = zip_with f (perm b xs) (perm b ys)!i"
    by simp
  ultimately have
    "\<forall> i < length ?zs. (perm b ?zs)!i = zip_with f (perm b xs) (perm b ys)!i"
    by presburger
  moreover have "length (perm b ?zs) = length ?zs"
    using bij
    by simp
  ultimately have
    "\<forall> i < length (perm b ?zs).
      (perm b ?zs)!i = zip_with f (perm b xs) (perm b ys)!i"
    by simp
  moreover have "length (perm b ?zs) =
                 length (zip_with f (perm b xs) (perm b ys))"
    by simp
  ultimately show ?thesis
    using nth_equalityI
    by metis
qed

end

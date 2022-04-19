(*  File:       List_Permutation.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Preliminaries\<close>

section \<open>List Permutation\<close>

theory List_Permutation
  imports Main
begin

text \<open>
  TODO.
\<close>

subsection \<open>Definition\<close>

definition n_permutation :: "nat \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "n_permutation n pi \<equiv>
    (\<forall> xs. length (pi xs) = length xs) \<and>
    (\<exists> b. bij_betw b {..< n} {..< n} \<and>
          (\<forall> xs. length xs = n \<longrightarrow> (\<forall> i < length xs. (pi xs)!i = xs!(b i))))"

definition newnameforpermut :: "('a list \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "newnameforpermut pi \<equiv> \<forall> n. n_permutation n pi"

subsection \<open>Auxiliary Functions\<close>

(* TODO: Maybe replace 'perm' with 'HOL-Combinatorics.Permutations.permute_list' *)
fun perm :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "perm b xs = map (\<lambda> (x, i). xs!(b i)) (zip xs [0..< length xs])"

fun bij :: "nat \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> nat \<Rightarrow> nat" where
  "bij n pi =
    (SOME b. bij_betw b {..< n} {..< n} \<and>
             (\<forall> xs. length xs = n \<longrightarrow> (\<forall> i < length xs. (pi xs)!i = xs!(b i))))"

fun inverse_perm :: "('a list \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inverse_perm pi xs = perm (the_inv_into {..< length xs} (bij (length xs) pi)) xs"

fun generalize_perm :: "('a list \<Rightarrow> 'a list) \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "generalize_perm pi xs = perm (bij (length xs) pi) xs"

subsection \<open>Auxiliary Lemmata\<close>

lemma bij_inv_bij:
  fixes
    n :: nat and
    b :: "nat \<Rightarrow> nat"
  assumes "bij_betw b {..< n} {..< n}"
  shows "bij_betw (the_inv_into {..< n} b) {..< n} {..< n}"
  using assms bij_betw_the_inv_into
  by metis

lemma perm_of_bij_is_perm:
  fixes
    b :: "nat \<Rightarrow> nat" and
    n :: nat
  assumes "bij_betw b {..< n} {..< n}"
  shows "n_permutation n (perm b)"
proof (unfold n_permutation_def, rule conjI)
  show "\<forall> xs. length (perm b xs) = length xs"
    by simp
next
  from assms
  have "bij_betw b {..< n} {..< n} \<and>
        (\<forall> xs. length xs = n \<longrightarrow> (\<forall> i < length xs. perm b xs!i = xs!b i))"
    by simp
  thus "\<exists> ba. bij_betw ba {..< n} {..< n} \<and>
        (\<forall> xs. length xs = n \<longrightarrow> (\<forall> i < length xs. perm b xs!i = xs!ba i))"
    by metis
qed

lemma bij_of_perm_is_bij:
  fixes
    pi :: "'a list \<Rightarrow> 'a list" and
    n :: nat
  assumes "n_permutation n pi"
  shows "bij_betw (bij n pi) {..< n} {..< n}"
proof -
  let ?P =
    "\<lambda> b. bij_betw b {..< n} {..< n} \<and>
      (\<forall> xs. length xs = n \<longrightarrow> (\<forall> i < length xs. (pi xs)!i = xs!(b i)))"
  have "\<exists> b. ?P b"
    using assms
    unfolding n_permutation_def
    by auto
  hence "?P (SOME b. ?P b)"
    using Hilbert_Choice.someI_ex[of ?P]
    by blast
  thus "bij_betw (bij n pi) {..< n} {..< n}"
    by auto
qed

lemma bij_of_perm_item_mapping:
  fixes
    pi :: "'a list \<Rightarrow> 'a list" and
    n :: nat
  assumes "n_permutation n pi"
  shows "\<forall> xs. length xs = n \<longrightarrow> (\<forall> i < length xs. (pi xs)!i = xs!((bij n pi) i))"
proof -
  let ?P =
    "\<lambda> b. bij_betw b {..< n} {..< n} \<and>
      (\<forall> xs. length xs = n \<longrightarrow> (\<forall> i < length xs. (pi xs)!i = xs!(b i)))"
  have "\<exists> b. ?P b"
    using assms
    unfolding n_permutation_def
    by simp
  hence "?P (SOME b. ?P b)"
    using Hilbert_Choice.someI_ex[of ?P]
    by blast
  thus "\<forall> xs. length xs = n \<longrightarrow>
        (\<forall> i < length xs. (pi xs)!i = xs!((bij n pi) i))"
    by simp
qed

lemma perm_bij_is_id:
  fixes
    n :: nat and
    xs :: "'a list"
  assumes
    l: "length xs = n" and
    perm: "n_permutation n pi"
  shows "pi xs = perm (bij n pi) xs"
proof -
  let ?P =
    "\<lambda> b. bij_betw b {..< n} {..< n} \<and>
      (\<forall> xs. length xs = n \<longrightarrow> (\<forall> i < length xs. (pi xs)!i = xs!(b i)))"
  from perm
  have "\<exists> b. ?P b"
    unfolding n_permutation_def
    by simp
  hence "?P (SOME b. ?P b)"
    using bij.elims bij_of_perm_is_bij bij_of_perm_item_mapping perm
    by (metis (mono_tags, lifting))
  hence "\<forall> i < length xs. (pi xs)!i = xs!((bij n pi) i)"
    using l bij_of_perm_item_mapping perm
    by (metis (no_types, opaque_lifting))
  hence "\<forall> i < length xs. (pi xs)!i = perm (bij n pi) xs!i"
    by auto
  moreover have "length (pi xs) = length (perm (bij n pi) xs)"
    using perm
    unfolding n_permutation_def
    by auto
  ultimately show ?thesis
    using nth_equalityI perm
    unfolding n_permutation_def
    by metis
qed

lemma perm_b_perm_inv_b_is_id:
  fixes
    xs :: "'a list" and
    b :: "nat \<Rightarrow> nat"
  assumes "bij_betw b {..< length xs} {..< length xs}"
  shows "perm b (perm (the_inv_into {..< length xs} b) xs) = xs"
proof -
  let ?inv_b = "the_inv_into {..< length xs} b"
  from assms
  have bij: "bij_betw ?inv_b {..< length xs} {..< length xs}"
    using bij_inv_bij
    by simp
  have "\<forall> i < length xs. xs!i = perm b (perm ?inv_b xs)!i"
  proof (safe)
    fix i :: nat
    assume l: "i < length xs"
    have any_idx: "\<forall> j \<in> {..< length xs}. b j \<in> {..< length xs}"
      using assms bij_betwE
      by metis
    have "perm b (perm ?inv_b xs)!i = (perm ?inv_b xs)!b i"
      using l
      by simp
    also have "\<dots> = xs!(?inv_b (b i))"
      using l any_idx
      by simp
    also have "\<dots> = xs!i"
      using l assms bij_betw_imp_inj_on lessThan_iff the_inv_into_f_f
      by metis
    finally show "xs!i = perm b (perm (the_inv_into {..< length xs} b) xs)!i"
      by simp
  qed
  moreover have "length xs = length (perm b (perm ?inv_b xs))"
    by simp
  ultimately show ?thesis
    using nth_equalityI
    by metis
qed

lemma inverse_perm_preserves_perm:
  fixes pi :: "'a list \<Rightarrow> 'a list"
  assumes "newnameforpermut pi"
  shows "newnameforpermut (inverse_perm pi)"
proof (unfold newnameforpermut_def n_permutation_def, safe)
  fix
    n :: nat and
    xs :: "'a list"
  show "length (inverse_perm pi xs) = length xs"
    using perm_of_bij_is_perm
    by simp
next
  fix n :: nat
  let ?b_inv = "the_inv_into {..< n} (bij n pi)"
  have  "bij_betw ?b_inv {..< n} {..< n}"
    using bij_of_perm_is_bij bij_inv_bij assms
    unfolding newnameforpermut_def
    by blast
  hence "bij_betw ?b_inv {..< n} {..< n} \<and>
             (\<forall> xs. length xs = n \<longrightarrow>
              (\<forall> i < length xs. inverse_perm pi xs!i = xs!?b_inv i))"
    by simp
  thus "\<exists> b. bij_betw b {..< n} {..< n} \<and>
           (\<forall> xs. length xs = n \<longrightarrow>
            (\<forall> i < length xs. inverse_perm pi xs!i = xs!b i))"
    by metis
qed

lemma pi_inverse_perm_pi_is_id:
  fixes
    pi::"'a list \<Rightarrow> 'a list" and
    xs::"'a list"
  assumes "newnameforpermut pi"
  shows "pi (inverse_perm pi xs) = xs"
proof -
  let ?b = "bij (length xs) pi"
  have bij_b: "bij_betw ?b {..< length xs} {..< length xs}"
    using assms bij_of_perm_is_bij
    unfolding newnameforpermut_def
    by blast
  have "pi (inverse_perm pi xs) = pi (perm (the_inv_into {..< length xs} ?b) xs)"
    by simp
  also have "\<dots> = perm ?b (perm (the_inv_into {..< length xs} ?b) xs)"
    using assms perm_bij_is_id[of "perm (the_inv_into {..< length xs} ?b) xs"]
    unfolding newnameforpermut_def
    by simp
  also from bij_b have "\<dots> = xs"
    using perm_b_perm_inv_b_is_id
    by simp
  finally show ?thesis
    by simp
qed

lemma generalize_perm_preserves_perm:
  fixes pi :: "'a list \<Rightarrow> 'a list"
  assumes "newnameforpermut pi"
  shows "newnameforpermut (generalize_perm pi)"
proof (unfold newnameforpermut_def n_permutation_def, safe)
  fix
    n :: nat and
    xs :: "'b list"
  have "n_permutation (length xs) (perm (bij (length xs) pi))"
    using assms bij_of_perm_is_bij[of "length xs" pi]
          perm_of_bij_is_perm[of "bij (length xs) pi" "length xs"]
    unfolding newnameforpermut_def
    by simp
  thus "length (generalize_perm pi xs) = length xs"
    by simp
next
  fix
    n :: nat
  have "bij_betw (bij n pi) {..< n} {..< n} \<and>
       (\<forall> xs. length xs = n \<longrightarrow>
        (\<forall> i < length xs. generalize_perm pi xs!i = xs!(bij n pi) i))"
    using assms bij_of_perm_is_bij
    unfolding newnameforpermut_def
    by fastforce
  thus "\<exists> b. bij_betw b {..< n} {..< n} \<and>
             (\<forall> xs. length xs = n \<longrightarrow>
              (\<forall> i < length xs. generalize_perm pi xs!i = xs!b i))"
    by metis
qed

lemma generalize_perm_preserves_mapping:
  fixes
    pi :: "'a list \<Rightarrow> 'a list" and
    p :: "'a list"
  assumes "n_permutation (length p) pi"
  shows "generalize_perm pi p = pi p"
  using perm_bij_is_id[of p] assms
  by simp

end

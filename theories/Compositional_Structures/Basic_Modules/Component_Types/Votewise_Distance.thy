(*  File:       Votewise_Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Votewise Distance\<close>

theory Votewise_Distance
  imports "Social_Choice_Types/Tools/Zip_With"
          "Distance"
          "Norm"
begin

text \<open>
  Votewise distances are a natural class of distances on elections distances
  which depend on the submitted votes in a simple and transparent manner.
  They are formed by using any distance d on individual orders and combining
  the components with a norm on R to n.
\<close>

subsection \<open>Definition\<close>

fun votewise_distance :: "'a Vote Distance \<Rightarrow> Norm \<Rightarrow> ('a set \<times> 'a Profile) Distance" where
  "votewise_distance d n (A, xs) (A', ys) =
    (if length xs = length ys \<and> (length xs > 0 \<or> A = A')
    then n (zip_with (\<lambda> x y. d (A, x) (A', y)) xs ys)
    else \<infinity>)"

subsection \<open>TODO\<close>

lemma el_dist_anon_if_norm_symm:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm"
  assumes "symmetry n"
  shows "el_distance_anonymity (votewise_distance d n)"
proof (unfold el_distance_anonymity_def, safe)
  fix
    A  :: "'a set" and
    A' :: "'a set" and
    pi :: "'a Profile \<Rightarrow> 'a Profile" and
    p  :: "'a Profile" and
    p' :: "'a Profile"
  assume perm: "newnameforpermut pi"
  show "votewise_distance d n (A, p) (A', p')
        = votewise_distance d n (A, pi p) (A', pi p')"
  proof (cases "length p = length p'")
    case False
    with perm
    show ?thesis
      unfolding newnameforpermut_def n_permutation_def
      by simp
  next
    case True
    from perm
    have perm_gen_perm_pi: "newnameforpermut (generalize_perm pi)"
      using generalize_perm_preserves_perm
      by metis
    with True
    have "votewise_distance d n (A, p) (A', p')
           = n (zip_with (\<lambda> x y. d (A, x) (A', y)) p p')"
      by simp
    also from assms perm_gen_perm_pi have
      "\<dots> = n (generalize_perm pi (zip_with (\<lambda> x y. d (A, x) (A', y)) p p'))"
      unfolding symmetry_def
      by (metis (no_types, lifting))
    also from True have
      "\<dots> = n (zip_with (\<lambda> x y. d (A, x) (A', y)) (generalize_perm pi p) (generalize_perm pi p'))"
      using perm bij_of_perm_is_bij[of "length p" pi]
            zipwith_perm_comm[of "bij (length p) pi" p p' "(\<lambda> x y. d (A, x) (A', y))"]
      unfolding newnameforpermut_def
      by simp
    also have "\<dots> = n (zip_with (\<lambda> x y. d (A, x) (A', y)) (pi p) (pi p'))"
      using perm generalize_perm_preserves_mapping[of p]
            generalize_perm_preserves_mapping[of p']
      unfolding newnameforpermut_def
      by simp
    also have "\<dots> = votewise_distance d n (A, pi p) (A', pi p')"
      using True perm
      unfolding newnameforpermut_def n_permutation_def
      by simp
    finally show ?thesis
      by simp
  qed
qed

end

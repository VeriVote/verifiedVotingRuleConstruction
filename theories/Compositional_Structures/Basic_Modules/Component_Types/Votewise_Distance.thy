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
    pi :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
    p  :: "'a Profile" and
    p' :: "'a Profile"
  assume perm: "is_perm pi"
  show "votewise_distance d n (A, p) (A', p')
        = votewise_distance d n (A, build_perm pi p) (A', build_perm pi p')"
  proof (cases "length p = length p'")
    case False
    with perm
    show ?thesis
      by simp
  next
    case True
    hence "votewise_distance d n (A, p) (A', p')
           = n (zip_with (\<lambda> x y. d (A, x) (A', y)) p p')"
      by simp
    also from assms have
      "\<dots> = n (build_perm pi (zip_with (\<lambda> x y. d (A, x) (A', y)) p p'))"
      using perm
      unfolding symmetry_def
      by (metis (mono_tags, lifting))
    also have "\<dots> = n (build_perm pi (map (case_prod (\<lambda>x y. d (A,x) (A',y))) (zip p p')))"
      by simp
    also have "\<dots> = n (map (case_prod (\<lambda>x y. d (A,x) (A',y))) (build_perm pi (zip p p')))"
      using permute_list_map[of \<open>pi (length p)\<close> \<open>zip p p'\<close> \<open>case_prod (\<lambda>x y. d (A,x) (A',y))\<close>] perm True 
      unfolding is_perm_def 
      by auto
    also have "\<dots> = n (zip_with (\<lambda>x y. d (A,x) (A',y)) (build_perm pi p) (build_perm pi p'))"
      using permute_list_zip[of \<open>pi (length p)\<close> \<open>{..< length p}\<close> p p'] perm True 
      unfolding is_perm_def
      by simp
    also have "\<dots> = votewise_distance d n (A, build_perm pi p) (A', build_perm pi p')"
      using True
      by auto
    finally show ?thesis
      by simp
  qed
qed

end

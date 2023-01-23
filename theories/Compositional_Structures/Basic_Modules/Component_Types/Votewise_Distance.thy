(*  File:       Votewise_Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Votewise Distance\<close>

theory Votewise_Distance
  imports "Distance"
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
    then n (map2 (\<lambda> x y. d (A, x) (A', y)) xs ys)
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
  let ?listpi = "\<lambda> xs. permute_list (pi (length xs)) xs"
  let ?q = "?listpi p" and
      ?q' = "?listpi p'"
  assume perm: "\<forall>n. pi n permutes {..< n}"
  hence "\<forall> zs. pi (length zs) permutes {..< length zs}"
    by metis
  hence listpi_sym: "\<forall> zs. ?listpi zs <~~> zs"
    using mset_permute_list
    by metis
  show "votewise_distance d n (A, p) (A', p')
        = votewise_distance d n (A, ?q) (A', ?q')"
  proof (cases "length p = length p' \<and> (length p > 0 \<or> A = A')")
    case False
    with perm
    show ?thesis
      by auto
  next
    case True
    hence "votewise_distance d n (A, p) (A', p')
           = n (map2 (\<lambda> x y. d (A, x) (A', y)) p p')"
      by auto
    also from assms listpi_sym
    have
      "\<dots> = n (?listpi (map2 (\<lambda> x y. d (A, x) (A', y)) p p'))"
      unfolding symmetry_def
      by (metis (no_types, lifting))
    also have "\<dots> = n (map (case_prod (\<lambda>x y. d (A,x) (A',y))) (?listpi (zip p p')))"
      using permute_list_map[of \<open>pi (length p)\<close> \<open>zip p p'\<close> \<open>case_prod (\<lambda>x y. d (A,x) (A',y))\<close>]
            perm True
      by simp
    also have "\<dots> = n (map2 (\<lambda>x y. d (A,x) (A',y)) (?listpi p) (?listpi p'))"
      using permute_list_zip[of \<open>pi (length p)\<close> \<open>{..< length p}\<close> p p'] perm True
      by simp
    also have "\<dots> = votewise_distance d n (A, ?listpi p) (A', ?listpi p')"
      using True
      by auto
    finally show ?thesis
      by simp
  qed
qed

end

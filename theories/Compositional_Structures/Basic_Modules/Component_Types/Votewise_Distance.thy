(*  File:       Votewise_Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Votewise Distance\<close>

theory Votewise_Distance
  imports "Social_Choice_Types/Norm"
          "Distance"
begin

text \<open>
  Votewise distances are a natural class of distances on elections
  which depend on the submitted votes in a simple and transparent manner.
  They are formed by using any distance d on individual orders and combining
  the components with a norm on \<real>^n.
\<close>

subsection \<open>Definition\<close>

fun votewise_distance :: "'a Vote Distance \<Rightarrow> Norm 
  \<Rightarrow> ('a,'v::linorder) Election Distance" where
  "votewise_distance d n (A, V, p) (A', V', p') =
    (if (finite V) \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')
    then n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))
    else \<infinity>)"

(* export_code votewise_distance in Haskell *)

subsection \<open>Inference Rules\<close>

(* lemma symmetric_norm_imp_distance_anonymous:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm"
  assumes "symmetry n"
  shows "distance_anonymity (votewise_distance d n)"
proof (unfold distance_anonymity_def, safe)
  fix
    A  :: "'a set" and
    A' :: "'a set" and
    pi :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
    p  :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  let ?z = "zip p p'" and
      ?lt_len = "\<lambda> i. {..< length i}" and
      ?pi_len = "\<lambda> i. pi (length i)" and
      ?c_prod = "case_prod (\<lambda> q q'. d (A, q) (A', q'))"
  let ?listpi = "\<lambda> q. permute_list (?pi_len q) q"
  let ?q = "?listpi p" and
      ?q' = "?listpi p'"
  assume perm: "\<forall> n. pi n permutes {..< n}"
  hence listpi_sym: "\<forall> l. ?listpi l <~~> l"
    using mset_permute_list
    by metis
  show "votewise_distance d n (A, p) (A', p') = votewise_distance d n (A, ?q) (A', ?q')"
  proof (cases "length p = length p' \<and> (0 < length p \<or> A = A')")
    case False
    thus ?thesis
      using perm
      by auto
  next
    case True
    hence "votewise_distance d n (A, p) (A', p') = n (map2 (\<lambda> x y. d (A, x) (A', y)) p p')"
      by auto
    also have "\<dots> = n (?listpi (map2 (\<lambda> x y. d (A, x) (A', y)) p p'))"
      using assms listpi_sym
      unfolding symmetry_def
      by (metis (no_types, lifting))
    also have "\<dots> = n (map (case_prod (\<lambda> x y. d (A, x) (A', y))) (?listpi (zip p p')))"
      using permute_list_map[of \<open>?pi_len p\<close> ?z ?c_prod] perm True
      by simp
    also have "\<dots> = n (map2 (\<lambda> x y. d (A, x) (A', y)) (?listpi p) (?listpi p'))"
      using permute_list_zip[of \<open>?pi_len p\<close> \<open>?lt_len p\<close> p p'] perm True
      by simp
    also have "\<dots> = votewise_distance d n (A, ?listpi p) (A', ?listpi p')"
      using True
      by auto
    finally show ?thesis
      by simp
  qed
qed *)

lemma symmetric_norm_imp_distance_anonymous:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm"
  assumes "symmetry n"
  shows "distance_anonymity (votewise_distance d n)"
proof (unfold distance_anonymity_def, safe, cases)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v::linorder set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  let ?rn1 = "(rename \<pi> (A, V, p))" and 
      ?rn2 = "(rename \<pi> (A', V', p'))"
  assume
    bij: "bij \<pi>" and
    fin_V: "(finite V) \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')"
  hence "votewise_distance d n (A, V, p) (A', V', p') 
            = n (map2 (\<lambda> x y. d (A, x) (A', y)) (to_list V p) (to_list V' p'))"
    by auto
  have "(to_list V p) <~~> (to_list (fst (snd ?rn1)) (snd (snd ?rn1)))"
    using to_list_permutes_under_bij rename.simps bij fst_conv snd_conv
    by metis
  moreover have "(to_list V' p') <~~> (to_list (fst (snd ?rn2)) (snd (snd ?rn2)))"
    using to_list_permutes_under_bij rename.simps bij fst_conv snd_conv
    by metis
  ultimately have "map2 (\<lambda> x y. d (A, x) (A', y)) (to_list V p) (to_list V' p')
      <~~> map2 (\<lambda> x y. d (fst ?rn1, x) (fst ?rn2, y)) 
                    (to_list (fst (snd ?rn1)) (snd (snd ?rn1))) 
                    (to_list (fst (snd ?rn2)) (snd (snd ?rn2)))"
    sorry
  moreover have "votewise_distance d n ?rn1 ?rn2
            = n (map2 (\<lambda> x y. d (fst ?rn1, x) (fst ?rn2, y)) 
                    (to_list (fst (snd ?rn1)) (snd (snd ?rn1))) 
                    (to_list (fst (snd ?rn2)) (snd (snd ?rn2))))"
  proof -
    have "(finite (fst (snd ?rn1))) \<and> (fst (snd ?rn1)) = (fst (snd ?rn2)) 
            \<and> ((fst (snd ?rn1)) \<noteq> {} \<or> (fst ?rn1) = (fst ?rn2))"
      using fin_V bij
      by force
    thus ?thesis 
      by auto
  qed
  ultimately show "votewise_distance d n (A, V, p) (A', V', p') 
                    = votewise_distance d n ?rn1 ?rn2"
    using \<open>symmetry n\<close>
    by (simp add: symmetry_def)
next
    fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v::linorder set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  let ?rn1 = "(rename \<pi> (A, V, p))" and ?rn2 = "(rename \<pi> (A', V', p'))"
  assume
    bij: "bij \<pi>" and
    inf_V:  "\<not>((finite V) \<and> V = V' \<and> (V \<noteq> {} \<or> A = A'))"
  hence inf_dist: "votewise_distance d n (A, V, p) (A', V', p') = infinity"
    by auto
  moreover have "infinite V \<Longrightarrow> infinite (fst (snd ?rn1))" 
    using bij rename.simps Pair_inject bij_betw_finite
          bij_betw_subset inf_V prod.exhaust_sel subset_UNIV
    by metis
  moreover have "V \<noteq> V' \<Longrightarrow> (fst (snd ?rn1)) \<noteq> (fst (snd ?rn2))"
    using bij rename.simps bij_def fst_conv inj_image_mem_iff 
          snd_conv subsetI subset_antisym
    by metis
  moreover have "V = {} \<Longrightarrow> (fst (snd ?rn1)) = {}"
    using bij
    by simp
  moreover have "A = A' \<Longrightarrow> fst ?rn1 = fst ?rn2"
    by simp
  ultimately have 
    "votewise_distance d n ?rn1 ?rn2 = infinity"
    using inf_V 
    by auto
  thus "votewise_distance d n (A, V, p) (A', V', p') = votewise_distance d n ?rn1 ?rn2"
    using inf_dist
    by simp
qed

end

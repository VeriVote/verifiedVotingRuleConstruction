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

lemma zip_perm: 
  fixes
    l_1 :: "'a list" and 
    l_2 :: "'a list" and 
    ls_1 :: "'a list" and 
    ls_2 :: "'a list" and
    \<pi> :: "nat \<Rightarrow> nat" and
    n :: "nat"
  assumes
    "\<pi> permutes {..< length l_1}" and
    "ls_1 = permute_list \<pi> l_1" and 
    "ls_2 = permute_list \<pi> l_2" and
    "length ls_2 = n" and
    "length l_2 = n" and
    "length ls_1 = n" and
    "length l_1 = n"
  shows "permute_list \<pi> (zip l_1 l_2) = zip ls_1 ls_2"
proof (simp add: assms, unfold permute_list_def, simp add: assms)
  have "\<forall>j < n. (map (\<lambda>i. zip l_1 l_2 ! \<pi> i) [0..<n])!j = (l_1 ! \<pi> j, l_2 ! \<pi> j)"
    using assms
    by (simp add: atLeast_upt permutes_nat_less)
  moreover have "\<forall>j < n. zip (map (\<lambda>i. l_1 ! \<pi> i) [0..<n]) (map (\<lambda>i. l_2 ! \<pi> i) [0..<n])!j 
              = (l_1 ! \<pi> j, l_2 ! \<pi> j)"
    using assms
    by auto
  ultimately have "\<forall>j < n. ((map (\<lambda>i. zip l_1 l_2 ! \<pi> i) [0..<n])!j
                   = zip (map (\<lambda>i. l_1 ! \<pi> i) [0..<n]) (map (\<lambda>i. l_2 ! \<pi> i) [0..<n])!j)"
    using assms
    by simp
  moreover have "length (zip l_1 l_2) = n" 
    using assms 
    by auto
  ultimately show "map (\<lambda>i. zip l_1 l_2 ! \<pi> i) [0..<n] 
                   = zip (map (\<lambda>i. l_1 ! \<pi> i) [0..<n]) (map (\<lambda>i. l_2 ! \<pi> i) [0..<n])"
    using assms permute_list_def permute_list_zip
    by metis
qed
    
lemma map_perm:
  fixes
    l :: "'a list" and 
    ls :: "'a list"
  assumes
    "l <~~> ls"
  shows "map f l <~~> map f ls"
  by (simp add: assms)

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
      ?img_V = "\<pi> ` V" and
      ?q_p = "(\<lambda>v. p (the_inv \<pi> v))" and
      ?img_V' = "\<pi> ` V'" and
      ?q_p' = "(\<lambda>v. p' (the_inv \<pi> v))" and
      ?rn2 = "(rename \<pi> (A', V', p'))" and
      ?perm = "(\<lambda>i. (card ({v\<in>(\<pi> ` V). v < \<pi> ((sorted_list_of_set V)!i)})))"
  assume
    bij: "bij \<pi>" and
    fin_V: "(finite V) \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')"
  hence dist_eq_norm: "votewise_distance d n (A, V, p) (A', V', p') 
                       = n (map2 (\<lambda> x y. d (A, x) (A', y)) (to_list V p) (to_list V' p'))"
    by auto
  have img_list_eq_list_V: "(to_list (fst (snd ?rn1)) (snd (snd ?rn1))) = to_list ?img_V ?q_p"
    using rename.simps 
    by auto
  hence img_list_perm_list_V: 
    "(to_list V p) = permute_list ?perm (to_list (fst (snd ?rn1)) (snd (snd ?rn1)))"
    using assms to_list_permutes_under_bij bij to_list_permutes_under_bij
    by (metis (no_types))
  have img_list_eq_list_V': "(to_list (fst (snd ?rn2)) (snd (snd ?rn2))) = to_list ?img_V' ?q_p'"
    using rename.simps 
    by auto
  hence img_list_perm_list_V': 
    "(to_list V' p') = permute_list ?perm (to_list (fst (snd ?rn2)) (snd (snd ?rn2)))"
    by (metis (no_types) fin_V bij to_list_permutes_under_bij)
  have "map2 (\<lambda> x y. d (A, x) (A', y)) (to_list V p) (to_list V' p')
        <~~> map2 (\<lambda> x y. d (fst ?rn1, x) (fst ?rn2, y)) 
                    (to_list (fst (snd ?rn1)) (snd (snd ?rn1))) 
                    (to_list (fst (snd ?rn2)) (snd (snd ?rn2)))"
  proof -
    have "map2 (\<lambda> x y. d (fst ?rn1, x) (fst ?rn2, y)) 
                  (to_list (fst (snd ?rn1)) (snd (snd ?rn1))) 
                  (to_list (fst (snd ?rn2)) (snd (snd ?rn2)))
          = map (\<lambda>(x,y). d (A, x) (A', y)) 
                  (zip
                    (to_list (fst (snd ?rn1)) (snd (snd ?rn1)))
                    (to_list (fst (snd ?rn2)) (snd (snd ?rn2))))"
      by simp
    moreover have "map2 (\<lambda> x y. d (A, x) (A', y)) (to_list V p) (to_list V' p')
                   = map (\<lambda>(x,y). d (A, x) (A', y)) (zip (to_list V p) (to_list V' p'))"
      by simp 
    moreover have "(zip
                      (to_list (fst (snd ?rn1)) (snd (snd ?rn1)))
                      (to_list (fst (snd ?rn2)) (snd (snd ?rn2))))
                    <~~> (zip (to_list V p) (to_list V' p'))"
    proof -
      let ?n = "length (to_list V p)"
      have "V = V'" using fin_V by auto
      hence "length (to_list V' p') = ?n"
        by (simp add: length_inv)
      moreover have length_V: "length (to_list (fst (snd ?rn1)) (snd (snd ?rn1))) = ?n"
        using bij rename.simps img_list_perm_list_V fst_conv 
              length_permute_list snd_conv to_list_permutes_under_bij
        by (metis (mono_tags, lifting))
      moreover have length_V': "length (to_list (fst (snd ?rn2)) (snd (snd ?rn2))) = ?n"
        using bij img_list_eq_list_V' img_list_perm_list_V'
              length_permute_list to_list.simps fin_V length_inv 
        by (metis (no_types, lifting))
      moreover have permutation: "?perm permutes {..<?n}" sorry (* TODO *)
      ultimately have 
        "permute_list ?perm (zip (to_list (fst (snd ?rn1)) (snd (snd ?rn1))) 
                                 (to_list (fst (snd ?rn2)) (snd (snd ?rn2))))
         = zip (to_list V p) (to_list V' p')"
        using img_list_perm_list_V img_list_perm_list_V' zip_perm zip_perm
        by (metis (no_types, lifting))
      thus ?thesis
        using length_V length_V' length_zip min.idem mset_permute_list permutation
        by (metis (no_types, lifting))
    qed
    ultimately show ?thesis 
      using map_perm
      by simp
  qed
  moreover have "votewise_distance d n ?rn1 ?rn2
            = n (map2 (\<lambda> x y. d (fst ?rn1, x) (fst ?rn2, y)) 
                    (to_list (fst (snd ?rn1)) (snd (snd ?rn1))) 
                    (to_list (fst (snd ?rn2)) (snd (snd ?rn2))))"
  proof -
    have "(finite (fst (snd ?rn1))) \<and> (fst (snd ?rn1)) = (fst (snd ?rn2)) 
            \<and> ((fst (snd ?rn1)) \<noteq> {} \<or> (fst ?rn1) = (fst ?rn2))"
      using fin_V bij
      by auto
    thus ?thesis 
      by auto
  qed
  ultimately show "votewise_distance d n (A, V, p) (A', V', p') 
                    = votewise_distance d n ?rn1 ?rn2"
    using \<open>symmetry n\<close> dist_eq_norm symmetry_def
    by auto
next
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
    inf_V: "\<not>((finite V) \<and> V = V' \<and> (V \<noteq> {} \<or> A = A'))"
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

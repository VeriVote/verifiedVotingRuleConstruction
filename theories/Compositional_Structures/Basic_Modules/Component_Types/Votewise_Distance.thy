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
  the components with a norm on $\mathbb{R}^n$.
\<close>

subsection \<open>Definition\<close>

fun votewise_distance :: "'a Vote Distance \<Rightarrow> Norm 
  \<Rightarrow> ('a,'v::linorder) Election Distance" where
  "votewise_distance d n (A, V, p) (A', V', p') =
    (if (finite V) \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')
    then n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))
    else \<infinity>)"

subsection \<open>Inference Rules\<close>

lemma symmetric_norm_inv_under_map2_permute:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm" and
    A  :: "'a set" and
    A' :: "'a set" and
    \<phi> :: "nat \<Rightarrow> nat" and
    p  :: "('a Preference_Relation) list" and
    p' :: "('a Preference_Relation) list"
  assumes
    perm: "\<phi> permutes {0 ..< length p}" and
    len_eq: "length p = length p'" and
    sym_n: "symmetry n"
  shows "n (map2 (\<lambda> q q'. d (A, q) (A', q')) p p')
         = n (map2 (\<lambda> q q'. d (A, q) (A', q')) (permute_list \<phi> p) (permute_list \<phi> p'))"
proof -
  let ?z = "zip p p'" and
      ?lt_len = "\<lambda> i. {..< length i}" and
      ?c_prod = "case_prod (\<lambda> q q'. d (A, q) (A', q'))"
  let ?listpi = "\<lambda> q. permute_list \<phi> q"
  let ?q = "?listpi p" and
      ?q' = "?listpi p'"
  have listpi_sym: "\<forall> l. (length l = length p \<longrightarrow> ?listpi l <~~> l)"
    using mset_permute_list perm atLeast_upt
    by simp
  moreover have "length (map2 (\<lambda> x y. d (A, x) (A', y)) p p') = length p"
    using len_eq
    by simp
  ultimately have "(map2 (\<lambda> q q'. d (A, q) (A', q')) p p')
                   <~~> (?listpi (map2 (\<lambda> x y. d (A, x) (A', y)) p p'))"
    by metis
  hence "n (map2 (\<lambda> q q'. d (A, q) (A', q')) p p')
         = n (?listpi (map2 (\<lambda> x y. d (A, x) (A', y)) p p'))"
    using sym_n
    unfolding symmetry_def
    by blast
  also have "... = n (map (case_prod (\<lambda> x y. d (A, x) (A', y)))
                          (?listpi (zip p p')))"
    using permute_list_map[of \<phi> ?z ?c_prod] perm len_eq atLeast_upt
    by simp
  also have "... = n (map2 (\<lambda> x y. d (A, x) (A', y)) (?listpi p) (?listpi p'))"
    using len_eq perm atLeast_upt
    by (simp add: permute_list_zip)
  finally show ?thesis
    by simp
qed

lemma permute_invariant_under_map:
  fixes
    l :: "'a list" and
    ls :: "'a list"
  assumes "l <~~> ls"
  shows "map f l <~~> map f ls"
  using assms
  by simp

lemma linorder_rank_injective:
  fixes
    V :: "'v::linorder set" and
    v :: "'v" and
    v' :: "'v"
  assumes
    v_in_V: "v \<in> V" and
    v'_in_V: "v' \<in> V" and
    v'_neq_v: "v' \<noteq> v" and
    fin_V: "finite V"
  (* the rank of v in an ordered list of V is the amount of smaller elements in V *)
  shows "card {x \<in> V. x < v} \<noteq> card {x \<in> V. x < v'}"
proof -
  have "v < v' \<or> v' < v"
    using v'_neq_v linorder_less_linear
    by metis
  hence "{x \<in> V. x < v} \<subset> {x \<in> V. x < v'} \<or> {x \<in> V. x < v'} \<subset> {x \<in> V. x < v}"
    using v_in_V v'_in_V dual_order.strict_trans
    by blast
  thus ?thesis
    using assms sorted_list_of_set_nth_equals_card
    by (metis (full_types))
qed

lemma permute_invariant_under_coinciding_funs:
  fixes
    l :: "'v list" and
    \<pi>_1 :: "nat \<Rightarrow> nat" and
    \<pi>_2 :: "nat \<Rightarrow> nat"
  assumes "\<forall> i < length l. \<pi>_1 i = \<pi>_2 i"
  shows "permute_list \<pi>_1 l = permute_list \<pi>_2 l"
  using assms
  unfolding permute_list_def
  by simp

lemma symmetric_norm_imp_distance_anonymous:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm"
  assumes "symmetry n"
  shows "distance_anonymity (votewise_distance d n)"
proof (unfold distance_anonymity_def, safe)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v::linorder set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  let ?rn1 = "rename \<pi> (A, V, p)" and
      ?rn2 = "rename \<pi> (A', V', p')" and
      ?rn_V = "\<pi> ` V" and
      ?rn_V' = "\<pi> ` V'" and
      ?rn_p = "p \<circ> (the_inv \<pi>)" and
      ?rn_p' = "p' \<circ> (the_inv \<pi>)" and
      ?len = "length (to_list V p)" and
      ?sl_V = "sorted_list_of_set V"
  let ?perm = "\<lambda> i. (card ({v \<in> ?rn_V. v < \<pi> (?sl_V!i)}))" and
      ?perm_total = "(\<lambda> i. (if (i < ?len)
                           then card ({v \<in> ?rn_V. v < \<pi> (?sl_V!i)})
                           else i))"
  assume bij: "bij \<pi>"
  show "votewise_distance d n (A, V, p) (A', V', p') = votewise_distance d n ?rn1 ?rn2"
  proof -
    have rn_A_eq_A: "fst ?rn1 = A"
      by simp
    have rn_A'_eq_A': "fst ?rn2 = A'"
      by simp
    have rn_V_eq_pi_V: "fst (snd ?rn1) = ?rn_V"
      by simp
    have rn_V'_eq_pi_V': "fst (snd ?rn2) = ?rn_V'"
      by simp
    have rn_p_eq_pi_p: "snd (snd ?rn1) = ?rn_p"
      by simp
    have rn_p'_eq_pi_p': "snd (snd ?rn2) = ?rn_p'"
      by simp
    show ?thesis
    proof (cases "finite V \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')")
      case False
      (* both distances are infinite *)
      hence inf_dist: "votewise_distance d n (A, V, p) (A', V', p') = \<infinity>"
        by auto
      moreover have "infinite V \<Longrightarrow> infinite ?rn_V"
        using False bij bij_betw_finite bij_betw_subset False subset_UNIV
        by metis
      moreover have "V \<noteq> V' \<Longrightarrow> ?rn_V \<noteq> ?rn_V'"
        using bij bij_def inj_image_mem_iff subsetI subset_antisym
        by metis
      moreover have "V = {} \<Longrightarrow> ?rn_V = {}"
        using bij
        by simp
      ultimately have inf_dist_rename: "votewise_distance d n ?rn1 ?rn2 = \<infinity>"
        using False
        by auto
      thus "votewise_distance d n (A, V, p) (A', V', p') = votewise_distance d n ?rn1 ?rn2"
        using inf_dist
        by simp
    next
      case True
      (* both distances are finite *)
      (* use a total permutation function in order to apply facts like  mset_permute_list *)
      have perm_funs_coincide: "\<forall> i < ?len. ?perm i = ?perm_total i"
        by presburger
      (* the lists of V and V' have equal lengths as the sets are equal by assumption *)
      have lengths_eq: "?len = length (to_list V' p')"
        using True
        by simp
      (* show that the list of the renamed (A, V, p)
          permutes the original list using ?perm_total *)
      have rn_V_permutes: "(to_list V p) = permute_list ?perm (to_list ?rn_V ?rn_p)"
        using assms to_list_permutes_under_bij bij to_list_permutes_under_bij
        unfolding comp_def
        by (metis (no_types))
      hence len_V_rn_V_eq: "?len = length (to_list ?rn_V ?rn_p)"
        by simp
      hence "permute_list ?perm (to_list ?rn_V ?rn_p)
              = permute_list ?perm_total (to_list ?rn_V ?rn_p)"
        using permute_invariant_under_coinciding_funs[of "(to_list ?rn_V ?rn_p)"]
              perm_funs_coincide
        by presburger
      hence rn_list_perm_list_V: "(to_list V p) = permute_list ?perm_total (to_list ?rn_V ?rn_p)"
        using rn_V_permutes
        by metis
      (* show that the list of the renamed (A', V', p')
          permutes the original list using ?perm_total *)
      have rn_V'_permutes: "(to_list V' p') = permute_list ?perm (to_list ?rn_V' ?rn_p')"
        unfolding comp_def
        using True bij to_list_permutes_under_bij
        by (metis (no_types))
      hence "permute_list ?perm (to_list ?rn_V' ?rn_p')
              = permute_list ?perm_total (to_list ?rn_V' ?rn_p')"
        using permute_invariant_under_coinciding_funs[of "(to_list ?rn_V' ?rn_p')"]
              perm_funs_coincide lengths_eq
        by fastforce
      hence rn_list_perm_list_V':
        "(to_list V' p') = permute_list ?perm_total (to_list ?rn_V' ?rn_p')"
        using rn_V'_permutes
        by metis
      (* show that the norms of the permuted lists are equal, yielding the ?thesis *)
      have rn_lengths_eq: "length (to_list ?rn_V ?rn_p) = length (to_list ?rn_V' ?rn_p')"
        using len_V_rn_V_eq lengths_eq rn_V'_permutes
        by simp
      have perm: "?perm_total permutes {0 ..< ?len}"
      proof -
        (*(\<lambda> i. (card ({v \<in> (\<pi> ` V). v < \<pi> ((sorted_list_of_set V)!i)})))*)
        have "\<forall> i j. (i < ?len \<and> j < ?len \<and> i \<noteq> j
                     \<longrightarrow> \<pi> ((sorted_list_of_set V)!i) \<noteq> \<pi> ((sorted_list_of_set V)!j))"
          using bij bij_pointE True nth_eq_iff_index_eq length_map
                sorted_list_of_set.distinct_sorted_key_list_of_set to_list.elims
          by (metis (mono_tags, opaque_lifting))
        moreover have in_bnds_imp_img_el: "\<forall> i. i < ?len \<longrightarrow> \<pi> ((sorted_list_of_set V)!i) \<in> \<pi> ` V"
          using True image_eqI nth_mem sorted_list_of_set(1) to_list.simps length_map
          by metis
        ultimately have "\<forall> i < ?len. \<forall> j < ?len. (?perm_total i = ?perm_total j \<longrightarrow> i = j)"
          using linorder_rank_injective Collect_cong True finite_imageI
          by (metis (no_types, lifting))
        moreover have "\<forall> i. i < ?len \<longrightarrow> i \<in> {0 ..< ?len}"
          by simp
        ultimately have "\<forall> i \<in> {0 ..< ?len}. \<forall> j \<in> {0 ..< ?len}.
                          (?perm_total i = ?perm_total j \<longrightarrow> i = j)"
          by simp
        hence inj: "inj_on ?perm_total {0 ..< ?len}"
          unfolding inj_on_def
          by simp
        have "\<forall> v' \<in> (\<pi> ` V). (card ({v\<in>(\<pi> ` V). v < v'})) < card (\<pi> ` V)"
          using card_seteq True finite_imageI less_irrefl linorder_not_le mem_Collect_eq subsetI
          by (metis (no_types, lifting))
        moreover have "\<forall> i < ?len. \<pi> ((sorted_list_of_set V)!i) \<in> \<pi> ` V"
          using in_bnds_imp_img_el
          by simp
        moreover have "card (\<pi> ` V) = card V"
          using bij bij_betw_same_card bij_betw_subset top_greatest
          by metis
        moreover have "card V = ?len"
          by simp
        ultimately have bounded_img: "\<forall> i. (i < ?len \<longrightarrow> ?perm_total i \<in> {0 ..< ?len})"
          using atLeast0LessThan lessThan_iff
          by (metis (full_types))
        hence "\<forall> i. i < ?len \<longrightarrow> ?perm_total i \<in> {0 ..< ?len}"
          by simp
        moreover have "\<forall> i. i \<in> {0 ..< ?len} \<longrightarrow> i < ?len"
          using atLeastLessThan_iff
          by blast
        ultimately have "\<forall> i. i \<in> {0 ..< ?len} \<longrightarrow> ?perm_total i \<in> {0 .. ?len}"
          by fastforce
        hence "?perm_total ` {0 ..< ?len} \<subseteq> {0 ..< ?len}"
          using bounded_img
          by force
        hence "?perm_total ` {0 ..< ?len} = {0 ..< ?len}"
          using inj card_image card_subset_eq finite_atLeastLessThan
          by blast
        hence bij_perm: "bij_betw ?perm_total {0 ..< ?len} {0 ..< ?len}"
          using inj bij_betw_def atLeast0LessThan
          by blast
        thus ?thesis
          using atLeast0LessThan bij_imp_permutes
          by fastforce
      qed
      have "votewise_distance d n ?rn1 ?rn2
              = n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list ?rn_V ?rn_p) (to_list ?rn_V' ?rn_p'))"
        using True rn_A_eq_A rn_A'_eq_A' rn_V_eq_pi_V rn_V'_eq_pi_V' rn_p_eq_pi_p rn_p'_eq_pi_p'
        by force
      also have "... = n (map2 (\<lambda> q q'. d (A, q) (A', q'))
                        (permute_list ?perm_total (to_list ?rn_V ?rn_p))
                        (permute_list ?perm_total (to_list ?rn_V' ?rn_p')))"
        using symmetric_norm_inv_under_map2_permute[of ?perm_total "to_list ?rn_V ?rn_p"]
              assms perm rn_lengths_eq len_V_rn_V_eq
        by simp
      also have "... = n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))"
        using rn_list_perm_list_V rn_list_perm_list_V'
        by presburger
      also have "votewise_distance d n (A, V, p) (A', V', p')
            = n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))"
        using True
        by force
      finally show "votewise_distance d n (A, V, p) (A', V', p')
                      = votewise_distance d n ?rn1 ?rn2"
        by linarith
    qed
  qed
qed

lemma neutral_dist_imp_neutral_votewise_dist:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm"
  defines "vote_action \<equiv> (\<lambda> \<pi> (A, q). (\<pi> ` A, rel_rename \<pi> q))"
  assumes invar: "invariant_dist d (carrier neutrality\<^sub>\<G>) UNIV vote_action"
  shows "distance_neutrality valid_elections (votewise_distance d n)"
proof (unfold distance_neutrality.simps,
        simp only: rewrite_invariant_dist,
        safe)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v::linorder set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assume
    carrier: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    valid: "(A, V, p) \<in> valid_elections" and
    valid': "(A', V', p') \<in> valid_elections"
  hence bij: "bij \<pi>"
    unfolding neutrality\<^sub>\<G>_def
    using rewrite_carrier
    by blast
  thus "votewise_distance d n (A, V, p) (A', V', p') =
          votewise_distance d n
            (\<phi>_neutr valid_elections \<pi> (A, V, p)) (\<phi>_neutr valid_elections \<pi> (A', V', p'))"
  proof (cases "finite V \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')")
    case True
    hence "finite V \<and> V = V' \<and> (V \<noteq> {} \<or> \<pi> ` A = \<pi> ` A')"
      by metis
    hence "votewise_distance d n
            (\<phi>_neutr valid_elections \<pi> (A, V, p)) (\<phi>_neutr valid_elections \<pi> (A', V', p'))
        = n (map2 (\<lambda> q q'. d (\<pi> ` A, q) (\<pi> ` A', q'))
          (to_list V (rel_rename \<pi> \<circ> p)) (to_list V' (rel_rename \<pi> \<circ> p')))"
      using valid valid'
      by auto
    also have "(map2 (\<lambda> q q'. d (\<pi> ` A, q) (\<pi> ` A', q'))
            (to_list V (rel_rename \<pi> \<circ> p)) (to_list V' (rel_rename \<pi> \<circ> p')))
        = (map2 (\<lambda> q q'. d (\<pi> ` A, q) (\<pi> ` A', q'))
        (map (rel_rename \<pi>) (to_list V p)) (map (rel_rename \<pi>) (to_list V' p')))"
      using to_list_comp
      by metis
    also have "(map2 (\<lambda> q q'. d (\<pi> ` A, q) (\<pi> ` A', q'))
            (map (rel_rename \<pi>) (to_list V p)) (map (rel_rename \<pi>) (to_list V' p')))
        = (map2 (\<lambda> q q'. d (\<pi> ` A, rel_rename \<pi> q) (\<pi> ` A', rel_rename \<pi> q'))
            (to_list V p) (to_list V' p'))"
      using map2_helper
      by blast
    also have "(\<lambda> q q'. d (\<pi> ` A, rel_rename \<pi> q) (\<pi> ` A', rel_rename \<pi> q'))
          = (\<lambda> q q'. d (A, q) (A', q'))"
      using rewrite_invariant_dist[of d "carrier neutrality\<^sub>\<G>" UNIV vote_action]
            invar carrier UNIV_I case_prod_conv
      unfolding vote_action_def
      by (metis (no_types, lifting))
    finally have "votewise_distance d n
        (\<phi>_neutr valid_elections \<pi> (A, V, p)) (\<phi>_neutr valid_elections \<pi> (A', V', p'))
          = n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))"
      by simp
    also have "votewise_distance d n (A, V, p) (A', V', p')
          = n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))"
      using True
      by auto
    finally show ?thesis
      by simp
  next
    case False
    hence "\<not> (finite V \<and> V = V' \<and> (V \<noteq> {} \<or> \<pi> ` A = \<pi> ` A'))"
      using bij bij_is_inj inj_image_eq_iff
      by metis
    hence "votewise_distance d n
        (\<phi>_neutr valid_elections \<pi> (A, V, p)) (\<phi>_neutr valid_elections \<pi> (A', V', p')) = \<infinity>"
      using valid valid'
      by auto
    also have "votewise_distance d n (A, V, p) (A', V', p') = \<infinity>"
      using False
      by auto
    finally show ?thesis
      by simp
  qed
qed

end
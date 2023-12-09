section \<open>Symmetry in Distance-Rationalizable Rules\<close>

theory Distance_Rationalization_Symmetry
  imports Voting_Symmetry
          Property_Interpretations
begin 

subsection \<open>Distance Rationalization as Minimizer\<close>

lemma \<K>\<^sub>\<E>_is_preimg:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    E :: "('a, 'v) Election" and
    w :: 'r
  shows 
    "preimg (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) {w} = \<K>\<^sub>\<E> C w"
proof -
  have "preimg (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) {w} = 
    {E \<in> \<K>_els C. (elect_r \<circ> on_els (rule_\<K> C)) E = {w}}"
    by simp
  also have "{E \<in> \<K>_els C. (elect_r \<circ> on_els (rule_\<K> C)) E = {w}} =
    {E \<in> \<K>_els C. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
    by simp
  also have "{E \<in> \<K>_els C. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}} =
    \<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
    by blast
  also have 
    "\<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}} = \<K>\<^sub>\<E> C w"
  proof (standard)
    show 
      "\<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}} \<subseteq> \<K>\<^sub>\<E> C w"
      unfolding \<K>\<^sub>\<E>.simps
      by force
  next
    have "\<forall>E \<in> \<K>\<^sub>\<E> C w. E \<in> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
      unfolding \<K>\<^sub>\<E>.simps
      by force
    hence "\<forall>E \<in> \<K>\<^sub>\<E> C w. E \<in> 
      \<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
      by simp
    thus "\<K>\<^sub>\<E> C w \<subseteq> \<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
      by blast
  qed
  finally show "preimg (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) {w} = \<K>\<^sub>\<E> C w"
    by simp
qed
   
lemma score_is_closest_preimg_dist:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    E :: "('a, 'v) Election" and
    w :: 'r
  shows
    "score d C E w = closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E {w}"
proof -
  have "score d C E w = Inf (d E ` (\<K>\<^sub>\<E> C w))" by simp
  also have "\<K>\<^sub>\<E> C w = preimg (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) {w}"
    using \<K>\<^sub>\<E>_is_preimg
    by metis
  also have "Inf (d E ` (preimg (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) {w}))
              = closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E {w}"
    by simp
  finally show ?thesis
    by simp
qed

lemma (in result) \<R>\<^sub>\<W>_is_minimizer:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class"
  shows "on_els (\<R>\<^sub>\<W> d C) = 
    (\<lambda>E. \<Union>(minimizer (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d 
                      (set_to_set_set (limit_set (alts_\<E> E) UNIV)) E))"
proof (standard)
  fix
    E :: "('a, 'v) Election"
  let ?min = "(minimizer (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d 
                          (set_to_set_set (limit_set (alts_\<E> E) UNIV)) E)"
  have 
    "?min = arg_min_set 
              (closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E) 
              (set_to_set_set (limit_set (alts_\<E> E) UNIV))"
    by simp
  also have 
    "arg_min_set 
              (closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E) 
              (set_to_set_set (limit_set (alts_\<E> E) UNIV))
      = set_to_set_set (arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV))"
  proof (safe)
    fix 
      R :: "'r set"
    assume 
      min: "R \<in> arg_min_set 
                  (closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E)
                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))"
    hence "R \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV)"
      by (meson arg_min_subset subsetD)
    then obtain r :: 'r where "R = {r}" and r_in_lim_set: "r \<in> limit_set (alts_\<E> E) UNIV"
      by auto
    have 
      "\<nexists>R'. R' \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV) \<and>
          closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E R'
            < closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E R"
      using min arg_min_set.simps is_arg_min_def CollectD
      by (metis (mono_tags, lifting))
    hence 
      "\<nexists>r'. r' \<in> limit_set (alts_\<E> E) UNIV \<and> 
          closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E {r'}
            < closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E {r}"
      using \<open>R = {r}\<close>
      by auto
    hence 
      "\<nexists>r'. r' \<in> limit_set (alts_\<E> E) UNIV \<and> score d C E r' < score d C E r"
      using score_is_closest_preimg_dist
      by metis
    hence "r \<in> arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV)"
      using r_in_lim_set arg_min_set.simps is_arg_min_def CollectI
      by metis
    thus "R \<in> set_to_set_set (arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV))"
      using \<open>R = {r}\<close>
      by simp
  next
    fix 
      R :: "'r set"
    assume "R \<in> set_to_set_set (arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV))"
    then obtain r :: 'r where 
      "R = {r}" and r_min_lim_set: "r \<in> arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV)"
      by auto
    hence 
      "\<nexists>r'. r' \<in> limit_set (alts_\<E> E) UNIV \<and> score d C E r' < score d C E r"
      by (metis CollectD arg_min_set.simps is_arg_min_def)
    hence 
      "\<nexists>r'. r' \<in> limit_set (alts_\<E> E) UNIV \<and> 
          closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E {r'}
            < closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E {r}"
      using score_is_closest_preimg_dist
      by metis
    moreover have 
      "\<forall>R' \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV). 
        \<exists>r' \<in> limit_set (alts_\<E> E) UNIV. R' = {r'}"
      by auto
    ultimately have "\<nexists>R'. R' \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV) \<and>
        closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E R'
          < closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E R"
      using \<open>R = {r}\<close> 
      by auto
    moreover have "R \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV)"
      using r_min_lim_set \<open>R = {r}\<close> arg_min_subset 
      by fastforce
    ultimately show "R \<in> arg_min_set 
                  (closest_preimg_dist (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d E)
                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))"
      using arg_min_set.simps is_arg_min_def CollectI
      by (metis (mono_tags, lifting))
  qed
  also have "(arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV)) = on_els (\<R>\<^sub>\<W> d C) E"
    by simp
  finally have 
    "\<Union>?min = \<Union>(set_to_set_set (on_els (\<R>\<^sub>\<W> d C) E))"
    by presburger
  thus "on_els (\<R>\<^sub>\<W> d C) E = \<Union>?min"
    using un_left_inv_set_to_set_set
    by auto
qed

subsection \<open>Auxiliary Lemmas\<close>

lemma (in result) cons_domain_valid:
  fixes
    C :: "('a, 'v, 'r Result) Consensus_Class"
  shows
    "\<K>_els C \<subseteq> valid_elections"
proof
  fix 
    E :: "('a,'v) Election"
  assume 
    "E \<in> \<K>_els C"
  hence "on_els profile E"
    unfolding \<K>\<^sub>\<E>.simps
    by force
  thus "E \<in> valid_elections"
    unfolding valid_elections_def
    by simp
qed

subsection \<open>Invariance\<close>

theorem (in result) tot_invar_dist_imp_invar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    rel :: "('a, 'v) Election rel"
  assumes
    r_refl: "restr_refl_on (\<K>_els C) rel" and
    tot_invar_d: "totally_invariant_dist d rel" and
    invar_res: "has_prop (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance rel)"
  shows "has_prop (on_els (distance_\<R> d C)) (Invariance rel)"
proof -
  let ?min = "(\<lambda>E. \<Union> \<circ> (minimizer (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d 
                                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))))"
  have "\<forall>E. has_prop (?min E) (Invariance rel)"
    using r_refl tot_invar_d invar_comp 
          minimizer_invar_under_refl_rel_and_tot_invar_dist[of 
            "\<K>_els C" rel d "elect_r \<circ> on_els (rule_\<K> C)"]
    by blast
  moreover have "has_prop ?min (Invariance rel)"
    using invar_res
    by auto
  ultimately have 
    "has_prop (\<lambda>E. ?min E E) (Invariance rel)"
    using invar_param_fun[of ?min rel]
    by blast
  also have "(\<lambda>E. ?min E E) = on_els (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer comp_def
    by metis
  finally have invar_\<R>\<^sub>\<W>: "has_prop (on_els (\<R>\<^sub>\<W> d C)) (Invariance rel)"
    by simp
  hence "has_prop (\<lambda>E. limit_set (alts_\<E> E) UNIV - on_els (\<R>\<^sub>\<W> d C) E) (Invariance rel)"
    using invar_res
    by fastforce
  thus "has_prop (on_els (distance_\<R> d C)) (Invariance rel)"
    using invar_\<R>\<^sub>\<W>
    by auto
qed

theorem (in result) invar_dist_cons_imp_invar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    G :: "'x monoid" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    B :: "('a, 'v) Election set" 
    \<comment> \<open>Base set of elections on which the DR rule is invariant, e.g. valid_elections.\<close>
  defines
    "rel \<equiv> rel_induced_by_action (carrier G) B \<phi>" and
    "restr_rel \<equiv> rel_induced_by_action (carrier G) (\<K>_els C) \<phi>"
  assumes        
    grp_act: "group_action G B \<phi>" and "\<K>_els C \<subseteq> B" and
    closed_domain: "rel \<inter> (\<K>_els C \<times> B) \<subseteq> restr_rel" and
    (* Could the closed_domain requirement be weakened? *)
    invar_res: "has_prop (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance rel)" and
    invar_d: "invariant_dist d (carrier G) B \<phi>" and
    invar_C_winners: "has_prop (elect_r \<circ> on_els (rule_\<K> C)) (Invariance restr_rel)" 
  shows
    "has_prop (on_els (distance_\<R> d C)) (Invariance rel)"
proof -                    
  let ?min = "(\<lambda>E. \<Union> \<circ> (minimizer (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d 
                                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))))"
  have "\<forall>E. has_prop (?min E) (Invariance rel)"
    using grp_act closed_domain \<open>\<K>_els C \<subseteq> B\<close> invar_d invar_C_winners 
          grp_act_invar_dist_and_invar_f_imp_invar_minimizer rel_def 
          restr_rel_def invar_comp Sigma_cong 
    by (metis (no_types, lifting))
  moreover have "has_prop ?min (Invariance rel)"
    using invar_res
    by auto
  ultimately have 
    "has_prop (\<lambda>E. ?min E E) (Invariance rel)"
    using invar_param_fun[of ?min rel]
    by blast
  also have "(\<lambda>E. ?min E E) = on_els (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer comp_def
    by metis
  finally have invar_\<R>\<^sub>\<W>: "has_prop (on_els (\<R>\<^sub>\<W> d C)) (Invariance rel)"
    by simp
  hence "has_prop (\<lambda>E. limit_set (alts_\<E> E) UNIV - on_els (\<R>\<^sub>\<W> d C) E) (Invariance rel)"
    using invar_res
    by fastforce
  thus "has_prop (on_els (distance_\<R> d C)) (Invariance rel)"
    using invar_\<R>\<^sub>\<W>
    by auto
qed

subsection \<open>Equivariance\<close>

theorem (in result) invar_dist_equivar_cons_imp_equivar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    G :: "'x monoid" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    \<psi> :: "('x, 'r) binary_fun" and
    B :: "('a, 'v) Election set" 
  defines
    "rel \<equiv> rel_induced_by_action (carrier G) B \<phi>" and
    "restr_rel \<equiv> rel_induced_by_action (carrier G) (\<K>_els C) \<phi>" and
    "equivar_prop \<equiv> 
      equivar_ind_by_act (carrier G) (\<K>_els C) \<phi> (set_action \<psi>)" and
    "equivar_prop_global_set_valued \<equiv> 
      equivar_ind_by_act (carrier G) B \<phi> (set_action \<psi>)" and
    "equivar_prop_global_result_valued \<equiv> 
      equivar_ind_by_act (carrier G) B \<phi> (result_action \<psi>)"
  assumes        
    grp_act: "group_action G B \<phi>" and grp_act_res: "group_action G UNIV \<psi>" and
    "\<K>_els C \<subseteq> B" and closed_domain: "rel \<inter> (\<K>_els C \<times> B) \<subseteq> restr_rel" and
    (* Could the closed_domain requirement be weakened? *)
    equivar_res: 
      "has_prop (\<lambda>E. limit_set (alts_\<E> E) UNIV) equivar_prop_global_set_valued" and
    invar_d: "invariant_dist d (carrier G) B \<phi>" and
    equivar_C_winners: "has_prop (elect_r \<circ> on_els (rule_\<K> C)) equivar_prop"
  shows "has_prop (on_els (distance_\<R> d C)) equivar_prop_global_result_valued"
proof -
  let ?min_E = "\<lambda>E. minimizer (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d 
                                (set_to_set_set (limit_set (alts_\<E> E) UNIV)) E"
  let ?min = "(\<lambda>E. \<Union> \<circ> (minimizer (elect_r \<circ> on_els (rule_\<K> C)) (\<K>_els C) d 
                                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))))"
  let ?\<psi>' = "set_action (set_action \<psi>)" \<comment> \<open>Apply \<psi> to a set of sets.\<close>
  let ?equivar_prop_global_set_valued' = "equivar_ind_by_act (carrier G) B \<phi> ?\<psi>'"
  have "\<forall>E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
          set_to_set_set (limit_set (alts_\<E> (\<phi> g E)) UNIV) =
            {{r} | r. r \<in> limit_set (alts_\<E> (\<phi> g E)) UNIV}"
    by simp
  moreover have 
    "\<forall>E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
      limit_set (alts_\<E> (\<phi> g E)) UNIV = \<psi> g ` (limit_set (alts_\<E> E) UNIV)"
    using equivar_res grp_act group_action.element_image
    unfolding equivar_prop_global_set_valued_def equivar_ind_by_act_def
    by fastforce
  ultimately have 
    "\<forall>E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
      set_to_set_set (limit_set (alts_\<E> (\<phi> g E)) UNIV) = 
        {{r} | r. r \<in> \<psi> g ` (limit_set (alts_\<E> E) UNIV)}"
    by simp
  moreover have "\<forall>E g. {{r} | r. r \<in> \<psi> g ` (limit_set (alts_\<E> E) UNIV)}
                  = {\<psi> g ` {r} | r. r \<in> limit_set (alts_\<E> E) UNIV}"
    by blast
  moreover have "\<forall>E g. {\<psi> g ` {r} | r. r \<in> limit_set (alts_\<E> E) UNIV} =
                  ?\<psi>' g {{r} | r. r \<in> limit_set (alts_\<E> E) UNIV}"
    unfolding set_action.simps
    by blast
  ultimately have 
    "has_prop (\<lambda>E. set_to_set_set (limit_set (alts_\<E> E) UNIV))
              ?equivar_prop_global_set_valued'"
    using rewrite_equivar_ind_by_act[of 
            "\<lambda>E. set_to_set_set (limit_set (alts_\<E> E) UNIV)" "carrier G" B \<phi> ?\<psi>']
    by force
  moreover have "group_action G UNIV (set_action \<psi>)"
    using grp_act_induces_set_grp_act[of G UNIV \<psi>] grp_act_res 
    unfolding set_action.simps
    by auto
  ultimately have "has_prop ?min_E ?equivar_prop_global_set_valued'"
    using grp_act invar_d \<open>\<K>_els C \<subseteq> B\<close> closed_domain equivar_C_winners
          grp_act_invar_dist_and_equivar_f_imp_equivar_minimizer[of 
              G B \<phi> "set_action \<psi>" "\<K>_els C" 
              "\<lambda>E. set_to_set_set (limit_set (alts_\<E> E) UNIV)" 
              d "elect_r \<circ> on_els (rule_\<K> C)"]
    unfolding restr_rel_def rel_def equivar_prop_def
    by blast
  moreover have 
    "has_prop \<Union> (equivar_ind_by_act (carrier G) UNIV ?\<psi>' (set_action \<psi>))"
    by (rule equivar_union_under_img_act[of "carrier G" \<psi>])
  ultimately have "has_prop (\<Union> \<circ> ?min_E) equivar_prop_global_set_valued"
    unfolding equivar_prop_global_set_valued_def
    using equivar_ind_by_act_comp[of ?min_E B UNIV "carrier G" ?\<psi>' \<phi> \<Union>]
    by blast
  moreover have "(\<lambda>E. ?min E E) = \<Union> \<circ> ?min_E"
    unfolding comp_def
    by blast
  ultimately have
    "has_prop (\<lambda>E. ?min E E) equivar_prop_global_set_valued"
    by simp
  moreover have "(\<lambda>E. ?min E E) = on_els (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer comp_def
    by metis
  \<comment> \<open>As all components of the result are equivariant, the whole result is equivariant.\<close>
  ultimately have equivar_\<R>\<^sub>\<W>: "has_prop (on_els (\<R>\<^sub>\<W> d C)) equivar_prop_global_set_valued"
    by simp
  moreover have "\<forall>g \<in> carrier G. bij (\<psi> g)"
    using grp_act_res
    by (simp add: bij_betw_def group_action.inj_prop group_action.surj_prop)
  ultimately have
    "has_prop (\<lambda>E. limit_set (alts_\<E> E) UNIV - on_els (\<R>\<^sub>\<W> d C) E) equivar_prop_global_set_valued"
    using equivar_res 
          equivar_set_minus[of 
            "\<lambda>E. limit_set (alts_\<E> E) UNIV" "carrier G" B \<phi> \<psi> "\<lambda>E. on_els (\<R>\<^sub>\<W> d C) E"]
    unfolding equivar_prop_global_set_valued_def equivar_ind_by_act_def set_action.simps
    by blast
  thus "has_prop (on_els (distance_\<R> d C)) equivar_prop_global_result_valued"
    using equivar_\<R>\<^sub>\<W>
    unfolding equivar_prop_global_result_valued_def equivar_prop_global_set_valued_def
    by (simp add: rewrite_equivar_ind_by_act)
qed

subsection \<open>Specific Properties\<close>

theorem (in result) anon_dist_and_cons_imp_anon_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class"
  assumes       
    anon_d: "anon_dist valid_elections d" and
    anon_C: "cons_anon C" and
    closed_C:
      "anon_rel valid_elections \<inter> (\<K>_els C \<times> valid_elections) \<subseteq> anon_rel (\<K>_els C)"
  shows "anon_mod valid_elections (distance_\<R> d C)"
  using cons_domain_valid[of C] assms anon_grp_act.group_action_axioms well_formed_res_anon
        invar_dist_cons_imp_invar_dr_rule[of anon_group valid_elections \<phi>_anon C d]
  unfolding anon_dist.simps anon_mod.simps anon_rel.simps anonymity2.simps cons_anon.simps
  by blast

theorem (in result_properties) neutr_dist_and_cons_imp_neutr_dr:
  fixes
    d :: "('a, 'c) Election Distance" and
    C :: "('a, 'c, 'b Result) Consensus_Class"
  assumes
    neutr_d: "neutr_dist valid_elections d" and
    neutr_C: "cons_neutr C" and
    closed_C:
      "neutr_rel valid_elections \<inter> (\<K>_els C \<times> valid_elections) \<subseteq> neutr_rel (\<K>_els C)"
  shows "neutr_mod valid_elections (distance_\<R> d C)" 
  using cons_domain_valid[of C] assms \<phi>_neutr_act.group_action_axioms
        well_formed_res_neutr act_neutr
        invar_dist_equivar_cons_imp_equivar_dr_rule[of 
          neutr_group valid_elections \<phi>_neutr \<psi>_neutr C d]
  unfolding neutr_dist.simps neutr_mod.simps neutr_rel.simps neutrality.simps cons_neutr.simps
  by blast

theorem (in result) tot_hom_dist_imp_hom_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class"
  assumes       
    hom_d: "anon_dist valid_elections d" and
    closed_C:
      "anon_rel valid_elections \<inter> (\<K>_els C \<times> valid_elections) \<subseteq> anon_rel (\<K>_els C)"
  shows "homogeneous (distance_\<R> d C)"
  sorry

end
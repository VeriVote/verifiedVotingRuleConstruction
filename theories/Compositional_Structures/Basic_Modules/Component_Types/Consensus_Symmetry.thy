theory Consensus_Symmetry
  imports Symmetry_Properties

begin

section \<open>TODO\<close>

theorem cons_conjunction_invariant:
  fixes
    C_set :: "('a,'v) Consensus set" and
    rel :: "('a,'v) Election rel"
  defines 
    "C \<equiv> (\<lambda>E. (\<forall>C' \<in> C_set. C' E))"
  assumes
    "\<And>C'. C' \<in> C_set \<Longrightarrow> invariant C' rel"
  shows "invariant C rel"
proof (unfold invariant_def, standard, standard, standard)
  fix
    E :: "('a,'v) Election" and
    E' :: "('a,'v) Election"
  assume
    "(E,E') \<in> rel"
  hence "\<forall>C' \<in> C_set. C' E = C' E'"
    using assms
    unfolding invariant_def
    by blast
  thus "C E = C E'"
    unfolding C_def
    by blast
qed

section \<open>Neutrality\<close>

abbreviation neutr_rel :: "('a,'v) Election rel"
  where "neutr_rel \<equiv> (rel_induced_by_action (carrier neutr_group) \<phi>_neutr UNIV)"

lemma nonempty_set\<^sub>\<C>_inv_neutr:
  "invariant nonempty_set\<^sub>\<C> neutr_rel"
  sorry

lemma nonempty_profile\<^sub>\<C>_inv_neutr:
  "invariant nonempty_profile\<^sub>\<C> neutr_rel"
  sorry
    
lemma equal_vote\<^sub>\<C>_inv_neutr:
  "invariant equal_vote\<^sub>\<C> neutr_rel"
  sorry

lemma strong_unanimity\<^sub>\<C>_inv_neutr: 
  "invariant strong_unanimity\<^sub>\<C> neutr_rel"
  using nonempty_set\<^sub>\<C>_inv_neutr equal_vote\<^sub>\<C>_inv_neutr nonempty_profile\<^sub>\<C>_inv_neutr 
        cons_conjunction_invariant[of "{nonempty_set\<^sub>\<C>, nonempty_profile\<^sub>\<C>, equal_vote\<^sub>\<C>}" neutr_rel]
  unfolding strong_unanimity\<^sub>\<C>.simps
  by auto

lemma strong_unanimity_neutral:
  shows
      "equivariant (elect_r \<circ> (on_els (rule_\<K> strong_unanimity))) (carrier neutr_group) UNIV 
                                                    \<phi>_neutr (\<lambda>g. \<lambda>S. \<psi>_neutr_soc_choice g ` S)"
  sorry

lemma strong_unanimity_closed_under_neutrality:
  shows 
      "(rel_induced_by_action (carrier neutr_group) \<phi>_neutr UNIV) \<inter> 
          ((\<K>_els strong_unanimity) \<times> UNIV) 
        \<subseteq> (rel_induced_by_action (carrier neutr_group) \<phi>_neutr (\<K>_els strong_unanimity))"
proof (unfold equivariant_def rel_induced_by_action_def neutr_group_def, safe, simp)
  fix
    A :: "'a set" and
    V :: "'b set" and
    p :: "('a, 'b) Profile" and
    A' :: "'a set" and
    V' :: "'b set" and
    p' :: "('a, 'b) Profile" and
    x :: "'a \<Rightarrow> 'a" and
    a :: 'a
  assume
    cons: "(A, V, p) \<in> \<K>\<^sub>\<E> strong_unanimity a" and
    bij: "x \<in> carrier (BijGroup UNIV)" and
    img: "\<phi>_neutr x (A, V, p) = (A', V', p')"
  thus "\<exists>x \<in> carrier (BijGroup UNIV). \<phi>_neutr x (A, V, p) = (A', V', p')"
    by blast
  from cons have "(A,V,p) \<in> finite_elections"
    unfolding \<K>\<^sub>\<E>.simps finite_elections_def
    by simp
  hence "(A',V',p') \<in> finite_elections"
    using bij img bij_fin_neutr bij_car_el
    by (metis bij_betw_apply)
  hence fin': "finite_profile V' A' p'"
    unfolding finite_elections_def
    by simp
  have "((A,V,p), (A',V',p')) \<in> (rel_induced_by_action (carrier neutr_group) \<phi>_neutr UNIV)"
    using bij img
    unfolding rel_induced_by_action_def neutr_group_def
    by (metis (mono_tags, lifting) CollectI UNIV_I UNIV_Times_UNIV case_prodI)
  moreover have "strong_unanimity\<^sub>\<C> (A,V,p)"
    using cons
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_def
    by simp
  ultimately have cons': "strong_unanimity\<^sub>\<C> (A',V',p')"
    using strong_unanimity\<^sub>\<C>_inv_neutr
    unfolding invariant_def
    by blast
  have "elect V' (rule_\<K> strong_unanimity) A' p' = 
          (elect_r \<circ> on_els (rule_\<K> strong_unanimity)) (\<phi>_neutr x (A, V, p))"
    using img
    by simp
  also have 
    "(elect_r \<circ> on_els (rule_\<K> strong_unanimity)) (\<phi>_neutr x (A, V, p)) = 
        \<psi>_neutr_soc_choice x ` ((elect_r \<circ> on_els (rule_\<K> strong_unanimity)) (A,V,p))"
    using strong_unanimity_neutral 
    unfolding \<K>\<^sub>\<E>.simps equivariant_def neutr_group_def
    using bij
    sorry
  also have "(elect_r \<circ> on_els (rule_\<K> strong_unanimity)) (A,V,p) = {a}"
    using cons
    unfolding \<K>\<^sub>\<E>.simps
    by simp
  finally have "elect V' (rule_\<K> strong_unanimity) A' p' = {\<psi>_neutr_soc_choice x a}"
    by blast
  hence "(A',V',p') \<in> \<K>\<^sub>\<E> strong_unanimity (\<psi>_neutr_soc_choice x a)"
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_def consensus_choice.simps
    using fin' cons'
    by auto
  thus "(A',V',p') \<in> \<K>_els strong_unanimity"
    by simp
qed

section \<open>Homogeneity\<close>


end
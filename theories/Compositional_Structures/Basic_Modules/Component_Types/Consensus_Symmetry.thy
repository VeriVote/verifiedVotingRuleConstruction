theory Consensus_Symmetry
  imports Distance_Rationalization_Symmetry
begin

subsection \<open>Definitions\<close>

subsection \<open>Auxiliary Lemmas\<close>

theorem cons_conjunction_invariant:
  fixes
    \<CC> :: "('a, 'v) Consensus set" and
    rel :: "('a, 'v) Election rel"
  defines 
    "C \<equiv> (\<lambda>E. (\<forall>C' \<in> \<CC>. C' E))"
  assumes
    "\<And>C'. C' \<in> \<CC> \<Longrightarrow> has_prop C' (Invariance rel)"
  shows "has_prop C (Invariance rel)"
proof (unfold has_prop.simps, standard, standard, standard)
  fix
    E :: "('a,'v) Election" and
    E' :: "('a,'v) Election"
  assume
    "(E,E') \<in> rel"
  hence "\<forall>C' \<in> \<CC>. C' E = C' E'"
    using assms
    unfolding has_prop.simps
    by blast
  thus "C E = C E'"
    unfolding C_def
    by blast
qed

subsection \<open>Neutrality\<close>

lemma nonempty_set\<^sub>\<C>_inv_neutr:
  "has_prop nonempty_set\<^sub>\<C> (Invariance (neutr_rel valid_elections))"
  sorry

lemma nonempty_profile\<^sub>\<C>_inv_neutr:
  "has_prop nonempty_profile\<^sub>\<C> (Invariance (neutr_rel valid_elections))"
  sorry
    
lemma equal_vote\<^sub>\<C>_inv_neutr:
  "has_prop equal_vote\<^sub>\<C> (Invariance (neutr_rel valid_elections))"
  sorry

lemma strong_unanimity\<^sub>\<C>_inv_neutr: 
  "has_prop strong_unanimity\<^sub>\<C> (Invariance (neutr_rel valid_elections))"
  using nonempty_set\<^sub>\<C>_inv_neutr equal_vote\<^sub>\<C>_inv_neutr nonempty_profile\<^sub>\<C>_inv_neutr 
        cons_conjunction_invariant[of 
          "{nonempty_set\<^sub>\<C>, nonempty_profile\<^sub>\<C>, equal_vote\<^sub>\<C>}" "neutr_rel valid_elections"]
  unfolding strong_unanimity\<^sub>\<C>.simps
  by fastforce

lemma strong_unanimity_neutral:
  shows "social_choice_properties.cons_neutr strong_unanimity"
  sorry

lemma strong_unanimity_closed_under_neutrality:
  "neutr_rel valid_elections \<inter> (\<K>_els strong_unanimity) \<times> valid_elections \<subseteq> 
    (neutr_rel (\<K>_els strong_unanimity))"
proof (unfold valid_elections_def neutr_rel.simps rel_induced_by_action.simps, clarify)
  fix
    A :: "'a set" and
    V :: "'b set" and
    p :: "('a, 'b) Profile" and
    A' :: "'a set" and
    V' :: "'b set" and
    p' :: "('a, 'b) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    a :: 'a
  assume
    prof: "on_els profile (A, V, p)" and
    cons: "(A, V, p) \<in> \<K>\<^sub>\<E> strong_unanimity a" and
    bij: "\<pi> \<in> carrier neutr_group" and
    img: "\<phi>_neutr \<pi> (A, V, p) = (A', V', p')"
  hence "(A, V, p) \<in> finite_elections"
    unfolding \<K>\<^sub>\<E>.simps finite_elections_def
    by simp
  hence fin': "(A', V', p') \<in> finite_elections"
    using bij img
    sorry
  hence prof': "finite_profile V' A' p'"
    unfolding finite_elections_def
    by simp
  have "((A, V, p), (A', V', p')) \<in> neutr_rel valid_elections"
    using bij img \<open>(A', V', p') \<in> finite_elections\<close> \<open>(A, V, p) \<in> finite_elections\<close>
    unfolding neutr_rel.simps rel_induced_by_action.simps neutr_group_def 
              finite_elections_def valid_elections_def 
    by blast
  moreover have "strong_unanimity\<^sub>\<C> (A, V, p)"
    using cons
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_def
    by simp
  ultimately have cons': "strong_unanimity\<^sub>\<C> (A', V', p')"
    using strong_unanimity\<^sub>\<C>_inv_neutr
    by force
  have "elect (rule_\<K> strong_unanimity) V' A' p' = 
          (elect_r \<circ> on_els (rule_\<K> strong_unanimity)) (\<phi>_neutr \<pi> (A, V, p))"
    using img
    by simp
  also have 
    "(elect_r \<circ> on_els (rule_\<K> strong_unanimity)) (\<phi>_neutr \<pi> (A, V, p)) = 
        \<psi>_neutr_soc_choice \<pi> ` ((elect_r \<circ> on_els (rule_\<K> strong_unanimity)) (A, V, p))"
    using strong_unanimity_neutral bij rewrite_equivar_ind_by_act[of
            "elect_r \<circ> on_els (rule_\<K> strong_unanimity)" "carrier neutr_group"
            valid_elections \<phi>_neutr "set_action \<psi>_neutr_soc_choice"]
          \<open>(A, V, p) \<in> finite_elections\<close> \<open>(A', V', p') \<in> finite_elections\<close> img
    unfolding social_choice_properties.cons_neutr.simps set_action.simps 
              finite_elections_def valid_elections_def
    sorry
  also have "(elect_r \<circ> on_els (rule_\<K> strong_unanimity)) (A, V, p) = {a}"
    using cons
    unfolding \<K>\<^sub>\<E>.simps
    by simp
  finally have "elect (rule_\<K> strong_unanimity) V' A' p' = {\<psi>_neutr_soc_choice \<pi> a}"
    by blast
  hence "(A', V', p') \<in> \<K>\<^sub>\<E> strong_unanimity (\<psi>_neutr_soc_choice \<pi> a)"
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_def consensus_choice.simps
    using cons' fin' prof'
    by simp
  hence "(A', V', p') \<in> \<K>_els strong_unanimity"
    by simp
  hence "((A, V, p), (A', V', p'))
          \<in> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity)) \<times> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity))"
    using cons 
    by blast
  moreover have "\<exists>\<pi> \<in> carrier neutr_group. \<phi>_neutr \<pi> (A, V, p) = (A', V', p')"
    using img bij 
    unfolding neutr_group_def
    by blast
  ultimately show
    "((A, V, p), (A', V', p'))
          \<in> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity)) \<times> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity)) \<and>
     (\<exists>\<pi> \<in> carrier neutr_group. \<phi>_neutr \<pi> (A, V, p) = (A', V', p'))"
    by blast
qed

section \<open>Homogeneity\<close>


end
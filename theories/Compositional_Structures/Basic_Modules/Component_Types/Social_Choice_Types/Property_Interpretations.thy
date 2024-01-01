section \<open>Result-Dependent Properties\<close>

theory Property_Interpretations
  imports Voting_Symmetry
begin    

subsection \<open>Properties Dependent on the Result Type\<close>

text \<open>
  The interpretation of equivariance properties generally depends on the result type.
  For example, neutrality for social choice rules means that single winners are renamed
  when the candidates in the votes are consistently renamed. For social welfare results,
  the complete result rankings must be renamed.

  New result-type-dependent definitions for properties can be added here.
\<close>

locale result_properties = result +
  fixes
    \<psi>_neutr :: "('a \<Rightarrow> 'a, 'b) binary_fun"
  assumes
    act_neutr: "group_action neutrality\<^sub>\<G> UNIV \<psi>_neutr" and
    well_formed_res_neutr:
      "satisfies (\<lambda>(E::('a, 'c) Election). limit_set (alts_\<E> E) UNIV) 
                (equivar_ind_by_act (carrier neutrality\<^sub>\<G>)
                    valid_elections (\<phi>_neutr valid_elections) (set_action \<psi>_neutr))"

sublocale result_properties \<subseteq> result by (rule result_axioms)

subsection \<open>Interpretations\<close>

global_interpretation social_choice_properties: 
  result_properties well_formed_soc_choice limit_set_soc_choice \<psi>_neutr\<^sub>\<c>
  unfolding result_properties_def result_properties_axioms_def
  using wf_res_neutr_soc_choice \<psi>_neutr\<^sub>\<c>_act.group_action_axioms 
        social_choice_result.result_axioms
  by blast

global_interpretation social_welfare_properties: 
  result_properties well_formed_welfare limit_set_welfare \<psi>_neutr\<^sub>\<w>
  unfolding result_properties_def result_properties_axioms_def
  using wf_res_neutr_soc_welfare \<psi>_neutr\<^sub>\<w>_act.group_action_axioms 
        social_welfare_result.result_axioms
  by blast

end
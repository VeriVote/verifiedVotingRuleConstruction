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
    \<psi>_neutr :: "('a \<Rightarrow> 'a, 'b) binary_fun" and
    \<psi>_rev :: "('a \<Rightarrow> 'a, 'b) binary_fun"
  assumes 
    act_neutr: "group_action neutr_group UNIV \<psi>_neutr" and
    well_formed_res_neutr: 
      "has_prop (\<lambda>E. limit_set (alts_\<E> E) UNIV) 
                (equivar_ind_by_act (carrier neutr_group) 
                    valid_elections \<phi>_neutr (set_action \<psi>_neutr))"

sublocale result_properties \<subseteq> result by (rule result_axioms)

subsection \<open>Interpretations\<close>

global_interpretation social_choice_properties: 
  result_properties well_formed_soc_choice limit_set_soc_choice \<psi>_neutr_soc_choice
  unfolding result_properties_def result_properties_axioms_def
  using wf_res_neutr_soc_choice \<psi>_neutr_soc_choice_act.group_action_axioms 
        social_choice_result.result_axioms
  by blast

global_interpretation social_welfare_properties: 
  result_properties well_formed_welfare limit_set_welfare \<psi>_neutr_soc_welfare
  unfolding result_properties_def result_properties_axioms_def
  using wf_res_neutr_soc_welfare \<psi>_neutr_soc_welfare_act.group_action_axioms 
        social_welfare_result.result_axioms
  by blast

subsection \<open>Definitions\<close>

fun (in result_properties) neutrality :: 
  "('a, 'v) Election set \<Rightarrow> (('a, 'v) Election, 'b Result) property" where
  "neutrality X = equivar_ind_by_act (carrier neutr_group) X \<phi>_neutr (result_action \<psi>_neutr)"

fun (in result_properties) neutr_mod :: 
  "('a, 'v) Election set \<Rightarrow> ('a, 'v, 'b Result) Electoral_Module \<Rightarrow> bool" where
  "neutr_mod X m = has_prop (on_els m) (neutrality X)"

fun (in result_properties) cons_neutr :: "('a, 'v, 'b Result) Consensus_Class \<Rightarrow> bool" where
  "cons_neutr C = has_prop (elect_r \<circ> on_els (rule_\<K> C))
    (equivar_ind_by_act (carrier neutr_group) (\<K>_els C) \<phi>_neutr (set_action \<psi>_neutr))"

end
(*  File:       Property_Interpretations.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Result-Dependent Voting Rule Properties\<close>

theory Property_Interpretations
  imports Voting_Symmetry
          Result_Interpretations
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
  fixes \<psi>_neutr :: "('a \<Rightarrow> 'a, 'b) binary_fun" and
        voter_type :: "'v itself"
  assumes
    act_neutr: "group_action neutrality\<^sub>\<G> UNIV \<psi>_neutr" and
    well_formed_res_neutr:
      "is_symmetry (\<lambda> \<E> :: ('a, 'v) Election. limit_set (alternatives_\<E> \<E>) UNIV)
                (action_induced_equivariance (carrier neutrality\<^sub>\<G>)
                    valid_elections (\<phi>_neutr valid_elections) (set_action \<psi>_neutr))"

sublocale result_properties \<subseteq> result
  using result_axioms
  by simp

subsection \<open>Interpretations\<close>

global_interpretation \<S>\<C>\<F>_properties:
  "result_properties" "well_formed_\<S>\<C>\<F>" "limit_set_\<S>\<C>\<F>" "\<psi>_neutr\<^sub>\<c>"
  unfolding result_properties_def result_properties_axioms_def
  using wf_result_neutrality_\<S>\<C>\<F> \<psi>_neutral\<^sub>\<c>_action.group_action_axioms
        \<S>\<C>\<F>_result.result_axioms
  by blast

global_interpretation \<S>\<W>\<F>_properties:
  "result_properties" "well_formed_\<S>\<W>\<F>" "limit_set_\<S>\<W>\<F>" "\<psi>_neutr\<^sub>\<w>"
  unfolding result_properties_def result_properties_axioms_def
  using wf_result_neutrality_\<S>\<W>\<F> \<psi>_neutral\<^sub>\<w>_action.group_action_axioms
        \<S>\<W>\<F>_result.result_axioms
  by blast

end
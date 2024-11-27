(*  File:       Property_Interpretations.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Result-Dependent Voting Rule Properties\<close>

theory Property_Interpretations
  imports Voting_Symmetry
          Result_Interpretations
begin

subsection \<open>Property Definitions\<close>

text \<open>
  The interpretation of equivariance properties generally depends on the result type.
  For example, neutrality for social choice rules means that single winners are renamed
  when the candidates in the votes are consistently renamed. For social welfare results,
  the complete result rankings must be renamed.

  New result-type-dependent definitions for properties can be added here.
\<close>

locale result_properties = result +
  fixes \<psi> :: "('a \<Rightarrow> 'a, 'b) binary_fun" and
        \<nu> :: "'v itself"
  assumes
    action_neutral: "group_action bijection\<^sub>\<A>\<^sub>\<G> UNIV \<psi>" and
    neutrality:
      "is_symmetry (\<lambda> \<E> :: ('a, 'v) Election. limit (alternatives_\<E> \<E>) UNIV)
                (action_induced_equivariance (carrier bijection\<^sub>\<A>\<^sub>\<G>)
                    well_formed_elections
                    (\<phi>_neutral well_formed_elections) (set_action \<psi>))"

sublocale result_properties \<subseteq> result
  using result_axioms
  by safe

subsection \<open>Interpretations\<close>

global_interpretation \<S>\<C>\<F>_properties: "result_properties" "well_formed_\<S>\<C>\<F>"
        "limit_\<S>\<C>\<F>" "\<psi>_neutral\<^sub>\<c>"
  unfolding result_properties_def result_properties_axioms_def
  using neutrality_action_presv_\<S>\<C>\<F>_symmetry \<psi>_neutral\<^sub>\<c>_action.group_action_axioms
        \<S>\<C>\<F>_result.result_axioms
  by blast

global_interpretation \<S>\<W>\<F>_properties: "result_properties" "well_formed_\<S>\<W>\<F>"
        "limit_\<S>\<W>\<F>" "\<psi>_neutral\<^sub>\<w>"
  unfolding result_properties_def result_properties_axioms_def
  using neutrality_action_presv_\<S>\<W>\<F>_symmetry \<psi>_neutral\<^sub>\<w>_action.group_action_axioms
        \<S>\<W>\<F>_result.result_axioms
  by blast

end
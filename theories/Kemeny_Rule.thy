(*  File:       Kemeny_Rule.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Kemeny Rule\<close>

theory Kemeny_Rule
  imports 
    "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Distance_Rationalization_Symmetry"
    "Compositional_Structures/Basic_Modules/Component_Types/Quotients/Quotient_Distance_Rationalization"
begin

text \<open>
  This is the Kemeny rule. It creates a complete ordering of alternatives and
  evaluates each ordering of the alternatives in terms of the sum of preference
  reversals on each ballot that would have to be performed in order to produce
  that transitive ordering. The complete ordering which requires the fewest
  preference reversals is the final result of the method.
\<close>

subsection \<open>Definition\<close>

fun kemeny_rule :: "('a, 'v::wellorder, 'a Result) Electoral_Module" where
  "kemeny_rule V A p = swap_\<R> strong_unanimity V A p"

subsection \<open>Soundness\<close>

theorem kemeny_rule_sound: "social_choice_result.electoral_module kemeny_rule"
  unfolding kemeny_rule.simps swap_\<R>.simps
  using social_choice_result.\<R>_sound
  by metis

subsection \<open>Anonymity Property\<close>

theorem kemeny_rule_anonymous: "social_choice_result.anonymity kemeny_rule"
proof (unfold kemeny_rule.simps swap_\<R>.simps)
  let ?swap_dist = "votewise_distance swap l_one"
  have "distance_anonymity ?swap_dist"
    using l_one_is_sym symmetric_norm_imp_distance_anonymous[of l_one]
    by simp
  thus "social_choice_result.anonymity 
          (social_choice_result.distance_\<R> ?swap_dist strong_unanimity)"
    using strong_unanimity_anonymous 
          social_choice_result.anonymous_distance_and_consensus_imp_rule_anonymity
    by metis
qed

subsection \<open>Neutrality Property\<close>

lemma swap_dist_neutral:
  "distance_neutrality valid_elections (votewise_distance swap l_one)"
  using neutral_dist_imp_neutral_votewise_dist swap_neutral
  by blast

theorem kemeny_rule_neutral: 
  "social_choice_properties.neutrality valid_elections kemeny_rule"  
  using strong_unanimity_neutral' swap_dist_neutral
        strong_unanimity_closed_under_neutrality
        social_choice_properties.neutr_dist_and_cons_imp_neutr_dr[of 
          "votewise_distance swap l_one" strong_unanimity]
  unfolding kemeny_rule.simps swap_\<R>.simps
  by blast

subsection \<open>Quotient Rule\<close>

thm social_choice_result.invar_dr_simple_dist_imp_quotient_dr

theorem (in result) kemeny_lattice_quotient:
  fixes
    X :: "('a, 'v::wellorder) Election set" and
    E :: "('a, 'v) Election"
  assumes
    "E \<in> X" and 
    "X \<subseteq> valid_elections" and
    "\<K>_els strong_unanimity \<subseteq> X" and
    "equiv X (anonymity\<^sub>\<R> X)"
  shows
  "fun\<^sub>\<E> kemeny_rule E = social_choice_result.distance_\<R>\<^sub>\<Q> 
    (anonymity\<^sub>\<R> X) (votewise_distance swap l_one) strong_unanimity (anonymity\<^sub>\<R> X `` {E})"
proof -
  have "satisfies (fun\<^sub>\<E> kemeny_rule) (Invariance (anonymity\<^sub>\<R> X))"
    sorry
  moreover have "simple (anonymity\<^sub>\<R> X) X (votewise_distance swap l_one)" 
    sorry
  moreover have 
    "closed_under_restr_rel (anonymity\<^sub>\<R> X) X (\<K>_els strong_unanimity)"
    sorry
  moreover have
    "satisfies (\<lambda>E. limit_set_soc_choice (alts_\<E> E) UNIV) (Invariance (anonymity\<^sub>\<R> X))"
    sorry
  moreover have
    "satisfies (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) 
      (Invariance (Restr (anonymity\<^sub>\<R> X) (\<K>_els strong_unanimity)))"
    sorry
  moreover have
    "satisfies (fun\<^sub>\<E> (social_choice_result.\<R>\<^sub>\<W> (votewise_distance swap l_one) 
                strong_unanimity)) (Invariance (anonymity\<^sub>\<R> X))"
    sorry
  moreover have "anonymity\<^sub>\<R> X `` {E} \<in> X // (anonymity\<^sub>\<R> X)"
    sorry
  moreover have
    "(social_choice_result.distance_\<R> (votewise_distance swap l_one) strong_unanimity)
      = kemeny_rule"
    unfolding kemeny_rule.simps swap_\<R>.simps
    by (metis (no_types))
  ultimately have
    "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> kemeny_rule) (anonymity\<^sub>\<R> X `` {E}) = 
      social_choice_result.distance_\<R>\<^sub>\<Q> 
        (anonymity\<^sub>\<R> X) (votewise_distance swap l_one) strong_unanimity (anonymity\<^sub>\<R> X `` {E})"
    using assms 
      social_choice_result.invar_dr_simple_dist_imp_quotient_dr[of
        "anonymity\<^sub>\<R> X" X "votewise_distance swap l_one" 
        strong_unanimity "anonymity\<^sub>\<R> X `` {E}"]
    by (metis (no_types))
  also have "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> kemeny_rule) (anonymity\<^sub>\<R> X `` {E}) = fun\<^sub>\<E> kemeny_rule E"
    sorry
  finally show ?thesis
    by (metis (no_types))
qed
    
subsection \<open>Datatype Instantiation\<close>

datatype alternative = a | b | c | d

lemma alternative_univ [code_unfold]: "UNIV = {a, b, c, d}" (is "_ = ?A")
proof (rule UNIV_eq_I)
  fix x :: "alternative"
  show "x \<in> ?A"
    by (cases x) simp_all
qed

instantiation alternative :: enum
begin
  definition "Enum.enum \<equiv> [a, b, c, d]"
  definition "Enum.enum_all P \<equiv> P a \<and> P b \<and> P c \<and> P d"
  definition "Enum.enum_ex P \<equiv> P a \<or> P b \<or> P c \<or> P d"
instance proof
  qed (simp_all only: enum_alternative_def enum_all_alternative_def
      enum_ex_alternative_def alternative_univ, simp_all)
end

(*
value "swap_\<R> strong_unanimity {a, b, c :: alternative}
         [{(a, c), (b, c), (c, c), (a, b), (b, b), (a, a)},
          {(c, b), (a, b), (b, b), (c, a), (a, a), (c, c)}]"
*)

end

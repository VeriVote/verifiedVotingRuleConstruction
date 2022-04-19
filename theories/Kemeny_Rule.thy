(*  File:       Kemeny_Rule.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Kemeny Rule\<close>

theory Kemeny_Rule
  imports "Compositional_Structures/Basic_Modules/Component_Types/Distance_Rationalization"
          "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance"
begin

text \<open>
  This is the Kemeny rule. It creates a complete ordering of alternatives and
  evaluates each ordering of the alternatives in terms of the sum of preference
  reversals on each ballot that would have to be performed in order to produce
  that transitive ordering. The complete ordering which requires the fewest
  preference reversals is the final result of the method.
\<close>

subsection \<open>Definition\<close>

fun kemeny_rule :: "'a Electoral_Module" where
  "kemeny_rule A p = (dr_rule (votewise_distance swap l_one) strong_unanimity) A p"

fun kemeny_rule_std :: "'a Electoral_Module" where
  "kemeny_rule_std A p = (dr_rule_std (votewise_distance swap l_one) strong_unanimity) A p"

subsection \<open>Anonymity Property\<close>

theorem kemeny_anonymous: "anonymity kemeny_rule"
proof (unfold kemeny_rule.simps)
  let ?swap_dist = "(votewise_distance swap l_one)"
  from l_one_is_symm
  have "el_distance_anonymity ?swap_dist"
    using el_dist_anon_if_norm_symm[of l_one]
    by simp
  with strong_unanimity_is_anon
  show "anonymity (dr_rule ?swap_dist strong_unanimity)"
    using rule_anon_if_el_dist_and_cons_class_anon
    by metis
qed

datatype alternative = a | b | c | d
lemma UNIV_alternative [code_unfold]:
  "UNIV = {a, b, c, d}" (is "_ = ?A")
proof (rule UNIV_eq_I)
  fix x show "x \<in> ?A" by (cases x) simp_all
qed
instantiation alternative :: enum
begin
definition "Enum.enum = [a, b, c, d]"
definition "Enum.enum_all P \<longleftrightarrow> P a \<and> P b \<and> P c \<and> P d"
definition "Enum.enum_ex P \<longleftrightarrow> P a \<or> P b \<or> P c \<or> P d"
instance proof
qed (simp_all only: enum_alternative_def enum_all_alternative_def
enum_ex_alternative_def UNIV_alternative, simp_all)
end

value "all_profiles 2 {a,b::alternative}"

value "(Set.filter (\<lambda>x. True) (all_profiles 2 {a,b::alternative}))"

definition "x = em_with_condition (\<lambda>x. True) elect_first_module"

export_code x in Haskell

value "all_profiles 2 {a,b,c::alternative}"

value "elect_first_module {a,b::alternative} [{(a,b), (a,a), (b,b)}]"

value "favoring_consensus_elections_std strong_unanimity a {a,b::alternative} 1"

value "score_std (votewise_distance swap l_one) strong_unanimity ({a,b::alternative}, [{(a,b), (a,a), (b,b)}]) a"

value "(votewise_distance swap l_one) ({a,b::alternative}, [{(a,b), (a,a), (b,b)}]) ({a,b::alternative}, [{(b,a), (a,a), (b,b)}])"

value "pairwise_disagreements_2 {a,b::alternative} {(a,b), (a,a), (b,b)} {(b,a), (a,a), (b,b)}"

definition "y = swap ({a,b::alternative}, {(a,b), (a,a), (b,b)}) ({a,b::alternative}, {(a,b), (a,a), (b,b)})"

code_thms x

value "dr_winners_std (votewise_distance swap l_one) strong_unanimity {a,b::alternative} [{(a,b), (a,a), (b,b)}]"

value "dr_rule_std (votewise_distance swap l_one) strong_unanimity {a,b::alternative} [{(a,b), (a,a), (b,b)}]"


value "kemeny_rule_std {a,b,c::alternative} [{(a, c), (b, c), (c, c), (a, b), (b, b), (a, a)},
                                             {(c, b), (a, b), (b, b), (c, a), (a, a), (c, c)}]"


end

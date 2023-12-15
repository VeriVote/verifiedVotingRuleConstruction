theory Election_Quotients
  imports Relation_Quotients
          "../Social_Choice_Types/Property_Interpretations"
begin

subsection \<open>Definitions\<close>

fun fixed_alt_elections :: "'a set \<Rightarrow> ('a, 'v) Election set" where
  "fixed_alt_elections A = {E. alts_\<E> E = A} \<inter> valid_elections"

subsection \<open>Specific Quotients\<close>

fun anonymity\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anonymity\<^sub>\<Q> A = quotient (fixed_alt_elections A) (anonymity\<^sub>\<R> (fixed_alt_elections A))"

theorem anonymity\<^sub>\<Q>_iso:
  fixes
    A :: "real set"
  assumes
    "finite A"
  defines
    "n \<equiv> fact (card A)"
  shows "True"
  sorry

end
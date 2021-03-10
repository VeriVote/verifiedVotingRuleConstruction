(*  File:       Borda_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Borda Rule\<close>

theory Borda_Rule
  imports Borda_Module Elect_Module
begin

text
\<open>This is the Borda rule. On each ballot, each alternative is assigned a score
that depends on how many alternatives are ranked below. The sum of all such
scores for an alternative is hence called their Borda score. The alternative
with the highest Borda score is elected.\<close>

subsection \<open>Definition\<close>

fun borda_rule :: "'a Electoral_Module" where
  "borda_rule A p = elector borda A p"

fun borda_rule_code :: "'a Electoral_Module" where
  "borda_rule_code A p = elector borda_code A p"

end

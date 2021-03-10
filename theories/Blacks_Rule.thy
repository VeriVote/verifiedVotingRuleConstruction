(*  File:       Blacks_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Black's Rule\<close>

theory Blacks_Rule
  imports Condorcet_Rule Borda_Rule
begin

text
\<open>This is Black's voting rule. It is composed of a function that determines
the Condorcet winner and the Borda rule. Whenever there exists no Condorcet
winner, it elects the choice made by the Borda rule, otherwise the Condorcet
winner is elected.\<close>

subsection \<open>Definition\<close>

fun blacks_rule :: "'a Electoral_Module" where
  "blacks_rule A p = (condorcet_rule \<triangleright> borda_rule) A p"

fun blacks_rule_code :: "'a Electoral_Module" where
  "blacks_rule_code A p = (condorcet_rule_code \<triangleright> borda_rule_code) A p"

end

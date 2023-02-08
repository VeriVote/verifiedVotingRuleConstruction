(*  File:       Blacks_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Black's Rule\<close>

theory Blacks_Rule
  imports Pairwise_Majority_Rule
          Borda_Rule
begin

text \<open>
  This is Black's voting rule. It is composed of a function that determines
  the Condorcet winner, i.e., the Pairwise Majority rule, and the Borda rule.
  Whenever there exists no Condorcet winner, it elects the choice made by the
  Borda rule, otherwise the Condorcet winner is elected.
\<close>

subsection \<open>Definition\<close>

fun blacks_rule :: "'a Electoral_Module" where
  "blacks_rule A p = (pairwise_majority_rule \<triangleright> borda_rule) A p"

end

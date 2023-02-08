(*  File:       Borda_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Borda Module\<close>

theory Borda_Module
  imports "Component_Types/Elimination_Module"
begin

text \<open>
  This is the Borda module used by the Borda rule. The Borda rule is a voting
  rule, where on each ballot, each alternative is assigned a score that depends
  on how many alternatives are ranked below. The sum of all such scores for an
  alternative is hence called their Borda score. The alternative with the
  highest Borda score is elected. The module implemented herein only rejects
  the alternatives not elected by the voting rule, and defers the alternatives
  that would be elected by the full voting rule.
\<close>

subsection \<open>Definition\<close>

fun borda_score :: "'a Evaluation_Function" where
  "borda_score x A p = (\<Sum> y \<in> A. (prefer_count p x y))"

fun borda :: "'a Electoral_Module" where
  "borda A p = max_eliminator borda_score A p"

end

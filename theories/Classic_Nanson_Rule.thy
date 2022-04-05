(*  File:       Classic_Nanson_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Classic Nanson Rule\<close>

theory Classic_Nanson_Rule
  imports "Compositional_Structures/Basic_Modules/Borda_Module"
          "Compositional_Structures/Defer_One_Loop_Composition"
begin

text \<open>
  This is the classic Nanson's voting rule, i.e., the rule that was originally
  invented by Nanson, but not the Nanson-Baldwin rule. The idea is similar,
  however, as alternatives with a Borda score less or equal than the average
  Borda score are excluded. The Borda scores of the remaining alternatives
  are hence adjusted to the new set of (still) eligible alternatives.
\<close>

subsection \<open>Definition\<close>

fun classic_nanson_rule :: "'a Electoral_Module" where
  "classic_nanson_rule A p =
    ((leq_average_eliminator borda_score) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"

end

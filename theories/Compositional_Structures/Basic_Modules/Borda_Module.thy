(*  File:       Borda_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Borda Module\<close>

theory Borda_Module
  imports "Component_Types/Elimination_Module"
begin

context social_choice_result
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

fun borda_score :: "('a, 'v) Evaluation_Function" where
  "borda_score V x A p = (\<Sum> y \<in> A. (prefer_count V p x y))"

fun borda :: "('a, 'v, 'a Result) Electoral_Module" where
  "borda V A p = max_eliminator borda_score V A p"

subsection \<open>Soundness\<close>

theorem borda_sound: "electoral_module borda"
  unfolding borda.simps
  using max_elim_sound
  by metis


subsection \<open>Non-Blocking\<close>

text \<open>
  The Borda module is non-blocking.
\<close>

theorem borda_mod_non_blocking[simp]: "non_blocking borda"
  unfolding borda.simps
  using max_elim_non_blocking
  by metis

subsection \<open>Non-Electing\<close>

text \<open>
  The Borda module is non-electing.
\<close>

theorem borda_mod_non_electing[simp]: "non_electing borda"
  using max_elim_non_electing
  unfolding borda.simps non_electing_def
  by metis

end
end

(*  File:       Elect_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elect Module\<close>

theory Elect_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  The elect module is not concerned about the voter's ballots, and
  just elects all alternatives. It is primarily used in sequence after
  an electoral module that only defers alternatives to finalize the decision,
  thereby inducing a proper voting rule in the social choice sense.
\<close>

subsection \<open>Definition\<close>

fun elect_module :: "('a, 'v, 'a Result) Electoral_Module" where
  "elect_module V A p = (A, {}, {})"

subsection \<open>Soundness\<close>

theorem elect_mod_sound[simp]: "social_choice_result.electoral_module elect_module"
  unfolding social_choice_result.electoral_module_def
  by simp

lemma elect_mod_only_voters: "only_voters_vote elect_module"
  unfolding only_voters_vote_def
  by simp

subsection \<open>Electing\<close>

theorem elect_mod_electing[simp]: "electing elect_module"
  unfolding electing_def
  by simp

end
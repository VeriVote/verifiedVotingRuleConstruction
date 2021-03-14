(*  File:       Defer_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Defer Module\<close>

theory Defer_Module
  imports "Component_Types/Electoral_Module"
begin

text
\<open>The defer module is not concerned about the voter's ballots, and
simply defers all alternatives.
It is primarily used for defining an empty loop.\<close>

subsection \<open>Definition\<close>

fun defer_module :: "'a Electoral_Module" where
  "defer_module A p = ({}, {}, A)"

subsection \<open>Soundness\<close>

theorem def_mod_sound[simp]: "electoral_module defer_module"
  by (simp add: electoral_module_def)

subsection \<open>Properties\<close>

theorem def_mod_non_electing: "non_electing defer_module"
  by (simp add: non_electing_def)

theorem def_mod_def_lift_inv: "defer_lift_invariance defer_module"
  by (simp add: defer_lift_invariance_def)

end

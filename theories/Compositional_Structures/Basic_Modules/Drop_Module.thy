(*  File:       Drop_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Drop Module\<close>

theory Drop_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  This is a family of electoral modules. For a natural number n and a
  lexicon (linear order) r of all alternatives, the according drop module
  rejects the lexicographically first n alternatives (from A) and
  defers the rest.
  It is primarily used as counterpart to the pass module in a
  parallel composition, in order to segment the alternatives into
  two groups.
\<close>

subsection \<open>Definition\<close>

fun drop_module :: "nat \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "drop_module n r A p =
    ({},
    {a \<in> A. rank (limit A r) a \<le> n},
    {a \<in> A. rank (limit A r) a > n})"

subsection \<open>Soundness\<close>

theorem drop_mod_sound[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: nat
  shows "electoral_module (drop_module n r)"
proof (intro electoral_modI)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  let ?mod = "drop_module n r"
  have "\<forall> a \<in> A. a \<in> {x \<in> A. rank (limit A r) x \<le> n} \<or> a \<in> {x \<in> A. rank (limit A r) x > n}"
    by auto
  hence "{a \<in> A. rank (limit A r) a \<le> n} \<union> {a \<in> A. rank (limit A r) a > n} = A"
    by blast
  hence set_partition: "set_equals_partition A (drop_module n r A p)"
    by simp
  have "\<forall> a \<in> A.
          \<not> (a \<in> {x \<in> A. rank (limit A r) x \<le> n} \<and> a \<in> {x \<in> A. rank (limit A r) x > n})"
    by simp
  hence "{a \<in> A. rank (limit A r) a \<le> n} \<inter> {a \<in> A. rank (limit A r) a > n} = {}"
    by blast
  thus "well_formed A (?mod A p)"
    using set_partition
    by simp
qed

subsection \<open>Non-Electing\<close>

text \<open>
  The drop module is non-electing.
\<close>

theorem drop_mod_non_electing[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: nat
  shows "non_electing (drop_module n r)"
  unfolding non_electing_def
  by simp

subsection \<open>Properties\<close>

text \<open>
  The drop module is strictly defer-monotone.
\<close>

theorem drop_mod_def_lift_inv[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: nat
  shows "defer_lift_invariance (drop_module n r)"
  unfolding defer_lift_invariance_def
  by simp

end

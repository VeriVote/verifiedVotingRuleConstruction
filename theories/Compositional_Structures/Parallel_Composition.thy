(*  File:       Parallel_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Parallel Composition\<close>

theory Parallel_Composition
  imports "Basic_Modules/Component_Types/Aggregator"
          "Basic_Modules/Component_Types/Electoral_Module"
begin

text
\<open>The parallel composition composes a new electoral module from
two electoral modules combined with an aggregator.
Therein, the two modules each make a decision and the aggregator combines
them to a single (aggregated) result.\<close>

subsection \<open>Definition\<close>

fun parallel_composition :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Aggregator \<Rightarrow> 'a Electoral_Module" where
  "parallel_composition m n agg A p = agg A (m A p) (n A p)"

abbreviation parallel :: "'a Electoral_Module \<Rightarrow> 'a Aggregator \<Rightarrow>
        'a Electoral_Module \<Rightarrow> 'a Electoral_Module"
      ("_ \<parallel>\<^sub>_ _" [50, 1000, 51] 50) where
  "m \<parallel>\<^sub>a n == parallel_composition m n a"

subsection \<open>Soundness\<close>

theorem par_comp_sound[simp]:
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n" and
    agg_a: "aggregator a"
  shows "electoral_module (m \<parallel>\<^sub>a n)"
  unfolding electoral_module_def
proof (safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p"
  have "well_formed A (a A (m A p) (n A p))"
    using aggregator_def combine_ele_rej_def par_comp_result_sound
          electoral_module_def mod_m mod_n fin_A prof_A agg_a
    by (smt (verit, ccfv_threshold))
  thus "well_formed A ((m \<parallel>\<^sub>a n) A p)"
    by simp
qed

subsection \<open>Composition Rule\<close>

(*
   Using a conservative aggregator, the parallel composition
   preserves the property non-electing.
*)
theorem conserv_agg_presv_non_electing[simp]:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n" and
    conservative: "agg_conservative a"
  shows "non_electing (m \<parallel>\<^sub>a n)"
  unfolding non_electing_def
proof (safe)
  have emod_m: "electoral_module m"
    using non_electing_m
    by (simp add: non_electing_def)
  have emod_n: "electoral_module n"
    using non_electing_n
    by (simp add: non_electing_def)
  have agg_a: "aggregator a"
    using conservative
    by (simp add: agg_conservative_def)
  thus "electoral_module (m \<parallel>\<^sub>a n)"
    using emod_m emod_n agg_a par_comp_sound
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    x_wins: "x \<in> elect (m \<parallel>\<^sub>a n) A p"
  have emod_m: "electoral_module m"
    using non_electing_m
    by (simp add: non_electing_def)
  have emod_n: "electoral_module n"
    using non_electing_n
    by (simp add: non_electing_def)
  have
    "let c = (a A (m A p) (n A p)) in
      (elect_r c \<subseteq> ((elect m A p) \<union> (elect n A p)))"
    using conservative agg_conservative_def
          emod_m emod_n par_comp_result_sound
          combine_ele_rej_def fin_A prof_A
    by (smt (verit, ccfv_SIG))
  hence "x \<in> ((elect m A p) \<union> (elect n A p))"
    using x_wins
    by auto
  thus "x \<in> {}"
    using sup_bot_right non_electing_def fin_A
          non_electing_m non_electing_n prof_A
    by (metis (no_types, lifting))
qed

end

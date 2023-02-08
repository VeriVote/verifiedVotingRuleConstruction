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

text \<open>
  The parallel composition composes a new electoral module from
  two electoral modules combined with an aggregator.
  Therein, the two modules each make a decision and the aggregator combines
  them to a single (aggregated) result.
\<close>

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
proof (unfold electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p"
  have wf_quant:
    "\<forall> a. aggregator a =
      (\<forall> A' e r d e' r' d'.
        (\<not> well_formed (A'::'a set) (e, r', d) \<or>
          \<not> well_formed A' (r, d', e')) \<or>
        well_formed A'
          (a A' (e, r', d) (r, d', e')))"
    unfolding aggregator_def
    by blast
  have wf_imp:
    "\<forall> m' A' p'.
      (electoral_module m' \<and> finite (A'::'a set) \<and>
        profile A' p') \<longrightarrow>
        well_formed A' (m' A' p')"
    using par_comp_result_sound
    by (metis (no_types))
  from mod_m mod_n fin_A prof_A agg_a
  have "well_formed A (a A (m A p) (n A p))"
    using agg_a combine_ele_rej_def fin_A
          mod_m mod_n prof_A wf_imp wf_quant
    by metis
  thus "well_formed A ((m \<parallel>\<^sub>a n) A p)"
    by simp
qed

subsection \<open>Composition Rule\<close>

text \<open>
  Using a conservative aggregator, the parallel composition
  preserves the property non-electing.
\<close>

theorem conserv_agg_presv_non_electing[simp]:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n" and
    conservative: "agg_conservative a"
  shows "non_electing (m \<parallel>\<^sub>a n)"
proof (unfold non_electing_def, safe)
  have emod_m: "electoral_module m"
    using non_electing_m
    unfolding non_electing_def
    by simp
  have emod_n: "electoral_module n"
    using non_electing_n
    unfolding non_electing_def
    by simp
  have agg_a: "aggregator a"
    using conservative
    unfolding agg_conservative_def
    by simp
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
    unfolding non_electing_def
    by simp
  have emod_n: "electoral_module n"
    using non_electing_n
    unfolding non_electing_def
    by simp
  have
    "\<forall> r r' d d' e e' A' f.
      (well_formed (A'::'a set) (e', r', d') \<and> well_formed A' (e, r, d) \<longrightarrow>
        elect_r (f A' (e', r', d') (e, r, d)) \<subseteq> e' \<union> e \<and>
          reject_r (f A' (e', r', d') (e, r, d)) \<subseteq> r' \<union> r \<and>
          defer_r (f A' (e', r', d') (e, r, d)) \<subseteq> d' \<union> d) =
            ((\<not> well_formed A' (e', r', d') \<or> \<not> well_formed A' (e, r, d)) \<or>
              elect_r (f A' (e', r', d') (e, r, d)) \<subseteq> e' \<union> e \<and>
                reject_r (f A' (e', r', d') (e, r, d)) \<subseteq> r' \<union> r \<and>
                defer_r (f A' (e', r', d') (e, r, d)) \<subseteq> d' \<union> d)"
    by linarith
  hence
    "\<forall> a. agg_conservative a =
      (aggregator a \<and>
        (\<forall> A' e e' d d' r r'. (\<not> well_formed (A'::'a set) (e, r, d) \<or>
            \<not> well_formed A' (e', r', d')) \<or>
          elect_r (a A' (e, r, d) (e', r', d')) \<subseteq> e \<union> e' \<and>
            reject_r (a A' (e, r, d) (e', r', d')) \<subseteq> r \<union> r' \<and>
            defer_r (a A' (e, r, d) (e', r', d')) \<subseteq> d \<union> d'))"
    unfolding agg_conservative_def
    by simp
  hence
    "aggregator a \<and>
      (\<forall> A' e e' d d' r r'. \<not> well_formed A' (e, r, d) \<or>
          \<not> well_formed A' (e', r', d') \<or>
          elect_r (a A' (e, r, d) (e', r', d')) \<subseteq> e \<union> e' \<and>
            reject_r (a A' (e, r, d) (e', r', d')) \<subseteq> r \<union> r' \<and>
            defer_r (a A' (e, r, d) (e', r', d')) \<subseteq> d \<union> d')"
    using conservative
    by presburger
  hence
    "let c = (a A (m A p) (n A p)) in
      (elect_r c \<subseteq> ((elect m A p) \<union> (elect n A p)))"
    using emod_m emod_n fin_A par_comp_result_sound
          prod.collapse prof_A
    by metis
  hence "x \<in> ((elect m A p) \<union> (elect n A p))"
    using x_wins
    by auto
  thus "x \<in> {}"
    using sup_bot_right fin_A prof_A
          non_electing_m non_electing_n
    unfolding non_electing_def
    by (metis (no_types, lifting))
qed

end

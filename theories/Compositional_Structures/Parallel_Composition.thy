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
  have wf_quant:
    "\<forall>f. aggregator f =
      (\<forall>a_set elec1 rej1 def1 elec2 rej2 def2.
        (\<not> well_formed (a_set::'a set) (elec1, rej2, def1) \<or>
          \<not> well_formed a_set (rej1, def2, elec2)) \<or>
        well_formed a_set
          (f a_set (elec1, rej2, def1) (rej1, def2, elec2)))"
    unfolding aggregator_def
    by blast
  have wf_imp:
    "\<forall>e_mod a_set prof.
      (electoral_module e_mod \<and> finite (a_set::'a set) \<and>
        profile a_set prof) \<longrightarrow>
        well_formed a_set (e_mod a_set prof)"
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
    "\<forall>x0 x1 x2 x3 x4 x5 x6 x7.
      (well_formed (x6::'a set) (x5, x1, x3) \<and> well_formed x6 (x4, x0, x2) \<longrightarrow>
        elect_r (x7 x6 (x5, x1, x3) (x4, x0, x2)) \<subseteq> x5 \<union> x4 \<and>
          reject_r (x7 x6 (x5, x1, x3) (x4, x0, x2)) \<subseteq> x1 \<union> x0 \<and>
          defer_r (x7 x6 (x5, x1, x3) (x4, x0, x2)) \<subseteq> x3 \<union> x2) =
            ((\<not> well_formed x6 (x5, x1, x3) \<or> \<not> well_formed x6 (x4, x0, x2)) \<or>
              elect_r (x7 x6 (x5, x1, x3) (x4, x0, x2)) \<subseteq> x5 \<union> x4 \<and>
                reject_r (x7 x6 (x5, x1, x3) (x4, x0, x2)) \<subseteq> x1 \<union> x0 \<and>
                defer_r (x7 x6 (x5, x1, x3) (x4, x0, x2)) \<subseteq> x3 \<union> x2)"
    by linarith
  hence
    "\<forall>f. agg_conservative f =
      (aggregator f \<and>
        (\<forall>A Aa Ab Ac Ad Ae Af. (\<not> well_formed (A::'a set) (Aa, Ae, Ac) \<or>
            \<not> well_formed A (Ab, Af, Ad)) \<or>
          elect_r (f A (Aa, Ae, Ac) (Ab, Af, Ad)) \<subseteq> Aa \<union> Ab \<and>
            reject_r (f A (Aa, Ae, Ac) (Ab, Af, Ad)) \<subseteq> Ae \<union> Af \<and>
            defer_r (f A (Aa, Ae, Ac) (Ab, Af, Ad)) \<subseteq> Ac \<union> Ad))"
    by (simp add: agg_conservative_def)
  hence
    "aggregator a \<and>
      (\<forall>A Aa Ab Ac Ad Ae Af. \<not> well_formed A (Aa, Ae, Ac) \<or>
          \<not> well_formed A (Ab, Af, Ad) \<or>
          elect_r (a A (Aa, Ae, Ac) (Ab, Af, Ad)) \<subseteq> Aa \<union> Ab \<and>
            reject_r (a A (Aa, Ae, Ac) (Ab, Af, Ad)) \<subseteq> Ae \<union> Af \<and>
            defer_r (a A (Aa, Ae, Ac) (Ab, Af, Ad)) \<subseteq> Ac \<union> Ad)"
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
    using sup_bot_right non_electing_def fin_A
          non_electing_m non_electing_n prof_A
    by (metis (no_types, lifting))
qed

end

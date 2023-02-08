(*  File:       Sequential_Majority_Comparison.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Sequential Majority Comparison\<close>

theory Sequential_Majority_Comparison
  imports "Compositional_Structures/Basic_Modules/Plurality_Module"
          "Compositional_Structures/Drop_And_Pass_Compatibility"
          "Compositional_Structures/Revision_Composition"
          "Compositional_Structures/Maximum_Parallel_Composition"
          "Compositional_Structures/Defer_One_Loop_Composition"
begin

text \<open>
  Sequential majority comparison compares two alternatives by plurality voting.
  The loser gets rejected, and the winner is compared to the next alternative.
  This process is repeated until only a single alternative is left, which is
  then elected.
\<close>

subsection \<open>Definition\<close>

fun smc :: "'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "smc x A p =
      ((((((pass_module 2 x) \<triangleright> ((plurality\<down>) \<triangleright> (pass_module 1 x))) \<parallel>\<^sub>\<up>
      (drop_module 2 x)) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) \<triangleright> elect_module) A p)"

subsection \<open>Soundness\<close>

text \<open>
  As all base components are electoral modules (, aggregators, or termination
  conditions), and all used compositional structures create electoral modules,
  sequential majority comparison unsurprisingly is an electoral module.
\<close>

theorem smc_sound:
  assumes order: "linear_order x"
  shows "electoral_module (smc x)"
proof (unfold electoral_module_def, simp, safe, simp_all)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    xa :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    reject_xa: "xa \<in> reject (?smc) A p" and
    elect_xa: "xa \<in> elect (?smc) A p"
  show False
    using IntI drop_mod_sound elect_xa emptyE fin_A
          loop_comp_sound max_agg_sound order prof_A
          par_comp_sound pass_mod_sound reject_xa
          plurality_sound result_disj rev_comp_sound
          seq_comp_sound
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    xa :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    reject_xa: "xa \<in> reject (?smc) A p" and
    defer_xa: "xa \<in> defer (?smc) A p"
  show False
    using IntI drop_mod_sound defer_xa emptyE fin_A
          loop_comp_sound max_agg_sound order prof_A
          par_comp_sound pass_mod_sound reject_xa
          plurality_sound result_disj rev_comp_sound
          seq_comp_sound
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    xa :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    elect_xa:
      "xa \<in> elect (?smc) A p"
  show "xa \<in> A"
    using drop_mod_sound elect_in_alts elect_xa fin_A
          in_mono loop_comp_sound max_agg_sound order
          par_comp_sound pass_mod_sound plurality_sound
          prof_A rev_comp_sound seq_comp_sound
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    xa :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    defer_xa: "xa \<in> defer (?smc) A p"
  show "xa \<in> A"
    using drop_mod_sound defer_in_alts defer_xa fin_A
          in_mono loop_comp_sound max_agg_sound order
          par_comp_sound pass_mod_sound plurality_sound
          prof_A rev_comp_sound seq_comp_sound
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    xa :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    reject_xa:
      "xa \<in> reject (?smc) A p"
  have plurality_rev_sound:
    "electoral_module
      (plurality::'a set \<Rightarrow> (_ \<times> _) set list \<Rightarrow> _ set \<times> _ set \<times> _ set\<down>)"
    by simp
  have par1_sound:
    "electoral_module (pass_module 2 x \<triangleright> ((plurality\<down>) \<triangleright> pass_module 1 x))"
    using order
    by simp
  also have par2_sound:
      "electoral_module (drop_module 2 x)"
    using order
    by simp
  show "xa \<in> A"
    using reject_in_alts reject_xa fin_A in_mono
          loop_comp_sound max_agg_sound order
          par_comp_sound pass_mod_sound prof_A
          seq_comp_sound pass_mod_sound par1_sound
          par2_sound plurality_rev_sound
    by (metis (no_types))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    xa :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    xa_in_A: "xa \<in> A" and
    not_defer_xa:
      "xa \<notin> defer (?smc) A p" and
    not_reject_xa:
      "xa \<notin> reject (?smc) A p"
  show "xa \<in> elect (?smc) A p"
    using drop_mod_sound loop_comp_sound max_agg_sound
          order par_comp_sound pass_mod_sound xa_in_A
          plurality_sound rev_comp_sound seq_comp_sound
          electoral_mod_defer_elem fin_A not_defer_xa
          not_reject_xa prof_A
    by metis
qed


subsection \<open>Electing\<close>

text \<open>
  The sequential majority comparison electoral module is electing.
  This property is needed to convert electoral modules to a social choice
  function. Apart from the very last proof step, it is a part of the
  monotonicity proof below.
\<close>

theorem smc_electing:
  assumes "linear_order x"
  shows "electing (smc x)"
proof -
  let ?pass2 = "pass_module 2 x"
  let ?tie_breaker = "(pass_module 1 x)"
  let ?plurality_defer = "(plurality\<down>) \<triangleright> ?tie_breaker"
  let ?compare_two = "?pass2 \<triangleright> ?plurality_defer"
  let ?drop2 = "drop_module 2 x"
  let ?eliminator = "?compare_two \<parallel>\<^sub>\<up> ?drop2"
  let ?loop =
    "let t = defer_equal_condition 1 in (?eliminator \<circlearrowleft>\<^sub>t)"

  have 00011: "non_electing (plurality\<down>)"
    by simp
  have 00012: "non_electing ?tie_breaker"
    using assms
    by simp
  have 00013: "defers 1 ?tie_breaker"
    using assms pass_one_mod_def_one
    by simp
  have 20000: "non_blocking (plurality\<down>)"
    by simp

  have 0020: "disjoint_compatibility ?pass2 ?drop2"
    using assms
    by simp (* disj_compat_comm *)
  have 1000: "non_electing ?pass2"
    using assms
    by simp
  have 1001: "non_electing ?plurality_defer"
    using 00011 00012
    by simp
  have 2000: "non_blocking ?pass2"
    using assms
    by simp
  have 2001: "defers 1 ?plurality_defer"
    using 20000 00011 00013 seq_comp_def_one
    by blast

  have 002: "disjoint_compatibility ?compare_two ?drop2"
    using assms 0020
    by simp
  have 100: "non_electing ?compare_two"
    using 1000 1001
    by simp
  have 101: "non_electing ?drop2"
    using assms
    by simp
  have 102: "agg_conservative max_aggregator"
    by simp
  have 200: "defers 1 ?compare_two"
    using 2000 1000 2001 seq_comp_def_one
    by auto
  have 201: "rejects 2 ?drop2"
    using assms
    by simp

  have 10: "non_electing ?eliminator"
    using 100 101 102
    by simp
  have 20: "eliminates 1 ?eliminator"
    using 200 100 201 002 par_comp_elim_one
    by metis

  have 2: "defers 1 ?loop"
    using 10 20
    by simp
  have 3: "electing elect_module"
    by simp

  show ?thesis
    using 2 3 assms seq_comp_electing smc_sound
    unfolding Defer_One_Loop_Composition.iter.simps
              smc.simps electing_def
    by metis
qed

subsection \<open>(Weak) Monotonicity Property\<close>

text \<open>
  The following proof is a fully modular proof for weak monotonicity of
  sequential majority comparison. It is composed of many small steps.
\<close>

theorem smc_monotone:
  assumes "linear_order x"
  shows "monotonicity (smc x)"
proof -
  let ?pass2 = "pass_module 2 x"
  let ?tie_breaker = "(pass_module 1 x)"
  let ?plurality_defer = "(plurality\<down>) \<triangleright> ?tie_breaker"
  let ?compare_two = "?pass2 \<triangleright> ?plurality_defer"
  let ?drop2 = "drop_module 2 x"
  let ?eliminator = "?compare_two \<parallel>\<^sub>\<up> ?drop2"
  let ?loop =
    "let t = defer_equal_condition 1 in (?eliminator \<circlearrowleft>\<^sub>t)"

  have 00010: "defer_invariant_monotonicity (plurality\<down>)"
    by simp (* rev_comp_def_inv_mono plurality_strict_strong_mono *)
  have 00011: "non_electing (plurality\<down>)"
    by simp (* rev_comp_non_electing plurality_sound *)
  have 00012: "non_electing ?tie_breaker"
    using assms
    by simp (* pass_mod_non_electing *)
  have 00013: "defers 1 ?tie_breaker"
    using assms pass_one_mod_def_one
    by simp
  have 00014: "defer_monotonicity ?tie_breaker"
    using assms
    by simp (* dl_inv_imp_def_mono pass_mod_dl_inv *)
  have 20000: "non_blocking (plurality\<down>)"
    by simp (* rev_comp_non_blocking plurality_electing *)

  have 0000: "defer_lift_invariance ?pass2"
    using assms
    by simp (* pass_mod_dl_inv *)
  have 0001: "defer_lift_invariance ?plurality_defer"
    using 00010 00011 00012 00013 00014
    by simp (* def_inv_mono_imp_def_lift_inv *)
  have 0020: "disjoint_compatibility ?pass2 ?drop2"
    using assms
    by simp (* disj_compat_comm drop_pass_disj_compat *)
  have 1000: "non_electing ?pass2"
    using assms
    by simp (* pass_mod_non_electing *)
  have 1001: "non_electing ?plurality_defer"
    using 00011 00012
    by simp (* seq_comp_presv_non_electing *)
  have 2000: "non_blocking ?pass2"
    using assms
    by simp (* pass_mod_non_blocking *)
  have 2001: "defers 1 ?plurality_defer"
    using 20000 00011 00013 seq_comp_def_one
    by blast

  have 000: "defer_lift_invariance ?compare_two"
    using 0000 0001
    by simp (* seq_comp_presv_def_lift_inv *)
  have 001: "defer_lift_invariance ?drop2"
    using assms
    by simp (* drop_mod_def_lift_inv *)
  have 002: "disjoint_compatibility ?compare_two ?drop2"
    using assms 0020
    by simp
      (* disj_compat_seq seq_comp_sound rev_comp_sound
         plurality_sound pass_mod_sound *)
  have 100: "non_electing ?compare_two"
    using 1000 1001
    by simp (* seq_comp_presv_non_electing *)
  have 101: "non_electing ?drop2"
    using assms
    by simp (* drop_mod_non_electing *)
  have 102: "agg_conservative max_aggregator"
    by simp (* max_agg_conserv *)
  have 200: "defers 1 ?compare_two"
    using 2000 1000 2001 seq_comp_def_one
    by auto
  have 201: "rejects 2 ?drop2"
    using assms
    by simp (* drop_two_mod_rej_two *)

  have 00: "defer_lift_invariance ?eliminator"
    using 000 001 002 par_comp_def_lift_inv
    by simp (* par_comp_def_lift_inv *)
  have 10: "non_electing ?eliminator"
    using 100 101 102
    by simp (* conserv_agg_presv_non_electing *)
  have 20: "eliminates 1 ?eliminator"
    using 200 100 201 002 par_comp_elim_one
    by simp

  have 0: "defer_lift_invariance ?loop"
    using 00
    by simp (* loop_comp_presv_def_lift_inv *)
  have 1: "non_electing ?loop"
    using 10
    by simp (* loop_comp_presv_non_electing *)
  have 2: "defers 1 ?loop"
    using 10 20
    by simp (* iter_elim_def_n *)
  have 3: "electing elect_module"
    by simp (* elect_mod_electing *)

  show ?thesis
    using 0 1 2 3 assms seq_comp_mono
    unfolding Electoral_Module.monotonicity_def
              Defer_One_Loop_Composition.iter.simps
              smc_sound smc.simps
    by (metis (full_types))
qed

end

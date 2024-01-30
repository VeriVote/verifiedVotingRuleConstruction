(*  File:       Sequential_Majority_Comparison.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Sequential Majority Comparison\<close>

theory Sequential_Majority_Comparison
  imports "Plurality_Rule"
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

fun smc :: "'a Preference_Relation \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "smc x V A p =
      ((elector ((((pass_module 2 x) \<triangleright> ((plurality_rule\<down>) \<triangleright> (pass_module 1 x))) \<parallel>\<^sub>\<up>
      (drop_module 2 x)) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)) V A p)"

subsection \<open>Soundness\<close>

text \<open>
  As all base components are electoral modules (, aggregators, or termination
  conditions), and all used compositional structures create electoral modules,
  sequential majority comparison unsurprisingly is an electoral module.
\<close>

theorem smc_sound:
  fixes x :: "'a Preference_Relation"
  assumes "linear_order x"
  shows "social_choice_result.electoral_module (smc x)"
proof (unfold social_choice_result.electoral_module_def, simp, safe, simp_all)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x' :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality_rule\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    "profile V A p" and
    "x' \<in> reject (?smc) V A p" and
    "x' \<in> elect (?smc) V A p"
  thus False
    using IntI drop_mod_sound emptyE loop_comp_sound max_agg_sound assms
          par_comp_sound pass_mod_sound plurality_rule_sound rev_comp_sound
          result_disj seq_comp_sound
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x' :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality_rule\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    "profile V A p" and
    "x' \<in> reject (?smc) V A p" and
    "x' \<in> defer (?smc) V A p"
  thus False
    using IntI assms result_disj emptyE drop_mod_sound loop_comp_sound
          max_agg_sound par_comp_sound pass_mod_sound plurality_rule_sound
          rev_comp_sound seq_comp_sound
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x' :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality_rule\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    prof: "profile V A p" and
    elect_x': "x' \<in> elect (?smc) V A p"
  have "social_choice_result.electoral_module ?smc"
    by (simp add: loop_comp_sound)
  thus "x' \<in> A"
    using prof elect_x' elect_in_alts
    by blast
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x' :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality_rule\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    prof: "profile V A p" and
    defer_x': "x' \<in> defer (?smc) V A p"
  have "social_choice_result.electoral_module ?smc"
    by (simp add: loop_comp_sound)
  thus "x' \<in> A"
    using prof defer_x' defer_in_alts
    by blast
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x' :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality_rule\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    prof: "profile V A p" and
    reject_x': "x' \<in> reject (?smc) V A p"
  have "social_choice_result.electoral_module ?smc"
    by (simp add: loop_comp_sound)
  thus "x' \<in> A"
    using prof reject_x' reject_in_alts
    by blast
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x' :: "'a"
  let ?a = "max_aggregator"
  let ?t = "defer_equal_condition"
  let ?smc =
    "pass_module 2 x \<triangleright>
       ((plurality_rule\<down>) \<triangleright> pass_module (Suc 0) x) \<parallel>\<^sub>?a
         drop_module 2 x \<circlearrowleft>\<^sub>?t (Suc 0)"
  assume
    "profile V A p" and
    "x' \<in> A" and
    "x' \<notin> defer (?smc) V A p" and
    "x' \<notin> reject (?smc) V A p"
  thus "x' \<in> elect (?smc) V A p"
    using assms electoral_mod_defer_elem drop_mod_sound loop_comp_sound
          max_agg_sound par_comp_sound pass_mod_sound plurality_rule_sound
          rev_comp_sound seq_comp_sound
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
  fixes x :: "'a Preference_Relation"
  assumes "linear_order x"
  shows "electing (smc x)"
proof -
  let ?pass2 = "pass_module 2 x"
  let ?tie_breaker = "(pass_module 1 x)"
  let ?plurality_defer = "(plurality_rule\<down>) \<triangleright> ?tie_breaker"
  let ?compare_two = "?pass2 \<triangleright> ?plurality_defer"
  let ?drop2 = "drop_module 2 x"
  let ?eliminator = "?compare_two \<parallel>\<^sub>\<up> ?drop2"
  let ?loop =
    "let t = defer_equal_condition 1 in (?eliminator \<circlearrowleft>\<^sub>t)"

  have 00011: "non_electing (plurality_rule\<down>)"
    by simp
  have 00012: "non_electing ?tie_breaker"
    using assms
    by simp
  have 00013: "defers 1 ?tie_breaker"
    using assms pass_one_mod_def_one
    by simp
  have 20000: "non_blocking (plurality_rule\<down>)"
    by simp
  have 0020: "disjoint_compatibility ?pass2 ?drop2"
    using assms
    by simp (* disj_compat_comm *)
  have 1000: "non_electing ?pass2"
    using assms
    by simp
  have 1001: "non_electing ?plurality_defer"
    using 00011 00012 seq_comp_presv_non_electing
    by blast
  have 2000: "non_blocking ?pass2"
    using assms
    by simp
  have 2001: "defers 1 ?plurality_defer"
    using 20000 00011 00013 seq_comp_def_one
    by blast
  have 002: "disjoint_compatibility ?compare_two ?drop2"
    using assms 0020 disj_compat_seq pass_mod_sound plurality_rule_sound 
          rev_comp_sound seq_comp_sound pass_mod_only_voters 
          plurality_rule_only_voters seq_comp_only_voters
          rev_comp_only_voters
    by metis
  have 100: "non_electing ?compare_two"
    using 1000 1001 seq_comp_presv_non_electing
    by simp
  have 101: "non_electing ?drop2"
    using assms
    by simp
  have 102: "agg_conservative max_aggregator"
    by simp
  have 200: "defers 1 ?compare_two"
    using 2000 1000 2001 seq_comp_def_one
    by simp
  have 201: "rejects 2 ?drop2"
    using assms
    by simp
  have 10: "non_electing ?eliminator"
    using 100 101 102 conserv_max_agg_presv_non_electing
    by blast
  have 20: "eliminates 1 ?eliminator"
    using 200 100 201 002 par_comp_elim_one
    by simp
  have 2: "defers 1 ?loop"
    using 10 20 iter_elim_def_n zero_less_one prod.exhaust_sel
          defer_equal_condition.simps
    by metis
  have 3: "electing elect_module"
    by simp
  show ?thesis
    using 2 3 assms seq_comp_electing smc_sound
    unfolding Defer_One_Loop_Composition.iter.simps
              smc.simps elector.simps electing_def
    by metis
qed

subsection \<open>(Weak) Monotonicity Property\<close>

text \<open>
  The following proof is a fully modular proof for weak monotonicity of
  sequential majority comparison. It is composed of many small steps.
\<close>

theorem smc_monotone:
  fixes x :: "'a Preference_Relation"
  assumes "linear_order x"
  shows "monotonicity (smc x)"
proof -
  let ?pass2 = "pass_module 2 x"
  let ?tie_breaker = "pass_module 1 x"
  let ?plurality_defer = "(plurality_rule\<down>) \<triangleright> ?tie_breaker"
  let ?compare_two = "?pass2 \<triangleright> ?plurality_defer"
  let ?drop2 = "drop_module 2 x"
  let ?eliminator = "?compare_two \<parallel>\<^sub>\<up> ?drop2"
  let ?loop =
    "let t = defer_equal_condition 1 in (?eliminator \<circlearrowleft>\<^sub>t)"

  have 00010: "defer_invariant_monotonicity (plurality_rule\<down>)"
    by simp (* rev_comp_def_inv_mono plurality_strict_strong_mono *)
  have 00011: "non_electing (plurality_rule\<down>)"
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
  have 20000: "non_blocking (plurality_rule\<down>)"
    by simp (* rev_comp_non_blocking plurality_electing *)
  have 0000: "defer_lift_invariance ?pass2"
    using assms
    by simp (* pass_mod_dl_inv *)
  have 0001: "defer_lift_invariance ?plurality_defer"
    using 00010 00012 00013 00014 def_inv_mono_imp_def_lift_inv
    unfolding pass_module.simps only_voters_vote_def
    by blast (* def_inv_mono_imp_def_lift_inv *)
  have 0020: "disjoint_compatibility ?pass2 ?drop2"
    using assms
    by simp (* disj_compat_comm drop_pass_disj_compat *)
  have 1000: "non_electing ?pass2"
    using assms
    by simp (* pass_mod_non_electing *)
  have 1001: "non_electing ?plurality_defer"
    using 00011 00012 seq_comp_presv_non_electing
    by blast (* seq_comp_presv_non_electing *)
  have 2000: "non_blocking ?pass2"
    using assms
    by simp (* pass_mod_non_blocking *)
  have 2001: "defers 1 ?plurality_defer"
    using 20000 00011 00013 seq_comp_def_one
    by blast
  have 000: "defer_lift_invariance ?compare_two"
    using 0000 0001 seq_comp_presv_def_lift_inv 
          plurality_rule_only_voters pass_mod_only_voters
          rev_comp_only_voters seq_comp_only_voters
    by blast
  have 001: "defer_lift_invariance ?drop2"
    using assms
    by simp
  have 002: "disjoint_compatibility ?compare_two ?drop2"
    using assms 0020 disj_compat_seq pass_mod_sound pass_mod_only_voters
          plurality_rule_sound rev_comp_sound seq_comp_sound
          plurality_rule_only_voters pass_mod_only_voters
          rev_comp_only_voters seq_comp_only_voters
    by metis
  have 100: "non_electing ?compare_two"
    using 1000 1001 seq_comp_presv_non_electing
    by simp
  have 101: "non_electing ?drop2"
    using assms
    by simp
  have 102: "agg_conservative max_aggregator"
    by simp
  have 200: "defers 1 ?compare_two"
    using 2000 1000 2001 seq_comp_def_one
    by simp
  have 201: "rejects 2 ?drop2"
    using assms
    by simp
  have 00: "defer_lift_invariance ?eliminator"
    using 000 001 002 par_comp_def_lift_inv
    by blast
  have 10: "non_electing ?eliminator"
    using 100 101 conserv_max_agg_presv_non_electing
    by blast
  have 20: "eliminates 1 ?eliminator"
    using 200 100 201 002 par_comp_elim_one
    by simp
  have 0: "defer_lift_invariance ?loop"
    using 00 loop_comp_presv_def_lift_inv
          plurality_rule_only_voters pass_mod_only_voters drop_mod_only_voters
          rev_comp_only_voters seq_comp_only_voters max_par_comp_only_voters
    by metis
  have 1: "non_electing ?loop"
    using 10 loop_comp_presv_non_electing
    by simp
  have 2: "defers 1 ?loop"
    using 10 20 iter_elim_def_n prod.exhaust_sel zero_less_one defer_equal_condition.simps
    by metis
  have 3: "electing elect_module"
    by simp
  show ?thesis
    using 0 1 2 3 assms seq_comp_mono
    unfolding Electoral_Module.monotonicity_def elector.simps
              Defer_One_Loop_Composition.iter.simps
              smc_sound smc.simps
    by (metis (full_types))
qed

end
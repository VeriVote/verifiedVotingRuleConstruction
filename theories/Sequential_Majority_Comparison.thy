(*  File:       Sequential_Majority_Comparison.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Sequential Majority Comparison\<close>

theory Sequential_Majority_Comparison
  imports Pass_Module Revision_Composition Plurality_Module Drop_Module
          Maximum_Parallel_Composition Defer_One_Loop_Composition Elect_Module
          Drop_And_Pass_Compatibility
begin

text
\<open>Sequential majority comparison compares two alternatives by plurality voting.
The loser gets rejected, and the winner is compared to the next alternative.
This process is repeated until only a single alternative is left, which is
then elected.\<close>

subsection \<open>Definition\<close>

fun smc :: "'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "smc x A p =
        ((let a = max_aggregator; t = defer_equal_condition 1 in
    ((((pass_module 2 x) \<triangleright> ((plurality\<down>) \<triangleright> (pass_module 1 x))) \<parallel>\<^sub>a
      (drop_module 2 x)) \<circlearrowleft>\<^sub>t) \<triangleright> elect_module) A p)"

subsection \<open>Soundness\<close>

(*
   As all base components are electoral modules (, aggregators, or termination
   conditions), and all used compositional structures create electoral modules,
   sequential majority comparison unsurprisingly is an electoral module.
*)
theorem smc_sound:
  assumes order: "linear_order x"
  shows "electoral_module (smc x)"
  using smc.simps drop_mod_sound elect_mod_sound
        electoral_module_def loop_comp_sound
        max_agg_sound order par_comp_sound
        pass_mod_sound plurality_sound rev_comp_sound
        seq_comp_sound
  by metis

subsection \<open>Electing Property\<close>

(*
   The sequential majority comparison electoral module is electing.
   This property is needed to convert electoral modules to a social choice
   function. Apart from the very last proof step, it is a part of the
   monotonicity proof below.
*)
theorem smc_electing:
  assumes order: "linear_order x"
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
    using order
    by simp
  have 00013: "defers 1 ?tie_breaker"
    using order pass_one_mod_def_one
    by simp
  have 20000: "non_blocking (plurality\<down>)"
    by simp

  have 0020: "disjoint_compatibility ?pass2 ?drop2"
    using order
    by simp (*disj_compat_comm*)
  have 1000: "non_electing ?pass2"
    using order
    by simp
  have 1001: "non_electing ?plurality_defer"
    using 00011 00012
    by simp
  have 2000: "non_blocking ?pass2"
    using order
    by simp
  have 2001: "defers 1 ?plurality_defer"
    using 20000 00011 00013 seq_comp_def_one
    by blast

  have 002: "disjoint_compatibility ?compare_two ?drop2"
    using order 0020
    by simp
  have 100: "non_electing ?compare_two"
    using 1000 1001
    by simp
  have 101: "non_electing ?drop2"
    using order
    by simp
  have 102: "agg_conservative max_aggregator"
    by simp
  have 200: "defers 1 ?compare_two"
    using 2000 1000 2001 seq_comp_def_one
    by auto
  have 201: "rejects 2 ?drop2"
    using order
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
    using 2 3 smc_sound smc.simps electing_def
          maximum_parallel_composition.simps
          order seq_comp_electing
    by metis
qed

subsection \<open>(Weak) Monotonicity Property\<close>

(*
   The following proof is a fully modular proof for weak monotonicity of
   sequential majority comparison. It is composed of many small steps.
*)
theorem smc_monotone:
  assumes order: "linear_order x"
  shows "monotonicity (smc x)"
proof -
(*Some aliases for parts of the SMC module.*)
  let ?pass2 = "pass_module 2 x"
  let ?tie_breaker = "(pass_module 1 x)"
  let ?plurality_defer = "(plurality\<down>) \<triangleright> ?tie_breaker"
  let ?compare_two = "?pass2 \<triangleright> ?plurality_defer"
  let ?drop2 = "drop_module 2 x"
  let ?eliminator = "?compare_two \<parallel>\<^sub>\<up> ?drop2"
  let ?loop =
    "let t = defer_equal_condition 1 in (?eliminator \<circlearrowleft>\<^sub>t)"

  have 00010: "defer_invariant_monotonicity (plurality\<down>)"
    by simp (*rev_comp_def_inv_mono plurality_strict_strong_mono*)
  have 00011: "non_electing (plurality\<down>)"
    by simp (*rev_comp_non_electing plurality_sound*)
  have 00012: "non_electing ?tie_breaker"
    using order
    by simp (*pass_mod_non_electing*)
  have 00013: "defers 1 ?tie_breaker"
    using order pass_one_mod_def_one
    by simp
  have 00014: "defer_monotonicity ?tie_breaker"
    using order
    by simp (*dl_inv_imp_def_mono pass_mod_dl_inv*)
  have 20000: "non_blocking (plurality\<down>)"
    by simp (*rev_comp_non_blocking plurality_electing*)

  have 0000: "defer_lift_invariance ?pass2"
    using order
    by simp (*pass_mod_dl_inv*)
  have 0001: "defer_lift_invariance ?plurality_defer"
    using 00010 00011 00012 00013 00014
    by simp (*def_inv_mono_imp_def_lift_inv*)
  have 0020: "disjoint_compatibility ?pass2 ?drop2"
    using order
    by simp (*disj_compat_comm drop_pass_disj_compat*)
  have 1000: "non_electing ?pass2"
    using order
    by simp (*pass_mod_non_electing*)
  have 1001: "non_electing ?plurality_defer"
    using 00011 00012
    by simp (*seq_comp_presv_non_electing*)
  have 2000: "non_blocking ?pass2"
    using order
    by simp (*pass_mod_non_blocking*)
  have 2001: "defers 1 ?plurality_defer"
    using 20000 00011 00013 seq_comp_def_one
    by blast

  have 000: "defer_lift_invariance ?compare_two"
    using 0000 0001
    by simp (*seq_comp_presv_def_lift_inv*)
  have 001: "defer_lift_invariance ?drop2"
    using order
    by simp (* drop_mod_def_lift_inv *)
  have 002: "disjoint_compatibility ?compare_two ?drop2"
    using order 0020
    by simp
      (*disj_compat_seq seq_comp_sound rev_comp_sound
        plurality_sound pass_mod_sound*)
  have 100: "non_electing ?compare_two"
    using 1000 1001
    by simp (*seq_comp_presv_non_electing*)
  have 101: "non_electing ?drop2"
    using order
    by simp (*drop_mod_non_electing*)
  have 102: "agg_conservative max_aggregator"
    by simp (*max_agg_conserv*)
  have 200: "defers 1 ?compare_two"
    using 2000 1000 2001 seq_comp_def_one
    by auto
  have 201: "rejects 2 ?drop2"
    using order
    by simp (*drop_two_mod_rej_two*)

  have 00: "defer_lift_invariance ?eliminator"
    using 000 001 002 par_comp_def_lift_inv
    by simp (*par_comp_def_lift_inv*)
  have 10: "non_electing ?eliminator"
    using 100 101 102
    by simp (*conserv_agg_presv_non_electing*)
  have 20: "eliminates 1 ?eliminator"
    using 200 100 201 002 par_comp_elim_one
    by simp

  have 0: "defer_lift_invariance ?loop"
    using 00
    by simp (*loop_comp_presv_def_lift_inv*)
  have 1: "non_electing ?loop"
    using 10
    by simp (*loop_comp_presv_non_electing*)
  have 2: "defers 1 ?loop"
    using 10 20
    by simp (*iter_elim_def_n*)
  have 3: "electing elect_module"
    by simp (*elect_mod_electing*)

  show ?thesis
    using 0 1 2 3
          Electoral_Module.monotonicity_def
          maximum_parallel_composition.simps
          smc_sound smc.simps assms
          seq_comp_mono
    by (smt (verit, del_insts))
qed

end

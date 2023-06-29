(*  File:       Blacks_Rule.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Black's Rule\<close>

theory Blacks_Rule
  imports Pairwise_Majority_Rule
          Borda_Rule
begin

text \<open>
  This is Black's voting rule. It is composed of a function that determines
  the Condorcet winner, i.e., the Pairwise Majority rule, and the Borda rule.
  Whenever there exists no Condorcet winner, it elects the choice made by the
  Borda rule, otherwise the Condorcet winner is elected.
\<close>

subsection \<open>Definition\<close>

declare seq_comp_alt_eq[simp]

fun blacks_rule :: "'a Electoral_Module" where
    "blacks_rule A p = elector (condorcet \<triangleright> borda) A p"

fun blacks_rule' :: "'a Electoral_Module" where
  "blacks_rule' A p = sequential_composition' 
  condorcet (sequential_composition' borda elect_module)  A p"

theorem elector_seqcomp:
  fixes a b :: "'a Electoral_Module"
  shows "(a \<triangleright> (elector b)) = (elector (a \<triangleright> b))"
  unfolding elector.simps elect_module.simps sequential_composition.simps
  by (clarsimp, metis (no_types, opaque_lifting) boolean_algebra_cancel.sup2 
      fst_eqD snd_eqD sup_commute)

lemma blackdef_eq:
  shows "blacks_rule' = blacks_rule"
  unfolding blacks_rule'.simps blacks_rule.simps seq_comp_alt_eq[symmetric] elector.simps[symmetric]
  using elector_seqcomp[of condorcet borda] .

declare seq_comp_alt_eq[simp del]

subsection \<open>Soundness\<close>

theorem blacks_rule_sound: "electoral_module blacks_rule"
  unfolding blacks_rule.simps
  using elector_sound seq_comp_sound condorcet_sound borda_sound
  by metis

subsection \<open>Condorcet Consistency Property\<close>

theorem black_condorcet: "condorcet_consistency blacks_rule"
proof (unfold blackdef_eq[symmetric] blacks_rule'.simps seq_comp_alt_eq[symmetric] elector.simps[symmetric])
  have emin: "electoral_module (elector borda)"
    unfolding borda_rule.simps[symmetric]
    using borda_rule_sound .
  have nbb: "non_blocking borda" unfolding non_blocking_def  
   using borda_sound by (auto) 
  have electingeb: "electing (elector borda)"
    using elector_electing[OF borda_sound nbb] .
  have nec: "non_electing condorcet" unfolding non_electing_def by (auto simp add: condorcet_sound)
  have comp_sound: "electoral_module (condorcet \<triangleright> elector borda)" 
     using condorcet_sound emin seq_comp_sound by blast
  show "condorcet_consistency (condorcet \<triangleright> elector borda)"
    unfolding condorcet_consistency3 condorcet_consistency_def
    using comp_sound
  proof (safe, blast)   
    fix A :: "'alt set"
    fix p :: "'alt Profile"
    fix w :: 'alt
    assume condw: "condorcet_winner A p w"     
    from this have dw: "defer condorcet A p = {w}"
    unfolding  condorcet_winner.simps
    by (metis (no_types, lifting) condw cond_winner_unique_3 condorcet_is_dcc 
          defer_condorcet_consistency_def snd_conv)
    then have cc1: "card (defer condorcet A p) = 1" by simp
    from condw have fprof: "finite_profile A p" by simp
     have electcondw: "elect (condorcet \<triangleright> elector borda) A p =
        (defer condorcet A p)"
    using seq_comp_def_then_elect2[OF nec cc1 electingeb fprof] .
  from electcondw dw have electcbw: "elect (condorcet \<triangleright> elector borda) A p = {w}"
    by blast
  have non_def: "defer (condorcet \<triangleright> elector borda) A p = {}" 
    by (auto simp del: condorcet.simps borda.simps, metis equals0D sndI)
  have rejrest: "reject (condorcet \<triangleright> elector borda) A p = A - {w}"
    unfolding electoral_module_def
  proof (auto simp del: condorcet.simps borda.simps sequential_composition.simps)
    fix x
    show "x \<in> reject (condorcet \<triangleright> (borda \<triangleright> elect_module)) A p \<Longrightarrow> x \<in> A"
      using fprof by (metis Diff_iff comp_sound elector.simps reject_not_elec_or_def)
  next
    assume w_rej: "w \<in> reject (condorcet \<triangleright> (borda \<triangleright> elect_module)) A p"
    have "(w \<notin> reject (condorcet \<triangleright> (borda \<triangleright> elect_module)) A p)"
    using fprof by (metis comp_sound dw electcondw elector.elims insert_disjoint(1) result_disj)
    with w_rej show "False"
      by blast 
  next
    fix x
    assume "x \<in> A"
    and    "x \<notin> reject (condorcet \<triangleright> (borda \<triangleright> elect_module)) A p"
    thus "x = w" using fprof
      by (metis comp_sound dw electcondw elector.simps electoral_mod_defer_elem 
          empty_iff insert_iff non_def)
  qed
  from electcbw non_def rejrest
  show "(condorcet \<triangleright> elector borda) A p = ({w}, A - {w}, {})"
    by (metis combine_ele_rej_def)
  qed
qed

           
end

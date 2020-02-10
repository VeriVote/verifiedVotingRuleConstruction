theory sequential_composition
imports electoral_modules

begin

(******************************************)
(*** Definition: Sequential Composition ***)
(******************************************)

(* The sequential composition creates a new electoral module out of two electoral modules. In a
   sequential composition the second electoral module makes decisions over alternatives deferred by
   the first electoral module.
*)
fun seq_comp :: "'a Electoral_module \<Rightarrow> 'a Electoral_module \<Rightarrow> 'a Electoral_module" where
  "seq_comp m n A p = (let new_A = defer m A p; new_p = limit_profile_to new_A p in (
    (elect m A p) \<union> (elect n new_A new_p),
    (reject m A p) \<union> (reject n new_A new_p),
    defer n new_A new_p))"
abbreviation sequence :: "'a Electoral_module \<Rightarrow> 'a Electoral_module \<Rightarrow> 'a Electoral_module"
    (infix "\<triangleright>" 50) where
  "m \<triangleright> n == seq_comp m n"

lemma seq_n_input_sound:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "let new_A = defer m A p in finite_profile new_A (limit_profile_to new_A p)"
  by (meson defer_from_input infinite_super limit_profile_consistent module profile)

lemma seq_out_disjoint:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          profile:  "finite_profile A p"
  shows "disjoint3 ((m \<triangleright> n) A p)"
proof -
  let ?new_A = "defer m A p"
  let ?new_p = "limit_profile_to ?new_A p"
  from module_m profile have disjoint_m: "disjoint3 (m A p)"
    by (meson electoral_module_def partition_of_def)
  from module_m module_n seq_n_input_sound profile have disjoint_n: "(disjoint3 (n ?new_A ?new_p))"
    by (metis electoral_module_def partition_of_def)
  from this disjoint_m module_m module_n profile
  have 0: "(elect m A p \<inter> reject n ?new_A ?new_p) = {}"
    by (smt disjoint_iff_not_equal reject_from_input seq_n_input_sound split_disjoint3 subset_eq)
  from disjoint_m disjoint_n seq_n_input_sound profile module_m module_n
  have 1: "(elect m A p \<inter> defer n ?new_A ?new_p) = {}"
    by (smt defer_from_input disjoint_iff_not_equal rev_subsetD split_disjoint3)
  from disjoint_m disjoint_n seq_n_input_sound profile module_m module_n
  have 2: "(reject m A p \<inter> reject n ?new_A ?new_p) = {}"
    by (smt disjoint_iff_not_equal reject_from_input set_rev_mp split_disjoint3)
  from disjoint_m disjoint_n seq_n_input_sound profile module_m module_n
  have 3: "(reject m A p \<inter> elect n ?new_A ?new_p) = {}"
    by (smt disjoint_iff_not_equal elect_from_input set_rev_mp split_disjoint3)
  from 0 1 2 3 disjoint_m disjoint_n module_m module_n profile
  have "(elect m A p \<union> elect n ?new_A ?new_p) \<inter> (reject m A p \<union> reject n ?new_A ?new_p) = {}"
    by (smt inf_sup_aci(1) inf_sup_distrib2 seq_n_input_sound split_disjoint3 sup_inf_absorb
        sup_inf_distrib1)
  moreover from 0 1 2 3 disjoint_n module_m module_n profile
  have "(elect m A p \<union> elect n ?new_A ?new_p) \<inter> (defer n ?new_A ?new_p) = {}"
    by (metis Int_Un_distrib2 Un_empty seq_n_input_sound split_disjoint3)
  moreover from 0 1 2 3 profile disjoint_m disjoint_n module_m module_n
  have "(reject m A p \<union> reject n ?new_A ?new_p) \<inter> (defer n ?new_A ?new_p) = {}"
    by (smt Int_Un_distrib2 defer_from_input distrib_imp2 seq_n_input_sound split_disjoint3
        subset_Un_eq sup_inf_distrib1)
  ultimately have "disjoint3 (elect m A p \<union> elect n ?new_A ?new_p,
                              reject m A p \<union> reject n ?new_A ?new_p,
                              defer n ?new_A ?new_p)"
    by (simp)
  thus ?thesis
    by (metis seq_comp.simps)
qed

lemma seq_output_unify_to_input:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          profile:  "finite_profile A p"
  shows "unify_to A ((m \<triangleright> n) A p)"
proof -
  let ?new_A = "defer m A p"
  let ?new_p = "limit_profile_to ?new_A p"
  from module_m profile have "unify_to A (m A p)"
    by (simp add: electoral_module_def partition_of_def)
  from this module_m profile have 0: "elect m A p \<union> reject m A p \<union> ?new_A = A"
    by (simp add: split_unify_result)
  from module_n seq_n_input_sound profile module_m
  have "unify_to ?new_A (n ?new_A ?new_p)"
    by (metis electoral_module_def partition_of_def)
  from this module_m module_n profile
  have 1: "elect n ?new_A ?new_p \<union> reject n ?new_A ?new_p \<union> defer n ?new_A ?new_p = ?new_A"
    by (meson seq_n_input_sound split_unify_result)
  from 0 1 have "(elect m A p \<union> elect n ?new_A ?new_p) \<union>
                 (reject m A p \<union> reject n ?new_A ?new_p) \<union>
                 defer n ?new_A ?new_p = A"
    by blast
  hence "unify_to A (elect m A p \<union> elect n ?new_A ?new_p,
                     reject m A p \<union> reject n ?new_A ?new_p,
                     defer n ?new_A ?new_p)"
    by simp
  thus ?thesis
    by (metis seq_comp.simps)
qed

(* A sequential compositions of 2 electoral modules creates an electoral module. *)
theorem seq_creates_modules[simp]:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n"
  shows "electoral_module (m \<triangleright> n)"
proof -
  have "\<forall>A p. partition_of (A::'a set) p = (disjoint3 p \<and> unify_to A p)"
    by (metis partition_of_def)
  then show ?thesis
    by (meson electoral_module_intro module_m module_n seq_out_disjoint seq_output_unify_to_input)
qed

(*****************************************)
(*** Lemmas for Sequential Composition ***)
(*****************************************)

lemma limit_profile_size_preserved:
  assumes profile: "finite_profile S p" and
          subset:  "A \<subseteq> S"
  shows "size p = size (limit_profile_to A p)"
  by simp

lemma trivial_seq1:
  assumes module_m:    "electoral_module m" and
          module_n:    "electoral_module n" and
          profile:     "finite_profile A p" and
          empty_defer: "defer m A p = {}"
  shows "(m \<triangleright> n) A p =  m A p"
  by (smt Int_lower1 Un_absorb2 bot.extremum_uniqueI defer_from_input elect_from_input empty_defer
      module_m module_n prod.collapse profile reject_from_input seq_comp.simps seq_n_input_sound
      split_disjoint3)

lemma elect_only_alternative:
  assumes one_alt:  "card A = 1" and
          electing: "electing m" and
          profile:  "finite_profile A p"
  shows "elect m A p = A"
  by (smt Int_empty_right Int_insert_right card_1_singletonE elect_from_input electing
      electing_def inf.orderE one_alt profile)

lemma elect_only_defered:
  assumes n_electing_m: "non_electing m" and
          def_one_m:    "defers 1 m" and
          electing_n:   "electing n" and
          profile:      "finite_profile A p"
  shows "elect (m \<triangleright> n) A p = defer m A p"
proof cases
  assume "A = {}"
  from this electing_n n_electing_m profile show ?thesis
    by (metis bot.extremum_uniqueI defer_from_input elect_from_input electing_def non_electing_def
        seq_creates_modules)
next
  assume assm: "A \<noteq> {}"
  from n_electing_m profile have ele: "elect m A p = {}"
    using non_electing_def by auto
  from assm def_one_m profile finite have def_card: "card (defer m A p) = 1"
    by (simp add: Suc_leI card_gt_0_iff defers_def)
  from this n_electing_m profile have def: "\<exists>a \<in> A. defer m A p = {a}"
    by (metis card_1_singletonE defer_from_input non_electing_def singletonI subsetCE)
  from ele def n_electing_m have rej: "\<exists>a \<in> A. reject m A p = A-{a}"
    by (metis Diff_empty def_one_m defers_def profile reject_alternative_representation)
  from ele rej def n_electing_m profile have res_m: "\<exists>a \<in> A. m A p = ({}, A-{a}, {a})"
    by (metis Diff_empty combine_ele_rej_def non_electing_def reject_alternative_representation)
  hence "\<exists>a \<in> A. elect (m \<triangleright> n) A p = elect n {a} (limit_profile_to {a} p)"
    by (metis prod.sel(1) prod.sel(2) seq_comp.simps sup_bot.left_neutral)
  from this def_card def electing_n n_electing_m profile have "\<exists>a \<in> A. elect (m \<triangleright> n) A p = {a}"
    by (smt elect_only_alternative non_electing_def prod.sel(1) seq_comp.simps seq_n_input_sound
        sup_bot.left_neutral)
  from this def def_card electing_n n_electing_m profile res_m show ?thesis
    by (smt Diff_disjoint Diff_insert_absorb Int_insert_right Un_Diff_Int elect_only_alternative
        empty_iff non_electing_def prod.sel(1) seq_comp.simps seq_n_input_sound singletonI profile)
qed

lemma seq_comp_does_not_grow_deferred_set:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          profile: "finite_profile A p"
  shows "card (defer (m \<triangleright> n) A p) \<le> card (defer m A p)"
  by (metis card_mono defer_from_input module_m module_n profile seq_comp.simps seq_n_input_sound
      snd_conv)

lemma seq_comp_does_not_grow_deferred_set2:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          profile: "finite_profile A p"
  shows "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
  by (metis defer_from_input module_m module_n prod.sel(2) profile seq_comp.simps seq_n_input_sound)

lemma seq_comp_defer_set_passing:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          profile: "finite_profile A p"
  shows "defer (m \<triangleright> n) A p = defer n (defer m A p) (limit_profile_to (defer m A p) p)"
  by (metis seq_comp.simps snd_conv)

lemma seq_comp_elect_set_passing:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          profile: "finite_profile A p"
        shows "elect (m \<triangleright> n) A p = elect n (defer m A p) (limit_profile_to (defer m A p) p) \<union> (elect m A p)"
  by (metis Un_commute fst_conv seq_comp.simps)

lemma seq_comp_defer_set_single_elimination_reject:
  assumes module_m: "electoral_module m" and
          module_n: "eliminates 1 n" and
          profile: "finite_profile A p" and
          enough_leftover: "card (defer m A p) > 1"
  shows "defer (m \<triangleright> n) A p \<subset> defer m A p"
  by (metis enough_leftover module_m module_n profile seq_comp.simps seq_n_input_sound
      single_elimination_reduces_defer_set_2 snd_conv)

lemma deferred_alt_always_deferred:
  assumes "electoral_module m" and
          "electoral_module n" and
          "finite_profile A p"
        shows "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
proof -
  have "\<forall>A p. finite_profile A p \<longrightarrow> partition_of A (n A p)"
    using assms(2) electoral_module_def by auto
  hence "finite_profile (defer m A p) (limit_profile_to (defer m A p) p) \<longrightarrow> partition_of (defer m A p) (n (defer m A p) (limit_profile_to (defer m A p) p))"
    by simp
  hence "partition_of (defer m A p) (n (defer m A p) (limit_profile_to (defer m A p) p))"
    by (meson assms(1) assms(3) seq_n_input_sound)
  thus ?thesis
    using assms(1) assms(2) assms(3) seq_comp_does_not_grow_deferred_set2 by blast
qed

lemma defer_and_elect_equal_impl_result_equal:
  assumes "electoral_module m" and
          "electoral_module n" and
          "finite_profile A p" and
          "finite_profile A q" and
          "elect m A p = elect n A q" and
          "defer m A p = defer n A q"
        shows "m A p = n A q"
proof -
  have "unify_to A ((elect m A p),(reject m A p),(defer m A p))"
    by (metis (mono_tags, lifting) assms(1) assms(3) split_unify_result unify_to.simps)
  moreover have "disjoint3 ((elect m A p),(reject m A p),(defer m A p))"
    by (metis assms(1) assms(3) electoral_module_def partition_of_def prod.collapse)
  ultimately have reject_p: "reject m A p = A - ((elect m A p) \<union> (defer m A p))"
    by (metis assms(1) assms(3) combine_ele_rej_def electoral_module_def partition_reject)
  have "unify_to A ((elect n A q),(reject n A q),(defer n A q))"
    by (metis (mono_tags, lifting) assms(2) assms(4) split_unify_result unify_to.simps)
  moreover have "disjoint3 ((elect n A q),(reject n A q),(defer n A q))"
    by (metis assms(2) assms(4) electoral_module_def partition_of_def prod.collapse)
  ultimately have reject_q: "reject n A q = A - ((elect n A q) \<union> (defer n A q))"
    by (metis assms(2) assms(4) combine_ele_rej_def electoral_module_def partition_reject)
  from reject_p reject_q show ?thesis
    by (simp add: assms(5) assms(6) prod_eqI)
qed

lemma seq_defer_in_both_defer:
  assumes "a \<in> (defer (m \<triangleright> n) A p)" and
          "electoral_module m \<and> electoral_module n" and
          "finite_profile A p"
  shows "a \<in> defer n (defer m A p) (limit_profile_to (defer m A p) p) \<and> a \<in> defer m A p"
  by (metis (no_types, lifting) assms seq_comp_defer_set_passing
      seq_comp_does_not_grow_deferred_set2 subsetCE)

(****************************************************)
(*** Composition Rules for Sequential Composition ***)
(****************************************************)

(* Composing two non blocking electoral modules in sequence results in a non blocking electoral
   module.
*)
theorem seq_comp_preserves_non_blocking[simp]:
  assumes non_blocking_m: "non_blocking m" and
          non_blocking_n: "non_blocking n"
  shows "non_blocking (m \<triangleright> n)"
proof -
  fix A p
  let ?input_sound = "((A::'a set) \<noteq> {} \<and> finite_profile A p)"
  from non_blocking_m have "?input_sound \<longrightarrow> reject m A p \<noteq> A"
    by (simp add: non_blocking_def)
  from this non_blocking_m have 0: "?input_sound \<longrightarrow> A - reject m A p \<noteq> {}"
    by (meson Diff_eq_empty_iff non_blocking_def reject_from_input subset_antisym)
  from non_blocking_m have "?input_sound \<longrightarrow> partition_of A (m A p)"
    by (simp add: electoral_module_def non_blocking_def)
  hence "?input_sound \<longrightarrow> elect m A p \<union> defer m A p = A - reject m A p "
    by (smt Diff_partition Diff_triv Un_Diff defer_alternative_representation elect_from_input
        non_blocking_def non_blocking_m split_disjoint3)
  from this 0 have "?input_sound \<longrightarrow> elect m A p \<union> defer m A p \<noteq> {}"
    by auto
  hence "?input_sound \<longrightarrow> (elect m A p \<noteq> {} \<or> defer m A p \<noteq> {})"
    by simp
  from this non_blocking_m non_blocking_n show ?thesis
    by (smt Diff_empty Diff_subset_conv Un_empty defer_alternative_representation elect_from_input
        fst_conv inf.absorb1 non_blocking_def reject_from_input seq_comp.simps seq_creates_modules
        seq_n_input_sound snd_conv split_disjoint3 subset_antisym sup_bot_right)
qed

(* Composing a defer lift invariant and non electing electoral module, that defers exactly one
   alternative, in sequence with an electing electoral module results in a monotone electoral
   module.
*)
theorem monotone_sequence[simp]:
  assumes def_monotone_m: "defer_lift_invariant m" and
          non_ele_m:      "non_electing m" and
          def_one_m:      "defers 1 m" and
          electing_n:     "electing n"
  shows "monotone (m \<triangleright> n)"
proof -
  have "\<forall>A p q w. (finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect (m \<triangleright> n) A q"
  proof fix A
  show "\<forall>p q w. (finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect (m \<triangleright> n) A q"
  proof fix p
  show "\<forall>q w. (finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect (m \<triangleright> n) A q"
  proof fix q
  show "\<forall>w. (finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect (m \<triangleright> n) A q"
  proof fix w show "(finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect (m \<triangleright> n) A q"
  proof assume a: "finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w"
    hence profiles: "finite_profile A p \<and> finite_profile A q"
      by (metis (no_types) lifted_def)
    from this a def_monotone_m non_ele_m def_one_m electing_n show "w \<in> elect (m \<triangleright> n) A q"
      by (metis elect_only_defered defer_lift_invariant_def)
  qed qed qed qed qed
  thus ?thesis
    by (metis (no_types, lifting) electing_def electing_n electoral_modules.monotone_def non_ele_m
        non_electing_def seq_creates_modules)
qed

lemma lift_invariant_seq_help:
  assumes monotone_m: "defer_lift_invariant m" and
          monotone_n: "defer_lift_invariant n" and
          input_ok:   "a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a"
  shows "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
proof -
  let ?new_Ap = "defer m A p"
  let ?new_Aq = "defer m A q"
  let ?new_p = "limit_profile_to ?new_Ap p"
  let ?new_q = "limit_profile_to ?new_Aq q"
  from monotone_m monotone_n have modules: "electoral_module m \<and> electoral_module n"
    by (simp add: defer_lift_invariant_def)
  hence "finite_profile A p \<longrightarrow> defer (m \<triangleright> n) A p \<subseteq> defer m A p"
    by (metis defer_from_input prod.sel(2) seq_comp.simps seq_n_input_sound)
  moreover have profile_p: "lifted A p q a \<longrightarrow> finite_profile A p"
    by (simp add: lifted_def)
  ultimately have defer_subset: "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
    using input_ok by blast
  hence mono_m: "m A p = m A q"
    by (meson monotone_m defer_lift_invariant_def subsetCE input_ok)
  hence new_A_eq: "?new_Ap = ?new_Aq"
    by presburger
  have defer_eq: "defer (m \<triangleright> n) A p = defer n ?new_Ap ?new_p"
    by (metis seq_comp.simps snd_conv)
  hence mono_n: "n ?new_Ap ?new_p = n ?new_Aq ?new_q"
  proof cases
    assume "lifted ?new_Ap ?new_p ?new_q a"
    thus ?thesis
      by (metis defer_eq mono_m monotone_n defer_lift_invariant_def input_ok)
  next
    assume a2: "\<not>lifted ?new_Ap ?new_p ?new_q a"
    from input_ok have "finite_profile A q"
      by (simp add: lifted_def)
    from this modules new_A_eq have 1: "finite_profile ?new_Ap ?new_q"
      by (metis (no_types) seq_n_input_sound)
    moreover from modules profile_p input_ok have 0: "finite_profile ?new_Ap ?new_p"
      by (metis (no_types) seq_n_input_sound)
    moreover from defer_subset input_ok have 2: "a \<in> ?new_Ap"
      by blast
    moreover from input_ok have eql_lengths: "size ?new_p = size ?new_q"
      by (simp add: lifted_def)
    ultimately have 0: "(\<forall>i::nat. i < size ?new_p \<longrightarrow>
                        \<not>linear_orders.lifted ?new_Ap (?new_p!i) (?new_q!i) a) \<or>
                     (\<exists>i::nat. i < size ?new_p \<and>
                        \<not>linear_orders.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<and>
                        (?new_p!i) \<noteq> (?new_q!i))"
      by (meson a2 lifted_def)
    from input_ok modules
    have "\<forall>i. (0 \<le> i \<and> i < size ?new_p) \<longrightarrow> (linear_orders.lifted A (p!i) (q!i) a \<or> (p!i) = (q!i))"
      by (metis defer_from_input electoral_modules.lifted_def limit_profile_size_preserved)
    from this input_ok modules mono_m have "\<forall>i. (0 \<le> i \<and> i < size ?new_p) \<longrightarrow>
             (linear_orders.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<or>
              (?new_p!i) = (?new_q!i))"
      by (metis (no_types, lifting) limit_lifted_interaction defer_from_input
          electoral_modules.lifted_def limit_profile_size_preserved limit_profile_to.simps nth_map)
    from this 0 eql_lengths mono_m show ?thesis
      by (metis leI not_less_zero nth_equalityI)
  qed
  from mono_m mono_n show ?thesis
    by (metis (full_types) seq_comp.simps)
qed

(* Composing two defer lift invariant electoral modules sequentially results in a defer lift
   invariant electoral module.
*)
theorem defer_lift_invariant_seq[simp]:
  assumes monotone_m: "defer_lift_invariant m" and
          monotone_n: "defer_lift_invariant n"
  shows "defer_lift_invariant (m \<triangleright> n)"
  by (metis (full_types) monotone_m monotone_n lift_invariant_seq_help seq_creates_modules
      defer_lift_invariant_def)

(* Composing two non electing electoral modules sequentially results in a non electing electoral
   module.
*)
theorem seq_comp_preserves_non_electing[simp]:
  assumes "non_electing m" and
          "non_electing n"
  shows "non_electing (m \<triangleright> n)"
  by (smt Un_empty assms(1) assms(2) non_electing_def prod.sel(1) seq_comp.simps seq_creates_modules
      seq_n_input_sound)

(* Composing a non blocking, non electing electoral module, in sequence with an electoral module,
   that defers exactly 1 alternative, results in an electoral module, that defers exactly 1
   alternative.
*)
theorem seq_comp_defers_1[simp]:
  assumes non_blocking_m: "non_blocking m" and
          non_electing_m: "non_electing m" and
          def_1_n: "defers 1 n"
        shows "defers 1 (m \<triangleright> n)"
proof -
  have "\<forall>A p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow> card (defer (m \<triangleright> n) A p) = 1"
  proof fix A show "\<forall> p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow> card (defer (m \<triangleright> n) A p) = 1"
  proof fix p show "(card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow> card (defer (m \<triangleright> n) A p) = 1"
  proof assume input_fine: "(card A \<ge> 1 \<and> finite_profile A p)"
    hence "A \<noteq> {}"
      by auto
    moreover from input_fine have finite_profile: "finite_profile A p"
      by simp
    ultimately have "reject m A p \<noteq> A"
      by (meson non_blocking_m non_blocking_def)
    moreover have "elect m A p = {}" using non_electing_m
      using finite_profile non_electing_def by auto
    ultimately have "defer m A p \<noteq> {}"
    proof - (* generated proof*)
      have "\<exists>a. a \<in> A \<and> a \<notin> reject m A p"
        by (meson \<open>reject m A p \<noteq> A\<close> input_fine non_electing_def non_electing_m reject_from_input subset_antisym subset_iff)
      then show ?thesis
        by (metis (no_types) electoral_module_element_in_defer empty_iff input_fine non_electing_def non_electing_m)
    qed
    hence "card (defer m A p) \<ge> 1"
      by (metis One_nat_def Suc_leI card_gt_0_iff input_fine non_blocking_def non_blocking_m
          seq_n_input_sound)
    thus "card (defer (m \<triangleright> n) A p) = 1"
    proof - (*generated proof*)
      have f1: "(elect (m \<triangleright> n) A p, snd ((m \<triangleright> n) A p)) = (elect m A p \<union> elect n (defer m A p) (limit_profile_to (defer m A p) p), reject m A p \<union> reject n (defer m A p) (limit_profile_to (defer m A p) p), defer n (defer m A p) (limit_profile_to (defer m A p) p))"
        by (metis prod.collapse seq_comp.simps)
      have "\<forall>n f. defers n f = (electoral_module f \<and> (\<forall>A rs. (\<not> n \<le> card (A::'a set) \<or> infinite A \<or> \<not> profile_on A rs) \<or> card (defer f A rs) = n))"
        using defers_def by blast
      then have "card (defer n (defer m A p) (limit_profile_to (defer m A p) p)) = 1"
        by (meson \<open>1 \<le> card (defer m A p)\<close> assms(3) finite_profile non_blocking_def non_blocking_m seq_n_input_sound)
      then show ?thesis
        using f1 by fastforce
    qed
  qed qed qed
  thus ?thesis
    by (metis def_1_n defers_def non_electing_def non_electing_m seq_creates_modules)
qed

(* Sequentially adding electoral modules to compatible electoral modules does not break their
   compatibility.
*)
theorem disjoint_compatible_seq[simp]:
  assumes compatible: "disjoint_compatible m n" and
          module_m2:  "electoral_module m2"
  shows "disjoint_compatible (m \<triangleright> m2) n"
proof -
  have modules: "electoral_module (m \<triangleright> m2) \<and> electoral_module n"
    by (metis compatible disjoint_compatible_def module_m2 seq_creates_modules)
  moreover have "\<forall>S. finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. independent_of (m \<triangleright> m2) S a \<and>
               (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
      (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)))"
  proof fix S show "finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. independent_of (m \<triangleright> m2) S a \<and>
               (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
      (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)))"
  proof assume fin: "finite S"
    obtain A where A: "A \<subseteq> S \<and>
        (\<forall>a \<in> A. independent_of m S a \<and>
                 (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
        (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
      by (metis (no_types, lifting) compatible disjoint_compatible_def fin)
    show "\<exists>A. A \<subseteq> S \<and>
        (\<forall>a \<in> A. independent_of (m \<triangleright> m2) S a \<and>
                 (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
        (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
    proof
      have "\<forall>a p q. a \<in> A \<and> only_change S p q a \<longrightarrow> (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
      proof fix a show "\<forall>p q. a \<in> A \<and> only_change S p q a \<longrightarrow> (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
      proof fix p show "\<forall>q. a \<in> A \<and> only_change S p q a \<longrightarrow> (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
      proof fix q show "a \<in> A \<and> only_change S p q a \<longrightarrow> (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
      proof assume a: "a \<in> A \<and> only_change S p q a"
        have eq_def: "defer m S p = defer m S q"
          by (metis A a independent_of_def)
        from a have profiles: "finite_profile S p \<and> finite_profile S q"
          using only_change_def by fastforce
        hence "(defer m S p) \<subseteq> S"
          using compatible defer_from_input disjoint_compatible_def by blast
        hence "limit_profile_to (defer m S p) p = limit_profile_to (defer m S q) q"
          by (metis (no_types, lifting) A DiffD2 a compatible defer_alternative_representation
              disjoint_compatible_def eq_def profiles remove_only_difference_profile)
        from this eq_def have "m2 (defer m S p) (limit_profile_to (defer m S p) p) =
                               m2 (defer m S q) (limit_profile_to (defer m S q) q)"
          by simp
        moreover have "m S p = m S q"
          by (meson A a independent_of_def)
        ultimately show "(m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
          by (metis (full_types) seq_comp.simps)
      qed qed qed qed
      moreover have "\<forall>a \<in> A. \<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p"
        by (metis A UnI1 prod.sel(1) prod.sel(2) seq_comp.simps)
      ultimately show "A \<subseteq> S \<and>
          (\<forall>a \<in> A. independent_of (m \<triangleright> m2) S a \<and>
                   (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
          (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
        by (metis (mono_tags, lifting) A independent_of_def modules)
    qed
  qed qed
  thus ?thesis
    by (simp add: disjoint_compatible_def modules)
qed

(* Composing a defer invariant monotone electoral module, in sequence with a non electing, defer
   motone electoral module, that defers exactly 1 alternative, results in a defer lift invariant
   electoral module.
*)
theorem defer_invariant_monotone_to_defer_lift_invariant[simp]:
  assumes strong_def_mon_m: "defer_invariant_monotone m" and
          non_electing_n:   "non_electing n" and
          defers_1:         "defers 1 n" and
          defer_monotone_n: "defer_monotone n"
        shows "defer_lift_invariant (m \<triangleright> n)"
proof -
  from strong_def_mon_m have non_electing_m: "non_electing m"
    by (simp add: defer_invariant_monotone_def)
  have electoral_module_m: "electoral_module m"
    using strong_def_mon_m defer_invariant_monotone_def by auto
  have electoral_module_n: "electoral_module n"
    using defers_1 defers_def by auto
  have "\<forall>A p q a. (a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow> (m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof fix A
  show "\<forall> p q a. (a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow> (m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof fix p show "\<forall> q a. (a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow> (m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof fix q show "\<forall> a. (a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow> (m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof fix a show "(a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow> (m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof cases
    assume "\<not> lifted A p q a"
    thus ?thesis
      by simp
  next
    assume "\<not>\<not> lifted A p q a"
    hence lifted: "lifted A p q a"
      by simp
    hence finite_profile_q: "finite_profile A q"
      by (simp add: electoral_modules.lifted_def lifted)
    from lifted have finite_profile_p: "finite_profile A p"
      by (simp add: electoral_modules.lifted_def)
    thus ?thesis
    proof cases
      assume " \<not>(a \<in> defer (m \<triangleright> n) A p \<and> electoral_modules.lifted A p q a)"
      thus ?thesis
        by blast
    next
      assume "\<not>\<not>(a \<in> defer (m \<triangleright> n) A p \<and> electoral_modules.lifted A p q a)"
      hence input_valid: "(a \<in> defer (m \<triangleright> n) A p \<and> electoral_modules.lifted A p q a)"
        by simp
      thus ?thesis
      proof cases
        assume not_unchanged: "\<not>(defer m A q = defer m A p)"
        hence a_single_defer: "{a} = defer m A q" using strong_def_mon_m
          by (metis electoral_module_n finite_profile_p input_valid seq_defer_in_both_defer
              defer_invariant_monotone_def)
        moreover have "(finite_profile A q \<and> {a} = defer m A q) \<longrightarrow> (defer (m \<triangleright> n) A q \<subseteq> {a})"
          using finite_profile_p electoral_module_m electoral_module_n deferred_alt_always_deferred
                non_electing_m by blast
        ultimately have "((a \<in> defer m A p) \<and> (lifted A p q a) \<and> finite_profile A q) \<longrightarrow>
                         defer (m \<triangleright> n) A q \<subseteq> {a}"
          by blast
        moreover have "(lifted A p q a) \<longrightarrow> finite_profile A q"
          using lifted_def by (simp add: electoral_modules.lifted_def)
        ultimately have "((a \<in> defer m A p) \<and> (lifted A p q a)) \<longrightarrow>
                         defer (m \<triangleright> n) A q \<subseteq> {a}" (*lifted defer subset of a*)
          by blast
        moreover have "((a \<in> defer m A p) \<and> (lifted A p q a)) \<longrightarrow> card (defer (m \<triangleright> n) A q) = 1"
          by (metis One_nat_def \<open>electoral_modules.lifted A p q a \<longrightarrow> finite_profile A q\<close>
              a_single_defer card_empty card_insert_disjoint defers_1 defers_def electoral_module_m
              empty_iff finite.emptyI le_numeral_extra(4) seq_comp_defer_set_passing
              seq_n_input_sound) (*lifted defer set size 1*)
        moreover have "a \<in> (defer (m \<triangleright> n) A p) \<longrightarrow> (a \<in> defer m A p)"
          using electoral_module_m electoral_module_n seq_comp_does_not_grow_deferred_set2
                finite_profile_p by blast
        ultimately have "(a \<in> (defer (m \<triangleright> n) A p) \<and> (lifted A p q a)) \<longrightarrow>
                         defer (m \<triangleright> n) A q = {a}" (*lifted defer set = a*)
          by (metis Collect_mem_eq card_1_singletonE empty_Collect_eq insertCI subset_singletonD)
        moreover have "(a \<in> (defer (m \<triangleright> n) A p) \<and> (lifted A p q a)) \<longrightarrow>
                       defer (m \<triangleright> n) A p = {a}" (*regular defer set = a*)
          using defers_1 by (smt Diff_insert_absorb One_nat_def Set.set_insert card_0_eq
                             card_Diff_singleton card_insert_disjoint card_mono defers_def
                             electoral_module_m empty_iff empty_subsetI finite.emptyI finite.insertI
                             finite_Diff finite_profile_p insert_subset seq_comp_defer_set_passing
                             seq_comp_does_not_grow_deferred_set2 seq_n_input_sound singletonI)
        ultimately have "(a \<in> defer (m \<triangleright> n) A p \<and> lifted A p q a) \<longrightarrow>
                         defer (m \<triangleright> n) A p = defer (m \<triangleright> n) A q" (* defer sets equal*)
          by blast
        moreover have "lifted A p q a \<longrightarrow> elect (m \<triangleright> n) A p = elect (m \<triangleright> n) A q"
                      (*elect sets sets equal*)
          using \<open>electoral_modules.lifted A p q a \<longrightarrow> finite_profile A q\<close> finite_profile_p
                non_electing_def non_electing_m non_electing_n seq_comp_preserves_non_electing
          by blast (* elect sets equal*)
        thus ?thesis
          by (meson \<open>electoral_modules.lifted A p q a \<longrightarrow> finite_profile A q\<close> calculation defer_and_elect_equal_impl_result_equal electoral_module_m electoral_module_n finite_profile_p seq_creates_modules)
      next
        assume not_different_alternatives: "\<not>\<not>(defer m A q = defer m A p)"
        have "elect m A p = {}" using non_electing_m lifted
          by (simp add: finite_profile_p non_electing_def)
        moreover have "elect m A q = {}"
          using non_electing_m lifted by (simp add: finite_profile_q non_electing_def)
        ultimately have elect_m_equal: "elect m A p = elect m A q"
          by simp (* m elects the same stuff *)
        from not_different_alternatives have same_alternatives: "defer m A q = defer m A p"
          by simp
        hence "(limit_profile_to (defer m A p) p) = (limit_profile_to (defer m A p) q) \<or>
               lifted (defer m A q) (limit_profile_to (defer m A p) p)
                                    (limit_profile_to (defer m A p) q) a"
          by (metis defer_from_input electoral_module_m finite_profile_p input_valid
              limit_lifted_profile_interaction)
        thus ?thesis
        proof assume "limit_profile_to (defer m A p) p = limit_profile_to (defer m A p) q"
          hence same_profile: "limit_profile_to (defer m A p) p = limit_profile_to (defer m A q) q"
            using same_alternatives by simp
          hence results_equal_n: "n (defer m A q) (limit_profile_to (defer m A q) q) =
                                  n (defer m A p) (limit_profile_to (defer m A p) p)"
            by (simp add: same_alternatives)
          moreover have results_equal_m: "m A p = m A q"
            using elect_m_equal same_alternatives
            by (simp add: defer_and_elect_equal_impl_result_equal electoral_module_m
                finite_profile_p finite_profile_q)
          hence "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
            using same_profile by auto
          thus ?thesis
            by blast
        next
          assume still_lifted: "lifted (defer m A q) (limit_profile_to (defer m A p) p)
                                                     (limit_profile_to (defer m A p) q) a"
          hence a_in_def_p: "a \<in> defer n (defer m A p) (limit_profile_to (defer m A p) p)"
            using defer_monotone_n
            by (meson electoral_module_m electoral_module_n finite_profile_p input_valid
                seq_defer_in_both_defer)
          hence a_still_deferred_p: "{a} \<subseteq>
                                     defer n (defer m A p) (limit_profile_to (defer m A p) p)"
            by simp
          have card_le_1_p: "card (defer m A p) \<ge> 1"
            by (metis One_nat_def Suc_leI card_gt_0_iff electoral_module_m electoral_module_n
                equals0D finite_profile_p input_valid seq_defer_in_both_defer seq_n_input_sound)
          hence "card (defer n (defer m A p) (limit_profile_to (defer m A p) p)) = 1"
            using defers_1
            by (meson defers_def electoral_module_m finite_profile_p seq_n_input_sound)
          hence def_set_is_a_p: "{a} = defer n (defer m A p) (limit_profile_to (defer m A p) p)"
            using a_still_deferred_p by (metis card_1_singletonE insert_subset singletonD)
          have a_still_deferred_q: "a \<in> defer n (defer m A q) (limit_profile_to (defer m A p) q)"
            using still_lifted
            by (metis a_in_def_p defer_monotone_def defer_monotone_n electoral_module_m
                finite_profile_p same_alternatives seq_n_input_sound)
          have "card (defer m A q) \<ge> 1"
            using card_le_1_p same_alternatives by auto
          hence "card (defer n (defer m A q) (limit_profile_to (defer m A q) q)) = 1"
            using defers_1
            by (meson defers_def electoral_module_m finite_profile_q seq_n_input_sound)
          hence def_set_is_a_q: "{a} = defer n (defer m A q) (limit_profile_to (defer m A q) q)"
            using a_still_deferred_q by (metis card_1_singletonE same_alternatives singletonD)
          have "defer n (defer m A p) (limit_profile_to (defer m A p) p) =
                defer n (defer m A q) (limit_profile_to (defer m A q) q)"
            using def_set_is_a_q def_set_is_a_p by auto
          thus ?thesis
            by (metis defer_and_elect_equal_impl_result_equal elect_m_equal electoral_module_m
                finite_profile_p finite_profile_q non_electing_def non_electing_n
                seq_comp_defer_set_passing seq_comp_elect_set_passing seq_creates_modules
                seq_n_input_sound)
        qed
      qed
    qed
  qed qed qed qed qed
  thus ?thesis
    using electoral_module_m electoral_module_n seq_creates_modules defer_lift_invariant_def
    by blast
qed


(* Composing an electoral module, that defers exactly 1 alternative, in sequence with an electing
   electoral results in an electing electoral module.
*)
theorem seq_electing[simp]:
  assumes def_one_m1:  "defers 1 m1" and
          electing_m2: "electing m2"
  shows "electing (m1 \<triangleright> m2)"
proof -
  have "\<forall>A p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow> card (defer m1 A p) = 1"
    using def_one_m1 defers_def by blast
  hence "\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> defer m1 A p \<noteq> {}"
    by (metis One_nat_def Suc_leI card_empty card_gt_0_iff zero_neq_one)
  thus ?thesis
    by (smt Un_empty def_one_m1 defers_def electing_def electing_m2 seq_comp_elect_set_passing
        seq_creates_modules seq_n_input_sound)
qed

end

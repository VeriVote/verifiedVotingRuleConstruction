(*  File:       Sequential_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Sequential Composition\<close>

theory Sequential_Composition
  imports Electoral_Module
begin

text
\<open>The sequential composition creates a new electoral module from
two electoral modules. In a sequential composition, the second
electoral module makes decisions over alternatives deferred by
the first electoral module.\<close>

subsection \<open>Definition\<close>

fun sequential_composition :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Electoral_Module" where
  "sequential_composition m n A p =
    (let new_A = defer m A p;
        new_p = limit_profile new_A p in (
                  (elect m A p) \<union> (elect n new_A new_p),
                  (reject m A p) \<union> (reject n new_A new_p),
                  defer n new_A new_p))"

abbreviation sequence ::
  "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow> 'a Electoral_Module"
     (infix "\<triangleright>" 50) where
  "m \<triangleright> n == sequential_composition m n"

lemma seq_comp_presv_disj:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          f_prof:  "finite_profile A p"
  shows "disjoint3 ((m \<triangleright> n) A p)"
proof -
  let ?new_A = "defer m A p"
  let ?new_p = "limit_profile ?new_A p"
  from module_m f_prof have disjoint_m: "disjoint3 (m A p)"
    using electoral_module_def well_formed.simps
    by blast
  from module_m module_n def_presv_fin_prof f_prof have disjoint_n:
    "(disjoint3 (n ?new_A ?new_p))"
    using electoral_module_def well_formed.simps
    by metis
  with disjoint_m module_m module_n f_prof have 0:
    "(elect m A p \<inter> reject n ?new_A ?new_p) = {}"
    using disjoint_iff_not_equal reject_in_alts 
          def_presv_fin_prof result_disj subset_eq
    by (smt (verit, best))
  from disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n have 1:
    "(elect m A p \<inter> defer n ?new_A ?new_p) = {}"
    using defer_in_alts disjoint_iff_not_equal
          rev_subsetD result_disj distrib_imp2
          Int_Un_distrib inf_sup_distrib1
          result_presv_alts sup_bot.left_neutral
          sup_bot.neutr_eq_iff sup_bot_right "0" 
    by (smt (verit, del_insts))
  from disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n have 2:
    "(reject m A p \<inter> reject n ?new_A ?new_p) = {}"
    using disjoint_iff_not_equal reject_in_alts
          set_rev_mp result_disj Int_Un_distrib2
          Un_Diff_Int boolean_algebra_cancel.inf2
          inf.order_iff inf_sup_aci(1) subsetD
    by (smt (verit, ccfv_threshold))
  from disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n have 3:
    "(reject m A p \<inter> elect n ?new_A ?new_p) = {}"
    using disjoint_iff_not_equal elect_in_alts set_rev_mp
          result_disj Int_commute boolean_algebra_cancel.inf2
          defer_not_elec_or_rej inf.commute inf.orderE inf_commute
    by (smt (verit, ccfv_threshold))
  from 0 1 2 3 disjoint_m disjoint_n module_m module_n f_prof have
    "(elect m A p \<union> elect n ?new_A ?new_p) \<inter>
          (reject m A p \<union> reject n ?new_A ?new_p) = {}"
    using inf_sup_aci(1) inf_sup_distrib2 def_presv_fin_prof 
          result_disj sup_inf_absorb sup_inf_distrib1
          distrib(3) sup_eq_bot_iff
    by (smt (verit, ccfv_threshold))
  moreover from 0 1 2 3 disjoint_n module_m module_n f_prof have
    "(elect m A p \<union> elect n ?new_A ?new_p) \<inter>
          (defer n ?new_A ?new_p) = {}"
    using Int_Un_distrib2 Un_empty def_presv_fin_prof result_disj
    by metis
  moreover from 0 1 2 3 f_prof disjoint_m disjoint_n module_m module_n
  have
    "(reject m A p \<union> reject n ?new_A ?new_p) \<inter>
          (defer n ?new_A ?new_p) = {}"
    using Int_Un_distrib2 defer_in_alts distrib_imp2
          def_presv_fin_prof result_disj subset_Un_eq
          sup_inf_distrib1
    by (smt (verit))
  ultimately have 
    "disjoint3 (elect m A p \<union> elect n ?new_A ?new_p,
                reject m A p \<union> reject n ?new_A ?new_p,
                defer n ?new_A ?new_p)"
    by simp
  thus ?thesis
    using sequential_composition.simps
    by metis
qed

lemma seq_comp_presv_alts:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          f_prof:  "finite_profile A p"
  shows "set_equals_partition A ((m \<triangleright> n) A p)"
proof -
  let ?new_A = "defer m A p"
  let ?new_p = "limit_profile ?new_A p"
  from module_m f_prof have "set_equals_partition A (m A p)"
    by (simp add: electoral_module_def)
  with module_m f_prof have 0:
    "elect m A p \<union> reject m A p \<union> ?new_A = A"
    by (simp add: result_presv_alts)
  from module_n def_presv_fin_prof f_prof module_m have
    "set_equals_partition ?new_A (n ?new_A ?new_p)"
    using electoral_module_def well_formed.simps
    by metis
  with module_m module_n f_prof have 1:
    "elect n ?new_A ?new_p \<union>
        reject n ?new_A ?new_p \<union>
        defer n ?new_A ?new_p = ?new_A"
    using def_presv_fin_prof result_presv_alts
    by metis
  from 0 1 have
    "(elect m A p \<union> elect n ?new_A ?new_p) \<union>
        (reject m A p \<union> reject n ?new_A ?new_p) \<union>
         defer n ?new_A ?new_p = A"
    by blast
  hence
    "set_equals_partition A
      (elect m A p \<union> elect n ?new_A ?new_p,
      reject m A p \<union> reject n ?new_A ?new_p,
      defer n ?new_A ?new_p)"
    by simp
  thus ?thesis
    using sequential_composition.simps
    by metis
qed

subsection \<open>Soundness\<close>

theorem seq_comp_sound[simp]:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n"
  shows "electoral_module (m \<triangleright> n)"
proof -
  have "\<forall>A p. well_formed (A::'a set) p =
          (disjoint3 p \<and> set_equals_partition A p)"
    using well_formed.simps
    by metis
  thus ?thesis
    using electoral_modI module_m module_n
          seq_comp_presv_disj seq_comp_presv_alts
    by metis
qed

subsection \<open>Lemmata\<close>

lemma seq_comp_dec_only_def:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    empty_defer: "defer m A p = {}"
  shows "(m \<triangleright> n) A p =  m A p"
  using Int_lower1 Un_absorb2 bot.extremum_uniqueI defer_in_alts
        elect_in_alts empty_defer module_m module_n prod.collapse
        f_prof reject_in_alts sequential_composition.simps
        def_presv_fin_prof result_disj
  by (smt (verit))

lemma seq_comp_def_then_elect:
  assumes
    n_electing_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n" and
    f_prof: "finite_profile A p"
  shows "elect (m \<triangleright> n) A p = defer m A p"
proof cases
  assume "A = {}"
  with electing_n n_electing_m f_prof show ?thesis
    using bot.extremum_uniqueI defer_in_alts elect_in_alts
          electing_def non_electing_def seq_comp_sound
    by metis
next
  assume assm: "A \<noteq> {}"
  from n_electing_m f_prof have ele: "elect m A p = {}"
    using non_electing_def
    by auto
  from assm def_one_m f_prof finite have def_card:
    "card (defer m A p) = 1"
    by (simp add: Suc_leI card_gt_0_iff defers_def)
  with n_electing_m f_prof have def:
    "\<exists>a \<in> A. defer m A p = {a}"
    using card_1_singletonE defer_in_alts
          non_electing_def singletonI subsetCE
    by metis
  from ele def n_electing_m have rej:
    "\<exists>a \<in> A. reject m A p = A-{a}"
    using Diff_empty def_one_m defers_def f_prof reject_not_elec_or_def
    by metis
  from ele rej def n_electing_m f_prof have res_m:
    "\<exists>a \<in> A. m A p = ({}, A-{a}, {a})"
    using Diff_empty combine_ele_rej_def non_electing_def
          reject_not_elec_or_def
    by metis
  hence
    "\<exists>a \<in> A. elect (m \<triangleright> n) A p =
        elect n {a} (limit_profile {a} p)"
    using prod.sel(1) prod.sel(2) sequential_composition.simps
          sup_bot.left_neutral
    by metis
  with def_card def electing_n n_electing_m f_prof have
    "\<exists>a \<in> A. elect (m \<triangleright> n) A p = {a}"
    using electing_for_only_alt non_electing_def prod.sel
          sequential_composition.simps def_presv_fin_prof
          sup_bot.left_neutral
    by metis
  with def def_card electing_n n_electing_m f_prof res_m
  show ?thesis
    using Diff_disjoint Diff_insert_absorb Int_insert_right
          Un_Diff_Int electing_for_only_alt empty_iff
          non_electing_def prod.sel sequential_composition.simps
          def_presv_fin_prof singletonI f_prof
    by (smt (verit, best))
qed

lemma seq_comp_def_card_bounded:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows "card (defer (m \<triangleright> n) A p) \<le> card (defer m A p)"
  using card_mono defer_in_alts module_m module_n f_prof
        sequential_composition.simps def_presv_fin_prof snd_conv
  by metis

lemma seq_comp_def_set_bounded:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
  using defer_in_alts module_m module_n prod.sel(2) f_prof
        sequential_composition.simps def_presv_fin_prof
  by metis

lemma seq_comp_defers_def_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows 
    "defer (m \<triangleright> n) A p =
      defer n (defer m A p) (limit_profile (defer m A p) p)"
  using sequential_composition.simps snd_conv
  by metis

lemma seq_comp_def_then_elect_elec_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows
    "elect (m \<triangleright> n) A p = 
      elect n (defer m A p) (limit_profile (defer m A p) p) \<union>
      (elect m A p)"
  using Un_commute fst_conv sequential_composition.simps
  by metis

lemma seq_comp_elim_one_red_def_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "eliminates 1 n" and
    f_prof: "finite_profile A p" and
    enough_leftover: "card (defer m A p) > 1"
  shows "defer (m \<triangleright> n) A p \<subset> defer m A p"
  using enough_leftover module_m module_n f_prof 
        sequential_composition.simps def_presv_fin_prof
        single_elim_imp_red_def_set snd_conv
  by metis

lemma seq_comp_def_set_sound:
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p"
  shows "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
proof -
  have "\<forall>A p. finite_profile A p \<longrightarrow> well_formed A (n A p)"
    using assms(2) electoral_module_def
    by auto
  hence
    "finite_profile (defer m A p) (limit_profile (defer m A p) p) \<longrightarrow>
        well_formed (defer m A p)
          (n (defer m A p) (limit_profile (defer m A p) p))"
    by simp
  hence
    "well_formed (defer m A p) (n (defer m A p)
      (limit_profile (defer m A p) p))"
    using assms(1) assms(3) def_presv_fin_prof
    by metis
  thus ?thesis
    using assms seq_comp_def_set_bounded
    by blast
qed

lemma seq_comp_def_set_trans:
  assumes
    "a \<in> (defer (m \<triangleright> n) A p)" and
    "electoral_module m \<and> electoral_module n" and
    "finite_profile A p"
  shows
    "a \<in> defer n (defer m A p) 
      (limit_profile (defer m A p) p) \<and>
      a \<in> defer m A p"
  using seq_comp_def_set_bounded assms(1) assms(2)
        assms(3) in_mono seq_comp_defers_def_set
  by (metis (no_types, hide_lams))

subsection \<open>Composition Rules\<close>

(*The sequential composition preserves the non-blocking property.*)
theorem seq_comp_presv_non_blocking[simp]:
  assumes
    non_blocking_m: "non_blocking m" and
    non_blocking_n: "non_blocking n"
  shows "non_blocking (m \<triangleright> n)"
proof -
  fix A p
  let ?input_sound = "((A::'a set) \<noteq> {} \<and> finite_profile A p)"
  from non_blocking_m have
    "?input_sound \<longrightarrow> reject m A p \<noteq> A"
    by (simp add: non_blocking_def)
  with non_blocking_m have 0:
    "?input_sound \<longrightarrow> A - reject m A p \<noteq> {}"
    using Diff_eq_empty_iff non_blocking_def
          reject_in_alts subset_antisym
    by metis
  from non_blocking_m have
    "?input_sound \<longrightarrow> well_formed A (m A p)"
    by (simp add: electoral_module_def non_blocking_def)
  hence
    "?input_sound \<longrightarrow>
        elect m A p \<union> defer m A p = A - reject m A p"
    using non_blocking_def non_blocking_m elec_and_def_not_rej
    by metis
  with 0 have
    "?input_sound \<longrightarrow> elect m A p \<union> defer m A p \<noteq> {}"
    by auto
  hence "?input_sound \<longrightarrow> (elect m A p \<noteq> {} \<or> defer m A p \<noteq> {})"
    by simp
  with non_blocking_m non_blocking_n
  show ?thesis
    using Diff_empty Diff_subset_conv Un_empty fst_conv snd_conv
          defer_not_elec_or_rej elect_in_alts inf.absorb1 sup_bot_right
          non_blocking_def reject_in_alts sequential_composition.simps
          seq_comp_sound def_presv_fin_prof result_disj subset_antisym
    by (smt (verit))
qed

(*Sequential composition preserves the non-electing property.*)
theorem seq_comp_presv_non_electing[simp]:
  assumes
    "non_electing m" and
    "non_electing n"
  shows "non_electing (m \<triangleright> n)"
  using Un_empty assms non_electing_def prod.sel seq_comp_sound
        sequential_composition.simps def_presv_fin_prof
  by (smt (verit, del_insts))

(*
   Composing an electoral module that defers exactly 1 alternative
   in sequence after an electoral module that is electing
   results (still) in an electing electoral module.
*)
theorem seq_comp_electing[simp]:
  assumes def_one_m1:  "defers 1 m1" and
          electing_m2: "electing m2"
  shows "electing (m1 \<triangleright> m2)"
proof -
  have
    "\<forall>A p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
        card (defer m1 A p) = 1"
    using def_one_m1 defers_def
    by blast
  hence
    "\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow>
        defer m1 A p \<noteq> {}"
    using One_nat_def Suc_leI card_eq_0_iff
          card_gt_0_iff zero_neq_one
    by metis
  thus ?thesis
    using Un_empty def_one_m1 defers_def electing_def
          electing_m2 seq_comp_def_then_elect_elec_set
          seq_comp_sound def_presv_fin_prof
    by (smt (verit, ccfv_threshold))
qed

lemma def_lift_inv_seq_comp_help:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n" and
    def_and_lifted: "a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a"
  shows "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
proof -
  let ?new_Ap = "defer m A p"
  let ?new_Aq = "defer m A q"
  let ?new_p = "limit_profile ?new_Ap p"
  let ?new_q = "limit_profile ?new_Aq q"
  from monotone_m monotone_n have modules:
    "electoral_module m \<and> electoral_module n"
    by (simp add: defer_lift_invariance_def)
  hence "finite_profile A p \<longrightarrow> defer (m \<triangleright> n) A p \<subseteq> defer m A p"
    using seq_comp_def_set_bounded
    by metis
  moreover have profile_p: "lifted A p q a \<longrightarrow> finite_profile A p"
    by (simp add: lifted_def)
  ultimately have defer_subset: "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
    using def_and_lifted
    by blast
  hence mono_m: "m A p = m A q"
    using monotone_m defer_lift_invariance_def def_and_lifted
          modules profile_p seq_comp_def_set_trans
    by metis
  hence new_A_eq: "?new_Ap = ?new_Aq"
    by presburger
  have defer_eq:
    "defer (m \<triangleright> n) A p = defer n ?new_Ap ?new_p"
    using sequential_composition.simps snd_conv
    by metis
  hence mono_n:
    "n ?new_Ap ?new_p = n ?new_Aq ?new_q"
  proof cases
    assume "lifted ?new_Ap ?new_p ?new_q a"
    thus ?thesis
      using defer_eq mono_m monotone_n
            defer_lift_invariance_def def_and_lifted
      by (metis (no_types, lifting))
  next
    assume a2: "\<not>lifted ?new_Ap ?new_p ?new_q a"
    from def_and_lifted have "finite_profile A q"
      by (simp add: lifted_def)
    with modules new_A_eq have 1:
      "finite_profile ?new_Ap ?new_q"
      using def_presv_fin_prof
      by (metis (no_types))
    moreover from modules profile_p def_and_lifted
    have 0:
      "finite_profile ?new_Ap ?new_p"
      using def_presv_fin_prof
      by (metis (no_types))
    moreover from defer_subset def_and_lifted
    have 2: "a \<in> ?new_Ap"
      by blast
    moreover from def_and_lifted have eql_lengths:
      "size ?new_p = size ?new_q"
      by (simp add: lifted_def)
    ultimately have 0:
      "(\<forall>i::nat. i < size ?new_p \<longrightarrow>
          \<not>Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a) \<or>
       (\<exists>i::nat. i < size ?new_p \<and>
          \<not>Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<and>
              (?new_p!i) \<noteq> (?new_q!i))"
      using a2 lifted_def
      by (metis (no_types, lifting))
    from def_and_lifted modules have
      "\<forall>i. (0 \<le> i \<and> i < size ?new_p) \<longrightarrow>
          (Preference_Relation.lifted A (p!i) (q!i) a \<or> (p!i) = (q!i))"
      using defer_in_alts Electoral_Module.lifted_def limit_prof_presv_size
      by metis
    with def_and_lifted modules mono_m have
      "\<forall>i. (0 \<le> i \<and> i < size ?new_p) \<longrightarrow>
          (Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<or>
           (?new_p!i) = (?new_q!i))"
      using limit_lifted_imp_eq_or_lifted defer_in_alts
            Electoral_Module.lifted_def limit_prof_presv_size
            limit_profile.simps nth_map
      by (metis (no_types, lifting))
    with 0 eql_lengths mono_m
    show ?thesis
      using leI not_less_zero nth_equalityI
      by metis
  qed
  from mono_m mono_n
  show ?thesis
    using sequential_composition.simps
    by (metis (full_types))
qed

(*Sequential composition preserves the property defer-lift-invariance.*)
theorem seq_comp_presv_def_lift_inv[simp]:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<triangleright> n)"
  using monotone_m monotone_n def_lift_inv_seq_comp_help
        seq_comp_sound defer_lift_invariance_def
  by (metis (full_types))

(*
   Composing a non-blocking, non-electing electoral module
   in sequence with an electoral module that defers exactly
   one alternative results in an electoral module that defers
   exactly one alternative.
*)
theorem seq_comp_def_one[simp]:
  assumes
    non_blocking_m: "non_blocking m" and
    non_electing_m: "non_electing m" and
    def_1_n: "defers 1 n"
  shows "defers 1 (m \<triangleright> n)"
proof -
  have
    "\<forall>A p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
      card (defer (m \<triangleright> n) A p) = 1"
  proof
    fix A
    show
      "\<forall> p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
          card (defer (m \<triangleright> n) A p) = 1"
    proof
      fix p
      show
        "(card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
            card (defer (m \<triangleright> n) A p) = 1"
      proof
        assume input_fine:
          "(card A \<ge> 1 \<and> finite_profile A p)"
        hence "A \<noteq> {}"
          by auto
        moreover from input_fine
        have finite_profile:
          "finite_profile A p"
          by simp
        ultimately have "reject m A p \<noteq> A"
          using non_blocking_m non_blocking_def
          by metis
        moreover have "elect m A p = {}"
          using non_electing_m finite_profile non_electing_def
          by auto
        ultimately have "defer m A p \<noteq> {}"
        proof - (* generated proof *)
          have "\<exists>a. a \<in> A \<and> a \<notin> reject m A p"
            using \<open>reject m A p \<noteq> A\<close> input_fine 
                  non_electing_def non_electing_m
                  reject_in_alts subset_antisym subset_iff
                  finite_profile subsetI
            by metis
          thus ?thesis
            using electoral_mod_defer_elem empty_iff input_fine
                  non_electing_def non_electing_m
            by (metis (no_types))
        qed
        hence "card (defer m A p) \<ge> 1"
          using One_nat_def Suc_leI card_gt_0_iff input_fine
                non_blocking_def non_blocking_m def_presv_fin_prof
          by metis
        thus "card (defer (m \<triangleright> n) A p) = 1"
        proof - (* generated proof *)
          have f1:
            "(elect (m \<triangleright> n) A p, snd ((m \<triangleright> n) A p)) =
              (elect m A p \<union>
              elect n (defer m A p) (limit_profile (defer m A p) p),
              reject m A p \<union>
              reject n (defer m A p) (limit_profile (defer m A p) p),
              defer n (defer m A p) (limit_profile (defer m A p) p))"
            using prod.collapse sequential_composition.simps
            by metis
          have
            "\<forall>n f. defers n f =
              (electoral_module f \<and>
                (\<forall>A rs. (\<not> n \<le> card (A::'a set) \<or> infinite A \<or>
                    \<not> profile A rs) \<or>
                  card (defer f A rs) = n))"
            using defers_def
            by blast
          hence
            "card (defer n (defer m A p)
                (limit_profile (defer m A p) p)) = 1"
            using \<open>1 \<le> card (defer m A p)\<close> assms(3)
                  finite_profile non_blocking_def
                  non_blocking_m def_presv_fin_prof
            by metis
          thus ?thesis
            using f1
            by auto
        qed
      qed
    qed
  qed
  thus ?thesis
    using def_1_n defers_def non_electing_def
          non_electing_m seq_comp_sound
    by metis
qed

(*
   Sequentially composing electoral modules after compatible
   electoral modules does not break their compatibility.
*)
theorem disj_compat_seq[simp]:
  assumes
    compatible: "disjoint_compatibility m n" and
    module_m2: "electoral_module m2"
  shows "disjoint_compatibility (m \<triangleright> m2) n"
proof -
  have modules:
    "electoral_module (m \<triangleright> m2) \<and> electoral_module n"
    using compatible disjoint_compatibility_def module_m2 seq_comp_sound
    by metis
  moreover have
    "\<forall>S. finite S \<longrightarrow>
      (\<exists>A \<subseteq> S. (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
        (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)))"
  proof
    fix S
    show
      "finite S \<longrightarrow>
        (\<exists>A \<subseteq> S. (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
            (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
          (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
            (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)))"
    proof
      assume fin: "finite S"
      obtain A where A:
        "A \<subseteq> S \<and> (\<forall>a \<in> A. indep_of_alt m S a \<and>
            (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
          (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
            (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
        using compatible disjoint_compatibility_def fin
        by (metis (no_types, lifting))
      show
        "\<exists>A. A \<subseteq> S \<and>
            (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
      proof
        have
          "\<forall>a p q. a \<in> A \<and> equiv_prof_except_a S p q a \<longrightarrow>
            (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
        proof
          fix a
          show
            "\<forall>p q. a \<in> A \<and> equiv_prof_except_a S p q a \<longrightarrow>
              (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
          proof
            fix p
            show
              "\<forall>q. a \<in> A \<and> equiv_prof_except_a S p q a \<longrightarrow>
                (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
            proof
              fix q
              show
                "a \<in> A \<and> equiv_prof_except_a S p q a \<longrightarrow>
                  (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
              proof
                assume a: "a \<in> A \<and> equiv_prof_except_a S p q a"
                have eq_def: "defer m S p = defer m S q"
                  using A a indep_of_alt_def
                  by metis
                  from a have profiles:
                  "finite_profile S p \<and> finite_profile S q"
                  using equiv_prof_except_a_def
                  by fastforce
                hence "(defer m S p) \<subseteq> S"
                  using compatible defer_in_alts disjoint_compatibility_def
                  by blast
                hence
                  "limit_profile (defer m S p) p =
                    limit_profile (defer m S q) q"
                  using A DiffD2 a compatible defer_not_elec_or_rej
                        disjoint_compatibility_def eq_def profiles
                        negl_diff_imp_eq_limit_prof
                  by (metis (no_types, lifting))
                with eq_def have
                  "m2 (defer m S p) (limit_profile (defer m S p) p) =
                    m2 (defer m S q) (limit_profile (defer m S q) q)"
                  by simp
                moreover have "m S p = m S q"
                  using A a indep_of_alt_def
                  by metis
                ultimately show
                  "(m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
                  using sequential_composition.simps
                  by (metis (full_types))
              qed
            qed
          qed
        qed
        moreover have 
          "\<forall>a \<in> A. \<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p"
          using A UnI1 prod.sel sequential_composition.simps
          by metis
        ultimately show
          "A \<subseteq> S \<and>
            (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
          using A indep_of_alt_def modules
          by (metis (mono_tags, lifting))
      qed
    qed
  qed
  thus ?thesis
    by (simp add: disjoint_compatibility_def modules)
qed

(*
   Composing a defer-lift invariant and a non-electing
   electoral module that defers exactly one alternative
   in sequence with an electing electoral module
   results in a monotone electoral module.
*)
theorem seq_comp_mono[simp]:
  assumes
    def_monotone_m: "defer_lift_invariance m" and
    non_ele_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n"
  shows "monotonicity (m \<triangleright> n)"
proof -
  have
    "\<forall>A p q w.
      (finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow>
        w \<in> elect (m \<triangleright> n) A q"
  proof
    fix A
    show
      "\<forall>p q w. (finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow>
        w \<in> elect (m \<triangleright> n) A q"
    proof
      fix p
      show
        "\<forall>q w. (finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow>
          w \<in> elect (m \<triangleright> n) A q"
      proof
        fix q
        show
          "\<forall>w. (finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow>
            w \<in> elect (m \<triangleright> n) A q"
        proof
          fix w
          show
            "(finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w) \<longrightarrow>
              w \<in> elect (m \<triangleright> n) A q"
          proof
            assume a:
              "finite A \<and> w \<in> elect (m \<triangleright> n) A p \<and> lifted A p q w"
            hence profiles:
              "finite_profile A p \<and> finite_profile A q"
              using lifted_def
              by metis
            with a def_monotone_m non_ele_m def_one_m electing_n
            show "w \<in> elect (m \<triangleright> n) A q"
              using seq_comp_def_then_elect defer_lift_invariance_def
              by metis
          qed
        qed
      qed
    qed
  qed
  thus ?thesis
    using electing_def electing_n Electoral_Module.monotonicity_def
          non_ele_m non_electing_def seq_comp_sound
    by (metis (no_types, lifting))
qed

(*
   Composing a defer-invariant-monotone electoral module in sequence before
   a non-electing, defer-monotone electoral module that defers exactly
   1 alternative results in a defer-lift-invariant electoral module.
*)
theorem def_inv_mono_imp_def_lift_inv[simp]:
  assumes
    strong_def_mon_m: "defer_invariant_monotonicity m" and
    non_electing_n: "non_electing n" and
    defers_1: "defers 1 n" and
    defer_monotone_n: "defer_monotonicity n"
  shows "defer_lift_invariance (m \<triangleright> n)"
proof -
  from strong_def_mon_m
  have non_electing_m: "non_electing m"
    by (simp add: defer_invariant_monotonicity_def)
  have electoral_mod_m: "electoral_module m"
    using strong_def_mon_m defer_invariant_monotonicity_def
    by auto
  have electoral_mod_n: "electoral_module n"
    using defers_1 defers_def
    by auto
  have
    "\<forall>A p q a. (a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow>
        (m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof
    fix A
    show
      "\<forall> p q a. (a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow>
        (m \<triangleright> n) A p = (m \<triangleright> n) A q"
    proof
      fix p
      show
        "\<forall> q a. (a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow>
          (m \<triangleright> n) A p = (m \<triangleright> n) A q"
      proof
        fix q
        show
          "\<forall> a. (a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow>
            (m \<triangleright> n) A p = (m \<triangleright> n) A q"
        proof
          fix a
          show
            "(a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a) \<longrightarrow>
              (m \<triangleright> n) A p = (m \<triangleright> n) A q"
          proof cases
            assume "\<not> lifted A p q a"
            thus ?thesis
              by simp
          next
            assume "\<not>\<not> lifted A p q a"
            hence lifted: "lifted A p q a"
              by simp
            hence finite_profile_q: "finite_profile A q"
              by (simp add: Electoral_Module.lifted_def lifted)
            from lifted have finite_profile_p: "profile A p"
              by (simp add: Electoral_Module.lifted_def)
            thus ?thesis
            proof cases
              assume
                "\<not>(a \<in> defer (m \<triangleright> n) A p \<and> Electoral_Module.lifted A p q a)"
              thus ?thesis
                by blast
            next
              assume
                "\<not>\<not>(a \<in> defer (m \<triangleright> n) A p \<and> Electoral_Module.lifted A p q a)"
              hence def_and_lifted:
                "(a \<in> defer (m \<triangleright> n) A p \<and> Electoral_Module.lifted A p q a)"
                by simp
              thus ?thesis
              proof cases
                assume not_unchanged: "\<not>(defer m A q = defer m A p)"
                hence a_single_defer: "{a} = defer m A q" 
                  using strong_def_mon_m electoral_mod_n
                        finite_profile_p finite_profile_q
                        def_and_lifted seq_comp_def_set_trans
                        defer_invariant_monotonicity_def
                  by metis
                moreover have
                  "(finite_profile A q \<and> {a} = defer m A q) \<longrightarrow>
                      (defer (m \<triangleright> n) A q \<subseteq> {a})"
                  using finite_profile_p electoral_mod_m
                        electoral_mod_n seq_comp_def_set_sound
                        non_electing_m
                  by blast
                ultimately have
                  "((a \<in> defer m A p) \<and> (lifted A p q a) \<and>
                      finite_profile A q) \<longrightarrow>
                  defer (m \<triangleright> n) A q \<subseteq> {a}"
                  by blast
                moreover have
                  "(lifted A p q a) \<longrightarrow> finite_profile A q"
                  by (simp add: Electoral_Module.lifted_def)
                ultimately have
                  "((a \<in> defer m A p) \<and> (lifted A p q a)) \<longrightarrow>
                      defer (m \<triangleright> n) A q \<subseteq> {a}" (* lifted defer-subset of a *)
                  by blast
                moreover have
                  "((a \<in> defer m A p) \<and> (lifted A p q a)) \<longrightarrow>
                      card (defer (m \<triangleright> n) A q) = 1"
                  using One_nat_def a_single_defer card_eq_0_iff
                        card_insert_disjoint defers_1 defers_def
                        electoral_mod_m empty_iff finite.emptyI
                        seq_comp_defers_def_set order_refl
                        def_presv_fin_prof card.empty
                        finite_profile_q
                  by metis    (* lifted defer set size 1 *)
                moreover have
                  "a \<in> (defer (m \<triangleright> n) A p) \<longrightarrow> (a \<in> defer m A p)"
                  using electoral_mod_m electoral_mod_n
                        seq_comp_def_set_bounded finite_profile_p
                        finite_profile_q
                  by blast
                ultimately have
                  "(a \<in> (defer (m \<triangleright> n) A p) \<and> (lifted A p q a)) \<longrightarrow>
                      defer (m \<triangleright> n) A q = {a}" (* lifted defer set = a *)
                  using Collect_mem_eq card_1_singletonE empty_Collect_eq
                        insertCI subset_singletonD
                  by metis
                moreover have
                  "(a \<in> (defer (m \<triangleright> n) A p) \<and> (lifted A p q a)) \<longrightarrow>
                      defer (m \<triangleright> n) A p = {a}" (* regular defer set = a *)
                  using Diff_insert_absorb One_nat_def Set.set_insert
                        card_0_eq card_Diff_singleton card_insert_disjoint
                        card_mono defers_def electoral_mod_m empty_iff
                        empty_subsetI finite.emptyI finite.insertI
                        finite_Diff finite_profile_p insert_subset
                        seq_comp_defers_def_set seq_comp_def_set_bounded
                        def_presv_fin_prof singletonI Suc_inject
                        Un_insert_left electoral_mod_n insert_Diff
                        insert_absorb2 insert_ident non_electing_m
                        seq_comp_def_card_bounded sup_bot_right
                        seq_comp_def_then_elect_elec_set calculation
                        card_Suc_Diff1 elect_in_alts non_electing_def
                        non_electing_n finite_profile_q card.empty
                        card_eq_0_iff defers_1
                  by (smt (verit, best))
                ultimately have
                  "(a \<in> defer (m \<triangleright> n) A p \<and> lifted A p q a) \<longrightarrow>
                      defer (m \<triangleright> n) A p =
                        defer (m \<triangleright> n) A q" (* defer sets equal *)
                  by blast
                moreover have
                  "lifted A p q a \<longrightarrow>
                      elect (m \<triangleright> n) A p = elect (m \<triangleright> n) A q" 
                      (* elect sets sets equal *)
                  using finite_profile_p non_electing_def non_electing_m
                        non_electing_n seq_comp_presv_non_electing
                        finite_profile_q
                  by metis (* elect sets equal *)
                thus ?thesis
                  using calculation eq_def_and_elect_imp_eq
                        electoral_mod_m electoral_mod_n
                        finite_profile_p seq_comp_sound
                        finite_profile_q
                  by  metis
              next
                assume not_different_alternatives:
                  "\<not>\<not>(defer m A q = defer m A p)"
                have "elect m A p = {}"
                  using non_electing_m
                  by (simp add: lifted finite_profile_p
                                finite_profile_q
                                non_electing_def)
                moreover have "elect m A q = {}"
                  using non_electing_m
                  by (simp add: lifted finite_profile_q
                                non_electing_def)
                ultimately have elect_m_equal:
                  "elect m A p = elect m A q"
                  by simp (* m elects the same stuff *)
                from not_different_alternatives
                have same_alternatives: "defer m A q = defer m A p"
                  by simp
                hence
                  "(limit_profile (defer m A p) p) =
                      (limit_profile (defer m A p) q) \<or>
                        lifted (defer m A q)
                          (limit_profile (defer m A p) p)
                            (limit_profile (defer m A p) q) a"
                  using defer_in_alts electoral_mod_m
                        finite_profile_p def_and_lifted
                        limit_prof_eq_or_lifted
                        finite_profile_q
                  by metis
                thus ?thesis
                proof
                  assume
                    "limit_profile (defer m A p) p =
                     limit_profile (defer m A p) q"
                  hence same_profile:
                    "limit_profile (defer m A p) p =
                     limit_profile (defer m A q) q"
                    using same_alternatives
                    by simp
                  hence results_equal_n:
                    "n (defer m A q) (limit_profile (defer m A q) q) =
                        n (defer m A p) (limit_profile (defer m A p) p)"
                    by (simp add: same_alternatives)
                  moreover have results_equal_m: "m A p = m A q"
                    by (simp add: elect_m_equal same_alternatives
                                  finite_profile_p finite_profile_q
                                  electoral_mod_m eq_def_and_elect_imp_eq)
                  hence "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
                    using same_profile
                    by auto
                  thus ?thesis
                    by blast
                next
                  assume still_lifted:
                    "lifted (defer m A q) (limit_profile (defer m A p) p)
                      (limit_profile (defer m A p) q) a"
                  hence a_in_def_p:
                    "a \<in> defer n (defer m A p)
                      (limit_profile (defer m A p) p)"
                    using defer_monotone_n
                          electoral_mod_m electoral_mod_n
                          finite_profile_p def_and_lifted
                          seq_comp_def_set_trans
                          finite_profile_q
                    by metis
                  hence a_still_deferred_p:
                    "{a} \<subseteq> defer n (defer m A p)
                        (limit_profile (defer m A p) p)"
                    by simp
                  have card_le_1_p: "card (defer m A p) \<ge> 1"
                    using One_nat_def Suc_leI card_gt_0_iff
                          electoral_mod_m electoral_mod_n
                          equals0D finite_profile_p def_and_lifted
                          seq_comp_def_set_trans def_presv_fin_prof
                          finite_profile_q
                    by metis
                  hence
                    "card (defer n (defer m A p) 
                      (limit_profile (defer m A p) p)) = 1"
                    using defers_1 defers_def electoral_mod_m
                          finite_profile_p def_presv_fin_prof
                          finite_profile_q
                    by metis
                  hence def_set_is_a_p:
                    "{a} =
                      defer n (defer m A p) (limit_profile (defer m A p) p)"
                    using a_still_deferred_p card_1_singletonE
                          insert_subset singletonD
                    by metis
                  have a_still_deferred_q:
                    "a \<in> defer n (defer m A q)
                      (limit_profile (defer m A p) q)"
                    using still_lifted a_in_def_p
                          defer_monotonicity_def
                          defer_monotone_n electoral_mod_m
                          finite_profile_p same_alternatives
                          def_presv_fin_prof finite_profile_q
                    by metis
                  have "card (defer m A q) \<ge> 1"
                    using card_le_1_p same_alternatives
                    by auto
                  hence
                    "card (defer n (defer m A q)
                      (limit_profile (defer m A q) q)) = 1"
                    using defers_1 defers_def electoral_mod_m
                          finite_profile_q def_presv_fin_prof
                          finite_profile_p not_different_alternatives
                    by metis
                  hence def_set_is_a_q:
                    "{a} =
                      defer n (defer m A q)
                        (limit_profile (defer m A q) q)"
                    using a_still_deferred_q card_1_singletonE
                          same_alternatives singletonD
                    by metis
                  have
                    "defer n (defer m A p)
                      (limit_profile (defer m A p) p) =
                          defer n (defer m A q)
                            (limit_profile (defer m A q) q)"
                    using def_set_is_a_q def_set_is_a_p
                    by auto
                  thus ?thesis
                    using eq_def_and_elect_imp_eq elect_m_equal
                          electoral_mod_m finite_profile_p
                          finite_profile_q non_electing_def
                          non_electing_n seq_comp_defers_def_set
                          def_set_is_a_p electoral_mod_n
                          non_electing_m not_different_alternatives
                          seq_comp_presv_non_electing def_set_is_a_q
                          same_alternatives
                    by metis
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis
    using electoral_mod_m electoral_mod_n
          seq_comp_sound defer_lift_invariance_def
    by blast
qed

end

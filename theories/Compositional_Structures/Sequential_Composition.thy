(*  File:       Sequential_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Sequential Composition\<close>

theory Sequential_Composition
  imports "Basic_Modules/Component_Types/Electoral_Module"
begin

text \<open>
  The sequential composition creates a new electoral module from
  two electoral modules. In a sequential composition, the second
  electoral module makes decisions over alternatives deferred by
  the first electoral module.
\<close>

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

fun sequential_composition' :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Electoral_Module" where
  "sequential_composition' m n A p =
    (let (m_e, m_r, m_d) = m A p; new_A = m_d;
        new_p = limit_profile new_A p;
        (n_e, n_r, n_d) = n new_A new_p in
            (m_e \<union> n_e, m_r \<union> n_r, n_d))"

lemma seq_comp_presv_disj:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          f_prof:  "finite_profile A p"
  shows "disjoint3 ((m \<triangleright> n) A p)"
proof -
  let ?new_A = "defer m A p"
  let ?new_p = "limit_profile ?new_A p"
  have fin_def: "finite (defer m A p)"
    using def_presv_fin_prof f_prof module_m
    by metis
  have prof_def_lim: "profile (defer m A p) (limit_profile (defer m A p) p)"
    using def_presv_fin_prof f_prof module_m
    by metis
  have defer_in_A:
    "\<forall> A' p' m' a.
      (profile A' p' \<and> finite A' \<and> electoral_module m' \<and> (a::'a) \<in> defer m' A' p') \<longrightarrow> a \<in> A'"
    using UnCI result_presv_alts
    by (metis (mono_tags))
  from module_m f_prof
  have disjoint_m: "disjoint3 (m A p)"
    unfolding electoral_module_def well_formed.simps
    by blast
  from module_m module_n def_presv_fin_prof f_prof
  have disjoint_n: "disjoint3 (n ?new_A ?new_p)"
    unfolding electoral_module_def well_formed.simps
    by metis
  have disj_n:
    "elect m A p \<inter> reject m A p = {} \<and>
      elect m A p \<inter> defer m A p = {} \<and>
      reject m A p \<inter> defer m A p = {}"
    using f_prof module_m
    by (simp add: result_disj)
  have "reject n (defer m A p) (limit_profile (defer m A p) p) \<subseteq> defer m A p"
    using def_presv_fin_prof reject_in_alts f_prof module_m module_n
    by metis
  with disjoint_m module_m module_n f_prof
  have elect_reject_diff: "elect m A p \<inter> reject n ?new_A ?new_p = {}"
    using disj_n
    by (simp add: disjoint_iff_not_equal subset_eq)
  from f_prof module_m module_n
  have elec_n_in_def_m: "elect n (defer m A p) (limit_profile (defer m A p) p) \<subseteq> defer m A p"
    using def_presv_fin_prof elect_in_alts
    by metis
  have elect_defer_diff: "elect m A p \<inter> defer n ?new_A ?new_p = {}"
  proof -
    obtain f :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall> B B'.
        (\<exists> a b. a \<in> B' \<and> b \<in> B \<and> a = b) =
          (f B B' \<in> B' \<and> (\<exists> a. a \<in> B \<and> f B B' = a))"
      by moura
    then obtain g :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall> B B'.
        (B \<inter> B' = {} \<longrightarrow> (\<forall> a b. a \<in> B \<and> b \<in> B' \<longrightarrow> a \<noteq> b)) \<and>
          (B \<inter> B' \<noteq> {} \<longrightarrow> (f B B' \<in> B \<and> g B B' \<in> B' \<and> f B B' = g B B'))"
      by auto
    thus ?thesis
      using defer_in_A disj_n fin_def module_n prof_def_lim
      by (metis (no_types))
  qed
  have rej_intersect_new_elect_empty: "reject m A p \<inter> elect n ?new_A ?new_p = {}"
    using disj_n disjoint_m disjoint_n def_presv_fin_prof f_prof
          module_m module_n elec_n_in_def_m
    by blast
  have "(elect m A p \<union> elect n ?new_A ?new_p) \<inter> (reject m A p \<union> reject n ?new_A ?new_p) = {}"
  proof (safe)
    fix x :: "'a"
    assume
      "x \<in> elect m A p" and
      "x \<in> reject m A p"
    hence "x \<in> elect m A p \<inter> reject m A p"
      by simp
    thus "x \<in> {}"
      using disj_n
      by simp
  next
    fix x :: "'a"
    assume
      "x \<in> elect m A p" and
      "x \<in> reject n (defer m A p)
        (limit_profile (defer m A p) p)"
    thus "x \<in> {}"
      using elect_reject_diff
      by blast
  next
    fix x :: "'a"
    assume
      "x \<in> elect n (defer m A p) (limit_profile (defer m A p) p)" and
      "x \<in> reject m A p"
    thus "x \<in> {}"
      using rej_intersect_new_elect_empty
      by blast
  next
    fix x :: "'a"
    assume
      "x \<in> elect n (defer m A p) (limit_profile (defer m A p) p)" and
      "x \<in> reject n (defer m A p) (limit_profile (defer m A p) p)"
    thus "x \<in> {}"
      using disjoint_iff_not_equal fin_def module_n prof_def_lim result_disj
      by metis
  qed
  moreover have "(elect m A p \<union> elect n ?new_A ?new_p) \<inter> (defer n ?new_A ?new_p) = {}"
    using Int_Un_distrib2 Un_empty elect_defer_diff fin_def module_n prof_def_lim result_disj
    by (metis (no_types))
  moreover have "(reject m A p \<union> reject n ?new_A ?new_p) \<inter> (defer n ?new_A ?new_p) = {}"
  proof (safe)
    fix x :: "'a"
    assume
      x_in_def: "x \<in> defer n (defer m A p) (limit_profile (defer m A p) p)" and
      x_in_rej: "x \<in> reject m A p"
    from x_in_def
    have "x \<in> defer m A p"
      using defer_in_A fin_def module_n prof_def_lim
      by blast
    with x_in_rej
    have "x \<in> reject m A p \<inter> defer m A p"
      by fastforce
    thus "x \<in> {}"
      using disj_n
      by blast
  next
    fix x :: "'a"
    assume
      "x \<in> defer n (defer m A p) (limit_profile (defer m A p) p)" and
      "x \<in> reject n (defer m A p) (limit_profile (defer m A p) p)"
    thus "x \<in> {}"
      using fin_def module_n prof_def_lim reject_not_elec_or_def
      by fastforce
  qed
  ultimately have
    "disjoint3 (elect m A p \<union> elect n ?new_A ?new_p,
                reject m A p \<union> reject n ?new_A ?new_p,
                defer n ?new_A ?new_p)"
    by simp
  thus ?thesis
    unfolding sequential_composition.simps
    by metis
qed

lemma seq_comp_presv_alts:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          f_prof:  "finite_profile A p"
  shows "set_equals_partition A ((m \<triangleright> n) A p)"
proof -
  let ?new_A = "defer m A p"
  let ?new_p = "limit_profile ?new_A p"
  have elect_reject_diff: "elect m A p \<union> reject m A p \<union> ?new_A = A"
    using module_m f_prof
    by (simp add: result_presv_alts)
  have "elect n ?new_A ?new_p \<union>
          reject n ?new_A ?new_p \<union>
            defer n ?new_A ?new_p = ?new_A"
    using module_m module_n f_prof def_presv_fin_prof result_presv_alts
    by metis
  hence "(elect m A p \<union> elect n ?new_A ?new_p) \<union>
          (reject m A p \<union> reject n ?new_A ?new_p) \<union>
            defer n ?new_A ?new_p = A"
    using elect_reject_diff
    by blast
  hence "set_equals_partition A
          (elect m A p \<union> elect n ?new_A ?new_p,
            reject m A p \<union> reject n ?new_A ?new_p,
              defer n ?new_A ?new_p)"
    by simp
  thus ?thesis
    unfolding sequential_composition.simps
    by metis
qed

lemma seq_comp_alt_eq[code]: "sequential_composition = sequential_composition'"
proof (unfold sequential_composition'.simps sequential_composition.simps)
  have "\<forall> m n A E.
      (case m A E of (e, r, d) \<Rightarrow>
        case n d (limit_profile d E) of (e', r', d') \<Rightarrow>
        (e \<union> e', r \<union> r', d')) =
          (elect m A E \<union> elect n (defer m A E) (limit_profile (defer m A E) E),
            reject m A E \<union> reject n (defer m A E) (limit_profile (defer m A E) E),
            defer n (defer m A E) (limit_profile (defer m A E) E))"
    using case_prod_beta'
    by (metis (no_types, lifting))
  thus
    "(\<lambda> m n A p.
        let A' = defer m A p; p' = limit_profile A' p in
      (elect m A p \<union> elect n A' p', reject m A p \<union> reject n A' p', defer n A' p')) =
      (\<lambda> m n A pr.
        let (e, r, d) = m A pr; A' = d; p' = limit_profile A' pr; (e', r', d') = n A' p' in
      (e \<union> e', r \<union> r', d'))"
    by metis
qed

subsection \<open>Soundness\<close>

theorem seq_comp_sound[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "electoral_module n"
  shows "electoral_module (m \<triangleright> n)"
proof (unfold electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p"
  have "\<forall> r. well_formed (A::'a set) r =
          (disjoint3 r \<and> set_equals_partition A r)"
    by simp
  thus "well_formed A ((m \<triangleright> n) A p)"
    using assms seq_comp_presv_disj seq_comp_presv_alts fin_A prof_A
    by metis
qed

subsection \<open>Lemmas\<close>

lemma seq_comp_dec_only_def:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    empty_defer: "defer m A p = {}"
  shows "(m \<triangleright> n) A p =  m A p"
proof
  have
    "\<forall> m' A' p'.
      (electoral_module m' \<and> finite_profile A' p') \<longrightarrow>
        finite_profile (defer m' A' p') (limit_profile (defer m' A' p') p')"
    using def_presv_fin_prof
    by metis
  hence "profile {} (limit_profile (defer m A p) p)"
    using empty_defer f_prof module_m
    by metis
  hence "(elect m A p) \<union> (elect n (defer m A p) (limit_profile (defer m A p) p)) = elect m A p"
    using elect_in_alts empty_defer module_n
    by auto
  thus "elect (m \<triangleright> n) A p = elect m A p"
    using fst_conv
    unfolding sequential_composition.simps
    by metis
next
  have rej_empty:
    "\<forall> m' p'.
      (electoral_module m' \<and> profile ({}::'a set) p') \<longrightarrow>
        reject m' {} p' = {}"
    using bot.extremum_uniqueI infinite_imp_nonempty reject_in_alts
    by metis
  have prof_no_alt: "profile {} (limit_profile (defer m A p) p)"
    using empty_defer f_prof module_m limit_profile_sound
    by auto
  hence "(reject m A p, defer n {} (limit_profile {} p)) = snd (m A p)"
    using bot.extremum_uniqueI defer_in_alts empty_defer
          infinite_imp_nonempty module_n prod.collapse
    by (metis (no_types))
  thus "snd ((m \<triangleright> n) A p) = snd (m A p)"
    using rej_empty empty_defer module_n prof_no_alt
    by simp
qed

lemma seq_comp_def_then_elect:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    n_electing_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n" and
    f_prof: "finite_profile A p"
  shows "elect (m \<triangleright> n) A p = defer m A p"
proof (cases)
  assume "A = {}"
  with electing_n n_electing_m f_prof
  show ?thesis
    using bot.extremum_uniqueI defer_in_alts elect_in_alts seq_comp_sound
    unfolding electing_def non_electing_def
    by metis
next
  assume non_empty_A: "A \<noteq> {}"
  from n_electing_m f_prof
  have ele: "elect m A p = {}"
    unfolding non_electing_def
    by simp
  from non_empty_A def_one_m f_prof finite
  have def_card: "card (defer m A p) = 1"
    unfolding defers_def
    by (simp add: Suc_leI card_gt_0_iff)
  with n_electing_m f_prof
  have def: "\<exists> a \<in> A. defer m A p = {a}"
    using card_1_singletonE defer_in_alts singletonI subsetCE
    unfolding non_electing_def
    by metis
  from ele def n_electing_m
  have rej: "\<exists> a \<in> A. reject m A p = A - {a}"
    using Diff_empty def_one_m f_prof reject_not_elec_or_def
    unfolding defers_def
    by metis
  from ele rej def n_electing_m f_prof
  have res_m: "\<exists> a \<in> A. m A p = ({}, A - {a}, {a})"
    using Diff_empty combine_ele_rej_def reject_not_elec_or_def
    unfolding non_electing_def
    by metis
  hence "\<exists> a \<in> A. elect (m \<triangleright> n) A p = elect n {a} (limit_profile {a} p)"
    using prod.sel(1, 2) sup_bot.left_neutral
    unfolding sequential_composition.simps
    by metis
  with def_card def electing_n n_electing_m f_prof
  have "\<exists> a \<in> A. elect (m \<triangleright> n) A p = {a}"
    using electing_for_only_alt prod.sel(1) def_presv_fin_prof sup_bot.left_neutral
    unfolding non_electing_def sequential_composition.simps
    by metis
  with def def_card electing_n n_electing_m f_prof res_m
  show ?thesis
    using def_presv_fin_prof electing_for_only_alt fst_conv sup_bot.left_neutral
    unfolding non_electing_def sequential_composition.simps
    by metis
qed

lemma seq_comp_def_card_bounded:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p"
  shows "card (defer (m \<triangleright> n) A p) \<le> card (defer m A p)"
  using card_mono defer_in_alts assms def_presv_fin_prof snd_conv
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_def_set_bounded:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p"
  shows "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
  using defer_in_alts assms prod.sel(2) def_presv_fin_prof
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_defers_def_set:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  shows "defer (m \<triangleright> n) A p = defer n (defer m A p) (limit_profile (defer m A p) p)"
  using snd_conv
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_def_then_elect_elec_set:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  shows "elect (m \<triangleright> n) A p = elect n (defer m A p) (limit_profile (defer m A p) p) \<union> (elect m A p)"
  using Un_commute fst_conv
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_elim_one_red_def_set:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "eliminates 1 n" and
    "finite_profile A p" and
    "card (defer m A p) > 1"
  shows "defer (m \<triangleright> n) A p \<subset> defer m A p"
  using assms snd_conv def_presv_fin_prof single_elim_imp_red_def_set
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_def_set_sound:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p"
  shows "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
  using assms seq_comp_def_set_bounded
  by simp

lemma seq_comp_def_set_trans:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assumes
    "a \<in> (defer (m \<triangleright> n) A p)" and
    "electoral_module m \<and> electoral_module n" and
    "finite_profile A p"
  shows "a \<in> defer n (defer m A p) (limit_profile (defer m A p) p) \<and> a \<in> defer m A p"
  using seq_comp_def_set_bounded assms in_mono seq_comp_defers_def_set
  by (metis (no_types, opaque_lifting))

subsection \<open>Composition Rules\<close>

text \<open>
  The sequential composition preserves the non-blocking property.
\<close>

theorem seq_comp_presv_non_blocking[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    non_blocking_m: "non_blocking m" and
    non_blocking_n: "non_blocking n"
  shows "non_blocking (m \<triangleright> n)"
proof -
  fix
    A :: "'a set" and
    p :: "'a Profile"
  let ?input_sound = "A \<noteq> {} \<and> finite_profile A p"
  from non_blocking_m
  have "?input_sound \<longrightarrow> reject m A p \<noteq> A"
    unfolding non_blocking_def
    by simp
  with non_blocking_m
  have A_reject_diff: "?input_sound \<longrightarrow> A - reject m A p \<noteq> {}"
    using Diff_eq_empty_iff reject_in_alts subset_antisym
    unfolding non_blocking_def
    by metis
  from non_blocking_m
  have "?input_sound \<longrightarrow> well_formed A (m A p)"
    unfolding electoral_module_def non_blocking_def
    by simp
  hence "?input_sound \<longrightarrow> elect m A p \<union> defer m A p = A - reject m A p"
    using non_blocking_m elec_and_def_not_rej
    unfolding non_blocking_def
    by metis
  with A_reject_diff
  have "?input_sound \<longrightarrow> elect m A p \<union> defer m A p \<noteq> {}"
    by simp
  hence "?input_sound \<longrightarrow> (elect m A p \<noteq> {} \<or> defer m A p \<noteq> {})"
    by simp
  with non_blocking_m non_blocking_n
  show ?thesis
  proof (unfold non_blocking_def)
    assume
      emod_reject_m:
      "electoral_module m \<and> (\<forall> A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow> reject m A p \<noteq> A)" and
      emod_reject_n:
      "electoral_module n \<and> (\<forall> A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow> reject n A p \<noteq> A)"
    show
      "electoral_module (m \<triangleright> n) \<and> (\<forall> A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow> reject (m \<triangleright> n) A p \<noteq> A)"
    proof (safe)
      show "electoral_module (m \<triangleright> n)"
        using emod_reject_m emod_reject_n
        by simp
    next
      fix
        A :: "'a set" and
        p :: "'a Profile" and
        x :: "'a"
      assume
        fin_A: "finite A" and
        prof_A: "profile A p" and
        rej_mn: "reject (m \<triangleright> n) A p = A" and
        x_in_A: "x \<in> A"
      from emod_reject_m fin_A prof_A
      have fin_defer: "finite_profile (defer m A p) (limit_profile (defer m A p) p)"
        using def_presv_fin_prof
        by (metis (no_types))
      from emod_reject_m emod_reject_n fin_A prof_A
      have seq_elect:
        "elect (m \<triangleright> n) A p = elect n (defer m A p) (limit_profile (defer m A p) p) \<union> elect m A p"
        using seq_comp_def_then_elect_elec_set
        by metis
      from emod_reject_n emod_reject_m fin_A prof_A
      have def_limit: "defer (m \<triangleright> n) A p = defer n (defer m A p) (limit_profile (defer m A p) p)"
        using seq_comp_defers_def_set
        by metis
      from emod_reject_n emod_reject_m fin_A prof_A
      have "elect (m \<triangleright> n) A p \<union> defer (m \<triangleright> n) A p = A - reject (m \<triangleright> n) A p"
        using elec_and_def_not_rej seq_comp_sound
        by metis
      hence elect_def_disj:
        "elect n (defer m A p) (limit_profile (defer m A p) p) \<union>
          elect m A p \<union>
          defer n (defer m A p) (limit_profile (defer m A p) p) = {}"
        using def_limit seq_elect Diff_cancel rej_mn
        by auto
      have rej_def_eq_set:
        "defer n (defer m A p) (limit_profile (defer m A p) p) -
          defer n (defer m A p) (limit_profile (defer m A p) p) = {} \<longrightarrow>
            reject n (defer m A p) (limit_profile (defer m A p) p) =
              defer m A p"
        using elect_def_disj emod_reject_n fin_defer
        by (simp add: reject_not_elec_or_def)
      have
        "defer n (defer m A p) (limit_profile (defer m A p) p) -
          defer n (defer m A p) (limit_profile (defer m A p) p) = {} \<longrightarrow>
            elect m A p = elect m A p \<inter> defer m A p"
        using elect_def_disj
        by blast
      thus "x \<in> {}"
        using rej_def_eq_set result_disj fin_defer Diff_cancel Diff_empty
              emod_reject_m emod_reject_n fin_A prof_A reject_not_elec_or_def x_in_A
        by metis
    qed
  qed
qed

text \<open>
  Sequential composition preserves the non-electing property.
\<close>

theorem seq_comp_presv_non_electing[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    "non_electing m" and
    "non_electing n"
  shows "non_electing (m \<triangleright> n)"
proof (unfold non_electing_def, safe)
  have "electoral_module m \<and> electoral_module n"
    using assms
    unfolding non_electing_def
    by blast
  thus "electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    "finite A" and
    "profile A p" and
    "x \<in> elect (m \<triangleright> n) A p"
  thus "x \<in> {}"
    using assms
    unfolding non_electing_def
    using seq_comp_def_then_elect_elec_set def_presv_fin_prof Diff_empty Diff_partition
          empty_subsetI
    by metis
qed

text \<open>
  Composing an electoral module that defers exactly 1 alternative
  in sequence after an electoral module that is electing
  results (still) in an electing electoral module.
\<close>

theorem seq_comp_electing[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    def_one_m:  "defers 1 m" and
    electing_n: "electing n"
  shows "electing (m \<triangleright> n)"
proof -
  have "\<forall> A p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow> card (defer m A p) = 1"
    using def_one_m
    unfolding defers_def
    by blast
  hence def_m1_not_empty: "\<forall> A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> defer m A p \<noteq> {}"
    using One_nat_def Suc_leI card_eq_0_iff
          card_gt_0_iff zero_neq_one
    by metis
  thus ?thesis
  proof -
    obtain
      p :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> 'a set" and
      A :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> 'a Profile" where
      f_mod:
      "\<forall> m'.
        (\<not> electing m' \<or> electoral_module m' \<and>
          (\<forall> A' p'. (A' \<noteq> {} \<and> finite A' \<and> profile A' p') \<longrightarrow> elect m' A' p' \<noteq> {})) \<and>
        (electing m' \<or> \<not> electoral_module m' \<or> p m' \<noteq> {} \<and> finite (p m') \<and>
          profile (p m') (A m') \<and> elect m' (p m') (A m') = {})"
      unfolding electing_def
      by moura
    hence f_elect:
      "electoral_module n \<and>
        (\<forall> A p. (A \<noteq> {} \<and> finite A \<and> profile A p) \<longrightarrow> elect n A p \<noteq> {})"
      using electing_n
      by metis
    have def_card_one:
      "electoral_module m \<and>
        (\<forall> A p. (1 \<le> card A \<and> finite A \<and> profile A p) \<longrightarrow> card (defer m A p) = 1)"
      using def_one_m
      unfolding defers_def
      by blast
    hence "electoral_module (m \<triangleright> n)"
      using f_elect seq_comp_sound
      by metis
    with f_mod f_elect def_card_one
    show ?thesis
      using seq_comp_def_then_elect_elec_set def_presv_fin_prof
            def_m1_not_empty bot_eq_sup_iff
      by metis
  qed
qed

lemma def_lift_inv_seq_comp_help:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
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
  from monotone_m monotone_n
  have modules: "electoral_module m \<and> electoral_module n"
    unfolding defer_lift_invariance_def
    by simp
  hence "finite_profile A p \<longrightarrow> defer (m \<triangleright> n) A p \<subseteq> defer m A p"
    using seq_comp_def_set_bounded
    by metis
  moreover have profile_p: "lifted A p q a \<longrightarrow> finite_profile A p"
    unfolding lifted_def
    by simp
  ultimately have defer_subset: "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
    using def_and_lifted
    by blast
  hence mono_m: "m A p = m A q"
    using monotone_m def_and_lifted modules profile_p
          seq_comp_def_set_trans
    unfolding defer_lift_invariance_def
    by metis
  hence new_A_eq: "?new_Ap = ?new_Aq"
    by presburger
  have defer_eq: "defer (m \<triangleright> n) A p = defer n ?new_Ap ?new_p"
    using snd_conv
    unfolding sequential_composition.simps
    by metis
  have mono_n: "n ?new_Ap ?new_p = n ?new_Aq ?new_q"
  proof (cases)
    assume "lifted ?new_Ap ?new_p ?new_q a"
    thus ?thesis
      using defer_eq mono_m monotone_n def_and_lifted
      unfolding defer_lift_invariance_def
      by (metis (no_types, lifting))
  next
    assume unlifted_a: "\<not>lifted ?new_Ap ?new_p ?new_q a"
    from def_and_lifted
    have "finite_profile A q"
      unfolding lifted_def
      by simp
    with modules new_A_eq
    have fin_prof: "finite_profile ?new_Ap ?new_q"
      using def_presv_fin_prof
      by (metis (no_types))
    moreover from modules profile_p def_and_lifted
    have fin_prof: "finite_profile ?new_Ap ?new_p"
      using def_presv_fin_prof
      by (metis (no_types))
    moreover from defer_subset def_and_lifted
    have "a \<in> ?new_Ap"
      by blast
    moreover from def_and_lifted
    have eql_lengths: "length ?new_p = length ?new_q"
      unfolding lifted_def
      by simp
    ultimately have lifted_stmt:
      "(\<exists> i::nat. i < length ?new_p \<and>
          Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a) \<longrightarrow>
       (\<exists> i::nat. i < length ?new_p \<and>
          \<not> Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<and>
              (?new_p!i) \<noteq> (?new_q!i))"
      using unlifted_a
      unfolding lifted_def
      by (metis (no_types, lifting))
    from def_and_lifted modules
    have "\<forall> i. (0 \<le> i \<and> i < length ?new_p) \<longrightarrow>
            (Preference_Relation.lifted A (p!i) (q!i) a \<or> (p!i) = (q!i))"
      using limit_prof_presv_size
      unfolding Profile.lifted_def
      by metis
    with def_and_lifted modules mono_m
    have "\<forall> i. (0 \<le> i \<and> i < length ?new_p) \<longrightarrow>
            (Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<or>
              (?new_p!i) = (?new_q!i))"
      using limit_lifted_imp_eq_or_lifted defer_in_alts
            limit_prof_presv_size nth_map
      unfolding Profile.lifted_def limit_profile.simps
      by (metis (no_types, lifting))
    with lifted_stmt eql_lengths mono_m
    show ?thesis
      using leI not_less_zero nth_equalityI
      by metis
  qed
  from mono_m mono_n
  show ?thesis
    unfolding sequential_composition.simps
    by (metis (full_types))
qed

text \<open>
  Sequential composition preserves the property defer-lift-invariance.
\<close>

theorem seq_comp_presv_def_lift_inv[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    "defer_lift_invariance m" and
    "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<triangleright> n)"
  using assms def_lift_inv_seq_comp_help
        seq_comp_sound defer_lift_invariance_def
  by (metis (full_types))

text \<open>
  Composing a non-blocking, non-electing electoral module
  in sequence with an electoral module that defers exactly
  one alternative results in an electoral module that defers
  exactly one alternative.
\<close>

theorem seq_comp_def_one[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    non_blocking_m: "non_blocking m" and
    non_electing_m: "non_electing m" and
    def_1_n: "defers 1 n"
  shows "defers 1 (m \<triangleright> n)"
proof (unfold defers_def, safe)
  have "electoral_module m"
    using non_electing_m
    unfolding non_electing_def
    by simp
  moreover have "electoral_module n"
    using def_1_n
    unfolding defers_def
    by simp
  ultimately show "electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    pos_card: "1 \<le> card A" and
    fin_A: "finite A" and
    prof_A: "profile A p"
  from pos_card
  have "A \<noteq> {}"
    by auto
  with fin_A prof_A
  have "reject m A p \<noteq> A"
    using non_blocking_m
    unfolding non_blocking_def
    by simp
  hence "\<exists> a. a \<in> A \<and> a \<notin> reject m A p"
    using non_electing_m reject_in_alts fin_A prof_A
    unfolding non_electing_def
    by auto
  hence "defer m A p \<noteq> {}"
    using electoral_mod_defer_elem empty_iff non_electing_m fin_A prof_A
    unfolding non_electing_def
    by (metis (no_types))
  hence "card (defer m A p) \<ge> 1"
    using Suc_leI card_gt_0_iff fin_A prof_A non_blocking_m def_presv_fin_prof
    unfolding One_nat_def non_blocking_def
    by metis
  moreover have
    "\<forall> i m'. defers i m' =
      (electoral_module m' \<and>
        (\<forall> A' p'. (i \<le> card A' \<and> finite A' \<and> profile A' p') \<longrightarrow> card (defer m' A' p') = i))"
    unfolding defers_def
    by simp
  ultimately have "card (defer n (defer m A p) (limit_profile (defer m A p) p)) = 1"
    using def_1_n fin_A prof_A non_blocking_m def_presv_fin_prof
    unfolding non_blocking_def
    by metis
  moreover have "defer (m \<triangleright> n) A p = defer n (defer m A p) (limit_profile (defer m A p) p)"
    using seq_comp_defers_def_set
    by (metis (no_types, opaque_lifting))
  ultimately show "card (defer (m \<triangleright> n) A p) = 1"
    by simp
qed

text \<open>
  Composing a defer-lift invariant and a non-electing
  electoral module that defers exactly one alternative
  in sequence with an electing electoral module
  results in a monotone electoral module.
\<close>

theorem disj_compat_seq[simp]:
  fixes
    m :: "'a Electoral_Module" and
    m' :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    compatible: "disjoint_compatibility m n" and
    module_m': "electoral_module m'"
  shows "disjoint_compatibility (m \<triangleright> m') n"
proof (unfold disjoint_compatibility_def, safe)
  show "electoral_module (m \<triangleright> m')"
    using compatible module_m' seq_comp_sound
    unfolding disjoint_compatibility_def
    by metis
next
  show "electoral_module n"
    using compatible
    unfolding disjoint_compatibility_def
    by metis
next
  fix S :: "'a set"
  have modules:
    "electoral_module (m \<triangleright> m') \<and> electoral_module n"
    using compatible module_m' seq_comp_sound
    unfolding disjoint_compatibility_def
    by metis
  assume "finite S"
  then obtain A where rej_A:
    "A \<subseteq> S \<and>
      (\<forall> a \<in> A. indep_of_alt m S a \<and> (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
      (\<forall> a \<in> S - A. indep_of_alt n S a \<and> (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
    using compatible
    unfolding disjoint_compatibility_def
    by (metis (no_types, lifting))
  show
    "\<exists> A \<subseteq> S.
      (\<forall> a \<in> A. indep_of_alt (m \<triangleright> m') S a \<and>
        (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m') S p)) \<and>
      (\<forall> a \<in> S - A. indep_of_alt n S a \<and> (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
  proof
    have "\<forall> a p q. a \<in> A \<and> equiv_prof_except_a S p q a \<longrightarrow> (m \<triangleright> m') S p = (m \<triangleright> m') S q"
    proof (safe)
      fix
        a :: "'a" and
        p :: "'a Profile" and
        q :: "'a Profile"
      assume
        a_in_A: "a \<in> A" and
        lifting_equiv_p_q: "equiv_prof_except_a S p q a"
      hence eq_def: "defer m S p = defer m S q"
        using rej_A
        unfolding indep_of_alt_def
        by metis
      from lifting_equiv_p_q
      have profiles: "finite_profile S p \<and> finite_profile S q"
        unfolding equiv_prof_except_a_def
        by simp
      hence "(defer m S p) \<subseteq> S"
        using compatible defer_in_alts
        unfolding disjoint_compatibility_def
        by metis
      hence "limit_profile (defer m S p) p = limit_profile (defer m S q) q"
        using rej_A DiffD2 a_in_A lifting_equiv_p_q compatible defer_not_elec_or_rej
              profiles negl_diff_imp_eq_limit_prof
        unfolding disjoint_compatibility_def eq_def
        by (metis (no_types, lifting))
      with eq_def
      have "m' (defer m S p) (limit_profile (defer m S p) p) =
              m' (defer m S q) (limit_profile (defer m S q) q)"
        by simp
      moreover have "m S p = m S q"
        using rej_A a_in_A lifting_equiv_p_q
        unfolding indep_of_alt_def
        by metis
      ultimately show "(m \<triangleright> m') S p = (m \<triangleright> m') S q"
        unfolding sequential_composition.simps
        by (metis (full_types))
    qed
    moreover have "\<forall> a' \<in> A. \<forall> p'. finite_profile S p' \<longrightarrow> a' \<in> reject (m \<triangleright> m') S p'"
      using rej_A UnI1 prod.sel
      unfolding sequential_composition.simps
      by metis
    ultimately show
      "A \<subseteq> S \<and>
        (\<forall> a' \<in> A. indep_of_alt (m \<triangleright> m') S a' \<and>
          (\<forall> p'. finite_profile S p' \<longrightarrow> a' \<in> reject (m \<triangleright> m') S p')) \<and>
        (\<forall> a' \<in> S - A. indep_of_alt n S a' \<and>
          (\<forall> p'. finite_profile S p' \<longrightarrow> a' \<in> reject n S p'))"
      using rej_A indep_of_alt_def modules
      by (metis (mono_tags, lifting))
  qed
qed

text \<open>
  Composing a defer-lift invariant and a non-electing
  electoral module that defers exactly one alternative
  in sequence with an electing electoral module
  results in a monotone electoral module.
\<close>

theorem seq_comp_mono[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    def_monotone_m: "defer_lift_invariance m" and
    non_ele_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n"
  shows "monotonicity (m \<triangleright> n)"
proof (unfold monotonicity_def, safe)
  have "electoral_module m"
    using non_ele_m
    unfolding non_electing_def
    by simp
  moreover have "electoral_module n"
    using electing_n
    unfolding electing_def
    by simp
  ultimately show "electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    w :: "'a"
  assume
    elect_w_in_p: "w \<in> elect (m \<triangleright> n) A p" and
    lifted_w: "Profile.lifted A p q w"
  thus "w \<in> elect (m \<triangleright> n) A q"
    unfolding lifted_def
    using seq_comp_def_then_elect lifted_w assms
    unfolding defer_lift_invariance_def
    by metis
qed

text \<open>
  Composing a defer-invariant-monotone electoral module in sequence before
  a non-electing, defer-monotone electoral module that defers exactly
  1 alternative results in a defer-lift-invariant electoral module.
\<close>

theorem def_inv_mono_imp_def_lift_inv[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    strong_def_mon_m: "defer_invariant_monotonicity m" and
    non_electing_n: "non_electing n" and
    defers_1: "defers 1 n" and
    defer_monotone_n: "defer_monotonicity n"
  shows "defer_lift_invariance (m \<triangleright> n)"
proof (unfold defer_lift_invariance_def, safe)
  have "electoral_module m"
    using strong_def_mon_m
    unfolding defer_invariant_monotonicity_def
    by metis
  moreover have "electoral_module n"
    using defers_1
    unfolding defers_def
    by metis
  ultimately show "electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume
    defer_a_p: "a \<in> defer (m \<triangleright> n) A p" and
    lifted_a: "Profile.lifted A p q a"
  have non_electing_m: "non_electing m"
    using strong_def_mon_m
    unfolding defer_invariant_monotonicity_def
    by simp
  have electoral_mod_m: "electoral_module m"
    using strong_def_mon_m
    unfolding defer_invariant_monotonicity_def
    by metis
  have electoral_mod_n: "electoral_module n"
    using defers_1
    unfolding defers_def
    by metis
  have finite_profile_p: "finite_profile A p"
    using lifted_a
    unfolding Profile.lifted_def
    by simp
  have finite_profile_q: "finite_profile A q"
    using lifted_a
    unfolding Profile.lifted_def
    by simp
  have "1 \<le> card A"
    using Profile.lifted_def card_eq_0_iff emptyE less_one lifted_a linorder_le_less_linear
    by metis
  hence n_defers_exactly_one_p: "card (defer n A p) = 1"
    using finite_profile_p defers_1
    unfolding defers_def
    by (metis (no_types))
  have fin_prof_def_m_q: "finite_profile (defer m A q) (limit_profile (defer m A q) q)"
    using def_presv_fin_prof electoral_mod_m finite_profile_q
    by (metis (no_types))
  have def_seq_m_n_q: "defer (m \<triangleright> n) A q = defer n (defer m A q) (limit_profile (defer m A q) q)"
    using seq_comp_defers_def_set
    by simp
  have fin_prof_def_m: "finite_profile (defer m A p) (limit_profile (defer m A p) p)"
    using def_presv_fin_prof electoral_mod_m finite_profile_p
    by (metis (no_types))
  hence fin_prof_seq_comp_m_n:
    "finite_profile (defer n (defer m A p) (limit_profile (defer m A p) p))
          (limit_profile (defer n (defer m A p) (limit_profile (defer m A p) p))
            (limit_profile (defer m A p) p))"
    using def_presv_fin_prof electoral_mod_n
    by (metis (no_types))
  have a_non_empty: "a \<notin> {}"
    by simp
  have def_seq_m_n: "defer (m \<triangleright> n) A p = defer n (defer m A p) (limit_profile (defer m A p) p)"
    using seq_comp_defers_def_set
    by simp
  have "1 \<le> card (defer n (defer m A p) (limit_profile (defer m A p) p))"
    using a_non_empty card_gt_0_iff def_presv_fin_prof defer_a_p electoral_mod_n
          fin_prof_def_m seq_comp_defers_def_set One_nat_def Suc_leI
    by (metis (no_types))
  hence "card (defer n (defer n (defer m A p) (limit_profile (defer m A p) p))
          (limit_profile (defer n (defer m A p) (limit_profile (defer m A p) p))
            (limit_profile (defer m A p) p))) = 1"
    using n_defers_exactly_one_p fin_prof_seq_comp_m_n defers_1 defers_def
    by blast
  hence defer_seq_m_n_eq_one: "card (defer (m \<triangleright> n) A p) = 1"
    using One_nat_def Suc_leI a_non_empty card_gt_0_iff def_seq_m_n defers_def defer_a_p
          defers_1 electoral_mod_m fin_prof_def_m finite_profile_p seq_comp_def_set_trans
    by metis
  hence def_seq_m_n_eq_a: "defer (m \<triangleright> n) A p = {a}"
    using defer_a_p is_singleton_altdef is_singleton_the_elem singletonD
    by (metis (no_types))
  show "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof (cases)
    assume "defer m A q \<noteq> defer m A p"
    hence "defer m A q = {a}"
      using defer_a_p electoral_mod_n finite_profile_p lifted_a seq_comp_def_set_trans
            strong_def_mon_m
      unfolding defer_invariant_monotonicity_def
      by (metis (no_types))
    moreover from this
    have "(a \<in> defer m A p) \<longrightarrow> card (defer (m \<triangleright> n) A q) = 1"
      using card_eq_0_iff card_insert_disjoint defers_1 electoral_mod_m empty_iff order_refl
            finite.emptyI seq_comp_defers_def_set def_presv_fin_prof finite_profile_q
      unfolding One_nat_def defers_def
      by metis
    moreover have "a \<in> defer m A p"
      using electoral_mod_m electoral_mod_n defer_a_p seq_comp_def_set_bounded finite_profile_p
            finite_profile_q
      by blast
    ultimately have "defer (m \<triangleright> n) A q = {a}"
      using Collect_mem_eq card_1_singletonE empty_Collect_eq insertCI subset_singletonD
            def_seq_m_n_q defer_in_alts electoral_mod_n fin_prof_def_m_q
      by (metis (no_types, lifting))
    hence "defer (m \<triangleright> n) A p = defer (m \<triangleright> n) A q"
      using def_seq_m_n_eq_a
      by presburger
    moreover have "elect (m \<triangleright> n) A p = elect (m \<triangleright> n) A q"
      using fin_prof_def_m fin_prof_def_m_q finite_profile_p finite_profile_q non_electing_def
            non_electing_m non_electing_n seq_comp_def_then_elect_elec_set
      by metis
    ultimately show ?thesis
      using electoral_mod_m electoral_mod_n eq_def_and_elect_imp_eq
            finite_profile_p finite_profile_q seq_comp_sound
      by (metis (no_types))
  next
    assume "\<not> (defer m A q \<noteq> defer m A p)"
    hence def_eq: "defer m A q = defer m A p"
      by presburger
    have "elect m A p = {}"
      using finite_profile_p non_electing_m
      unfolding non_electing_def
      by simp
    moreover have "elect m A q = {}"
      using finite_profile_q non_electing_m
      unfolding non_electing_def
      by simp
    ultimately have elect_m_equal: "elect m A p = elect m A q"
      by simp
    have "(limit_profile (defer m A p) p) = (limit_profile (defer m A p) q) \<or>
            lifted (defer m A q) (limit_profile (defer m A p) p) (limit_profile (defer m A p) q) a"
      using def_eq defer_in_alts electoral_mod_m lifted_a finite_profile_q limit_prof_eq_or_lifted
      by metis
    hence "defer (m \<triangleright> n) A p = defer (m \<triangleright> n) A q"
      using a_non_empty card_1_singletonE def_eq def_seq_m_n def_seq_m_n_q defer_a_p
            defer_monotone_n defer_monotonicity_def defer_seq_m_n_eq_one defers_1 defers_def
            electoral_mod_m fin_prof_def_m_q finite_profile_p insertE seq_comp_def_card_bounded
      by (metis (no_types, lifting))
    moreover from this
    have "reject (m \<triangleright> n) A p = reject (m \<triangleright> n) A q"
      using electoral_mod_m electoral_mod_n finite_profile_p finite_profile_q non_electing_def
            non_electing_m non_electing_n eq_def_and_elect_imp_eq seq_comp_presv_non_electing
      by (metis (no_types))
    ultimately have "snd ((m \<triangleright> n) A p) = snd ((m \<triangleright> n) A q)"
      using prod_eqI
      by metis
    moreover have "elect (m \<triangleright> n) A p = elect (m \<triangleright> n) A q"
      using fin_prof_def_m fin_prof_def_m_q non_electing_n finite_profile_p finite_profile_q
            non_electing_def def_eq elect_m_equal prod.sel(1)
      unfolding sequential_composition.simps
      by (metis (no_types))
    ultimately show "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
      using prod_eqI
      by metis
  qed
qed

end

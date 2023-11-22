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

fun sequential_composition :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 
                               ('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
                               ('a, 'v, 'a Result) Electoral_Module" where
  "sequential_composition m n V A p =
    (let new_A = defer V m A p;
        new_p = limit_profile new_A p in (
                  (elect V m A p) \<union> (elect V n new_A new_p),
                  (reject V m A p) \<union> (reject V n new_A new_p),
                  defer V n new_A new_p))"

abbreviation sequence ::
  "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module 
    \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module"
     (infix "\<triangleright>" 50) where
  "m \<triangleright> n == sequential_composition m n"

fun sequential_composition' :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 
        ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "sequential_composition' m n V A p =
    (let (m_e, m_r, m_d) = m V A p; new_A = m_d;
        new_p = limit_profile new_A p;
        (n_e, n_r, n_d) = n V new_A new_p in
            (m_e \<union> n_e, m_r \<union> n_r, n_d))"

lemma seq_comp_presv_only_voters_vote:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes 
    "only_voters_vote m \<and> only_voters_vote n"
  shows "only_voters_vote (m \<triangleright> n)"
proof (unfold only_voters_vote_def, clarify)
  fix 
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  assume coincide: "\<forall>v\<in>V. p v = p' v"
  hence eq: "m V A p = m V A p' \<and> n V A p = n V A p'" 
    using assms 
    unfolding only_voters_vote_def 
    by blast
  hence coincide_limit: 
    "\<forall> v \<in> V. limit_profile (defer V m A p) p v = limit_profile (defer V m A p') p' v"
    using coincide
    by simp
  moreover have
    "elect V m A p \<union> elect V n (defer V m A p) (limit_profile (defer V m A p) p)
      = elect V m A p' \<union> elect V n (defer V m A p') (limit_profile (defer V m A p') p')"
    using assms eq coincide_limit
    unfolding only_voters_vote_def
    by metis
  moreover have 
    "reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p)
      = reject V m A p' \<union> reject V n (defer V m A p') (limit_profile (defer V m A p') p')"
    using assms eq coincide_limit
    unfolding only_voters_vote_def
    by metis
  moreover have 
    "defer V n (defer V m A p) (limit_profile (defer V m A p) p)
      = defer V n (defer V m A p') (limit_profile (defer V m A p') p')"
    using assms eq coincide_limit
    unfolding only_voters_vote_def
    by metis
  ultimately show "(m \<triangleright> n) V A p = (m \<triangleright> n) V A p'"
    by (metis sequential_composition.simps)
qed

lemma seq_comp_presv_disj:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes module_m: "social_choice_result.electoral_module m" and
          module_n: "social_choice_result.electoral_module n" and
          f_prof:  "finite_profile V A p"
  shows "disjoint3 ((m \<triangleright> n) V A p)"
proof -
  let ?new_A = "defer V m A p"
  let ?new_p = "limit_profile ?new_A p"
  have fin_def: "finite (defer V m A p)"
    using def_presv_fin_prof f_prof module_m
    by metis
  have prof_def_lim: "profile V (defer V m A p) (limit_profile (defer V m A p) p)"
    using def_presv_fin_prof f_prof module_m
    by metis
  have defer_in_A:
    "\<forall> A' V' p' m' a.
      (profile V' A' p' \<and> finite A' \<and> finite V' \<and> 
       social_choice_result.electoral_module m' \<and>
       (a::'a) \<in> defer V' m' A' p') \<longrightarrow>
      a \<in> A'"
    using UnCI result_presv_alts
    by fastforce
  from module_m f_prof
  have disjoint_m: "disjoint3 (m V A p)"
    unfolding social_choice_result.electoral_module_def well_formed_soc_choice.simps
    by blast
  from module_m module_n def_presv_fin_prof f_prof
  have disjoint_n: "disjoint3 (n V ?new_A ?new_p)"
    unfolding social_choice_result.electoral_module_def well_formed_soc_choice.simps
    by metis
  have disj_n:
    "elect V m A p \<inter> reject V m A p = {} \<and>
      elect V m A p \<inter> defer V m A p = {} \<and>
      reject V m A p \<inter> defer V m A p = {}"
    using f_prof module_m
    by (simp add: result_disj)
  have "reject V n (defer V m A p) (limit_profile (defer V m A p) p) \<subseteq> defer V m A p"
    using def_presv_fin_prof reject_in_alts f_prof module_m module_n
    by metis
  with disjoint_m module_m module_n f_prof
  have elect_reject_diff: "elect V m A p \<inter> reject V n ?new_A ?new_p = {}"
    using disj_n
    by blast
  from f_prof module_m module_n
  have elec_n_in_def_m:
    "elect V n (defer V m A p) (limit_profile (defer V m A p) p) \<subseteq> defer V m A p"
    using def_presv_fin_prof elect_in_alts
    by metis
  have elect_defer_diff: "elect V m A p \<inter> defer V n ?new_A ?new_p = {}"
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
      using defer_in_A disj_n fin_def module_n prof_def_lim f_prof 
      by fastforce
  qed
  have rej_intersect_new_elect_empty: "reject V m A p \<inter> elect V n ?new_A ?new_p = {}"
    using disj_n disjoint_m disjoint_n def_presv_fin_prof f_prof
          module_m module_n elec_n_in_def_m
    by blast
  have "(elect V m A p \<union> elect V n ?new_A ?new_p) \<inter>
          (reject V m A p \<union> reject V n ?new_A ?new_p) = {}"
  proof (safe)
    fix x :: "'a"
    assume
      "x \<in> elect V m A p" and
      "x \<in> reject V m A p"
    hence "x \<in> elect V m A p \<inter> reject V m A p"
      by simp
    thus "x \<in> {}"
      using disj_n
      by simp
  next
    fix x :: "'a"
    assume
      "x \<in> elect V m A p" and
      "x \<in> reject V n (defer V m A p)
        (limit_profile (defer V m A p) p)"
    thus "x \<in> {}"
      using elect_reject_diff
      by blast
  next
    fix x :: "'a"
    assume
      "x \<in> elect V n (defer V m A p) (limit_profile (defer V m A p) p)" and
      "x \<in> reject V m A p"
    thus "x \<in> {}"
      using rej_intersect_new_elect_empty
      by blast
  next
    fix x :: "'a"
    assume
      "x \<in> elect V n (defer V m A p) (limit_profile (defer V m A p) p)" and
      "x \<in> reject V n (defer V m A p) (limit_profile (defer V m A p) p)"
    thus "x \<in> {}"
      using disjoint_iff_not_equal fin_def module_n prof_def_lim result_disj f_prof
      by metis
  qed
  moreover have
    "(elect V m A p \<union> elect V n ?new_A ?new_p) \<inter> (defer V n ?new_A ?new_p) = {}"
    using Int_Un_distrib2 Un_empty elect_defer_diff fin_def module_n
          prof_def_lim result_disj f_prof
    by (metis (no_types))
  moreover have
    "(reject V m A p \<union> reject V n ?new_A ?new_p) \<inter> (defer V n ?new_A ?new_p) = {}"
  proof (safe)
    fix x :: "'a"
    assume
      x_in_def: "x \<in> defer V n (defer V m A p) (limit_profile (defer V m A p) p)" and
      x_in_rej: "x \<in> reject V m A p"
    from x_in_def
    have "x \<in> defer V m A p"
      using defer_in_A fin_def module_n prof_def_lim f_prof
      by blast
    with x_in_rej
    have "x \<in> reject V m A p \<inter> defer V m A p"
      by fastforce
    thus "x \<in> {}"
      using disj_n
      by blast
  next
    fix x :: "'a"
    assume
      "x \<in> defer V n (defer V m A p) (limit_profile (defer V m A p) p)" and
      "x \<in> reject V n (defer V m A p) (limit_profile (defer V m A p) p)"
    thus "x \<in> {}"
      using fin_def module_n prof_def_lim reject_not_elec_or_def f_prof
      by fastforce
  qed
  ultimately have
    "disjoint3 (elect V m A p \<union> elect V n ?new_A ?new_p,
                reject V m A p \<union> reject V n ?new_A ?new_p,
                defer V n ?new_A ?new_p)"
    by simp
  thus ?thesis
    unfolding sequential_composition.simps
    by metis
qed

lemma seq_comp_presv_alts:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes module_m: "social_choice_result.electoral_module m" and
          module_n: "social_choice_result.electoral_module n" and
          f_prof:  "finite_profile V A p"
  shows "set_equals_partition A ((m \<triangleright> n) V A p)"
proof -
  let ?new_A = "defer V m A p"
  let ?new_p = "limit_profile ?new_A p"
  have elect_reject_diff: "elect V m A p \<union> reject V m A p \<union> ?new_A = A"
    using module_m f_prof
    by (simp add: result_presv_alts)
  have "elect V n ?new_A ?new_p \<union>
          reject V n ?new_A ?new_p \<union>
            defer V n ?new_A ?new_p = ?new_A"
    using module_m module_n f_prof def_presv_fin_prof result_presv_alts
    by metis
  hence "(elect V m A p \<union> elect V n ?new_A ?new_p) \<union>
          (reject V m A p \<union> reject V n ?new_A ?new_p) \<union>
            defer V n ?new_A ?new_p = A"
    using elect_reject_diff
    by blast
  hence "set_equals_partition A
          (elect V m A p \<union> elect V n ?new_A ?new_p,
            reject V m A p \<union> reject V n ?new_A ?new_p,
              defer V n ?new_A ?new_p)"
    by simp
  thus ?thesis
    unfolding sequential_composition.simps
    by metis
qed

lemma seq_comp_alt_eq[code]: "sequential_composition = sequential_composition'"
proof (unfold sequential_composition'.simps sequential_composition.simps)
  have "\<forall> m n V A E.
      (case m V A E of (e, r, d) \<Rightarrow>
        case n V d (limit_profile d E) of (e', r', d') \<Rightarrow>
        (e \<union> e', r \<union> r', d')) =
          (elect V m A E \<union> elect V n (defer V m A E) (limit_profile (defer V m A E) E),
            reject V m A E \<union> reject V n (defer V m A E) (limit_profile (defer V m A E) E),
            defer V n (defer V m A E) (limit_profile (defer V m A E) E))"
    using case_prod_beta'
    by (metis (no_types, lifting))
  thus
    "(\<lambda> m n V A p.
        let A' = defer V m A p; p' = limit_profile A' p in
      (elect V m A p \<union> elect V n A' p', reject V m A p \<union> reject V n A' p', defer V n A' p')) =
      (\<lambda> m n V A pr.
        let (e, r, d) = m V A pr; A' = d; p' = limit_profile A' pr;
          (e', r', d') = n V A' p' in
      (e \<union> e', r \<union> r', d'))"
    by metis
qed

subsection \<open>Soundness\<close>

theorem seq_comp_sound[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    "social_choice_result.electoral_module m" and
    "social_choice_result.electoral_module n"
  shows "social_choice_result.electoral_module (m \<triangleright> n)"
proof (unfold social_choice_result.electoral_module_def, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    fin_A: "finite A" and
    fin_V: "finite V" and
    prof_A: "profile V A p"
  have "\<forall> r. well_formed_soc_choice (A::'a set) r =
          (disjoint3 r \<and> set_equals_partition A r)"
    by simp
  thus "well_formed_soc_choice A ((m \<triangleright> n) V A p)"
    using assms seq_comp_presv_disj seq_comp_presv_alts fin_A fin_V prof_A
    by metis
qed

subsection \<open>Lemmas\<close>

lemma seq_comp_dec_only_def:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a,'v) Profile"
  assumes
    module_m: "social_choice_result.electoral_module m" and
    module_n: "social_choice_result.electoral_module n" and
    f_prof: "finite_profile V A p" and
    empty_defer: "defer V m A p = {}"
  shows "(m \<triangleright> n) V A p =  m V A p"
proof -
  have                     
    "\<forall> m' A' V' p'.
      (social_choice_result.electoral_module m' \<and> finite_profile V' A' p') \<longrightarrow>
        finite_profile V' (defer V' m' A' p') (limit_profile (defer V' m' A' p') p')"
    using def_presv_fin_prof
    by metis
  hence prof_no_alt: "finite_profile V {} (limit_profile (defer V m A p) p)"
    using empty_defer f_prof module_m
    by metis
  show ?thesis
  proof
      have
      "(elect V m A p) \<union> (elect V n (defer V m A p) (limit_profile (defer V m A p) p)) =
          elect V m A p"
      using elect_in_alts[of n "defer V m A p" V "(limit_profile (defer V m A p) p)"]
            empty_defer module_n f_prof prof_no_alt
      by auto
    thus "elect V (m \<triangleright> n) A p = elect V m A p"
      using fst_conv
      unfolding sequential_composition.simps
      by metis
  next
    have rej_empty:
      "\<forall> m' V' p'.
        (social_choice_result.electoral_module m' \<and> finite V' 
          \<and> profile V' ({}::'a set) p') \<longrightarrow> reject V' m' {} p' = {}"
      using bot.extremum_uniqueI infinite_imp_nonempty reject_in_alts
      by metis
    have "(reject V m A p, defer V n {} (limit_profile {} p)) = snd (m V A p)"
      using bot.extremum_uniqueI defer_in_alts empty_defer
            infinite_imp_nonempty module_n prod.collapse prof_no_alt
      by (metis (no_types))
    thus "snd ((m \<triangleright> n) V A p) = snd (m V A p)"
      using rej_empty empty_defer module_n prof_no_alt f_prof
      by fastforce
  qed
qed

lemma seq_comp_def_then_elect:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    n_electing_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n" and
    f_prof: "finite_profile V A p"
  shows "elect V (m \<triangleright> n) A p = defer V m A p"
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
  have ele: "elect V m A p = {}"
    unfolding non_electing_def
    by simp
  from non_empty_A def_one_m f_prof finite
  have def_card: "card (defer V m A p) = 1"
    unfolding defers_def
    by (simp add: Suc_leI card_gt_0_iff)
  with n_electing_m f_prof
  have def: "\<exists> a \<in> A. defer V m A p = {a}"
    using card_1_singletonE defer_in_alts singletonI subsetCE
    unfolding non_electing_def
    by metis
  from ele def n_electing_m
  have rej: "\<exists> a \<in> A. reject V m A p = A - {a}"
    using Diff_empty def_one_m f_prof reject_not_elec_or_def
    unfolding defers_def
    by metis
  from ele rej def n_electing_m f_prof
  have res_m: "\<exists> a \<in> A. m V A p = ({}, A - {a}, {a})"
    using Diff_empty combine_ele_rej_def reject_not_elec_or_def
    unfolding non_electing_def
    by metis
  hence "\<exists> a \<in> A. elect V (m \<triangleright> n) A p = elect V n {a} (limit_profile {a} p)"
    using prod.sel(1, 2) sup_bot.left_neutral
    unfolding sequential_composition.simps
    by metis
  with def_card def electing_n n_electing_m f_prof
  have "\<exists> a \<in> A. elect V (m \<triangleright> n) A p = {a}"
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
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "social_choice_result.electoral_module n" and
    "finite_profile V A p"
  shows "card (defer V (m \<triangleright> n) A p) \<le> card (defer V m A p)"
  using card_mono defer_in_alts assms def_presv_fin_prof snd_conv
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_def_set_bounded:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "social_choice_result.electoral_module n" and
    "finite_profile V A p"
  shows "defer V (m \<triangleright> n) A p \<subseteq> defer V m A p"
  using defer_in_alts assms prod.sel(2) def_presv_fin_prof
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_defers_def_set:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "defer V (m \<triangleright> n) A p = defer V n (defer V m A p) (limit_profile (defer V m A p) p)"
  using snd_conv
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_def_then_elect_elec_set:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "elect V (m \<triangleright> n) A p =
            elect V n (defer V m A p) (limit_profile (defer V m A p) p) \<union> (elect V m A p)"
  using Un_commute fst_conv
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_elim_one_red_def_set:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "eliminates 1 n" and
    "finite_profile V A p" and
    "card (defer V m A p) > 1"
  shows "defer V (m \<triangleright> n) A p \<subset> defer V m A p"
  using assms snd_conv def_presv_fin_prof single_elim_imp_red_def_set
  unfolding sequential_composition.simps
  by metis

lemma seq_comp_def_set_sound:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "social_choice_result.electoral_module n" and
    "finite_profile V A p"
  shows "defer V (m \<triangleright> n) A p \<subseteq> defer V m A p"
  using assms seq_comp_def_set_bounded
  by simp

lemma seq_comp_def_set_trans:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "a \<in> (defer V (m \<triangleright> n) A p)" and
    "social_choice_result.electoral_module m \<and> social_choice_result.electoral_module n" and
    "finite_profile V A p"
  shows "a \<in> defer V n (defer V m A p) (limit_profile (defer V m A p) p) \<and>
          a \<in> defer V m A p"
  using seq_comp_def_set_bounded assms in_mono seq_comp_defers_def_set
  by (metis (no_types, opaque_lifting))

subsection \<open>Composition Rules\<close>

text \<open>
  The sequential composition preserves the non-blocking property.
\<close>

theorem seq_comp_presv_non_blocking[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    non_blocking_m: "non_blocking m" and
    non_blocking_n: "non_blocking n"
  shows "non_blocking (m \<triangleright> n)"
proof -
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  let ?input_sound = "A \<noteq> {} \<and> finite_profile V A p"
  from non_blocking_m
  have "?input_sound \<longrightarrow> reject V m A p \<noteq> A"
    unfolding non_blocking_def
    by simp
  with non_blocking_m
  have A_reject_diff: "?input_sound \<longrightarrow> A - reject V m A p \<noteq> {}"
    using Diff_eq_empty_iff reject_in_alts subset_antisym
    unfolding non_blocking_def
    by metis
  from non_blocking_m
  have "?input_sound \<longrightarrow> well_formed_soc_choice A (m V A p)"
    unfolding social_choice_result.electoral_module_def non_blocking_def
    by simp
  hence "?input_sound \<longrightarrow> elect V m A p \<union> defer V m A p = A - reject V m A p"
    using non_blocking_m elec_and_def_not_rej
    unfolding non_blocking_def
    by metis
  with A_reject_diff
  have "?input_sound \<longrightarrow> elect V m A p \<union> defer V m A p \<noteq> {}"
    by simp
  hence "?input_sound \<longrightarrow> (elect V m A p \<noteq> {} \<or> defer V m A p \<noteq> {})"
    by simp
  with non_blocking_m non_blocking_n
  show ?thesis
  proof (unfold non_blocking_def)
    assume
      emod_reject_m:
      "social_choice_result.electoral_module m \<and>
        (\<forall> A V p. A \<noteq> {} \<and> finite_profile V A p \<longrightarrow> reject V m A p \<noteq> A)" and
      emod_reject_n:
      "social_choice_result.electoral_module n \<and>
        (\<forall> A V p. A \<noteq> {} \<and> finite_profile V A p \<longrightarrow> reject V n A p \<noteq> A)"
    show
      "social_choice_result.electoral_module (m \<triangleright> n) \<and>
        (\<forall> A V p. A \<noteq> {} \<and> finite_profile V A p \<longrightarrow> reject V (m \<triangleright> n) A p \<noteq> A)"
    proof (safe)
      show "social_choice_result.electoral_module (m \<triangleright> n)"
        using emod_reject_m emod_reject_n
        by simp
    next
      fix
        A :: "'a set" and
        V :: "'v set" and
        p :: "('a, 'v) Profile" and
        x :: "'a"
      assume
        fin_A: "finite A" and
        fin_V: "finite V" and
        prof_A: "profile V A p" and
        rej_mn: "reject V (m \<triangleright> n) A p = A" and
        x_in_A: "x \<in> A"
      from emod_reject_m fin_A prof_A fin_V
      have fin_defer: "finite_profile V (defer V m A p) (limit_profile (defer V m A p) p)"
        using def_presv_fin_prof
        by (metis (no_types))
      from emod_reject_m emod_reject_n fin_A prof_A
      have seq_elect:
        "elect V (m \<triangleright> n) A p =
          elect V n (defer V m A p) (limit_profile (defer V m A p) p) \<union> elect V m A p"
        using seq_comp_def_then_elect_elec_set
        by metis
      from emod_reject_n emod_reject_m fin_A prof_A
      have def_limit:
        "defer V (m \<triangleright> n) A p = defer V n (defer V m A p) (limit_profile (defer V m A p) p)"
        using seq_comp_defers_def_set
        by metis
      from emod_reject_n emod_reject_m fin_A prof_A
      have "elect V (m \<triangleright> n) A p \<union> defer V (m \<triangleright> n) A p = A - reject V (m \<triangleright> n) A p"
        using elec_and_def_not_rej seq_comp_sound fin_V
        by metis
      hence elect_def_disj:
        "elect V n (defer V m A p) (limit_profile (defer V m A p) p) \<union>
          elect V m A p \<union>
          defer V n (defer V m A p) (limit_profile (defer V m A p) p) = {}"
        using def_limit seq_elect Diff_cancel rej_mn
        by auto
      have rej_def_eq_set:
        "defer V n (defer V m A p) (limit_profile (defer V m A p) p) -
          defer V n (defer V m A p) (limit_profile (defer V m A p) p) = {} \<longrightarrow>
            reject V n (defer V m A p) (limit_profile (defer V m A p) p) =
              defer V m A p"
        using elect_def_disj emod_reject_n fin_defer
        by (simp add: reject_not_elec_or_def)
      have
        "defer V n (defer V m A p) (limit_profile (defer V m A p) p) -
          defer V n (defer V m A p) (limit_profile (defer V m A p) p) = {} \<longrightarrow>
            elect V m A p = elect V m A p \<inter> defer V m A p"
        using elect_def_disj
        by blast
      thus "x \<in> {}"
        using rej_def_eq_set result_disj fin_defer Diff_cancel Diff_empty fin_A prof_A
              emod_reject_m emod_reject_n reject_not_elec_or_def x_in_A
        by metis
    qed
  qed
qed

text \<open>
  Sequential composition preserves the non-electing property.
\<close>

theorem seq_comp_presv_non_electing[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    "non_electing m" and
    "non_electing n"
  shows "non_electing (m \<triangleright> n)"
proof (unfold non_electing_def, safe)
  have "social_choice_result.electoral_module m \<and> social_choice_result.electoral_module n"
    using assms
    unfolding non_electing_def
    by blast
  thus "social_choice_result.electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x :: "'a"
  assume
    "finite A" and
    "finite V" and
    "profile V A p" and
    "x \<in> elect V (m \<triangleright> n) A p"
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
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    def_one_m:  "defers 1 m" and
    electing_n: "electing n"
  shows "electing (m \<triangleright> n)"
proof -
  have "\<forall> A V p. (card A \<ge> 1 \<and> finite_profile V A p) \<longrightarrow> card (defer V m A p) = 1"
    using def_one_m
    unfolding defers_def
    by blast
  hence def_m1_not_empty:
    "\<forall> A V p. (A \<noteq> {} \<and> finite_profile V A p) \<longrightarrow> defer V m A p \<noteq> {}"
    using One_nat_def Suc_leI card_eq_0_iff card_gt_0_iff zero_neq_one
    by metis
  thus ?thesis
  proof -
    have "\<forall> m'.
          (\<not> electing m' \<or> social_choice_result.electoral_module m' \<and>
            (\<forall> A' V' p'. (A' \<noteq> {} \<and> finite_profile V' A' p') 
              \<longrightarrow> elect V' m' A' p' \<noteq> {})) \<and> 
            (electing m' \<or> \<not> social_choice_result.electoral_module m' \<or> (\<exists> A V p. (A \<noteq> {} \<and> 
              finite_profile V A p \<and> elect V m' A p = {})))"
      unfolding electing_def
      by blast
    hence "\<forall> m'.
          (\<not> electing m' \<or> social_choice_result.electoral_module m' \<and>
            (\<forall> A' V' p'. (A' \<noteq> {} \<and> finite_profile V' A' p') 
              \<longrightarrow> elect V' m' A' p' \<noteq> {})) \<and> 
          (\<exists> A V p. (electing m' \<or> \<not> social_choice_result.electoral_module m' \<or> A \<noteq> {} \<and> 
            finite_profile V A p \<and> elect V m' A p = {}))"
      by simp
    then obtain
      A :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a set" and
      V :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'v set" and
      p :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> ('a, 'v) Profile" where
      f_mod:
       "\<forall> m'::('a, 'v, 'a Result) Electoral_Module.
        (\<not> electing m' \<or> social_choice_result.electoral_module m' \<and>
          (\<forall> A' V' p'. (A' \<noteq> {} \<and> finite_profile V' A' p') 
            \<longrightarrow> elect V' m' A' p' \<noteq> {})) \<and> 
          (electing m' \<or> \<not> social_choice_result.electoral_module m' \<or> A m' \<noteq> {} \<and> 
          finite_profile (V m') (A m') (p m') \<and> elect (V m') m' (A m') (p m') = {})"
      by metis
    hence f_elect:
      "social_choice_result.electoral_module n \<and>
        (\<forall> A V p. (A \<noteq> {} \<and> finite A \<and> finite V \<and> profile V A p) \<longrightarrow> elect V n A p \<noteq> {})"
      using electing_n
      by metis
    have def_card_one:
      "social_choice_result.electoral_module m \<and>
        (\<forall> A V p. (1 \<le> card A \<and> finite A \<and> finite V \<and> profile V A p) \<longrightarrow> 
                    card (defer V m A p) = 1)"
      using def_one_m
      unfolding defers_def
      by blast
    hence "social_choice_result.electoral_module (m \<triangleright> n)"
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
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n" and
    only_voters_n: "only_voters_vote n" and
    def_and_lifted: "a \<in> (defer V (m \<triangleright> n) A p) \<and> lifted V A p q a"
  shows "(m \<triangleright> n) V A p = (m \<triangleright> n) V A q"
proof -
  let ?new_Ap = "defer V m A p"
  let ?new_Aq = "defer V m A q"
  let ?new_p = "limit_profile ?new_Ap p"
  let ?new_q = "limit_profile ?new_Aq q"
  from monotone_m monotone_n
  have modules: "social_choice_result.electoral_module m 
                  \<and> social_choice_result.electoral_module n"
    unfolding defer_lift_invariance_def
    by simp
  hence "finite_profile V A p \<longrightarrow> defer V (m \<triangleright> n) A p \<subseteq> defer V m A p"
    using seq_comp_def_set_bounded
    by metis
  moreover have profile_p: "lifted V A p q a \<longrightarrow> finite_profile V A p"
    unfolding lifted_def
    by simp
  ultimately have defer_subset: "defer V (m \<triangleright> n) A p \<subseteq> defer V m A p"
    using def_and_lifted
    by blast
  hence mono_m: "m V A p = m V A q"
    using monotone_m def_and_lifted modules profile_p
          seq_comp_def_set_trans
    unfolding defer_lift_invariance_def
    by metis
  hence new_A_eq: "?new_Ap = ?new_Aq"
    by presburger
  have defer_eq: "defer V (m \<triangleright> n) A p = defer V n ?new_Ap ?new_p"
    using snd_conv
    unfolding sequential_composition.simps
    by metis
  have mono_n: "n V ?new_Ap ?new_p = n V ?new_Aq ?new_q"
  proof (cases)
    assume "lifted V ?new_Ap ?new_p ?new_q a"
    thus ?thesis
      using defer_eq mono_m monotone_n def_and_lifted
      unfolding defer_lift_invariance_def
      by (metis (no_types, lifting))
  next
    assume unlifted_a: "\<not>lifted V ?new_Ap ?new_p ?new_q a"
    from def_and_lifted
    have "finite_profile V A q"
      unfolding lifted_def
      by simp
    with modules new_A_eq
    have fin_prof: "finite_profile V ?new_Ap ?new_q"
      using def_presv_fin_prof
      by (metis (no_types))
    moreover from modules profile_p def_and_lifted
    have fin_prof: "finite_profile V ?new_Ap ?new_p"
      using def_presv_fin_prof
      by (metis (no_types))
    moreover from defer_subset def_and_lifted
    have "a \<in> ?new_Ap"
      by blast
    ultimately have lifted_stmt:
      "(\<exists> v \<in> V.
          Preference_Relation.lifted ?new_Ap (?new_p v) (?new_q v) a) \<longrightarrow>
       (\<exists> v \<in> V.
          \<not> Preference_Relation.lifted ?new_Ap (?new_p v) (?new_q v) a \<and>
              (?new_p v) \<noteq> (?new_q v))"
      using unlifted_a
      unfolding lifted_def
      by (metis (no_types, lifting))
    from def_and_lifted modules
    have "\<forall> v \<in> V. (Preference_Relation.lifted A (p v) (q v) a \<or> (p v) = (q v))"
      unfolding Profile.lifted_def
      by metis
    with def_and_lifted modules mono_m
    have "\<forall> v \<in> V.
            (Preference_Relation.lifted ?new_Ap (?new_p v) (?new_q v) a \<or>
              (?new_p v) = (?new_q v))"
      using limit_lifted_imp_eq_or_lifted defer_in_alts
      unfolding Profile.lifted_def limit_profile.simps
      by (metis (no_types, lifting))
    with lifted_stmt
    have "\<forall> v \<in> V. (?new_p v) = (?new_q v)"
      by blast
    with mono_m
    show ?thesis
      using leI not_less_zero nth_equalityI only_voters_n 
      unfolding only_voters_vote_def
      by presburger
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
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    "defer_lift_invariance m" and
    "defer_lift_invariance n" and 
    "only_voters_vote n"
  shows "defer_lift_invariance (m \<triangleright> n)"
proof (unfold defer_lift_invariance_def, safe)
  show "social_choice_result.electoral_module (m \<triangleright> n)"
    using assms seq_comp_sound
    unfolding defer_lift_invariance_def
    by blast
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: 'a
  assume
    "a \<in> defer V (m \<triangleright> n) A p" and
    "Profile.lifted V A p q a"
  thus "(m \<triangleright> n) V A p = (m \<triangleright> n) V A q"
    unfolding defer_lift_invariance_def
    by (meson assms def_lift_inv_seq_comp_help)
qed

text \<open>
  Composing a non-blocking, non-electing electoral module
  in sequence with an electoral module that defers exactly
  one alternative results in an electoral module that defers
  exactly one alternative.
\<close>

theorem seq_comp_def_one[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    non_blocking_m: "non_blocking m" and
    non_electing_m: "non_electing m" and
    def_1_n: "defers 1 n"
  shows "defers 1 (m \<triangleright> n)"
proof (unfold defers_def, safe)
  have "social_choice_result.electoral_module m"
    using non_electing_m
    unfolding non_electing_def
    by simp
  moreover have "social_choice_result.electoral_module n"
    using def_1_n
    unfolding defers_def
    by simp
  ultimately show "social_choice_result.electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    pos_card: "1 \<le> card A" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    prof_A: "profile V A p"
  from pos_card
  have "A \<noteq> {}"
    by auto
  with fin_A prof_A
  have "reject V m A p \<noteq> A"
    using non_blocking_m fin_V
    unfolding non_blocking_def
    by simp
  hence "\<exists> a. a \<in> A \<and> a \<notin> reject V m A p"
    using non_electing_m reject_in_alts fin_A prof_A fin_V
          card_seteq infinite_super subsetI upper_card_bounds_for_result
    unfolding non_electing_def
    by metis
  hence "defer V m A p \<noteq> {}"
    using electoral_mod_defer_elem empty_iff non_electing_m fin_A prof_A fin_V
    unfolding non_electing_def
    by (metis (no_types))
  hence "card (defer V m A p) \<ge> 1"
    using Suc_leI card_gt_0_iff fin_A prof_A fin_V non_blocking_m def_presv_fin_prof
    unfolding One_nat_def non_blocking_def
    by metis
  moreover have
    "\<forall> i m'. defers i m' =
      (social_choice_result.electoral_module m' \<and>
        (\<forall> A' V' p'. (i \<le> card A' \<and> finite A' \<and> finite V' \<and> profile V' A' p') \<longrightarrow>
            card (defer V' m' A' p') = i))"
    unfolding defers_def
    by simp
  ultimately have
    "card (defer V n (defer V m A p) (limit_profile (defer V m A p) p)) = 1"
    using def_1_n fin_A prof_A fin_V non_blocking_m def_presv_fin_prof
    unfolding non_blocking_def
    by metis
  moreover have
    "defer V (m \<triangleright> n) A p = defer V n (defer V m A p) (limit_profile (defer V m A p) p)"
    using seq_comp_defers_def_set
    by (metis (no_types, opaque_lifting))
  ultimately show "card (defer V (m \<triangleright> n) A p) = 1"
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
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    m' :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    compatible: "disjoint_compatibility m n" and
    module_m': "social_choice_result.electoral_module m'" and
    only_voters: "only_voters_vote m'"
  shows "disjoint_compatibility (m \<triangleright> m') n"
proof (unfold disjoint_compatibility_def, safe)
  show "social_choice_result.electoral_module (m \<triangleright> m')"
    using compatible module_m' seq_comp_sound
    unfolding disjoint_compatibility_def
    by metis
next
  show "social_choice_result.electoral_module n"
    using compatible
    unfolding disjoint_compatibility_def
    by metis
next
  fix S :: "'a set" and V :: "'v set"
  have modules:
    "social_choice_result.electoral_module (m \<triangleright> m') \<and> social_choice_result.electoral_module n"
    using compatible module_m' seq_comp_sound
    unfolding disjoint_compatibility_def
    by metis
  assume "finite S" and "finite V"
  then obtain A where rej_A:
    "A \<subseteq> S \<and>
      (\<forall> a \<in> A.
        indep_of_alt V m S a \<and> (\<forall> p. finite_profile V S p \<longrightarrow> a \<in> reject V m S p)) \<and>
      (\<forall> a \<in> S - A.
        indep_of_alt V n S a \<and> (\<forall> p. finite_profile V S p \<longrightarrow> a \<in> reject V n S p))"
    using compatible
    unfolding disjoint_compatibility_def
    by (metis (no_types, lifting))
  show
    "\<exists> A \<subseteq> S.
      (\<forall> a \<in> A. indep_of_alt V (m \<triangleright> m') S a \<and>
        (\<forall> p. finite_profile V S p \<longrightarrow> a \<in> reject V (m \<triangleright> m') S p)) \<and>
      (\<forall> a \<in> S - A.
        indep_of_alt V n S a \<and> (\<forall> p. finite_profile V S p \<longrightarrow> a \<in> reject V n S p))"
  proof
    have "\<forall> a p q. a \<in> A \<and> equiv_prof_except_a V S p q a \<longrightarrow>
            (m \<triangleright> m') V S p = (m \<triangleright> m') V S q"
    proof (safe)
      fix
        a :: "'a" and
        p :: "('a, 'v) Profile" and
        q :: "('a, 'v) Profile"
      assume
        a_in_A: "a \<in> A" and
        lifting_equiv_p_q: "equiv_prof_except_a V S p q a"
      hence eq_def: "defer V m S p = defer V m S q"
        using rej_A
        unfolding indep_of_alt_def
        by metis
      from lifting_equiv_p_q
      have profiles: "finite_profile V S p \<and> finite_profile V S q"
        using \<open>finite S\<close> \<open>finite V\<close>
        unfolding equiv_prof_except_a_def 
        by blast
      hence "(defer V m S p) \<subseteq> S"
        using compatible defer_in_alts
        unfolding disjoint_compatibility_def
        by metis
      hence "\<forall> v \<in> V. limit_profile (defer V m S p) p v = limit_profile (defer V m S q) q v"
        using rej_A DiffD2 a_in_A lifting_equiv_p_q compatible defer_not_elec_or_rej
              profiles negl_diff_imp_eq_limit_prof
        unfolding disjoint_compatibility_def eq_def
        by (metis (no_types, lifting))
      with eq_def
      have "m' V (defer V m S p) (limit_profile (defer V m S p) p) =
              m' V (defer V m S q) (limit_profile (defer V m S q) q)"
        using only_voters
        unfolding only_voters_vote_def
        by simp
      moreover have "m V S p = m V S q"
        using rej_A a_in_A lifting_equiv_p_q
        unfolding indep_of_alt_def
        by metis
      ultimately show "(m \<triangleright> m') V S p = (m \<triangleright> m') V S q"
        unfolding sequential_composition.simps
        by (metis (full_types))
    qed
    moreover have
      "\<forall> a' \<in> A. \<forall> p'. finite_profile V S p' \<longrightarrow> a' \<in> reject V (m \<triangleright> m') S p'"
      using rej_A UnI1 prod.sel
      unfolding sequential_composition.simps
      by metis
    ultimately show
      "A \<subseteq> S \<and>
        (\<forall> a' \<in> A. indep_of_alt V (m \<triangleright> m') S a' \<and>
          (\<forall> p'. finite_profile V S p' \<longrightarrow> a' \<in> reject V (m \<triangleright> m') S p')) \<and>
        (\<forall> a' \<in> S - A. indep_of_alt V n S a' \<and>
          (\<forall> p'. finite_profile V S p' \<longrightarrow> a' \<in> reject V n S p'))"
      using rej_A indep_of_alt_def modules
      by (metis (mono_tags, lifting))
  qed
qed

theorem seq_comp_cond_compat[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    dcc_m: "defer_condorcet_consistency m" and
    nb_n: "non_blocking n" and
    ne_n: "non_electing n"
  shows "condorcet_compatibility (m \<triangleright> n)"
proof (unfold condorcet_compatibility_def, safe)
  have "social_choice_result.electoral_module m"
    using dcc_m
    unfolding defer_condorcet_consistency_def
    by presburger
  moreover have "social_choice_result.electoral_module n"
    using nb_n
    unfolding non_blocking_def
    by presburger
  ultimately have "social_choice_result.electoral_module (m \<triangleright> n)"
    by simp
  thus "social_choice_result.electoral_module (m \<triangleright> n)"
    by presburger
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    cw_a: "condorcet_winner V A p a" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    a_in_rej_seq_m_n: "a \<in> reject V (m \<triangleright> n) A p"
  hence "\<exists> a'. defer_condorcet_consistency m \<and> condorcet_winner V A p a'"
    using dcc_m
    by blast
  hence "m V A p = ({}, A - (defer V m A p), {a})"
    using defer_condorcet_consistency_def cw_a cond_winner_unique_3 condorcet_winner.simps
    by (metis (no_types, lifting))
  have sound_m: "social_choice_result.electoral_module m"
    using dcc_m
    unfolding defer_condorcet_consistency_def
    by presburger
  moreover have "social_choice_result.electoral_module n"
    using nb_n
    unfolding non_blocking_def
    by presburger
  ultimately have sound_seq_m_n: "social_choice_result.electoral_module (m \<triangleright> n)"
    by simp
  have def_m: "defer V m A p = {a}"
    using cw_a fin_A fin_V cond_winner_unique_3 dcc_m snd_conv
    unfolding defer_condorcet_consistency_def
    by (metis (mono_tags, lifting))
  have rej_m: "reject V m A p = A - {a}"
    using cw_a fin_A fin_V cond_winner_unique_3 dcc_m prod.sel(1) snd_conv
    unfolding defer_condorcet_consistency_def
    by (metis (mono_tags, lifting))
  have "elect V m A p = {}"
    using cw_a fin_A fin_V def_m rej_m dcc_m prod.sel(1)
    unfolding defer_condorcet_consistency_def
    by (metis (mono_tags, lifting))
  hence diff_elect_m: "A - elect V m A p = A"
    using Diff_empty
    by (metis (full_types))
  have cond_win:
    "finite A \<and> finite V \<and> profile V A p \<and> a \<in> A \<and> (\<forall> a'. a' \<in> A - {a'} \<longrightarrow> wins V a p a')"
    using cw_a condorcet_winner.simps DiffD2 singletonI
    by (metis (no_types))
  have "\<forall> a' A'. (a'::'a) \<in> A' \<longrightarrow> insert a' (A' - {a'}) = A'"
    by blast
  have nb_n_full:
    "social_choice_result.electoral_module n \<and>
      (\<forall> A' V' p'. A' \<noteq> {} \<and> finite A' \<and> finite V' \<and> profile V' A' p' \<longrightarrow> reject V' n A' p' \<noteq> A')"
    using nb_n non_blocking_def
    by metis
  have def_seq_diff:
    "defer V (m \<triangleright> n) A p = A - elect V (m \<triangleright> n) A p - reject V (m \<triangleright> n) A p"
    using defer_not_elec_or_rej cond_win sound_seq_m_n
    by metis
  have set_ins: "\<forall> a' A'. (a'::'a) \<in> A' \<longrightarrow> insert a' (A' - {a'}) = A'"
    by fastforce
  have "\<forall> p' A' p''. p' = (A'::'a set, p''::'a set \<times> 'a set) \<longrightarrow> snd p' = p''"
    by simp
  hence "snd (elect V m A p \<union> elect V n (defer V m A p) (limit_profile (defer V m A p) p),
          reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
          defer V n (defer V m A p) (limit_profile (defer V m A p) p)) =
            (reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
            defer V n (defer V m A p) (limit_profile (defer V m A p) p))"
    by blast
  hence seq_snd_simplified:
    "snd ((m \<triangleright> n) V A p) =
      (reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
        defer V n (defer V m A p) (limit_profile (defer V m A p) p))"
    using sequential_composition.simps
    by metis
  hence seq_rej_union_eq_rej:
    "reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p) =
        reject V (m \<triangleright> n) A p"
    by simp
  hence seq_rej_union_subset_A:
    "reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p) \<subseteq> A"
    using sound_seq_m_n cond_win reject_in_alts
    by (metis (no_types))
  hence "A - {a} = reject V (m \<triangleright> n) A p - {a}"
    using seq_rej_union_eq_rej defer_not_elec_or_rej cond_win def_m diff_elect_m
          double_diff rej_m sound_m sup_ge1
    by (metis (no_types))
  hence "reject V (m \<triangleright> n) A p \<subseteq> A - {a}"
    using seq_rej_union_subset_A seq_snd_simplified set_ins def_seq_diff nb_n_full
          cond_win fst_conv Diff_empty Diff_eq_empty_iff a_in_rej_seq_m_n def_m
          def_presv_fin_prof sound_m ne_n diff_elect_m insert_not_empty
          reject_not_elec_or_def seq_comp_def_then_elect_elec_set
          seq_comp_defers_def_set sup_bot.left_neutral
    unfolding non_electing_def
    by (metis (no_types))
  thus "False"
    using a_in_rej_seq_m_n
    by blast
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    a' :: "'a"
  assume
    cw_a: "condorcet_winner V A p a" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    not_cw_a': "\<not> condorcet_winner V A p a'" and
    a'_in_elect_seq_m_n: "a' \<in> elect V (m \<triangleright> n) A p"
  hence "\<exists> a''. defer_condorcet_consistency m \<and> condorcet_winner V A p a''"
    using dcc_m
    by blast
  hence result_m: "m V A p = ({}, A - (defer V m A p), {a})"
    using defer_condorcet_consistency_def cw_a cond_winner_unique_3 condorcet_winner.simps
    by (metis (no_types, lifting))
  have sound_m: "social_choice_result.electoral_module m"
    using dcc_m
    unfolding defer_condorcet_consistency_def
    by presburger
  moreover have "social_choice_result.electoral_module n"
    using nb_n
    unfolding non_blocking_def
    by presburger
  ultimately have sound_seq_m_n: "social_choice_result.electoral_module (m \<triangleright> n)"
    by simp
  have "reject V m A p = A - {a}"
    using cw_a fin_A dcc_m prod.sel(1) snd_conv result_m
    unfolding defer_condorcet_consistency_def
    by (metis (mono_tags, lifting))
  hence a'_in_rej: "a' \<in> reject V m A p"
    using Diff_iff cw_a not_cw_a' a'_in_elect_seq_m_n condorcet_winner.elims(1)
          elect_in_alts singleton_iff sound_seq_m_n subset_iff
    by (metis (no_types, lifting))
  have "\<forall> p' A' p''. p' = (A'::'a set, p''::'a set \<times> 'a set) \<longrightarrow> snd p' = p''"
    by simp
  hence m_seq_n:
    "snd (elect V m A p \<union> elect V n (defer V m A p) (limit_profile (defer V m A p) p),
      reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
        defer V n (defer V m A p) (limit_profile (defer V m A p) p)) =
          (reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
            defer V n (defer V m A p) (limit_profile (defer V m A p) p))"
    by blast
  have "a' \<in> elect V m A p"
    using a'_in_elect_seq_m_n condorcet_winner.simps cw_a def_presv_fin_prof ne_n
          seq_comp_def_then_elect_elec_set sound_m sup_bot.left_neutral
    unfolding non_electing_def
    by (metis (no_types))
  hence a_in_rej_union:
    "a \<in> reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p)"
    using Diff_iff a'_in_rej condorcet_winner.simps cw_a
          reject_not_elec_or_def sound_m
    by (metis (no_types))
  have m_seq_n_full:
    "(m \<triangleright> n) V A p =
      (elect V m A p \<union> elect V n (defer V m A p) (limit_profile (defer V m A p) p),
      reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
      defer V n (defer V m A p) (limit_profile (defer V m A p) p))"
    unfolding sequential_composition.simps
    by metis
  have "\<forall> A' A''. (A'::'a set) = fst (A', A''::'a set)"
    by simp
  hence "a \<in> reject V (m \<triangleright> n) A p"
    using a_in_rej_union m_seq_n m_seq_n_full
    by presburger
  moreover have
    "finite A \<and> finite V \<and> profile V A p \<and> a \<in> A \<and> (\<forall> a''. a'' \<in> A - {a} \<longrightarrow> wins V a p a'')"
    using cw_a m_seq_n_full a'_in_elect_seq_m_n a'_in_rej ne_n sound_m
    unfolding condorcet_winner.simps
    by metis
  ultimately show "False"
    using a'_in_elect_seq_m_n IntI empty_iff result_disj sound_seq_m_n a'_in_rej def_presv_fin_prof
          fst_conv m_seq_n_full ne_n non_electing_def sound_m sup_bot.right_neutral
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    a' :: "'a"
  assume
    cw_a: "condorcet_winner V A p a" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    a'_in_A: "a' \<in> A" and
    not_cw_a': "\<not> condorcet_winner V A p a'"
  have "reject V m A p = A - {a}"
    using cw_a fin_A fin_V cond_winner_unique_3 dcc_m prod.sel(1) snd_conv
    unfolding defer_condorcet_consistency_def
    by (metis (mono_tags, lifting))
  moreover have "a \<noteq> a'"
    using cw_a not_cw_a'
    by safe
  ultimately have "a' \<in> reject V m A p"
    using DiffI a'_in_A singletonD
    by (metis (no_types))
  hence "a' \<in> reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p)"
    by blast
  moreover have
    "(m \<triangleright> n) V A p =
      (elect V m A p \<union> elect V n (defer V m A p) (limit_profile (defer V m A p) p),
        reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
        defer V n (defer V m A p) (limit_profile (defer V m A p) p))"
    unfolding sequential_composition.simps
    by metis
  moreover have
    "snd (elect V m A p \<union> elect V n (defer V m A p) (limit_profile (defer V m A p) p),
      reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
      defer V n (defer V m A p) (limit_profile (defer V m A p) p)) =
        (reject V m A p \<union> reject V n (defer V m A p) (limit_profile (defer V m A p) p),
        defer V n (defer V m A p) (limit_profile (defer V m A p) p))"
    using snd_conv
    by metis
  ultimately show "a' \<in> reject V (m \<triangleright> n) A p"
    using fst_eqD
    by (metis (no_types))
qed

text \<open>
  Composing a defer-condorcet-consistent electoral module
  in sequence with a non-blocking and non-electing electoral
  module results in a defer-condorcet-consistent module.
\<close>

theorem seq_comp_dcc[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    dcc_m: "defer_condorcet_consistency m" and
    nb_n: "non_blocking n" and
    ne_n: "non_electing n"
  shows "defer_condorcet_consistency (m \<triangleright> n)"
proof (unfold defer_condorcet_consistency_def, safe)
  have "social_choice_result.electoral_module m"
    using dcc_m
    unfolding defer_condorcet_consistency_def
    by metis
  thus "social_choice_result.electoral_module (m \<triangleright> n)"
    using ne_n
    by (simp add: non_electing_def)
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    cw_a: "condorcet_winner V A p a" and
    fin_A: "finite A" and
    fin_V: "finite V"
  hence "\<exists> a'. defer_condorcet_consistency m \<and> condorcet_winner V A p a'"
    using dcc_m
    by blast
  hence result_m: "m V A p = ({}, A - (defer V m A p), {a})"
    using defer_condorcet_consistency_def cw_a cond_winner_unique_3 condorcet_winner.simps
    by (metis (no_types, lifting))
  hence elect_m_empty: "elect V m A p = {}"
    using eq_fst_iff
    by metis
  have sound_m: "social_choice_result.electoral_module m"
    using dcc_m
    unfolding defer_condorcet_consistency_def
    by metis
  hence sound_seq_m_n: "social_choice_result.electoral_module (m \<triangleright> n)"
    using ne_n
    by (simp add: non_electing_def)
  have defer_eq_a: "defer V (m \<triangleright> n) A p = {a}"
  proof (safe)
    fix a' :: "'a"
    assume a'_in_def_seq_m_n: "a' \<in> defer V (m \<triangleright> n) A p"
    have "{a} = {a \<in> A. condorcet_winner V A p a}"
      using cond_winner_unique_3 cw_a
      by metis
    moreover have "defer_condorcet_consistency m \<longrightarrow>
            m V A p = ({}, A - defer V m A p, {a \<in> A. condorcet_winner V A p a})"
      using condorcet_winner.elims(2) cw_a defer_condorcet_consistency_def fin_V
      by (metis (no_types))
    ultimately have "defer V m A p = {a}"
      using dcc_m snd_conv
      by (metis (no_types, lifting))
    hence "defer V (m \<triangleright> n) A p = {a}"
      using cw_a a'_in_def_seq_m_n condorcet_winner.elims(2) empty_iff seq_comp_def_set_bounded
            sound_m subset_singletonD nb_n
      unfolding non_blocking_def
      by metis
    thus "a' = a"
      using a'_in_def_seq_m_n
      by blast
  next
    have "\<exists> a'. defer_condorcet_consistency m \<and> condorcet_winner V A p a'"
      using cw_a dcc_m
      by blast
    hence "m V A p = ({}, A - (defer V m A p), {a})"
      using defer_condorcet_consistency_def cw_a cond_winner_unique_3 condorcet_winner.simps
      by (metis (no_types, lifting))
    hence elect_m_empty: "elect V m A p = {}"
      using eq_fst_iff
      by metis
    have "finite_profile V (defer V m A p) (limit_profile (defer V m A p) p)"
      using condorcet_winner.simps cw_a def_presv_fin_prof sound_m
      by (metis (no_types))
    hence "elect V n (defer V m A p) (limit_profile (defer V m A p) p) = {}"
      using ne_n non_electing_def
      by metis
    hence "elect V (m \<triangleright> n) A p = {}"
      using elect_m_empty seq_comp_def_then_elect_elec_set sup_bot.right_neutral
      by (metis (no_types))
    moreover have "condorcet_compatibility (m \<triangleright> n)"
      using dcc_m nb_n ne_n
      by simp
    hence "a \<notin> reject V (m \<triangleright> n) A p"
      unfolding condorcet_compatibility_def
      using cw_a fin_A fin_V
      by metis
    ultimately show "a \<in> defer V (m \<triangleright> n) A p"
      using condorcet_winner.elims(2) cw_a electoral_mod_defer_elem empty_iff
            sound_seq_m_n
      by metis
  qed
  have "finite_profile V (defer V m A p) (limit_profile (defer V m A p) p)"
    using condorcet_winner.simps cw_a def_presv_fin_prof sound_m
    by (metis (no_types))
  hence "elect V n (defer V m A p) (limit_profile (defer V m A p) p) = {}"
    using ne_n non_electing_def
    by metis
  hence "elect V (m \<triangleright> n) A p = {}"
    using elect_m_empty seq_comp_def_then_elect_elec_set sup_bot.right_neutral
    by (metis (no_types))
  moreover have def_seq_m_n_eq_a: "defer V (m \<triangleright> n) A p = {a}"
    using cw_a defer_eq_a
    by (metis (no_types))
  ultimately have "(m \<triangleright> n) V A p = ({}, A - {a}, {a})"
    using Diff_empty cw_a combine_ele_rej_def condorcet_winner.elims(2)
          reject_not_elec_or_def sound_seq_m_n
    by (metis (no_types))
  moreover have "{a' \<in> A. condorcet_winner V A p a'} = {a}"
    using cw_a cond_winner_unique_3
    by metis
  ultimately show
    "(m \<triangleright> n) V A p =
      ({}, A - defer V (m \<triangleright> n) A p, {a' \<in> A. condorcet_winner V A p a'})"
    using def_seq_m_n_eq_a
    by metis
qed

text \<open>
  Composing a defer-lift invariant and a non-electing
  electoral module that defers exactly one alternative
  in sequence with an electing electoral module
  results in a monotone electoral module.
\<close>

theorem seq_comp_mono[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    def_monotone_m: "defer_lift_invariance m" and
    non_ele_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n"
  shows "monotonicity (m \<triangleright> n)"
proof (unfold monotonicity_def, safe)
  have "social_choice_result.electoral_module m"
    using non_ele_m
    unfolding non_electing_def
    by simp
  moreover have "social_choice_result.electoral_module n"
    using electing_n
    unfolding electing_def
    by simp
  ultimately show "social_choice_result.electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    w :: "'a"
  assume
    elect_w_in_p: "w \<in> elect V (m \<triangleright> n) A p" and
    lifted_w: "Profile.lifted V A p q w"
  thus "w \<in> elect V (m \<triangleright> n) A q"
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
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    strong_def_mon_m: "defer_invariant_monotonicity m" and
    non_electing_n: "non_electing n" and
    defers_one: "defers 1 n" and
    defer_monotone_n: "defer_monotonicity n" and
    only_voters: "only_voters_vote n"
  shows "defer_lift_invariance (m \<triangleright> n)"
proof (unfold defer_lift_invariance_def, safe)
  have "social_choice_result.electoral_module m"
    using strong_def_mon_m
    unfolding defer_invariant_monotonicity_def
    by metis
  moreover have "social_choice_result.electoral_module n"
    using defers_one
    unfolding defers_def
    by metis
  ultimately show "social_choice_result.electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    defer_a_p: "a \<in> defer V (m \<triangleright> n) A p" and
    lifted_a: "Profile.lifted V A p q a"
  have non_electing_m: "non_electing m"
    using strong_def_mon_m
    unfolding defer_invariant_monotonicity_def
    by simp
  have electoral_mod_m: "social_choice_result.electoral_module m"
    using strong_def_mon_m
    unfolding defer_invariant_monotonicity_def
    by metis
  have electoral_mod_n: "social_choice_result.electoral_module n"
    using defers_one
    unfolding defers_def
    by metis
  have finite_profile_p: "finite_profile V A p"
    using lifted_a
    unfolding Profile.lifted_def
    by simp
  have finite_profile_q: "finite_profile V A q"
    using lifted_a
    unfolding Profile.lifted_def
    by simp
  have "1 \<le> card A"
    using Profile.lifted_def card_eq_0_iff emptyE less_one lifted_a linorder_le_less_linear
    by metis
  hence n_defers_exactly_one_p: "card (defer V n A p) = 1"
    using finite_profile_p defers_one
    unfolding defers_def
    by (metis (no_types))
  have fin_prof_def_m_q: "finite_profile V (defer V m A q) (limit_profile (defer V m A q) q)"
    using def_presv_fin_prof electoral_mod_m finite_profile_q
    by (metis (no_types))
  have def_seq_m_n_q:
    "defer V (m \<triangleright> n) A q = defer V n (defer V m A q) (limit_profile (defer V m A q) q)"
    using seq_comp_defers_def_set
    by simp
  have fin_prof_def_m: "finite_profile V (defer V m A p) (limit_profile (defer V m A p) p)"
    using def_presv_fin_prof electoral_mod_m finite_profile_p
    by (metis (no_types))
  hence fin_prof_seq_comp_m_n:
    "finite_profile V (defer V n (defer V m A p) (limit_profile (defer V m A p) p))
          (limit_profile (defer V n (defer V m A p) (limit_profile (defer V m A p) p))
            (limit_profile (defer V m A p) p))"
    using def_presv_fin_prof electoral_mod_n
    by (metis (no_types))
  have a_non_empty: "a \<notin> {}"
    by simp
  have def_seq_m_n:
    "defer V (m \<triangleright> n) A p = defer V n (defer V m A p) (limit_profile (defer V m A p) p)"
    using seq_comp_defers_def_set
    by simp
  have "1 \<le> card (defer V n (defer V m A p) (limit_profile (defer V m A p) p))"
    using a_non_empty card_gt_0_iff def_presv_fin_prof defer_a_p electoral_mod_n
          fin_prof_def_m seq_comp_defers_def_set One_nat_def Suc_leI
    by (metis (full_types))
  hence "card (defer V n (defer V n (defer V m A p) (limit_profile (defer V m A p) p))
          (limit_profile (defer V n (defer V m A p) (limit_profile (defer V m A p) p))
            (limit_profile (defer V m A p) p))) = 1"
    using n_defers_exactly_one_p fin_prof_seq_comp_m_n defers_one defers_def
    by blast
  hence defer_seq_m_n_eq_one: "card (defer V (m \<triangleright> n) A p) = 1"
    using One_nat_def Suc_leI a_non_empty card_gt_0_iff def_seq_m_n defer_a_p
          defers_one electoral_mod_m fin_prof_def_m finite_profile_p
          seq_comp_def_set_trans
    unfolding defers_def
    by metis
  hence def_seq_m_n_eq_a: "defer V (m \<triangleright> n) A p = {a}"
    using defer_a_p is_singleton_altdef is_singleton_the_elem singletonD
    by (metis (no_types))
  show "(m \<triangleright> n) V A p = (m \<triangleright> n) V A q"
  proof (cases)
    assume "defer V m A q \<noteq> defer V m A p"
    hence "defer V m A q = {a}"
      using defer_a_p electoral_mod_n finite_profile_p lifted_a seq_comp_def_set_trans
            strong_def_mon_m
      unfolding defer_invariant_monotonicity_def
      by (metis (no_types))
    moreover from this
    have "(a \<in> defer V m A p) \<longrightarrow> card (defer V (m \<triangleright> n) A q) = 1"
      using card_eq_0_iff card_insert_disjoint defers_one electoral_mod_m empty_iff
            order_refl finite.emptyI seq_comp_defers_def_set def_presv_fin_prof
            finite_profile_q
      unfolding One_nat_def defers_def
      by metis
    moreover have "a \<in> defer V m A p"
      using electoral_mod_m electoral_mod_n defer_a_p seq_comp_def_set_bounded
            finite_profile_p finite_profile_q
      by blast
    ultimately have "defer V (m \<triangleright> n) A q = {a}"
      using Collect_mem_eq card_1_singletonE empty_Collect_eq insertCI subset_singletonD
            def_seq_m_n_q defer_in_alts electoral_mod_n fin_prof_def_m_q
      by (metis (no_types, lifting))
    hence "defer V (m \<triangleright> n) A p = defer V (m \<triangleright> n) A q"
      using def_seq_m_n_eq_a
      by presburger
    moreover have "elect V (m \<triangleright> n) A p = elect V (m \<triangleright> n) A q"
      using fin_prof_def_m fin_prof_def_m_q finite_profile_p finite_profile_q non_electing_def
            non_electing_m non_electing_n seq_comp_def_then_elect_elec_set
      by metis
    ultimately show ?thesis
      using electoral_mod_m electoral_mod_n eq_def_and_elect_imp_eq
            finite_profile_p finite_profile_q seq_comp_sound
      by (metis (no_types))
  next
    assume "\<not> (defer V m A q \<noteq> defer V m A p)"
    hence def_eq: "defer V m A q = defer V m A p"
      by presburger
    have "elect V m A p = {}"
      using finite_profile_p non_electing_m
      unfolding non_electing_def
      by simp
    moreover have "elect V m A q = {}"
      using finite_profile_q non_electing_m
      unfolding non_electing_def
      by simp
    ultimately have elect_m_equal: "elect V m A p = elect V m A q"
      by simp
    have 
      "(\<forall> v \<in> V. (limit_profile (defer V m A p) p) v = (limit_profile (defer V m A p) q) v) 
        \<or> lifted V (defer V m A q) (limit_profile (defer V m A p) p)
                  (limit_profile (defer V m A p) q) a"
      using def_eq defer_in_alts electoral_mod_m lifted_a finite_profile_q 
            limit_prof_eq_or_lifted
      by metis
    moreover have 
      "(\<forall> v \<in> V. (limit_profile (defer V m A p) p) v = (limit_profile (defer V m A p) q) v)
        \<Longrightarrow> n V (defer V m A p) (limit_profile (defer V m A p) p)
            = n V (defer V m A q) (limit_profile (defer V m A q) q)"
      using only_voters def_eq 
      unfolding only_voters_vote_def
      by presburger
    moreover have 
      "lifted V (defer V m A q) (limit_profile (defer V m A p) p) 
                                (limit_profile (defer V m A p) q) a
        \<Longrightarrow> defer V n (defer V m A p) (limit_profile (defer V m A p) p)
            = defer V n (defer V m A q) (limit_profile (defer V m A q) q)"
    proof -
      assume "Profile.lifted V (defer V m A q) (limit_profile (defer V m A p) p)
              (limit_profile (defer V m A p) q) a" 
      hence "a \<in> defer V n (defer V m A q) (limit_profile (defer V m A q) q)"
        using lifted_a def_seq_m_n defer_a_p defer_monotone_n 
              fin_prof_def_m_q def_eq
        unfolding defer_monotonicity_def
        by metis
      hence "a \<in> defer V (m \<triangleright> n) A q"
        using def_seq_m_n_q
        by simp      
      moreover have "card (defer V (m \<triangleright> n) A q) = 1"
        using def_seq_m_n_q defers_one def_eq defer_seq_m_n_eq_one defers_def 
              electoral_mod_m fin_prof_def_m_q finite_profile_p seq_comp_def_card_bounded
        by (metis (no_types, lifting))
      ultimately have "defer V (m \<triangleright> n) A q = {a}"
        by (metis a_non_empty card_1_singletonE insertE)
      thus "defer V n (defer V m A p) (limit_profile (defer V m A p) p)
            = defer V n (defer V m A q) (limit_profile (defer V m A q) q)"
        using def_seq_m_n_eq_a def_seq_m_n_q def_seq_m_n
        by presburger
    qed
    ultimately have "defer V (m \<triangleright> n) A p = defer V (m \<triangleright> n) A q"
      using def_seq_m_n def_seq_m_n_q
      by presburger
    moreover from this
    have "reject V (m \<triangleright> n) A p = reject V (m \<triangleright> n) A q"
      using electoral_mod_m electoral_mod_n finite_profile_p finite_profile_q non_electing_def
            non_electing_m non_electing_n eq_def_and_elect_imp_eq seq_comp_presv_non_electing
      by (metis (no_types))
    ultimately have "snd ((m \<triangleright> n) V A p) = snd ((m \<triangleright> n) V A q)"
      using prod_eqI
      by metis
    moreover have "elect V (m \<triangleright> n) A p = elect V (m \<triangleright> n) A q"
      using fin_prof_def_m fin_prof_def_m_q non_electing_n finite_profile_p finite_profile_q
            non_electing_def def_eq elect_m_equal prod.sel(1)
      unfolding sequential_composition.simps
      by (metis (no_types))
    ultimately show "(m \<triangleright> n) V A p = (m \<triangleright> n) V A q"
      using prod_eqI
      by metis
  qed
qed

end
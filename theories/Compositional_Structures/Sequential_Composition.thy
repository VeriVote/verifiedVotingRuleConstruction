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
  have fin_def: "finite (defer m A p)"
    using def_presv_fin_prof f_prof module_m
    by metis
  have prof_def_lim:
    "profile (defer m A p) (limit_profile (defer m A p) p)"
    using def_presv_fin_prof f_prof module_m
    by metis
  have defer_in_A:
    "\<forall>prof f a A.
      (profile A prof \<and> finite A \<and> electoral_module f \<and>
        (a::'a) \<in> defer f A prof) \<longrightarrow>
          a \<in> A"
    using UnCI result_presv_alts
    by (metis (mono_tags))
  from module_m f_prof
  have disjoint_m: "disjoint3 (m A p)"
    using electoral_module_def well_formed.simps
    by blast
  from module_m module_n def_presv_fin_prof f_prof
  have disjoint_n:
    "(disjoint3 (n ?new_A ?new_p))"
    using electoral_module_def well_formed.simps
    by metis
  have disj_n:
    "elect m A p \<inter> reject m A p = {} \<and>
      elect m A p \<inter> defer m A p = {} \<and>
      reject m A p \<inter> defer m A p = {}"
    using f_prof module_m
    by (simp add: result_disj)
  from f_prof module_m module_n
  have rej_n_in_def_m:
    "reject n (defer m A p)
      (limit_profile (defer m A p) p) \<subseteq> defer m A p"
    using def_presv_fin_prof reject_in_alts
    by metis
  with disjoint_m module_m module_n f_prof
  have 0:
    "(elect m A p \<inter> reject n ?new_A ?new_p) = {}"
    using disj_n
    by (simp add: disjoint_iff_not_equal subset_eq)
  from f_prof module_m module_n
  have elec_n_in_def_m:
    "elect n (defer m A p)
      (limit_profile (defer m A p) p) \<subseteq> defer m A p"
    using def_presv_fin_prof elect_in_alts
    by metis
  from disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n
  have 1:
    "(elect m A p \<inter> defer n ?new_A ?new_p) = {}"
  proof -
    obtain sf :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall>a b.
        (\<exists>c. c \<in> b \<and> (\<exists>d. d \<in> a \<and> c = d)) =
          (sf a b \<in> b \<and>
            (\<exists>e. e \<in> a \<and> sf a b = e))"
      by moura
    then obtain sf2 :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall>A B.
        (A \<inter> B \<noteq> {} \<or> (\<forall>a. a \<notin> A \<or> (\<forall>b. b \<notin> B \<or> a \<noteq> b))) \<and>
          (A \<inter> B = {} \<or> sf B A \<in> A \<and> sf2 B A \<in> B \<and>
            sf B A = sf2 B A)"
      by auto
    thus ?thesis
      using defer_in_A disj_n fin_def module_n prof_def_lim
      by (metis (no_types))
  qed
  from disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n
  have 2:
    "(reject m A p \<inter> reject n ?new_A ?new_p) = {}"
    using disjoint_iff_not_equal reject_in_alts
          set_rev_mp result_disj Int_Un_distrib2
          Un_Diff_Int boolean_algebra_cancel.inf2
          inf.order_iff inf_sup_aci(1) subsetD
          rej_n_in_def_m disj_n
    by auto
  have "\<forall>A Aa. \<not> (A::'a set) \<subseteq> Aa \<or> A = A \<inter> Aa"
    by blast
  with disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n elec_n_in_def_m
  have 3:
    "(reject m A p \<inter> elect n ?new_A ?new_p) = {}"
    using disj_n
    by blast
  have
    "(elect m A p \<union> elect n ?new_A ?new_p) \<inter>
          (reject m A p \<union> reject n ?new_A ?new_p) = {}"
  proof (safe)
    fix x :: "'a"
    assume
      elec_x: "x \<in> elect m A p" and
      rej_x: "x \<in> reject m A p"
    from elec_x rej_x
    have "x \<in> elect m A p \<inter> reject m A p"
      by simp
    thus "x \<in> {}"
      using disj_n
      by simp
  next
    fix x :: "'a"
    assume
      elec_x: "x \<in> elect m A p" and
      rej_lim_x:
      "x \<in> reject n (defer m A p)
        (limit_profile (defer m A p) p)"
    from elec_x rej_lim_x
    show "x \<in> {}"
      using "0"
      by blast
  next
    fix x :: "'a"
    assume
      elec_lim_x:
      "x \<in> elect n (defer m A p) (limit_profile (defer m A p) p)" and
      rej_x: "x \<in> reject m A p"
    from elec_lim_x rej_x
    show "x \<in> {}"
      using "3"
      by blast
  next
    fix x :: "'a"
    assume
      elec_lim_x:
      "x \<in> elect n (defer m A p) (limit_profile (defer m A p) p)" and
      rej_lim_x:
      "x \<in> reject n (defer m A p) (limit_profile (defer m A p) p)"
    from elec_lim_x rej_lim_x
    show "x \<in> {}"
      using disjoint_iff_not_equal elec_lim_x fin_def
            module_n prof_def_lim rej_lim_x result_disj
      by metis
  qed
  moreover from 0 1 2 3 disjoint_n module_m module_n f_prof
  have
    "(elect m A p \<union> elect n ?new_A ?new_p) \<inter>
          (defer n ?new_A ?new_p) = {}"
    using Int_Un_distrib2 Un_empty def_presv_fin_prof result_disj
    by metis
  moreover from 0 1 2 3 f_prof disjoint_m disjoint_n module_m module_n
  have
    "(reject m A p \<union> reject n ?new_A ?new_p) \<inter>
          (defer n ?new_A ?new_p) = {}"
(*    using Int_Un_distrib2 defer_in_alts distrib_imp2
          def_presv_fin_prof result_disj subset_Un_eq
          sup_inf_distrib1 *)
  proof (safe)
    fix x :: "'a"
    assume
      elec_rej_disj:
      "elect m A p \<inter>
        reject n (defer m A p) (limit_profile (defer m A p) p) = {}" and
      elec_def_disj:
      "elect m A p \<inter>
        defer n (defer m A p) (limit_profile (defer m A p) p) = {}" and
      rej_rej_disj:
      "reject m A p \<inter>
        reject n (defer m A p) (limit_profile (defer m A p) p) = {}" and
      rej_elec_disj:
      "reject m A p \<inter>
        elect n (defer m A p) (limit_profile (defer m A p) p) = {}" and
      disj_p: "disjoint3 (m A p)" and
      disj_limit:
      "disjoint3 (n (defer m A p) (limit_profile (defer m A p) p))" and
      mod_m: "electoral_module m" and
      mod_n: "electoral_module n" and
      fin_A: "finite A" and
      prof_A: "profile A p" and
      x_in_def:
      "x \<in> defer n (defer m A p) (limit_profile (defer m A p) p)" and
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
      elec_rej_disj:
      "elect m A p \<inter>
        reject n (defer m A p) (limit_profile (defer m A p) p) = {}" and
      elec_def_disj:
      "elect m A p \<inter>
        defer n (defer m A p) (limit_profile (defer m A p) p) = {}" and
      rej_rej_disj:
      "reject m A p \<inter>
        reject n (defer m A p) (limit_profile (defer m A p) p) = {}" and
      rej_elec_disj:
      "reject m A p \<inter>
        elect n (defer m A p) (limit_profile (defer m A p) p) = {}" and
      disj_p: "disjoint3 (m A p)" and
      disj_limit:
      "disjoint3 (n (defer m A p) (limit_profile (defer m A p) p))" and
      mod_m: "electoral_module m" and
      mod_n: "electoral_module n" and
      fin_A: "finite A" and
      prof_A: "profile A p" and
      x_in_def:
      "x \<in> defer n (defer m A p) (limit_profile (defer m A p) p)" and
      x_in_rej:
      "x \<in> reject n (defer m A p) (limit_profile (defer m A p) p)"
    from x_in_def x_in_rej
    show "x \<in> {}"
      using fin_def module_n prof_def_lim reject_not_elec_or_def
      by fastforce
  qed
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
  unfolding electoral_module_def
proof (safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p"
  have "\<forall>r. well_formed (A::'a set) r =
          (disjoint3 r \<and> set_equals_partition A r)"
    by simp
  thus "well_formed A ((m \<triangleright> n) A p)"
    using module_m module_n seq_comp_presv_disj
          seq_comp_presv_alts fin_A prof_A
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
proof
  have
    "\<forall>f A prof.
      (electoral_module f \<and> finite_profile A prof) \<longrightarrow>
        finite_profile (defer f A prof)
          (limit_profile (defer f A prof) prof)"
    using def_presv_fin_prof
    by metis
  hence prof_no_alt:
    "profile {} (limit_profile (defer m A p) p)"
    using empty_defer f_prof module_m
    by metis
  hence
    "(elect m A p) \<union>
      (elect n (defer m A p)
        (limit_profile (defer m A p) p))
    = elect m A p"
    using elect_in_alts empty_defer module_n
    by auto
  thus "elect (m \<triangleright> n) A p = elect m A p"
    using fst_conv sequential_composition.simps
    by metis
next
  have rej_empty:
    "\<forall>f prof.
      (electoral_module f \<and> profile ({}::'a set) prof) \<longrightarrow>
        reject f {} prof = {}"
    using bot.extremum_uniqueI infinite_imp_nonempty reject_in_alts
    by metis
  have prof_no_alt:
    "profile {} (limit_profile (defer m A p) p)"
    using empty_defer f_prof module_m limit_profile_sound
    by auto
  hence
    "(reject m A p, defer n {} (limit_profile {} p)) =
        snd (m A p)"
    using bot.extremum_uniqueI defer_in_alts empty_defer
          infinite_imp_nonempty module_n prod.collapse
    by (metis (no_types))
  thus "snd ((m \<triangleright> n) A p) = snd (m A p)"
    using rej_empty empty_defer module_n prof_no_alt
    by auto
qed

lemma seq_comp_def_then_elect:
  assumes
    n_electing_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n" and
    f_prof: "finite_profile A p"
  shows "elect (m \<triangleright> n) A p = defer m A p"
proof cases
  assume "A = {}"
  with electing_n n_electing_m f_prof
  show ?thesis
    using bot.extremum_uniqueI defer_in_alts elect_in_alts
          electing_def non_electing_def seq_comp_sound
    by metis
next
  assume assm: "A \<noteq> {}"
  from n_electing_m f_prof
  have ele: "elect m A p = {}"
    using non_electing_def
    by auto
  from assm def_one_m f_prof finite
  have def_card:
    "card (defer m A p) = 1"
    by (simp add: Suc_leI card_gt_0_iff defers_def)
  with n_electing_m f_prof
  have def:
    "\<exists>a \<in> A. defer m A p = {a}"
    using card_1_singletonE defer_in_alts
          non_electing_def singletonI subsetCE
    by metis
  from ele def n_electing_m
  have rej:
    "\<exists>a \<in> A. reject m A p = A-{a}"
    using Diff_empty def_one_m defers_def
          f_prof reject_not_elec_or_def
    by metis
  from ele rej def n_electing_m f_prof
  have res_m:
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
  with def_card def electing_n n_electing_m f_prof
  have
    "\<exists>a \<in> A. elect (m \<triangleright> n) A p = {a}"
    using electing_for_only_alt non_electing_def prod.sel
          sequential_composition.simps def_presv_fin_prof
          sup_bot.left_neutral
    by metis
  with def def_card electing_n n_electing_m f_prof res_m
  show ?thesis
    using def_presv_fin_prof electing_for_only_alt fst_conv
          non_electing_def sequential_composition.simps
          sup_bot.left_neutral
    by metis
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
  fix
    A :: "'a set" and
    p :: "'a Profile"
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
  proof (unfold non_blocking_def)
    assume
      emod_reject_m:
      "electoral_module m \<and>
        (\<forall>A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow>
          reject m A p \<noteq> A)" and
      emod_reject_n:
      "electoral_module n \<and>
        (\<forall>A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow>
          reject n A p \<noteq> A)"
    show
      "electoral_module (m \<triangleright> n) \<and>
        (\<forall>A p.
          A \<noteq> {} \<and> finite_profile A p \<longrightarrow>
            reject (m \<triangleright> n) A p \<noteq> A)"
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
      have fin_defer:
        "finite_profile (defer m A p) (limit_profile (defer m A p) p)"
        using def_presv_fin_prof
        by (metis (no_types))
      from emod_reject_m emod_reject_n fin_A prof_A
      have seq_elect:
        "elect (m \<triangleright> n) A p =
          elect n (defer m A p) (limit_profile (defer m A p) p) \<union>
            elect m A p"
        using seq_comp_def_then_elect_elec_set
        by metis
      from emod_reject_n emod_reject_m fin_A prof_A
      have def_limit:
        "defer (m \<triangleright> n) A p =
          defer n (defer m A p) (limit_profile (defer m A p) p)"
        using seq_comp_defers_def_set
        by metis
      from emod_reject_n emod_reject_m fin_A prof_A
      have
        "elect (m \<triangleright> n) A p \<union> defer (m \<triangleright> n) A p = A - reject (m \<triangleright> n) A p"
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
        using rej_def_eq_set result_disj fin_defer
        using Diff_cancel Diff_empty emod_reject_m emod_reject_n
              fin_A prof_A reject_not_elec_or_def x_in_A
        by metis
    qed
  qed
qed

(*Sequential composition preserves the non-electing property.*)
theorem seq_comp_presv_non_electing[simp]:
  assumes
    m_elect: "non_electing m" and
    n_elect: "non_electing n"
  shows "non_electing (m \<triangleright> n)"
  unfolding non_electing_def
proof (safe)
  from m_elect n_elect
  have "electoral_module m \<and> electoral_module n"
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
  with m_elect n_elect
  show "x \<in> {}"
    unfolding non_electing_def
    using seq_comp_def_then_elect_elec_set def_presv_fin_prof
          Diff_empty Diff_partition empty_subsetI
    by metis
qed

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
  hence def_m1_not_empty:
    "\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow>
        defer m1 A p \<noteq> {}"
    using One_nat_def Suc_leI card_eq_0_iff
          card_gt_0_iff zero_neq_one
    by metis
  thus ?thesis
    using Un_empty def_one_m1 defers_def electing_def
          electing_m2 seq_comp_def_then_elect_elec_set
          seq_comp_sound def_presv_fin_prof
  proof -
    obtain
      f_set ::
      "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> 'a set" and
      f_prof ::
      "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> 'a Profile" where
      f_mod:
      "\<forall>f.
        (\<not> electing f \<or> electoral_module f \<and>
          (\<forall>A prof.
            (A \<noteq> {} \<and> finite A \<and> profile A prof) \<longrightarrow>
              elect f A prof \<noteq> {})) \<and>
        (electing f \<or> \<not> electoral_module f \<or> f_set f \<noteq> {} \<and> finite (f_set f) \<and>
          profile (f_set f) (f_prof f) \<and> elect f (f_set f) (f_prof f) = {})"
      unfolding electing_def
      by moura
    hence f_elect:
      "electoral_module m2 \<and>
        (\<forall>A prof. (A \<noteq> {} \<and> finite A \<and> profile A prof) \<longrightarrow> elect m2 A prof \<noteq> {})"
      using electing_m2
      by metis
    have def_card_one:
      "electoral_module m1 \<and>
        (\<forall>A prof.
          (1 \<le> card A \<and> finite A \<and> profile A prof) \<longrightarrow>
            card (defer m1 A prof) = 1)"
      using def_one_m1 defers_def
      by blast
    hence "electoral_module (m1 \<triangleright> m2)"
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
    from def_and_lifted
    have "finite_profile A q"
      by (simp add: lifted_def)
    with modules new_A_eq
    have 1:
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
    moreover from def_and_lifted
    have eql_lengths:
      "length ?new_p = length ?new_q"
      by (simp add: lifted_def)
    ultimately have 0:
      "(\<forall>i::nat. i < length ?new_p \<longrightarrow>
          \<not>Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a) \<or>
       (\<exists>i::nat. i < length ?new_p \<and>
          \<not>Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<and>
              (?new_p!i) \<noteq> (?new_q!i))"
      using a2 lifted_def
      by (metis (no_types, lifting))
    from def_and_lifted modules have
      "\<forall>i. (0 \<le> i \<and> i < length ?new_p) \<longrightarrow>
          (Preference_Relation.lifted A (p!i) (q!i) a \<or> (p!i) = (q!i))"
      using defer_in_alts Profile.lifted_def limit_prof_presv_size
      by metis
    with def_and_lifted modules mono_m have
      "\<forall>i. (0 \<le> i \<and> i < length ?new_p) \<longrightarrow>
          (Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<or>
           (?new_p!i) = (?new_q!i))"
      using limit_lifted_imp_eq_or_lifted defer_in_alts
            Profile.lifted_def limit_prof_presv_size
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
  unfolding defers_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using non_electing_m
    by (simp add: non_electing_def)
  have electoral_mod_n: "electoral_module n"
    using def_1_n
    by (simp add: defers_def)
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    pos_card: "1 \<le> card A" and
    fin_A: "finite A" and
    prof_A: "profile A p"
  from pos_card have
    "A \<noteq> {}"
    by auto
  with fin_A prof_A have m_non_blocking:
    "reject m A p \<noteq> A"
    using non_blocking_m non_blocking_def
    by metis
  hence
    "\<exists>a. a \<in> A \<and> a \<notin> reject m A p"
    using pos_card non_electing_def non_electing_m
          reject_in_alts subset_antisym subset_iff
          fin_A prof_A subsetI
    by metis
  hence "defer m A p \<noteq> {}"
    using electoral_mod_defer_elem empty_iff pos_card
          non_electing_def non_electing_m fin_A prof_A
    by (metis (no_types))
  hence defer_non_empty:
    "card (defer m A p) \<ge> 1"
    using One_nat_def Suc_leI card_gt_0_iff pos_card fin_A prof_A
          non_blocking_def non_blocking_m def_presv_fin_prof
    by metis
  have defer_fun:
    "defer (m \<triangleright> n) A p =
      defer n (defer m A p) (limit_profile (defer m A p) p)"
    using def_1_n defers_def fin_A non_blocking_def non_blocking_m
          prof_A seq_comp_defers_def_set
    by (metis (no_types, hide_lams))
  have
    "\<forall>n f. defers n f =
      (electoral_module f \<and>
        (\<forall>A prof.
          (\<not> n \<le> card (A::'a set) \<or> infinite A \<or>
            \<not> profile A prof) \<or>
          card (defer f A prof) = n))"
    using defers_def
    by blast
  hence
    "card (defer n (defer m A p)
      (limit_profile (defer m A p) p)) = 1"
    using defer_non_empty def_1_n
          fin_A prof_A non_blocking_def
          non_blocking_m def_presv_fin_prof
    by metis
  thus "card (defer (m \<triangleright> n) A p) = 1"
    using defer_fun
    by auto
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
  unfolding disjoint_compatibility_def
proof (safe)
  show "electoral_module (m \<triangleright> m2)"
    using compatible disjoint_compatibility_def
          module_m2 seq_comp_sound
    by metis
next
  show "electoral_module n"
    using compatible disjoint_compatibility_def
    by metis
next
  fix
    S :: "'a set"
  assume
    fin_S: "finite S"
  have modules:
    "electoral_module (m \<triangleright> m2) \<and> electoral_module n"
    using compatible disjoint_compatibility_def
          module_m2 seq_comp_sound
    by metis
  obtain A where A:
    "A \<subseteq> S \<and>
      (\<forall>a \<in> A. indep_of_alt m S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
    using compatible disjoint_compatibility_def fin_S
    by (metis (no_types, lifting))
  show
    "\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
  proof
    have
      "\<forall>a p q.
        a \<in> A \<and> equiv_prof_except_a S p q a \<longrightarrow>
          (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
    proof (safe)
      fix
        a :: "'a" and
        p :: "'a Profile" and
        q :: "'a Profile"
      assume
        a: "a \<in> A" and
        b: "equiv_prof_except_a S p q a"
      have eq_def:
        "defer m S p = defer m S q"
        using A a b indep_of_alt_def
        by metis
      from a b have profiles:
        "finite_profile S p \<and> finite_profile S q"
        using equiv_prof_except_a_def
        by fastforce
      hence "(defer m S p) \<subseteq> S"
        using compatible defer_in_alts disjoint_compatibility_def
        by blast
      hence
        "limit_profile (defer m S p) p =
          limit_profile (defer m S q) q"
        using A DiffD2 a b compatible defer_not_elec_or_rej
              disjoint_compatibility_def eq_def profiles
              negl_diff_imp_eq_limit_prof
        by (metis (no_types, lifting))
      with eq_def have
        "m2 (defer m S p) (limit_profile (defer m S p) p) =
          m2 (defer m S q) (limit_profile (defer m S q) q)"
        by simp
      moreover have "m S p = m S q"
        using A a b indep_of_alt_def
        by metis
      ultimately show
        "(m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
        using sequential_composition.simps
        by (metis (full_types))
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
  unfolding monotonicity_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using non_ele_m
    by (simp add: non_electing_def)
  have electoral_mod_n: "electoral_module n"
    using electing_n
    by (simp add: electing_def)
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    w :: "'a"
  assume
    fin_A: "finite A" and
    elect_w_in_p: "w \<in> elect (m \<triangleright> n) A p" and
    lifted_w: "Profile.lifted A p q w"
  have
    "finite_profile A p \<and> finite_profile A q"
    using lifted_w lifted_def
    by metis
  thus "w \<in> elect (m \<triangleright> n) A q"
    using seq_comp_def_then_elect defer_lift_invariance_def
          elect_w_in_p lifted_w def_monotone_m non_ele_m
          def_one_m electing_n
    by metis
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
  unfolding defer_lift_invariance_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using defer_invariant_monotonicity_def
          strong_def_mon_m
    by auto
  have electoral_mod_n: "electoral_module n"
    using defers_1 defers_def
    by auto
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
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
  from strong_def_mon_m
  have non_electing_m: "non_electing m"
    by (simp add: defer_invariant_monotonicity_def)
  have electoral_mod_m: "electoral_module m"
    using strong_def_mon_m defer_invariant_monotonicity_def
    by auto
  have electoral_mod_n: "electoral_module n"
    using defers_1 defers_def
    by auto
  have finite_profile_q: "finite_profile A q"
    using lifted_a
    by (simp add: Profile.lifted_def)
  have finite_profile_p: "profile A p"
    using lifted_a
    by (simp add: Profile.lifted_def)
  show "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof cases
    assume not_unchanged: "defer m A q \<noteq> defer m A p"
    from not_unchanged
    have a_single_defer: "{a} = defer m A q"
      using strong_def_mon_m electoral_mod_n defer_a_p
            defer_invariant_monotonicity_def lifted_a
            seq_comp_def_set_trans finite_profile_p
            finite_profile_q
      by metis
    moreover have
      "{a} = defer m A q \<longrightarrow> defer (m \<triangleright> n) A q \<subseteq> {a}"
      using finite_profile_q electoral_mod_m electoral_mod_n
            seq_comp_def_set_sound
      by (metis (no_types, hide_lams))
    ultimately have
      "(a \<in> defer m A p) \<longrightarrow> defer (m \<triangleright> n) A q \<subseteq> {a}"
      by blast (* lifted defer-subset of a *)
    moreover have def_card_one:
      "(a \<in> defer m A p) \<longrightarrow> card (defer (m \<triangleright> n) A q) = 1"
      using One_nat_def a_single_defer card_eq_0_iff
            card_insert_disjoint defers_1 defers_def
            electoral_mod_m empty_iff finite.emptyI
            seq_comp_defers_def_set order_refl
            def_presv_fin_prof finite_profile_q
      by metis (* lifted defer set size 1 *)
    moreover have defer_a_in_m_p:
      "a \<in> defer m A p"
      using electoral_mod_m electoral_mod_n defer_a_p
            seq_comp_def_set_bounded finite_profile_p
            finite_profile_q
      by blast
    ultimately have
      "defer (m \<triangleright> n) A q = {a}" (* lifted defer set = a *)
      using Collect_mem_eq card_1_singletonE empty_Collect_eq
            insertCI subset_singletonD
      by metis
    moreover have
      "defer (m \<triangleright> n) A p = {a}" (* regular defer set = a *)
    proof (safe)
      fix x :: "'a"
      assume
      defer_x: "x \<in> defer (m \<triangleright> n) A p" and
      x_exists: "x \<notin> {}"
      show "x = a"
      proof -
        have fin_defer:
          "\<forall>f (A::'a set) prof.
            (electoral_module f \<and> finite A \<and> profile A prof) \<longrightarrow>
              finite_profile (defer f A prof)
                (limit_profile (defer f A prof) prof)"
          using def_presv_fin_prof
          by (metis (no_types))
        have "finite_profile (defer m A p) (limit_profile (defer m A p) p)"
          using electoral_mod_m finite_profile_p finite_profile_q fin_defer
          by blast
        hence "Suc (card (defer m A p - {a})) = card (defer m A p)"
          using card_Suc_Diff1 defer_a_in_m_p
          by metis
        hence min_card:
          "Suc 0 \<le> card (defer m A p)"
          by linarith
        have emod_n_then_mn:
          "electoral_module n \<longrightarrow> electoral_module (m \<triangleright> n)"
          using electoral_mod_m
          by simp
        have "defers (Suc 0) n"
          using defers_1
          by auto
        hence defer_card_one:
          "electoral_module n \<and>
            (\<forall>A prof.
              (Suc 0 \<le> card A \<and> finite A \<and> profile A prof) \<longrightarrow>
                card (defer n A prof) = Suc 0)"
          by (simp add: defers_def)
        hence emod_mn: "electoral_module (m \<triangleright> n)"
          using emod_n_then_mn
          by blast
        have nat_diff:
          "\<forall> (i::nat) j. i \<le> j \<longrightarrow> i - j = 0"
          by auto
        have nat_comp:
          "\<forall> (i::nat) j k.
            i \<le> j \<and> j \<le> k \<or>
              j \<le> i \<and> i \<le> k \<or>
              i \<le> k \<and> k \<le> j \<or>
              k \<le> j \<and> j \<le> i \<or>
              j \<le> k \<and> k \<le> i \<or>
              k \<le> i \<and> i \<le> j"
          using le_cases3
          by linarith
        have fin_diff_card:
          "\<forall>A a.
            (finite A \<and> (a::'a) \<in> A) \<longrightarrow>
              card (A - {a}) = card A - 1"
          using card_Diff_singleton
          by metis
        with fin_defer defer_card_one min_card
        have "card (defer (m \<triangleright> n) A p) = Suc 0"
          using electoral_mod_m seq_comp_defers_def_set
                finite_profile_p finite_profile_q
          by metis
        with fin_diff_card nat_comp nat_diff emod_mn fin_defer
        have "{a} = {x}"
          using One_nat_def card_1_singletonE singletonD
                defer_a_p defer_x
          by metis
        thus ?thesis
          by force
      qed
    next
      show "a \<in> defer (m \<triangleright> n) A p"
        using defer_a_p
        by linarith
    qed
    ultimately have (* defer sets equal *)
      "defer (m \<triangleright> n) A p = defer (m \<triangleright> n) A q"
      by blast
    moreover have (* elect sets sets equal *)
      "elect (m \<triangleright> n) A p = elect (m \<triangleright> n) A q"
      using finite_profile_p finite_profile_q
            non_electing_m non_electing_n
            seq_comp_presv_non_electing
            non_electing_def
      by metis (* elect sets equal *)
    thus ?thesis
      using calculation eq_def_and_elect_imp_eq
            electoral_mod_m electoral_mod_n
            finite_profile_p seq_comp_sound
            finite_profile_q
      by metis
  next
    assume not_different_alternatives:
      "\<not>(defer m A q \<noteq> defer m A p)"
    have "elect m A p = {}"
      using non_electing_m finite_profile_p finite_profile_q
      by (simp add: non_electing_def)
    moreover have "elect m A q = {}"
      using non_electing_m finite_profile_q
      by (simp add: non_electing_def)
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
            lifted_a finite_profile_q
            limit_prof_eq_or_lifted
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
        using elect_m_equal same_alternatives
              finite_profile_p finite_profile_q
        by (simp add: electoral_mod_m eq_def_and_elect_imp_eq)
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
        using electoral_mod_m electoral_mod_n
              finite_profile_p defer_a_p
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
              equals0D finite_profile_p defer_a_p
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
        "{a} = defer n (defer m A p) (limit_profile (defer m A p) p)"
        using a_still_deferred_p card_1_singletonE
              insert_subset singletonD
        by metis
      have a_still_deferred_q:
        "a \<in> defer n (defer m A q)
          (limit_profile (defer m A p) q)"
        using still_lifted a_in_def_p
              defer_monotonicity_def
              defer_monotone_n electoral_mod_m
              same_alternatives
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
        using seq_comp_presv_non_electing
              eq_def_and_elect_imp_eq non_electing_def
              finite_profile_p finite_profile_q
              non_electing_m non_electing_n
              seq_comp_defers_def_set
        by metis
    qed
  qed
qed

end

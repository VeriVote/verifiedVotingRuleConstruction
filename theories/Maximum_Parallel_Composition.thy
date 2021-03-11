(*  File:       Maximum_Parallel_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Maximum Parallel Composition\<close>

theory Maximum_Parallel_Composition
  imports Parallel_Composition Maximum_Aggregator
begin

text
\<open>This is a family of parallel compositions. It composes a new electoral module
from two electoral modules combined with the maximum aggregator. Therein, the
two modules each make a decision and then a partition is returned where every
alternative receives the maximum result of the two input partitions. This means
that, if any alternative is elected by at least one of the modules, then it
gets elected, if any non-elected alternative is deferred by at least one of the
modules, then it gets deferred, only alternatives rejected by both modules get
rejected.\<close>

subsection \<open>Definition\<close>

fun maximum_parallel_composition :: "'a Electoral_Module \<Rightarrow>
        'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "maximum_parallel_composition m n =
    (let a = max_aggregator in (m \<parallel>\<^sub>a n))"

subsection \<open>Soundness\<close>

theorem max_par_comp_sound:
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n"
  shows "electoral_module (maximum_parallel_composition m n)"
  using mod_m mod_n
  by simp

subsection \<open>Lemmata\<close>

lemma max_agg_eq_result:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    in_A: "x \<in> A"
  shows
    "mod_contains_result (maximum_parallel_composition m n) m A p x \<or> 
      mod_contains_result (maximum_parallel_composition m n) n A p x"
proof cases
  assume a1: "x \<in> elect (maximum_parallel_composition m n) A p"
  hence
    "let (e1, r1, d1) = m A p;
        (e2, r2, d2) = n A p in
      x \<in> e1 \<union> e2"
    by auto
  hence "x \<in> (elect m A p) \<union> (elect n A p)"
    by auto
  thus ?thesis
    using IntI Un_iff a1 empty_iff mod_contains_result_def
          in_A max_agg_sound module_m module_n par_comp_sound
          f_prof result_disj maximum_parallel_composition.simps
    by (smt (verit, ccfv_threshold))
next
  assume not_a1: "x \<notin> elect (maximum_parallel_composition m n) A p"
  thus ?thesis
  proof cases
    assume a2: "x \<in> defer (maximum_parallel_composition m n) A p"
    thus ?thesis
      using CollectD DiffD1 DiffD2 max_aggregator.simps Un_iff 
            case_prod_conv defer_not_elec_or_rej max_agg_sound
            mod_contains_result_def module_m module_n par_comp_sound
            parallel_composition.simps prod.collapse f_prof sndI
            Int_iff electoral_mod_defer_elem electoral_module_def
            max_agg_rej_set prod.sel(1) maximum_parallel_composition.simps
      by (smt (verit, del_insts))
  next
    assume not_a2: "x \<notin> defer (maximum_parallel_composition m n) A p"
    with not_a1 have a3:
      "x \<in> reject (maximum_parallel_composition m n) A p"
      using electoral_mod_defer_elem in_A max_agg_sound module_m module_n
            par_comp_sound f_prof maximum_parallel_composition.simps
      by metis
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> fst (snd (max_aggregator A (e1, r1, d1) (e2, r2, d2)))"
      using case_prod_unfold parallel_composition.simps
            surjective_pairing maximum_parallel_composition.simps
      by (smt (verit, ccfv_threshold))
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    thus ?thesis
      using Un_iff combine_ele_rej_def agg_conservative_def
            contra_subsetD disjoint_iff_not_equal in_A
            electoral_module_def mod_contains_result_def
            max_agg_consv module_m module_n par_comp_sound
            parallel_composition.simps f_prof result_disj
            max_agg_rej_set not_a1 not_a2 Int_iff
            maximum_parallel_composition.simps
      by (smt (verit, del_insts))
  qed
qed

lemma max_agg_rej_iff_both_reject:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n"
  shows
    "x \<in> reject (maximum_parallel_composition m n) A p \<longleftrightarrow>
      (x \<in> reject m A p \<and> x \<in> reject n A p)"
proof -
  have
    "x \<in> reject (maximum_parallel_composition m n) A p \<longrightarrow>
      (x \<in> reject m A p \<and> x \<in> reject n A p)"
  proof
    assume a: "x \<in> reject (maximum_parallel_composition m n) A p"
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> fst (snd (max_aggregator A (e1, r1, d1) (e2, r2, d2)))"
      using case_prodI2 maximum_parallel_composition.simps split_def
            parallel_composition.simps prod.collapse split_beta
      by (smt (verit, ccfv_threshold))
    hence
      "let (e1, r1, d1) = m A p; 
          (e2, r2, d2) = n A p in
        x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    thus "x \<in> reject m A p \<and> x \<in> reject n A p"
      using Int_iff a electoral_module_def max_agg_rej_set module_m
            module_n parallel_composition.simps surjective_pairing
            maximum_parallel_composition.simps f_prof
      by (smt (verit, best))
  qed
  moreover have
    "(x \<in> reject m A p \<and> x \<in> reject n A p) \<longrightarrow>
        x \<in> reject (maximum_parallel_composition m n) A p"
  proof
    assume a: "x \<in> reject m A p \<and> x \<in> reject n A p"
    hence
      "x \<notin> elect m A p \<and> x \<notin> defer m A p \<and>
        x \<notin> elect n A p \<and> x \<notin> defer n A p"
      using IntI empty_iff module_m module_n f_prof result_disj
      by metis
    thus "x \<in> reject (maximum_parallel_composition m n) A p"
      using CollectD DiffD1 max_aggregator.simps Un_iff a
            electoral_mod_defer_elem prod.simps max_agg_sound
            module_m module_n f_prof old.prod.inject par_comp_sound
            prod.collapse parallel_composition.simps
            reject_not_elec_or_def maximum_parallel_composition.simps
      by (smt (verit, ccfv_threshold))
  qed
  ultimately show ?thesis
    by blast
qed

lemma max_agg_rej1:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject n A p"
  shows
    "mod_contains_result m (maximum_parallel_composition m n) A p x"
  using Set.set_insert contra_subsetD disjoint_insert
        mod_contains_result_comm mod_contains_result_def
        max_agg_eq_result max_agg_rej_iff_both_reject
        module_m module_n f_prof reject_in_alts rejected
        result_disj
  by (smt (verit, best))

lemma max_agg_rej2:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject n A p"
  shows
    "mod_contains_result (maximum_parallel_composition m n) m A p x"
  using mod_contains_result_comm max_agg_rej1
        module_m module_n f_prof rejected
  by metis

lemma max_agg_rej3:
  assumes
    f_prof:  "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject m A p"
  shows
    "mod_contains_result n (maximum_parallel_composition m n) A p x"
  using contra_subsetD disjoint_iff_not_equal result_disj
        mod_contains_result_comm mod_contains_result_def
        max_agg_eq_result max_agg_rej_iff_both_reject
        module_m module_n f_prof reject_in_alts rejected
  by (smt (verit, ccfv_SIG))

lemma max_agg_rej4:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject m A p"
  shows
    "mod_contains_result (maximum_parallel_composition m n) n A p x"
  using mod_contains_result_comm max_agg_rej3
        module_m module_n f_prof rejected
  by metis

lemma max_agg_rej_intersect:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows
    "reject (maximum_parallel_composition m n) A p =
      (reject m A p) \<inter> (reject n A p)"
proof -
  have
    "A = (elect m A p) \<union> (reject m A p) \<union> (defer m A p) \<and>
      A = (elect n A p) \<union> (reject n A p) \<union> (defer n A p)"
    by (simp add: module_m module_n f_prof result_presv_alts)
  hence
    "A - ((elect m A p) \<union> (defer m A p)) = (reject m A p) \<and>
      A - ((elect n A p) \<union> (defer n A p)) = (reject n A p)"
    using module_m module_n f_prof reject_not_elec_or_def
    by auto
  hence
    "A - ((elect m A p) \<union> (elect n A p) \<union> (defer m A p) \<union> (defer n A p)) =
      (reject m A p) \<inter> (reject n A p)"
    by blast
  hence
    "let (e1, r1, d1) = m A p;
        (e2, r2, d2) = n A p in
      A - (e1 \<union> e2 \<union> d1 \<union> d2) = r1 \<inter> r2"
    by fastforce
  thus ?thesis
    by auto
qed

lemma dcompat_dec_by_one_mod:
  assumes
    compatible: "disjoint_compatibility m n" and
    in_A: "x \<in> A"
  shows
    "(\<forall>p. finite_profile A p \<longrightarrow>
          mod_contains_result m (maximum_parallel_composition m n) A p x) \<or>
        (\<forall>p. finite_profile A p \<longrightarrow>
          mod_contains_result n (maximum_parallel_composition m n) A p x)"
  using DiffI compatible disjoint_compatibility_def
        in_A max_agg_rej1 max_agg_rej3
  by metis

subsection \<open>Composition Rules\<close>

(*
   Using a conservative aggregator, the parallel composition
   preserves the property non-electing.
*)
theorem conserv_max_agg_presv_non_electing[simp]:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n"
  shows "non_electing (maximum_parallel_composition m n)"
  using non_electing_m non_electing_n
  by simp

(*
   Using the max aggregator, composing two compatible
   electoral modules in parallel preserves defer-lift-invariance.
*)
theorem par_comp_def_lift_inv[simp]:
  assumes
    compatible: "disjoint_compatibility m n" and
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (maximum_parallel_composition m n)"
proof -
  have
    "\<forall>S p q x.
      (x \<in> (defer (maximum_parallel_composition m n) S p) \<and>
          lifted S p q x) \<longrightarrow>
        (maximum_parallel_composition m n) S p =
          (maximum_parallel_composition m n) S q"
  proof
    fix S :: "'a set"
    show
      "\<forall>p q x.
        (x \<in> (defer (maximum_parallel_composition m n) S p) \<and>
            lifted S p q x) \<longrightarrow>
          (maximum_parallel_composition m n) S p =
            (maximum_parallel_composition m n) S q"
    proof
      fix p :: "'a Profile"
      show
        "\<forall>q x.
          (x \<in> (defer (maximum_parallel_composition m n) S p) \<and>
              lifted S p q x) \<longrightarrow>
            (maximum_parallel_composition m n) S p =
              (maximum_parallel_composition m n) S q"
      proof
        fix q :: "'a Profile"
        show
          "\<forall> x.
            (x \<in> (defer (maximum_parallel_composition m n) S p) \<and>
                lifted S p q x) \<longrightarrow>
              (maximum_parallel_composition m n) S p =
                (maximum_parallel_composition m n) S q"
        proof
          fix x :: "'a"
          show
            "(x \<in> (defer (maximum_parallel_composition m n) S p) \<and>
                lifted S p q x) \<longrightarrow>
              (maximum_parallel_composition m n) S p =
                (maximum_parallel_composition m n) S q"
          proof
            assume a:
              "x \<in> (defer (maximum_parallel_composition m n) S p) \<and>
                lifted S p q x"
            hence f_profs: "finite_profile S p \<and> finite_profile S q"
              by (simp add: lifted_def)
            from compatible obtain A::"'a set" where A:
              "A \<subseteq> S \<and> (\<forall>x \<in> A. indep_of_alt m S x \<and>
                  (\<forall>p. finite_profile S p \<longrightarrow> x \<in> reject m S p)) \<and>
                (\<forall>x \<in> S-A. indep_of_alt n S x \<and>
                  (\<forall>p. finite_profile S p \<longrightarrow> x \<in> reject n S p))"
              using disjoint_compatibility_def f_profs
              by (metis (no_types, lifting))
            have
              "\<forall>x \<in> S.
                prof_contains_result
                  (maximum_parallel_composition m n) S p q x"
            proof cases
              assume a0: "x \<in> A"
              hence "x \<in> reject m S p"
                using A f_profs
                by blast
              with a have defer_n: "x \<in> defer n S p"
                using compatible disjoint_compatibility_def
                      mod_contains_result_def f_profs max_agg_rej4
                by metis
              have
                "\<forall>x \<in> A.
                  mod_contains_result
                    (maximum_parallel_composition m n) n S p x"
                using A compatible disjoint_compatibility_def
                      max_agg_rej4 f_profs
                by metis
              moreover have "\<forall>x \<in> S. prof_contains_result n S p q x"
                using defer_n a prof_contains_result_def monotone_n f_profs
                      defer_lift_invariance_def
                by (smt (verit, del_insts))
              moreover have
                "\<forall>x \<in> A.
                  mod_contains_result n
                    (maximum_parallel_composition m n) S q x"
                using A compatible disjoint_compatibility_def
                      max_agg_rej3 f_profs
                by metis
              ultimately have 00:
                "\<forall>x \<in> A.
                  prof_contains_result
                    (maximum_parallel_composition m n) S p q x"
                by (simp add: mod_contains_result_def prof_contains_result_def)
              have
                "\<forall>x \<in> S-A.
                  mod_contains_result
                    (maximum_parallel_composition m n) m S p x"
                using A max_agg_rej2 monotone_m monotone_n f_profs
                      defer_lift_invariance_def
                by metis
              moreover have "\<forall>x \<in> S. prof_contains_result m S p q x"
                using A a a0 prof_contains_result_def indep_of_alt_def
                      lifted_imp_equiv_prof_except_a f_profs IntI
                      electoral_mod_defer_elem empty_iff result_disj
                by (smt (verit, ccfv_threshold))
              moreover have
                "\<forall>x \<in> S-A.
                  mod_contains_result m
                    (maximum_parallel_composition m n) S q x"
                using A max_agg_rej1 monotone_m monotone_n f_profs
                      defer_lift_invariance_def
                by metis
              ultimately have 01:
                "\<forall>x \<in> S-A.
                  prof_contains_result
                    (maximum_parallel_composition m n) S p q x"
                by (simp add: mod_contains_result_def prof_contains_result_def)
              from 00 01
              show ?thesis
                by blast
            next
              assume "x \<notin> A"
              hence a1: "x \<in> S-A"
                using DiffI a compatible f_profs
                      Electoral_Module.lifted_def
                by (metis (no_types, lifting))
              hence "x \<in> reject n S p"
                using A f_profs
                by blast
              with a have defer_n: "x \<in> defer m S p"
                using DiffD1 DiffD2 compatible dcompat_dec_by_one_mod
                      defer_not_elec_or_rej disjoint_compatibility_def
                      not_rej_imp_elec_or_def mod_contains_result_def
                      max_agg_sound par_comp_sound f_profs
                      maximum_parallel_composition.simps
                by metis
              have
                "\<forall>x \<in> A.
                  mod_contains_result
                    (maximum_parallel_composition m n) n S p x"
                using A compatible disjoint_compatibility_def
                      max_agg_rej4 f_profs
                by metis
              moreover have "\<forall>x \<in> S. prof_contains_result n S p q x"
                using A a a1 prof_contains_result_def indep_of_alt_def
                      lifted_imp_equiv_prof_except_a f_profs
                      electoral_mod_defer_elem
                by (smt (verit, ccfv_threshold))
              moreover have
                "\<forall>x \<in> A.
                  mod_contains_result n
                    (maximum_parallel_composition m n) S q x"
                using A compatible disjoint_compatibility_def
                      max_agg_rej3 f_profs
                by metis
              ultimately have 10:
                "\<forall>x \<in> A.
                  prof_contains_result
                    (maximum_parallel_composition m n) S p q x"
                by (simp add: mod_contains_result_def prof_contains_result_def)
              have
                "\<forall>x \<in> S-A.
                  mod_contains_result
                    (maximum_parallel_composition m n) m S p x"
                using A max_agg_rej2 monotone_m monotone_n
                      f_profs defer_lift_invariance_def
                by metis
              moreover have "\<forall>x \<in> S. prof_contains_result m S p q x"
                using a defer_n prof_contains_result_def monotone_m
                      f_profs defer_lift_invariance_def
                by (smt (verit, ccfv_threshold))
              moreover have
                "\<forall>x \<in> S-A.
                  mod_contains_result m
                    (maximum_parallel_composition m n) S q x"
                using A max_agg_rej1 monotone_m monotone_n
                      f_profs defer_lift_invariance_def
                by metis
              ultimately have 11:
                "\<forall>x \<in> S-A.
                  prof_contains_result
                    (maximum_parallel_composition m n) S p q x"
                by (simp add: electoral_mod_defer_elem
                    mod_contains_result_def prof_contains_result_def)
              from 10 11
              show ?thesis
                by blast
            qed
            thus
              "(maximum_parallel_composition m n) S p =
                (maximum_parallel_composition m n) S q"
              using compatible disjoint_compatibility_def f_profs
                    eq_alts_in_profs_imp_eq_results max_par_comp_sound
              by metis
          qed
        qed
      qed
    qed
  qed
  thus ?thesis
    using monotone_m monotone_n max_par_comp_sound
          defer_lift_invariance_def
    by (metis (full_types))
qed

lemma par_comp_rej_card:
  assumes
    compatible: "disjoint_compatibility x y" and
    f_prof: "finite_profile S p" and
    reject_sum: "card (reject x S p) + card (reject y S p) = card S + n"
  shows "card (reject (maximum_parallel_composition x y) S p) = n"
proof -
  from compatible obtain A where A:
    "A \<subseteq> S \<and>
      (\<forall>a \<in> A. indep_of_alt x S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject x S p)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt y S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject y S p))"
    using disjoint_compatibility_def f_prof
    by metis
  from f_prof compatible
  have reject_representation:
    "reject (maximum_parallel_composition x y) S p =
      (reject x S p) \<inter> (reject y S p)"
    using max_agg_rej_intersect disjoint_compatibility_def
    by blast
  have "electoral_module x \<and> electoral_module y"
    using compatible disjoint_compatibility_def
    by auto
  hence subsets: "(reject x S p) \<subseteq> S \<and> (reject y S p) \<subseteq> S"
    by (simp add: f_prof reject_in_alts)
  hence "finite (reject x S p) \<and> finite (reject y S p)"
    using rev_finite_subset f_prof reject_in_alts
    by auto
  hence 0:
    "card (reject (maximum_parallel_composition x y) S p) =
        card S + n -
          card ((reject x S p) \<union> (reject y S p))"
    using card_Un_Int reject_representation reject_sum
    by fastforce
  have "\<forall>a \<in> S. a \<in> (reject x S p) \<or> a \<in> (reject y S p)"
    using A f_prof
    by blast
  hence 1: "card ((reject x S p) \<union> (reject y S p)) = card S"
    using subsets subset_eq sup.absorb_iff1
          sup.cobounded1 sup_left_commute
    by (smt (verit, best))
  from 0 1
  show
    "card (reject (maximum_parallel_composition x y) S p) = n"
    by simp
qed

(*
   Using the max-aggregator for composing two compatible modules in parallel,
   whereof the first one is non-electing and defers exactly one alternative,
   and the second one rejects exactly two alternatives, the composition
   results in an electoral module that eliminates exactly one alternative.
*)
theorem par_comp_elim_one[simp]:
  assumes
    "defers 1 m" and
    "non_electing m" and
    "rejects 2 n" and
    "disjoint_compatibility m n"
  shows "eliminates 1 (maximum_parallel_composition m n)"
proof -
  have
    "\<forall>A p. (card A > 1 \<and> finite_profile A p) \<longrightarrow>
        card (reject (maximum_parallel_composition m n) A p) = 1"
  proof
    fix A
    show
      "\<forall>p. (card A > 1 \<and> finite_profile A p) \<longrightarrow>
          card (reject (maximum_parallel_composition m n) A p) = 1"
    proof
      fix p
      show
        "(card A > 1 \<and> finite_profile A p) \<longrightarrow>
            card (reject (maximum_parallel_composition m n) A p) = 1"
      proof
        assume asm0: "card A > 1 \<and> finite_profile A p"
        have card_geq_1: "card A \<ge> 1"
          using asm0 dual_order.strict_trans2 less_imp_le_nat
          by blast
        have module: "electoral_module m"
          using assms(2) non_electing_def
          by auto
        have "card (elect m A p) = 0"
          using asm0 assms(2) card_eq_0_iff non_electing_def
          by metis
        moreover
        from card_geq_1 have "card (defer m A p) = 1"
          using assms(1) module
          by (simp add: asm0 defers_def)
        ultimately have card_reject_m:
          "card (reject m A p) = card A - 1"
        proof -
          have "finite A"
            by (simp add: asm0)
          moreover have
            "well_formed A
              (elect m A p, reject m A p, defer m A p)"
            using asm0 electoral_module_def module
            by auto
          ultimately have
            "card A =
                card (elect m A p) + card (reject m A p) +
                  card (defer m A p)"
            using result_count
            by blast
          thus ?thesis
            by (simp add:
                \<open>card (defer m A p) = 1\<close> 
                \<open>card (elect m A p) = 0\<close>)
        qed
        have case1: "card A \<ge> 2"
          using asm0
          by auto
        from case1 have card_reject_n:
          "card (reject n A p) = 2"
          using asm0 assms(3) rejects_def
          by blast
        from card_reject_m card_reject_n
        have
          "card (reject m A p) + card (reject n A p) =
              card A + 1"
          using card_geq_1
          by linarith
        with assms(4) asm0 card_reject_m card_reject_n
        show
          "card
            (reject
              (maximum_parallel_composition m n) A p) = 1"
          using par_comp_rej_card
          by blast
      qed
    qed
  qed
  moreover have
    "electoral_module (maximum_parallel_composition m n)"
    using assms(4) disjoint_compatibility_def max_par_comp_sound
    by metis
  ultimately show ?thesis
    using eliminates_def
    by blast
qed

end

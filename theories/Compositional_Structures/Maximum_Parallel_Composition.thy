(*  File:       Maximum_Parallel_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Maximum Parallel Composition\<close>

theory Maximum_Parallel_Composition
  imports "Basic_Modules/Component_Types/Maximum_Aggregator"
          Parallel_Composition
begin

text \<open>
  This is a family of parallel compositions. It composes a new electoral module
  from two electoral modules combined with the maximum aggregator. Therein, the
  two modules each make a decision and then a partition is returned where every
  alternative receives the maximum result of the two input partitions. This
  means that, if any alternative is elected by at least one of the modules,
  then it gets elected, if any non-elected alternative is deferred by at least
  one of the modules, then it gets deferred, only alternatives rejected by both
  modules get rejected.
\<close>

subsection \<open>Definition\<close>

fun maximum_parallel_composition :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "maximum_parallel_composition m n =
    (let a = max_aggregator in (m \<parallel>\<^sub>a n))"

abbreviation max_parallel :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 
        ('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" (infix "\<parallel>\<^sub>\<up>" 50) where
  "m \<parallel>\<^sub>\<up> n == maximum_parallel_composition m n"

subsection \<open>Soundness\<close>

theorem max_par_comp_sound:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
     "social_choice_result.electoral_module m" and
     "social_choice_result.electoral_module n"
  shows "social_choice_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
  using assms
  by simp

subsection \<open>Lemmas\<close>

lemma max_agg_eq_result:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    module_m: "social_choice_result.electoral_module m" and
    module_n: "social_choice_result.electoral_module n" and
    f_prof: "finite_profile V A p" and
    a_in_A: "a \<in> A"
  shows "mod_contains_result V (m \<parallel>\<^sub>\<up> n) m A p a \<or>
          mod_contains_result V (m \<parallel>\<^sub>\<up> n) n A p a"
proof (cases)
  assume a_elect: "a \<in> elect V (m \<parallel>\<^sub>\<up> n) A p"
  hence "let (e, r, d) = m V A p;
           (e', r', d') = n V A p in
         a \<in> e \<union> e'"
    by auto
  hence "a \<in> (elect V m A p) \<union> (elect V n A p)"
    by auto
  moreover have
    "\<forall> m' n' A' V' p' a'.
      mod_contains_result V' m' n' A' p' (a'::'a) =
        (social_choice_result.electoral_module m' \<and> 
         social_choice_result.electoral_module n' \<and> 
          finite A' \<and> finite V' \<and> profile V' A' p' \<and> a' \<in> A' \<and>
          (a' \<notin> elect V' m' A' p' \<or> a' \<in> elect V' n' A' p') \<and>
          (a' \<notin> reject V' m' A' p' \<or> a' \<in> reject V' n' A' p') \<and>
          (a' \<notin> defer V' m' A' p' \<or> a' \<in> defer V' n' A' p'))"
    unfolding mod_contains_result_def
    by simp
  moreover have module_mn: "social_choice_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n
    by simp
  moreover have "a \<notin> defer V (m \<parallel>\<^sub>\<up> n) A p"
    using module_mn IntI a_elect empty_iff f_prof result_disj
    by (metis (no_types))
  moreover have "a \<notin> reject V (m \<parallel>\<^sub>\<up> n) A p"
    using module_mn IntI a_elect empty_iff f_prof result_disj
    by (metis (no_types))
  ultimately show ?thesis
    using assms
    by blast
next
  assume not_a_elect: "a \<notin> elect V (m \<parallel>\<^sub>\<up> n) A p"
  thus ?thesis
  proof (cases)
    assume a_in_def: "a \<in> defer V (m \<parallel>\<^sub>\<up> n) A p"
    thus ?thesis
    proof (safe)
      assume not_mod_cont_mn: "\<not> mod_contains_result V (m \<parallel>\<^sub>\<up> n) n A p a"
      have par_emod:
        "\<forall> m' n'. (social_choice_result.electoral_module m' \<and> 
                    social_choice_result.electoral_module n') \<longrightarrow>
                    social_choice_result.electoral_module (m' \<parallel>\<^sub>\<up> n')"
        using max_par_comp_sound
        by blast
      have set_intersect: "\<forall> a' A' A''. (a' \<in> A' \<inter> A'') = (a' \<in> A' \<and> a' \<in> A'')"
        by blast
      have wf_n: "well_formed_soc_choice A (n V A p)"
        using f_prof module_n
        unfolding social_choice_result.electoral_module_def
        by blast
      have wf_m: "well_formed_soc_choice A (m V A p)"
        using f_prof module_m
        unfolding social_choice_result.electoral_module_def
        by blast
      have e_mod_par: "social_choice_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
        using par_emod module_m module_n
        by blast
      hence "social_choice_result.electoral_module (m \<parallel>\<^sub>max_aggregator n)"
        by simp
      hence result_disj_max:
        "elect V (m \<parallel>\<^sub>max_aggregator n) A p \<inter>
            reject V (m \<parallel>\<^sub>max_aggregator n) A p = {} \<and>
          elect V (m \<parallel>\<^sub>max_aggregator n) A p \<inter>
            defer V (m \<parallel>\<^sub>max_aggregator n) A p = {} \<and>
          reject V (m \<parallel>\<^sub>max_aggregator n) A p \<inter>
            defer V (m \<parallel>\<^sub>max_aggregator n) A p = {}"
        using f_prof result_disj
        by metis
      have a_not_elect: "a \<notin> elect V (m \<parallel>\<^sub>max_aggregator n) A p"
        using result_disj_max a_in_def
        by force
      have result_m: "(elect V m A p, reject V m A p, defer V m A p) = m V A p"
        by auto
      have result_n: "(elect V n A p, reject V n A p, defer V n A p) = n V A p"
        by auto
      have max_pq:
        "\<forall> (A'::'a set) m' n'.
          elect_r (max_aggregator A' m' n') = elect_r m' \<union> elect_r n'"
        by force
      have "a \<notin> elect V (m \<parallel>\<^sub>max_aggregator n) A p"
        using a_not_elect
        by blast
      hence "a \<notin> elect V m A p \<union> elect V n A p"
        using max_pq
        by simp
      hence b_not_elect_mn: "a \<notin> elect V m A p \<and> a \<notin> elect V n A p"
        by blast
      have b_not_mpar_rej: "a \<notin> reject V (m \<parallel>\<^sub>max_aggregator n) A p"
        using result_disj_max a_in_def
        by fastforce
      have mod_cont_res_fg:
        "\<forall> m' n' A' V' p' (a'::'a).
          mod_contains_result V' m' n' A' p' a' =
            (social_choice_result.electoral_module m' \<and> 
              social_choice_result.electoral_module n' \<and> finite A' \<and>
              profile V' A' p' \<and> a' \<in> A' \<and> finite V' \<and>
              (a' \<in> elect V' m' A' p' \<longrightarrow> a' \<in> elect V' n' A' p') \<and>
              (a' \<in> reject V' m' A' p' \<longrightarrow> a' \<in> reject V' n' A' p') \<and>
              (a' \<in> defer V' m' A' p' \<longrightarrow> a' \<in> defer V' n' A' p'))"
        using mod_contains_result_def
        by fastforce
      have max_agg_res:
        "max_aggregator A (elect V m A p, reject V m A p, defer V m A p)
          (elect V n A p, reject V n A p, defer V n A p) = (m \<parallel>\<^sub>max_aggregator n) V A p"
        by simp
      have well_f_max:
        "\<forall> r' r'' e' e'' d' d'' A'.
          well_formed_soc_choice A' (e', r', d') \<and> 
          well_formed_soc_choice A' (e'', r'', d'') \<longrightarrow>
            reject_r (max_aggregator A' (e', r', d') (e'', r'', d'')) = r' \<inter> r''"
        using max_agg_rej_set
        by metis
      have e_mod_disj:
        "\<forall> m' (A'::'a set) (V'::'v set) p'.
          (social_choice_result.electoral_module m' \<and> finite (A'::'a set) 
            \<and> finite V' \<and> profile V' A' p') \<longrightarrow>
            elect V' m' A' p' \<union> reject V' m' A' p' \<union> defer V' m' A' p' = A'"
        using result_presv_alts
        by blast
      hence e_mod_disj_n: "elect V n A p \<union> reject V n A p \<union> defer V n A p = A"
        using f_prof module_n
        by metis
      have "\<forall> m' n' A' V' p' (b::'a).
              mod_contains_result V' m' n' A' p' b =
                (social_choice_result.electoral_module m' \<and> 
                  social_choice_result.electoral_module n' \<and> finite A' \<and>
                  profile V' A' p' \<and> b \<in> A' \<and> finite V' \<and>
                  (b \<in> elect V' m' A' p' \<longrightarrow> b \<in> elect V' n' A' p') \<and>
                  (b \<in> reject V' m' A' p' \<longrightarrow> b \<in> reject V' n' A' p') \<and>
                  (b \<in> defer V' m' A' p' \<longrightarrow> b \<in> defer V' n' A' p'))"
        unfolding mod_contains_result_def
        by auto
      hence "a \<in> reject V n A p"
        using e_mod_disj_n e_mod_par f_prof a_in_A module_n not_mod_cont_mn
              a_not_elect b_not_elect_mn b_not_mpar_rej
        by fastforce
      hence "a \<notin> reject V m A p"
        using well_f_max max_agg_res result_m result_n set_intersect
              wf_m wf_n b_not_mpar_rej
        by (metis (no_types))
      hence "a \<notin> defer V (m \<parallel>\<^sub>\<up> n) A p \<or> a \<in> defer V m A p"
          using e_mod_disj f_prof a_in_A module_m b_not_elect_mn
          by blast
      thus "mod_contains_result V (m \<parallel>\<^sub>\<up> n) m A p a"
        using b_not_mpar_rej mod_cont_res_fg e_mod_par f_prof a_in_A
              module_m a_not_elect
        by fastforce
    qed
  next
    assume not_a_defer: "a \<notin> defer V (m \<parallel>\<^sub>\<up> n) A p"
    have el_rej_defer: "(elect V m A p, reject V m A p, defer V m A p) = m V A p"
      by auto
    from not_a_elect not_a_defer
    have a_reject: "a \<in> reject V (m \<parallel>\<^sub>\<up> n) A p"
      using electoral_mod_defer_elem a_in_A module_m module_n f_prof max_par_comp_sound
      by metis
    hence "case snd (m V A p) of (r, d) \<Rightarrow>
            case n V A p of (e', r', d') \<Rightarrow>
              a \<in> reject_r (max_aggregator A (elect V m A p, r, d) (e', r', d'))"
      using el_rej_defer
      by force
    hence "let (e, r, d) = m V A p;
            (e', r', d') = n V A p in
              a \<in> reject_r (max_aggregator A (e, r, d) (e', r', d'))"
      by (simp add: case_prod_unfold)
    hence "let (e, r, d) = m V A p;
            (e', r', d') = n V A p in
              a \<in> A - (e \<union> e' \<union> d \<union> d')"
      by simp
    hence "a \<notin> elect V m A p \<union> (defer V n A p \<union> defer V m A p)"
      by force
    thus ?thesis
      using mod_contains_result_comm mod_contains_result_def Un_iff
            a_reject f_prof a_in_A module_m module_n max_par_comp_sound
      by (metis (no_types))
  qed
qed

lemma max_agg_rej_iff_both_reject:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a,'v) Profile" and
    a :: "'a"
  assumes
    "finite_profile V A p" and
    "social_choice_result.electoral_module m" and
    "social_choice_result.electoral_module n"
  shows "(a \<in> reject V (m \<parallel>\<^sub>\<up> n) A p) = (a \<in> reject V m A p \<and> a \<in> reject V n A p)"
proof
  assume rej_a: "a \<in> reject V (m \<parallel>\<^sub>\<up> n) A p"
  hence "case n V A p of (e, r, d) \<Rightarrow>
          a \<in> reject_r (max_aggregator A
                (elect V m A p, reject V m A p, defer V m A p) (e, r, d))"
    by auto
  hence "case snd (m V A p) of (r, d) \<Rightarrow>
          case n V A p of (e', r', d') \<Rightarrow>
            a \<in> reject_r (max_aggregator A (elect V m A p, r, d) (e', r', d'))"
    by force
  with rej_a
  have "let (e, r, d) = m V A p;
          (e', r', d') = n V A p in
            a \<in> reject_r (max_aggregator A (e, r, d) (e', r', d'))"
    by (simp add: prod.case_eq_if)
  hence "let (e, r, d) = m V A p;
            (e', r', d') = n V A p in
              a \<in> A - (e \<union> e' \<union> d \<union> d')"
    by simp
  hence "a \<in> A - (elect V m A p \<union> elect V n A p \<union> defer V m A p \<union> defer V n A p)"
    by auto
  thus "a \<in> reject V m A p \<and> a \<in> reject V n A p"
    using Diff_iff Un_iff electoral_mod_defer_elem assms
    by metis
next
  assume "a \<in> reject V m A p \<and> a \<in> reject V n A p"
  moreover from this
  have "a \<notin> elect V m A p \<and> a \<notin> defer V m A p \<and> a \<notin> elect V n A p \<and> a \<notin> defer V n A p"
    using IntI empty_iff assms result_disj
    by metis
  ultimately show "a \<in> reject V (m \<parallel>\<^sub>\<up> n) A p"
    using DiffD1 max_agg_eq_result mod_contains_result_comm mod_contains_result_def
          reject_not_elec_or_def assms
    by (metis (no_types))
qed

lemma max_agg_rej_1:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    f_prof: "finite_profile V A p" and
    module_m: "social_choice_result.electoral_module m" and
    module_n: "social_choice_result.electoral_module n" and
    rejected: "a \<in> reject V n A p"
  shows "mod_contains_result V m (m \<parallel>\<^sub>\<up> n) A p a"
proof (unfold mod_contains_result_def, safe)
  show "social_choice_result.electoral_module m"
    using module_m
    by simp
next
  show "social_choice_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n
    by simp
next
  show "finite V"
    using f_prof
    by simp
next
  show "finite A"
    using f_prof
    by simp
next
  show "profile V A p"
    using f_prof
    by simp
next
  show "a \<in> A"
    using f_prof module_n reject_in_alts rejected
    by fastforce
next
  assume a_in_elect: "a \<in> elect V m A p"
  hence a_not_reject: "a \<notin> reject V m A p"
    using disjoint_iff_not_equal f_prof module_m result_disj
    by metis
  have "reject V n A p \<subseteq> A"
    using f_prof module_n
    by (simp add: reject_in_alts)
  hence "a \<in> A"
    using in_mono rejected
    by metis
  with a_in_elect a_not_reject
  show "a \<in> elect V (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_eq_result module_m module_n rejected
          max_agg_rej_iff_both_reject mod_contains_result_comm
          mod_contains_result_def
    by metis
next
  assume "a \<in> reject V m A p"
  hence "a \<in> reject V m A p \<and> a \<in> reject V n A p"
    using rejected
    by simp
  thus "a \<in> reject V (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_rej_iff_both_reject module_m module_n
    by (metis (no_types))
next
  assume a_in_defer: "a \<in> defer V m A p"
  then obtain d :: 'a where
    defer_a: "a = d \<and> d \<in> defer V m A p"
    by metis
  have a_not_rej: "a \<notin> reject V m A p"
    using disjoint_iff_not_equal f_prof defer_a module_m result_disj
    by (metis (no_types))
  have
    "\<forall> m' A' V' p'.
      (social_choice_result.electoral_module m' \<and> finite A' \<and> finite V' \<and> profile V' A' p') \<longrightarrow>
        elect V' m' A' p' \<union> reject V' m' A' p' \<union> defer V' m' A' p' = A'"
    using result_presv_alts
    by metis
  hence "a \<in> A"
    using a_in_defer f_prof module_m
    by blast
  with defer_a a_not_rej
  show "a \<in> defer V (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_eq_result max_agg_rej_iff_both_reject
          mod_contains_result_comm mod_contains_result_def
          module_m module_n rejected
    by metis
qed

lemma max_agg_rej_2:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "finite_profile V A p" and
    "social_choice_result.electoral_module m" and
    "social_choice_result.electoral_module n" and
    "a \<in> reject V n A p"
  shows "mod_contains_result V (m \<parallel>\<^sub>\<up> n) m A p a"
  using mod_contains_result_comm max_agg_rej_1 assms
  by metis

lemma max_agg_rej_3:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    f_prof:  "finite_profile V A p" and
    module_m: "social_choice_result.electoral_module m" and
    module_n: "social_choice_result.electoral_module n" and
    rejected: "a \<in> reject V m A p"
  shows "mod_contains_result V n (m \<parallel>\<^sub>\<up> n) A p a"
proof (unfold mod_contains_result_def, safe)
  show "social_choice_result.electoral_module n"
    using module_n
    by simp
next
  show "social_choice_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n
    by simp
next
  show "finite A"
    using f_prof
    by simp
next
  show "finite V"
    using f_prof
    by simp
next
  show "profile V A p"
    using f_prof
    by simp
next
  show "a \<in> A"
    using f_prof in_mono module_m reject_in_alts rejected
    by (metis (no_types))
next
  assume "a \<in> elect V n A p"
  hence "a \<in> elect V m A p \<union> elect V n A p"
    by simp
  thus "a \<in> elect V (m \<parallel>\<^sub>\<up> n) A p"
    using fst_conv maximum_parallel_composition.simps prod.collapse    
          parallel_composition.simps max_aggregator.simps
    by (metis (mono_tags, lifting))
next
  assume "a \<in> reject V n A p"
  thus "a \<in> reject V (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_rej_iff_both_reject module_m module_n rejected
    by metis
next
  assume "a \<in> defer V n A p"
  moreover have "a \<in> A"
    using f_prof max_agg_rej_1 mod_contains_result_def module_m rejected
    by metis
  ultimately show "a \<in> defer V (m \<parallel>\<^sub>\<up> n) A p"
    using disjoint_iff_not_equal max_agg_eq_result max_agg_rej_iff_both_reject
          f_prof mod_contains_result_comm mod_contains_result_def
          module_m module_n rejected result_disj
      by metis
qed

lemma max_agg_rej_4:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "finite_profile V A p" and
    "social_choice_result.electoral_module m" and
    "social_choice_result.electoral_module n" and
    "a \<in> reject V m A p"
  shows "mod_contains_result V (m \<parallel>\<^sub>\<up> n) n A p a"
  using mod_contains_result_comm max_agg_rej_3 assms
  by metis

lemma max_agg_rej_intersect:
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
  shows "reject V (m \<parallel>\<^sub>\<up> n) A p = (reject V m A p) \<inter> (reject V n A p)"
proof -
  have "A = (elect V m A p) \<union> (reject V m A p) \<union> (defer V m A p) \<and>
          A = (elect V n A p) \<union> (reject V n A p) \<union> (defer V n A p)"
    using assms result_presv_alts
    by metis
  hence "A - ((elect V m A p) \<union> (defer V m A p)) = (reject V m A p) \<and>
          A - ((elect V n A p) \<union> (defer V n A p)) = (reject V n A p)"
    using assms reject_not_elec_or_def
    by fastforce
  hence "A - ((elect V m A p) \<union> (elect V n A p) \<union> (defer V m A p) \<union> (defer V n A p)) =
          (reject V m A p) \<inter> (reject V n A p)"
    by blast
  hence "let (e, r, d) = m V A p;
          (e', r', d') = n V A p in
            A - (e \<union> e' \<union> d \<union> d') = r \<inter> r'"
    by fastforce
  thus ?thesis
    by auto
qed

lemma dcompat_dec_by_one_mod:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    a :: "'a"
  assumes
     "disjoint_compatibility m n" and
     "a \<in> A"
  shows
    "(\<forall> p. finite_profile V A p \<longrightarrow> mod_contains_result V m (m \<parallel>\<^sub>\<up> n) A p a) \<or>
        (\<forall> p. finite_profile V A p \<longrightarrow> mod_contains_result V n (m \<parallel>\<^sub>\<up> n) A p a)"
  using DiffI assms max_agg_rej_1 max_agg_rej_3
  unfolding disjoint_compatibility_def
  by metis

subsection \<open>Composition Rules\<close>

text \<open>
  Using a conservative aggregator, the parallel composition
  preserves the property non-electing.
\<close>

theorem conserv_max_agg_presv_non_electing[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    "non_electing m" and
    "non_electing n"
  shows "non_electing (m \<parallel>\<^sub>\<up> n)"
  using assms
  by simp

text \<open>
  Using the max aggregator, composing two compatible
  electoral modules in parallel preserves defer-lift-invariance.
\<close>

theorem par_comp_def_lift_inv[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    compatible: "disjoint_compatibility m n" and
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<parallel>\<^sub>\<up> n)"
proof (unfold defer_lift_invariance_def, safe)
  have "social_choice_result.electoral_module m"
    using monotone_m
    unfolding defer_lift_invariance_def
    by simp
  moreover have "social_choice_result.electoral_module n"
    using monotone_n
    unfolding defer_lift_invariance_def
    by simp
  ultimately show "social_choice_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    defer_a: "a \<in> defer V (m \<parallel>\<^sub>\<up> n) A p" and
    lifted_a: "Profile.lifted V A p q a"
  hence f_profs: "finite_profile V A p \<and> finite_profile V A q"
    unfolding lifted_def
    by simp
  from compatible
  obtain B :: "'a set" where
    alts: "B \<subseteq> A \<and>
            (\<forall> b \<in> B. indep_of_alt V m A b \<and>
                (\<forall> p'. finite_profile V A p' \<longrightarrow> b \<in> reject V m A p')) \<and>
            (\<forall> b \<in> A - B. indep_of_alt V n A b \<and>
                (\<forall> p'. finite_profile V A p' \<longrightarrow> b \<in> reject V n A p'))"
    using f_profs
    unfolding disjoint_compatibility_def
    by (metis (no_types, lifting))
  have "\<forall> b \<in> A. prof_contains_result V (m \<parallel>\<^sub>\<up> n) A p q b"
  proof (cases)
    assume a_in_B: "a \<in> B"
    hence "a \<in> reject V m A p"
      using alts f_profs
      by blast
    with defer_a
    have defer_n: "a \<in> defer V n A p"
      using compatible f_profs max_agg_rej_4
      unfolding disjoint_compatibility_def mod_contains_result_def
      by metis
    have "\<forall> b \<in> B. mod_contains_result V (m \<parallel>\<^sub>\<up> n) n A p b"
      using alts compatible max_agg_rej_4 f_profs
      unfolding disjoint_compatibility_def
      by metis
    moreover have "\<forall> b \<in> A. prof_contains_result V n A p q b"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show "social_choice_result.electoral_module n \<and> finite_profile V A p 
              \<and> finite_profile V A q \<and> b \<in> A \<and>
              (b \<in> elect V n A p \<longrightarrow> b \<in> elect V n A q) \<and>
              (b \<in> reject V n A p \<longrightarrow> b \<in> reject V n A q) \<and>
              (b \<in> defer V n A p \<longrightarrow> b \<in> defer V n A q)"
      proof (safe)
        show "social_choice_result.electoral_module n"
          using monotone_n
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "finite V"
          using f_profs
          by simp
      next
        show "profile V A p"
          using f_profs
          by simp
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "finite V"
          using f_profs
          by simp
      next
        show "profile V A q"
          using f_profs
          by simp
      next
        show "b \<in> A"
          using b_in_A
          by simp
      next
        assume "b \<in> elect V n A p"
        thus "b \<in> elect V n A q"
          using defer_n lifted_a monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      next
        assume "b \<in> reject V n A p"
        thus "b \<in> reject V n A q"
          using defer_n lifted_a monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      next
        assume "b \<in> defer V n A p"
        thus "b \<in> defer V n A q"
          using defer_n lifted_a monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      qed
    qed
    moreover have "\<forall> b \<in> B. mod_contains_result V n (m \<parallel>\<^sub>\<up> n) A q b"
      using alts compatible max_agg_rej_3 f_profs
      unfolding disjoint_compatibility_def
      by metis
    ultimately have prof_contains_result_of_comps_for_elems_in_B:
      "\<forall> b \<in> B. prof_contains_result V (m \<parallel>\<^sub>\<up> n) A p q b"
      unfolding mod_contains_result_def prof_contains_result_def
      by simp
    have "\<forall> b \<in> A - B. mod_contains_result V (m \<parallel>\<^sub>\<up> n) m A p b"
      using alts max_agg_rej_2 monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    moreover have "\<forall> b \<in> A. prof_contains_result V m A p q b"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show "social_choice_result.electoral_module m \<and> finite_profile V A p \<and> 
              finite_profile V A q \<and> b \<in> A \<and>
              (b \<in> elect V m A p \<longrightarrow> b \<in> elect V m A q) \<and>
              (b \<in> reject V m A p \<longrightarrow> b \<in> reject V m A q) \<and>
              (b \<in> defer V m A p \<longrightarrow> b \<in> defer V m A q)"
      proof (safe)
        show "social_choice_result.electoral_module m"
          using monotone_m
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "finite V"
          using f_profs
          by simp
      next
        show "profile V A p"
          using f_profs
          by simp
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "finite V"
          using f_profs
          by simp
      next
        show "profile V A q"
          using f_profs
          by simp
      next
        show "b \<in> A"
          using b_in_A
          by simp
      next
        assume "b \<in> elect V m A p"
        thus "b \<in> elect V m A q"
          using alts a_in_B lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "b \<in> reject V m A p"
        thus "b \<in> reject V m A q"
          using alts a_in_B lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "b \<in> defer V m A p"
        thus "b \<in> defer V m A q"
          using alts a_in_B lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      qed
    qed
    moreover have "\<forall> b \<in> A - B. mod_contains_result V m (m \<parallel>\<^sub>\<up> n) A q b"
      using alts max_agg_rej_1 monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    ultimately have "\<forall> b \<in> A - B. prof_contains_result V (m \<parallel>\<^sub>\<up> n) A p q b"
      unfolding mod_contains_result_def prof_contains_result_def
      by simp
    thus ?thesis
      using prof_contains_result_of_comps_for_elems_in_B
      by blast
  next
    assume "a \<notin> B"
    hence a_in_set_diff: "a \<in> A - B"
      using DiffI lifted_a compatible f_profs
      unfolding Profile.lifted_def
      by (metis (no_types, lifting))
    hence "a \<in> reject V n A p"
      using alts f_profs
      by blast
    hence defer_m: "a \<in> defer V m A p"
      using DiffD1 DiffD2 compatible dcompat_dec_by_one_mod f_profs defer_not_elec_or_rej
            max_agg_sound par_comp_sound disjoint_compatibility_def not_rej_imp_elec_or_def
            mod_contains_result_def defer_a
      unfolding maximum_parallel_composition.simps
      by (metis (no_types, lifting))
    have "\<forall> b \<in> B. mod_contains_result V (m \<parallel>\<^sub>\<up> n) n A p b"
      using alts compatible max_agg_rej_4 f_profs
      unfolding disjoint_compatibility_def
      by metis
    moreover have "\<forall> b \<in> A. prof_contains_result V n A p q b"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show "social_choice_result.electoral_module n \<and> finite_profile V A p \<and> 
              finite_profile V A q \<and> b \<in> A \<and>
              (b \<in> elect V n A p \<longrightarrow> b \<in> elect V n A q) \<and>
              (b \<in> reject V n A p \<longrightarrow> b \<in> reject V n A q) \<and>
              (b \<in> defer V n A p \<longrightarrow> b \<in> defer V n A q)"
      proof (safe)
        show "social_choice_result.electoral_module n"
          using monotone_n
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "finite V"
          using f_profs
          by simp
      next
        show "profile V A p"
          using f_profs
          by simp
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "finite V"
          using f_profs
          by simp
      next
        show "profile V A q"
          using f_profs
          by simp
      next
        show "b \<in> A"
          using b_in_A
          by simp
      next
        assume "b \<in> elect V n A p"
        thus "b \<in> elect V n A q"
          using alts a_in_set_diff lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "b \<in> reject V n A p"
        thus "b \<in> reject V n A q"
          using alts a_in_set_diff lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "b \<in> defer V n A p"
        thus "b \<in> defer V n A q"
          using alts a_in_set_diff lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      qed
  qed
  moreover have "\<forall> b \<in> B. mod_contains_result V n (m \<parallel>\<^sub>\<up> n) A q b"
    using alts compatible max_agg_rej_3 f_profs
    unfolding disjoint_compatibility_def
    by metis
  ultimately have prof_contains_result_of_comps_for_elems_in_B:
    "\<forall> b \<in> B. prof_contains_result V (m \<parallel>\<^sub>\<up> n) A p q b"
    unfolding mod_contains_result_def prof_contains_result_def
    by simp
  have "\<forall> b \<in> A - B. mod_contains_result V (m \<parallel>\<^sub>\<up> n) m A p b"
    using alts max_agg_rej_2 monotone_m monotone_n f_profs
    unfolding defer_lift_invariance_def
    by metis
  moreover have "\<forall> b \<in> A. prof_contains_result V m A p q b"
  proof (unfold prof_contains_result_def, clarify)
    fix b :: "'a"
    assume b_in_A: "b \<in> A"
    show "social_choice_result.electoral_module m \<and> finite_profile V A p \<and> 
            finite_profile V A q \<and> b \<in> A \<and>
            (b \<in> elect V m A p \<longrightarrow> b \<in> elect V m A q) \<and>
            (b \<in> reject V m A p \<longrightarrow> b \<in> reject V m A q) \<and>
            (b \<in> defer V m A p \<longrightarrow> b \<in> defer V m A q)"
    proof (safe)
      show "social_choice_result.electoral_module m"
        using monotone_m
        unfolding defer_lift_invariance_def
        by simp
    next
      show "finite A"
        using f_profs
        by simp
    next 
      show "finite V"
        using f_profs
        by simp
    next
      show "profile V A p"
        using f_profs
        by simp
    next
      show "finite A"
        using f_profs
        by simp
    next
      show "finite V"
        using f_profs
        by simp
    next
      show "profile V A q"
        using f_profs
        by simp
    next
      show "b \<in> A"
        using b_in_A
        by simp
    next
      assume "b \<in> elect V m A p"
      thus "b \<in> elect V m A q"
        using defer_m lifted_a monotone_m
        unfolding defer_lift_invariance_def
        by metis
    next
      assume "b \<in> reject V m A p"
      thus "b \<in> reject V m A q"
        using defer_m lifted_a monotone_m
        unfolding defer_lift_invariance_def
        by metis
    next
      assume "b \<in> defer V m A p"
      thus "b \<in> defer V m A q"
        using defer_m lifted_a monotone_m
        unfolding defer_lift_invariance_def
        by metis
    qed
  qed
  moreover have "\<forall> x \<in> A - B. mod_contains_result V m (m \<parallel>\<^sub>\<up> n) A q x"
    using alts max_agg_rej_1 monotone_m monotone_n f_profs
    unfolding defer_lift_invariance_def
    by metis
  ultimately have "\<forall> x \<in> A - B. prof_contains_result V (m \<parallel>\<^sub>\<up> n) A p q x"
    using electoral_mod_defer_elem
    unfolding mod_contains_result_def prof_contains_result_def
    by simp
  thus ?thesis
    using prof_contains_result_of_comps_for_elems_in_B
    by blast
  qed
  thus "(m \<parallel>\<^sub>\<up> n) V A p = (m \<parallel>\<^sub>\<up> n) V A q"
    using compatible f_profs eq_alts_in_profs_imp_eq_results max_par_comp_sound
    unfolding disjoint_compatibility_def
    by metis
qed

lemma par_comp_rej_card:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    c :: nat
  assumes
    compatible: "disjoint_compatibility m n" and
    f_prof: "finite_profile V A p" and
    reject_sum: "card (reject V m A p) + card (reject V n A p) = card A + c"
  shows "card (reject V (m \<parallel>\<^sub>\<up> n) A p) = c"
proof -
  obtain B where
    alt_set: "B \<subseteq> A \<and>
         (\<forall> a \<in> B. indep_of_alt V m A a \<and>
            (\<forall> q. finite_profile V A q \<longrightarrow> a \<in> reject V m A q)) \<and>
         (\<forall> a \<in> A - B. indep_of_alt V n A a \<and>
            (\<forall> q. finite_profile V A q \<longrightarrow> a \<in> reject V n A q))"
    using compatible f_prof
    unfolding disjoint_compatibility_def
    by metis
  have reject_representation:
    "reject V (m \<parallel>\<^sub>\<up> n) A p = (reject V m A p) \<inter> (reject V n A p)"
    using f_prof compatible max_agg_rej_intersect
    unfolding disjoint_compatibility_def
    by metis
  have "social_choice_result.electoral_module m \<and> social_choice_result.electoral_module n"
    using compatible
    unfolding disjoint_compatibility_def
    by simp
  hence subsets: "(reject V m A p) \<subseteq> A \<and> (reject V n A p) \<subseteq> A"
    by (simp add: f_prof reject_in_alts)
  hence "finite (reject V m A p) \<and> finite (reject V n A p)"
    using rev_finite_subset f_prof
    by metis
  hence card_difference:
    "card (reject V (m \<parallel>\<^sub>\<up> n) A p) =
      card A + c - card ((reject V m A p) \<union> (reject V n A p))"
    using card_Un_Int reject_representation reject_sum
    by fastforce
  have "\<forall> a \<in> A. a \<in> (reject V m A p) \<or> a \<in> (reject V n A p)"
    using alt_set f_prof
    by blast
  hence "A = reject V m A p \<union> reject V n A p"
    using subsets
    by force
  thus "card (reject V (m \<parallel>\<^sub>\<up> n) A p) = c"
    using card_difference
    by simp
qed

text \<open>
  Using the max-aggregator for composing two compatible modules in parallel,
  whereof the first one is non-electing and defers exactly one alternative,
  and the second one rejects exactly two alternatives, the composition
  results in an electoral module that eliminates exactly one alternative.
\<close>

theorem par_comp_elim_one[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    defers_m_one: "defers 1 m" and
    non_elec_m: "non_electing m" and
    rejec_n_two: "rejects 2 n" and
    disj_comp: "disjoint_compatibility m n"
  shows "eliminates 1 (m \<parallel>\<^sub>\<up> n)"
proof (unfold eliminates_def, safe)
  have "social_choice_result.electoral_module m"
    using non_elec_m
    unfolding non_electing_def
    by simp
  moreover have "social_choice_result.electoral_module n"
    using rejec_n_two
    unfolding rejects_def
    by simp
  ultimately show "social_choice_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    min_card_two: "1 < card A" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    prof_A: "profile V A p"
  have card_geq_one: "card A \<ge> 1"
    using min_card_two dual_order.strict_trans2 less_imp_le_nat
    by blast
  have module: "social_choice_result.electoral_module m"
    using non_elec_m
    unfolding non_electing_def
    by simp
  have elec_card_zero: "card (elect V m A p) = 0"
    using fin_A fin_V prof_A non_elec_m card_eq_0_iff
    unfolding non_electing_def
    by simp
  moreover from card_geq_one
  have def_card_one: "card (defer V m A p) = 1"
    using defers_m_one module fin_A fin_V prof_A
    unfolding defers_def
    by simp
  ultimately have card_reject_m: "card (reject V m A p) = card A - 1"
  proof -
    have "finite A"
      using fin_A
      by simp
    moreover have "well_formed_soc_choice A (elect V m A p, reject V m A p, defer V m A p)"
      using fin_A fin_V prof_A module
      unfolding social_choice_result.electoral_module_def
      by simp
    ultimately have
      "card A = card (elect V m A p) + card (reject V m A p) + card (defer V m A p)"
      using result_count
      by blast
    thus ?thesis
      using def_card_one elec_card_zero
      by simp
  qed
  have "card A \<ge> 2"
    using min_card_two
    by simp
  hence "card (reject V n A p) = 2"
    using fin_A fin_V prof_A rejec_n_two
    unfolding rejects_def
    by blast
  moreover from this
  have "card (reject V m A p) + card (reject V n A p) = card A + 1"
    using card_reject_m card_geq_one
    by linarith
  ultimately show "card (reject V (m \<parallel>\<^sub>\<up> n) A p) = 1"
    using disj_comp prof_A fin_A fin_V card_reject_m par_comp_rej_card
    by blast
qed

end

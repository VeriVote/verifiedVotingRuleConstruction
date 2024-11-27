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
        ('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" where
  "maximum_parallel_composition m n =
    (let a = max_aggregator in (m \<parallel>\<^sub>a n))"

abbreviation max_parallel :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" (infix "\<parallel>\<^sub>\<up>" 50) where
  "m \<parallel>\<^sub>\<up> n \<equiv> maximum_parallel_composition m n"

subsection \<open>Soundness\<close>

theorem max_par_comp_sound:
  fixes m n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
     "\<S>\<C>\<F>_result.electoral_module m" and
     "\<S>\<C>\<F>_result.electoral_module n"
  shows "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
  using assms max_agg_sound par_comp_sound
  unfolding maximum_parallel_composition.simps
  by metis

lemma voters_determine_max_par_comp:
  fixes m n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
     "voters_determine_election m" and
     "voters_determine_election n"
  shows "voters_determine_election (m \<parallel>\<^sub>\<up> n)"
  using max_aggregator.simps assms
  unfolding Let_def maximum_parallel_composition.simps
            parallel_composition.simps
            voters_determine_election.simps
  by presburger

subsection \<open>Lemmas\<close>

lemma max_agg_eq_result:
  fixes
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    module_m: "\<S>\<C>\<F>_result.electoral_module m" and
    module_n: "\<S>\<C>\<F>_result.electoral_module n" and
    prof_p: "profile V A p" and
    a_in_A: "a \<in> A"
  shows "mod_contains_result (m \<parallel>\<^sub>\<up> n) m V A p a \<or>
          mod_contains_result (m \<parallel>\<^sub>\<up> n) n V A p a"
proof (cases)
  assume a_elect: "a \<in> elect (m \<parallel>\<^sub>\<up> n) V A p"
  hence "let (e, r, d) = m V A p;
           (e', r', d') = n V A p in
         a \<in> e \<union> e'"
    by auto
  hence "a \<in> (elect m V A p) \<union> (elect n V A p)"
    by auto
  moreover have
    "\<forall> m' n' V' A' p' a'.
      mod_contains_result m' n' V' A' p' (a' :: 'a) =
        (\<S>\<C>\<F>_result.electoral_module m'
          \<and> \<S>\<C>\<F>_result.electoral_module n'
          \<and> profile V' A' p' \<and> a' \<in> A'
          \<and> (a' \<notin> elect m' V' A' p' \<or> a' \<in> elect n' V' A' p')
          \<and> (a' \<notin> reject m' V' A' p' \<or> a' \<in> reject n' V' A' p')
          \<and> (a' \<notin> defer m' V' A' p' \<or> a' \<in> defer n' V' A' p'))"
    unfolding mod_contains_result_def
    by simp
  moreover have module_mn: "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n max_par_comp_sound
    by metis
  moreover have "a \<notin> defer (m \<parallel>\<^sub>\<up> n) V A p"
    using module_mn IntI a_elect empty_iff prof_p result_disj
    by (metis (no_types))
  moreover have "a \<notin> reject (m \<parallel>\<^sub>\<up> n) V A p"
    using module_mn IntI a_elect empty_iff prof_p result_disj
    by (metis (no_types))
  ultimately show ?thesis
    using assms
    by blast
next
  assume not_a_elect: "a \<notin> elect (m \<parallel>\<^sub>\<up> n) V A p"
  thus ?thesis
  proof (cases)
    assume a_in_defer: "a \<in> defer (m \<parallel>\<^sub>\<up> n) V A p"
    thus ?thesis
    proof (safe)
      assume not_mod_cont_mn: "\<not> mod_contains_result (m \<parallel>\<^sub>\<up> n) n V A p a"
      have par_emod: "\<forall> m' n'.
        \<S>\<C>\<F>_result.electoral_module m' \<and>
        \<S>\<C>\<F>_result.electoral_module n' \<longrightarrow>
        \<S>\<C>\<F>_result.electoral_module (m' \<parallel>\<^sub>\<up> n')"
        using max_par_comp_sound
        by blast
      have set_intersect: "\<forall> a' A' A''. (a' \<in> A' \<inter> A'') = (a' \<in> A' \<and> a' \<in> A'')"
        by blast
      have wf_n: "well_formed_\<S>\<C>\<F> A (n V A p)"
        using prof_p module_n
        unfolding \<S>\<C>\<F>_result.electoral_module.simps
        by blast
      have wf_m: "well_formed_\<S>\<C>\<F> A (m V A p)"
        using prof_p module_m
        unfolding \<S>\<C>\<F>_result.electoral_module.simps
        by blast
      have e_mod_par: "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
        using par_emod module_m module_n
        by blast
      hence "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>max_aggregator n)"
        by simp
      hence result_disj_max:
        "elect (m \<parallel>\<^sub>max_aggregator n) V A p \<inter>
            reject (m \<parallel>\<^sub>max_aggregator n) V A p = {} \<and>
          elect (m \<parallel>\<^sub>max_aggregator n) V A p \<inter>
            defer (m \<parallel>\<^sub>max_aggregator n) V A p = {} \<and>
          reject (m \<parallel>\<^sub>max_aggregator n) V A p \<inter>
            defer (m \<parallel>\<^sub>max_aggregator n) V A p = {}"
        using prof_p result_disj
        by metis
      have a_not_elect: "a \<notin> elect (m \<parallel>\<^sub>max_aggregator n) V A p"
        using result_disj_max a_in_defer
        by force
      have result_m: "(elect m V A p, reject m V A p, defer m V A p) = m V A p"
        by auto
      have result_n: "(elect n V A p, reject n V A p, defer n V A p) = n V A p"
        by auto
      have max_pq:
        "\<forall> (A' :: 'a set) m' n'.
          elect_r (max_aggregator A' m' n') = elect_r m' \<union> elect_r n'"
        by force
      have "a \<notin> elect (m \<parallel>\<^sub>max_aggregator n) V A p"
        using a_not_elect
        by blast
      hence "a \<notin> elect m V A p \<union> elect n V A p"
        using max_pq
        by simp
      hence a_not_elect_mn: "a \<notin> elect m V A p \<and> a \<notin> elect n V A p"
        by blast
      have a_not_mpar_rej: "a \<notin> reject (m \<parallel>\<^sub>\<up> n) V A p"
        using result_disj_max a_in_defer
        by fastforce
      have mod_cont_res_fg:
        "\<forall> m' n' A' V' p' (a' :: 'a).
          mod_contains_result m' n' V' A' p' a' =
            (\<S>\<C>\<F>_result.electoral_module m'
              \<and> \<S>\<C>\<F>_result.electoral_module n'
              \<and> profile V' A' p' \<and> a' \<in> A'
              \<and> (a' \<in> elect m' V' A' p' \<longrightarrow> a' \<in> elect n' V' A' p')
              \<and> (a' \<in> reject m' V' A' p' \<longrightarrow> a' \<in> reject n' V' A' p')
              \<and> (a' \<in> defer m' V' A' p' \<longrightarrow> a' \<in> defer n' V' A' p'))"
        unfolding mod_contains_result_def
        by simp
      have max_agg_res:
        "max_aggregator A (elect m V A p, reject m V A p, defer m V A p)
          (elect n V A p, reject n V A p, defer n V A p) =
        (m \<parallel>\<^sub>max_aggregator n) V A p"
        by simp
      have well_f_max:
        "\<forall> r' r'' e' e'' d' d'' A'.
          well_formed_\<S>\<C>\<F> A' (e', r', d') \<and>
          well_formed_\<S>\<C>\<F> A' (e'', r'', d'') \<longrightarrow>
            reject_r (max_aggregator A' (e', r', d') (e'', r'', d'')) =
        r' \<inter> r''"
        using max_agg_rej_set
        by metis
      have e_mod_disj:
        "\<forall> m' (V' :: 'v set) (A' :: 'a set) p'.
          \<S>\<C>\<F>_result.electoral_module m' \<and> profile V' A' p'
          \<longrightarrow> elect m' V' A' p' \<union> reject m' V' A' p' \<union> defer m' V' A' p' = A'"
        using result_presv_alts
        by blast
      hence e_mod_disj_n: "elect n V A p \<union> reject n V A p \<union> defer n V A p = A"
        using prof_p module_n
        by metis
      have "\<forall> m' n' A' V' p' (b :: 'a).
              mod_contains_result m' n' V' A' p' b =
                (\<S>\<C>\<F>_result.electoral_module m'
                  \<and> \<S>\<C>\<F>_result.electoral_module n'
                  \<and> profile V' A' p' \<and> b \<in> A'
                  \<and> (b \<in> elect m' V' A' p' \<longrightarrow> b \<in> elect n' V' A' p')
                  \<and> (b \<in> reject m' V' A' p' \<longrightarrow> b \<in> reject n' V' A' p')
                  \<and> (b \<in> defer m' V' A' p' \<longrightarrow> b \<in> defer n' V' A' p'))"
        unfolding mod_contains_result_def
        by simp
      hence "a \<notin> defer n V A p"
        using a_not_mpar_rej a_in_A e_mod_par module_n not_a_elect
              not_mod_cont_mn prof_p
        by blast
      hence "a \<in> reject n V A p"
        using a_in_A a_not_elect_mn module_n not_rej_imp_elec_or_defer prof_p
        by metis
      hence "a \<notin> reject m V A p"
        using well_f_max max_agg_res result_m result_n set_intersect
              wf_m wf_n a_not_mpar_rej
        unfolding maximum_parallel_composition.simps
        by (metis (no_types))
      hence "a \<notin> defer (m \<parallel>\<^sub>\<up> n) V A p \<or> a \<in> defer m V A p"
          using e_mod_disj prof_p a_in_A module_m a_not_elect_mn
          by blast
      thus "mod_contains_result (m \<parallel>\<^sub>\<up> n) m V A p a"
        using a_not_mpar_rej mod_cont_res_fg e_mod_par prof_p a_in_A
              module_m a_not_elect
        unfolding maximum_parallel_composition.simps
        by metis
    qed
  next
    assume not_a_defer: "a \<notin> defer (m \<parallel>\<^sub>\<up> n) V A p"
    have el_rej_defer: "(elect m V A p, reject m V A p, defer m V A p) = m V A p"
      by auto
    from not_a_elect not_a_defer
    have a_reject: "a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p"
      using electoral_mod_defer_elem a_in_A module_m
            module_n prof_p max_par_comp_sound
      by metis
    hence "case snd (m V A p) of (r, d) \<Rightarrow>
            case n V A p of (e', r', d') \<Rightarrow>
              a \<in> reject_r (max_aggregator A (elect m V A p, r, d) (e', r', d'))"
      using el_rej_defer
      by force
    hence "let (e, r, d) = m V A p;
            (e', r', d') = n V A p in
              a \<in> reject_r (max_aggregator A (e, r, d) (e', r', d'))"
      unfolding case_prod_unfold
      by simp
    hence "let (e, r, d) = m V A p;
            (e', r', d') = n V A p in
              a \<in> A - (e \<union> e' \<union> d \<union> d')"
      by simp
    hence "a \<notin> elect m V A p \<union> (defer n V A p \<union> defer m V A p)"
      by force
    thus ?thesis
      using mod_contains_result_comm mod_contains_result_def Un_iff
            a_reject prof_p a_in_A module_m module_n max_par_comp_sound
      by (metis (no_types))
  qed
qed

lemma max_agg_rej_iff_both_reject:
  fixes
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "finite_profile V A p" and
    "\<S>\<C>\<F>_result.electoral_module m" and
    "\<S>\<C>\<F>_result.electoral_module n"
  shows "(a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p) =
            (a \<in> reject m V A p \<and> a \<in> reject n V A p)"
proof
  assume rej_a: "a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p"
  hence "case n V A p of (e, r, d) \<Rightarrow>
          a \<in> reject_r (max_aggregator A
                (elect m V A p, reject m V A p, defer m V A p) (e, r, d))"
    by auto
  hence "case snd (m V A p) of (r, d) \<Rightarrow>
          case n V A p of (e', r', d') \<Rightarrow>
            a \<in> reject_r (max_aggregator A (elect m V A p, r, d) (e', r', d'))"
    by force
  with rej_a
  have "let (e, r, d) = m V A p;
          (e', r', d') = n V A p in
            a \<in> reject_r (max_aggregator A (e, r, d) (e', r', d'))"
    unfolding prod.case_eq_if
    by simp
  hence "let (e, r, d) = m V A p;
            (e', r', d') = n V A p in
              a \<in> A - (e \<union> e' \<union> d \<union> d')"
    by simp
  hence
    "a \<in> A - (elect m V A p \<union> elect n V A p \<union> defer m V A p \<union> defer n V A p)"
    by auto
  thus "a \<in> reject m V A p \<and> a \<in> reject n V A p"
    using Diff_iff Un_iff electoral_mod_defer_elem assms
    by metis
next
  assume "a \<in> reject m V A p \<and> a \<in> reject n V A p"
  moreover from this
  have "a \<notin> elect m V A p \<and> a \<notin> defer m V A p
      \<and> a \<notin> elect n V A p \<and> a \<notin> defer n V A p"
    using IntI empty_iff assms result_disj
    by metis
  ultimately show "a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p"
    using DiffD1 max_agg_eq_result mod_contains_result_comm mod_contains_result_def
          reject_not_elected_or_deferred assms
    by (metis (no_types))
qed

lemma max_agg_rej_fst_imp_seq_contained:
  fixes
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    f_prof: "finite_profile V A p" and
    module_m: "\<S>\<C>\<F>_result.electoral_module m" and
    module_n: "\<S>\<C>\<F>_result.electoral_module n" and
    rejected: "a \<in> reject n V A p"
  shows "mod_contains_result m (m \<parallel>\<^sub>\<up> n) V A p a"
  using assms
proof (unfold mod_contains_result_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n max_par_comp_sound
    by metis
next
  show "a \<in> A"
    using f_prof module_n rejected reject_in_alts
    by blast
next
  assume a_in_elect: "a \<in> elect m V A p"
  hence a_not_reject: "a \<notin> reject m V A p"
    using disjoint_iff_not_equal f_prof module_m result_disj
    by metis
  have "reject n V A p \<subseteq> A"
    using f_prof module_n
    by (simp add: reject_in_alts)
  hence "a \<in> A"
    using in_mono rejected
    by metis
  with a_in_elect a_not_reject
  show "a \<in> elect (m \<parallel>\<^sub>\<up> n) V A p"
    using f_prof max_agg_eq_result module_m module_n rejected
          max_agg_rej_iff_both_reject mod_contains_result_comm
          mod_contains_result_def
    by metis
next
  assume "a \<in> reject m V A p"
  hence "a \<in> reject m V A p \<and> a \<in> reject n V A p"
    using rejected
    by simp
  thus "a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p"
    using f_prof max_agg_rej_iff_both_reject module_m module_n
    by (metis (no_types))
next
  assume a_in_defer: "a \<in> defer m V A p"
  then obtain d :: "'a" where
    defer_a: "a = d \<and> d \<in> defer m V A p"
    by metis
  have a_not_rej: "a \<notin> reject m V A p"
    using disjoint_iff_not_equal f_prof defer_a module_m result_disj
    by (metis (no_types))
  have
    "\<forall> m' A' V' p'.
      \<S>\<C>\<F>_result.electoral_module m' \<and> finite A' \<and> finite V' \<and> profile V' A' p'
        \<longrightarrow> elect m' V' A' p' \<union> reject m' V' A' p' \<union> defer m' V' A' p' = A'"
    using result_presv_alts
    by metis
  hence "a \<in> A"
    using a_in_defer f_prof module_m
    by blast
  with defer_a a_not_rej
  show "a \<in> defer (m \<parallel>\<^sub>\<up> n) V A p"
    using f_prof max_agg_eq_result max_agg_rej_iff_both_reject
          mod_contains_result_comm mod_contains_result_def
          module_m module_n rejected
    by metis
qed

lemma max_agg_rej_fst_equiv_seq_contained:
  fixes
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "finite_profile V A p" and
    "\<S>\<C>\<F>_result.electoral_module m" and
    "\<S>\<C>\<F>_result.electoral_module n" and
    "a \<in> reject n V A p"
  shows "mod_contains_result_sym (m \<parallel>\<^sub>\<up> n) m V A p a"
  using assms
proof (unfold mod_contains_result_sym_def, safe)
  assume "a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p"
  thus "a \<in> reject m V A p"
    using assms max_agg_rej_iff_both_reject
    by (metis (no_types))
next
  have "mod_contains_result m (m \<parallel>\<^sub>\<up> n) V A p a"
    using assms max_agg_rej_fst_imp_seq_contained
    by (metis (full_types))
  thus
    "a \<in> elect (m \<parallel>\<^sub>\<up> n) V A p \<Longrightarrow> a \<in> elect m V A p" and
    "a \<in> defer (m \<parallel>\<^sub>\<up> n) V A p \<Longrightarrow> a \<in> defer m V A p"
    using mod_contains_result_comm
    unfolding mod_contains_result_def
    by (metis (full_types), metis (full_types))
next
  show
    "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)" and
    "a \<in> A"
    using assms max_agg_rej_fst_imp_seq_contained
    unfolding mod_contains_result_def
    by (metis (full_types), metis (full_types))
next
  show
    "a \<in> elect m V A p \<Longrightarrow> a \<in> elect (m \<parallel>\<^sub>\<up> n) V A p" and
    "a \<in> reject m V A p \<Longrightarrow> a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p" and
    "a \<in> defer m V A p \<Longrightarrow> a \<in> defer (m \<parallel>\<^sub>\<up> n) V A p"
    using assms max_agg_rej_fst_imp_seq_contained
    unfolding mod_contains_result_def
    by (metis (no_types), metis (no_types), metis (no_types))
qed

lemma max_agg_rej_snd_imp_seq_contained:
  fixes
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    f_prof: "finite_profile V A p" and
    module_m: "\<S>\<C>\<F>_result.electoral_module m" and
    module_n: "\<S>\<C>\<F>_result.electoral_module n" and
    rejected: "a \<in> reject m V A p"
  shows "mod_contains_result n (m \<parallel>\<^sub>\<up> n) V A p a"
  using assms
proof (unfold mod_contains_result_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n max_par_comp_sound
    by metis
next
  show "a \<in> A"
    using f_prof in_mono module_m reject_in_alts rejected
    by (metis (no_types))
next
  assume "a \<in> elect n V A p"
  thus "a \<in> elect (m \<parallel>\<^sub>\<up> n) V A p"
    using max_aggregator.simps[of
            _ "elect m V A p" "reject m V A p" "defer m V A p"
            "elect n V A p" "reject n V A p" "defer n V A p"]
    by simp
next
  assume "a \<in> reject n V A p"
  thus "a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p"
    using f_prof max_agg_rej_iff_both_reject module_m module_n rejected
    by metis
next
  assume "a \<in> defer n V A p"
  moreover have "a \<in> A"
    using f_prof max_agg_rej_fst_imp_seq_contained module_m rejected
    unfolding mod_contains_result_def
    by metis
  ultimately show "a \<in> defer (m \<parallel>\<^sub>\<up> n) V A p"
    using disjoint_iff_not_equal max_agg_eq_result max_agg_rej_iff_both_reject
          f_prof mod_contains_result_comm mod_contains_result_def
          module_m module_n rejected result_disj
    by (metis (no_types, opaque_lifting))
qed

lemma max_agg_rej_snd_equiv_seq_contained:
  fixes
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "finite_profile V A p" and
    "\<S>\<C>\<F>_result.electoral_module m" and
    "\<S>\<C>\<F>_result.electoral_module n" and
    "a \<in> reject m V A p"
  shows "mod_contains_result_sym (m \<parallel>\<^sub>\<up> n) n V A p a"
  using assms
proof (unfold mod_contains_result_sym_def, safe)
  assume "a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p"
  thus "a \<in> reject n V A p"
    using assms max_agg_rej_iff_both_reject
    by (metis (no_types))
next
  have "mod_contains_result n (m \<parallel>\<^sub>\<up> n) V A p a"
    using assms max_agg_rej_snd_imp_seq_contained
    by (metis (full_types))
  thus
    "a \<in> elect (m \<parallel>\<^sub>\<up> n) V A p \<Longrightarrow> a \<in> elect n V A p" and
    "a \<in> defer (m \<parallel>\<^sub>\<up> n) V A p \<Longrightarrow> a \<in> defer n V A p"
    using mod_contains_result_comm
    unfolding mod_contains_result_def
    by (metis (full_types), metis (full_types))
next
  show
    "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)" and
    "a \<in> A"
    using assms max_agg_rej_snd_imp_seq_contained
    unfolding mod_contains_result_def
    by (metis (full_types), metis (full_types))
next
  show
    "a \<in> elect n V A p \<Longrightarrow> a \<in> elect (m \<parallel>\<^sub>\<up> n) V A p" and
    "a \<in> reject n V A p \<Longrightarrow> a \<in> reject (m \<parallel>\<^sub>\<up> n) V A p" and
    "a \<in> defer n V A p \<Longrightarrow> a \<in> defer (m \<parallel>\<^sub>\<up> n) V A p"
    using assms max_agg_rej_snd_imp_seq_contained
    unfolding mod_contains_result_def
    by (metis (no_types), metis (no_types), metis (no_types))
qed

lemma max_agg_rej_intersect:
  fixes
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "\<S>\<C>\<F>_result.electoral_module n" and
    "profile V A p" and
    "finite A"
  shows "reject (m \<parallel>\<^sub>\<up> n) V A p = (reject m V A p) \<inter> (reject n V A p)"
proof -
  have "A = (elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p)
      \<and> A = (elect n V A p) \<union> (reject n V A p) \<union> (defer n V A p)"
    using assms result_presv_alts
    by metis
  hence "A - ((elect m V A p) \<union> (defer m V A p)) = (reject m V A p)
      \<and> A - ((elect n V A p) \<union> (defer n V A p)) = (reject n V A p)"
    using assms reject_not_elected_or_deferred
    by fastforce
  hence
    "A - ((elect m V A p) \<union> (elect n V A p)
          \<union> (defer m V A p) \<union> (defer n V A p)) =
    (reject m V A p) \<inter> (reject n V A p)"
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
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    a :: "'a"
  assumes
     "disjoint_compatibility m n" and
     "a \<in> A"
   shows
    "(\<forall> p. finite_profile V A p \<longrightarrow> mod_contains_result m (m \<parallel>\<^sub>\<up> n) V A p a)
      \<or> (\<forall> p. finite_profile V A p \<longrightarrow> mod_contains_result n (m \<parallel>\<^sub>\<up> n) V A p a)"
  using DiffI assms max_agg_rej_fst_imp_seq_contained max_agg_rej_snd_imp_seq_contained
  unfolding disjoint_compatibility_def
  by metis

subsection \<open>Composition Rules\<close>

text \<open>
  Using a conservative aggregator, the parallel composition
  preserves the property non-electing.
\<close>

theorem conserv_max_agg_presv_non_electing[simp]:
  fixes m n :: "('a, 'v, 'a Result) Electoral_Module"
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
  fixes m n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    compatible: "disjoint_compatibility m n" and
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<parallel>\<^sub>\<up> n)"
proof (unfold defer_lift_invariance_def, safe)
  have mod_m: "\<S>\<C>\<F>_result.electoral_module m"
    using monotone_m
    unfolding defer_lift_invariance_def
    by simp
  moreover have mod_n: "\<S>\<C>\<F>_result.electoral_module n"
    using monotone_n
    unfolding defer_lift_invariance_def
    by simp
  ultimately show "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    using max_par_comp_sound
    by metis
  fix
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    defer_a: "a \<in> defer (m \<parallel>\<^sub>\<up> n) V A p" and
    lifted_a: "Profile.lifted V A p q a"
  hence f_profs: "finite_profile V A p \<and> finite_profile V A q"
    unfolding lifted_def
    by simp
  from compatible
  obtain B :: "'a set" where
    alts: "B \<subseteq> A
        \<and> (\<forall> b \<in> B. indep_of_alt m V A b \<and>
              (\<forall> p'. finite_profile V A p' \<longrightarrow> b \<in> reject m V A p'))
        \<and> (\<forall> b \<in> A - B. indep_of_alt n V A b \<and>
              (\<forall> p'. finite_profile V A p' \<longrightarrow> b \<in> reject n V A p'))"
    using f_profs
    unfolding disjoint_compatibility_def
    by (metis (no_types, lifting))
  have "\<forall> b \<in> A. prof_contains_result (m \<parallel>\<^sub>\<up> n) V A p q b"
  proof (cases)
    assume a_in_B: "a \<in> B"
    hence "a \<in> reject m V A p"
      using alts f_profs
      by blast
    with defer_a
    have defer_n: "a \<in> defer n V A p"
      using compatible f_profs max_agg_rej_snd_equiv_seq_contained
      unfolding disjoint_compatibility_def mod_contains_result_sym_def
      by metis
    have "\<forall> b \<in> B. mod_contains_result_sym (m \<parallel>\<^sub>\<up> n) n V A p b"
      using alts compatible max_agg_rej_snd_equiv_seq_contained f_profs
      unfolding disjoint_compatibility_def
      by metis
    moreover have "\<forall> b \<in> A. prof_contains_result n V A p q b"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show "\<S>\<C>\<F>_result.electoral_module n \<and> profile V A p
              \<and> profile V A q \<and> b \<in> A \<and>
              (b \<in> elect n V A p \<longrightarrow> b \<in> elect n V A q) \<and>
              (b \<in> reject n V A p \<longrightarrow> b \<in> reject n V A q) \<and>
              (b \<in> defer n V A p \<longrightarrow> b \<in> defer n V A q)"
      proof (safe)
        show "\<S>\<C>\<F>_result.electoral_module n"
          using monotone_n
          unfolding defer_lift_invariance_def
          by metis
      next
        show
          "profile V A p" and
          "profile V A q" and
          "b \<in> A"
          using f_profs b_in_A
          by (simp, simp, simp)
      next
        show
          "b \<in> elect n V A p \<Longrightarrow> b \<in> elect n V A q" and
          "b \<in> reject n V A p \<Longrightarrow> b \<in> reject n V A q" and
          "b \<in> defer n V A p \<Longrightarrow> b \<in> defer n V A q"
          using defer_n lifted_a monotone_n f_profs
          unfolding defer_lift_invariance_def
          by (metis, metis, metis)
      qed
    qed
    moreover have "\<forall> b \<in> B. mod_contains_result n (m \<parallel>\<^sub>\<up> n) V A q b"
      using alts compatible max_agg_rej_snd_imp_seq_contained f_profs
      unfolding disjoint_compatibility_def
      by metis
    ultimately have prof_contains_result_of_comps_for_elems_in_B:
      "\<forall> b \<in> B. prof_contains_result (m \<parallel>\<^sub>\<up> n) V A p q b"
      unfolding mod_contains_result_def mod_contains_result_sym_def
                prof_contains_result_def
      by simp
    have "\<forall> b \<in> A - B. mod_contains_result_sym (m \<parallel>\<^sub>\<up> n) m V A p b"
      using alts max_agg_rej_fst_equiv_seq_contained monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    moreover have "\<forall> b \<in> A. prof_contains_result m V A p q b"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show "\<S>\<C>\<F>_result.electoral_module m \<and> profile V A p \<and>
              profile V A q \<and> b \<in> A \<and>
              (b \<in> elect m V A p \<longrightarrow> b \<in> elect m V A q) \<and>
              (b \<in> reject m V A p \<longrightarrow> b \<in> reject m V A q) \<and>
              (b \<in> defer m V A p \<longrightarrow> b \<in> defer m V A q)"
      proof (safe)
        show "\<S>\<C>\<F>_result.electoral_module m"
          using monotone_m
          unfolding defer_lift_invariance_def
          by metis
      next
        show
          "profile V A p" and
          "profile V A q" and
          "b \<in> A"
          using f_profs b_in_A
          by (simp, simp, simp)
      next
        show
          "b \<in> elect m V A p \<Longrightarrow> b \<in> elect m V A q" and
          "b \<in> reject m V A p \<Longrightarrow> b \<in> reject m V A q" and
          "b \<in> defer m V A p \<Longrightarrow> b \<in> defer m V A q"
          using alts a_in_B lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by (metis, metis, metis)
      qed
    qed
    moreover have "\<forall> b \<in> A - B. mod_contains_result m (m \<parallel>\<^sub>\<up> n) V A q b"
      using alts max_agg_rej_fst_imp_seq_contained monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    ultimately have "\<forall> b \<in> A - B. prof_contains_result (m \<parallel>\<^sub>\<up> n) V A p q b"
      unfolding mod_contains_result_def mod_contains_result_sym_def
                prof_contains_result_def
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
    hence reject_n: "a \<in> reject n V A p"
      using alts f_profs
      by blast
    hence defer_m: "a \<in> defer m V A p"
      using mod_m mod_n defer_a f_profs max_agg_rej_fst_equiv_seq_contained
      unfolding mod_contains_result_sym_def
      by (metis (no_types))
    have "\<forall> b \<in> B. mod_contains_result (m \<parallel>\<^sub>\<up> n) n V A p b"
      using alts compatible f_profs max_agg_rej_snd_imp_seq_contained mod_contains_result_comm
      unfolding disjoint_compatibility_def
      by metis
    have "\<forall> b \<in> B. mod_contains_result_sym (m \<parallel>\<^sub>\<up> n) n V A p b"
      using alts max_agg_rej_snd_equiv_seq_contained monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    moreover have "\<forall> b \<in> A. prof_contains_result n V A p q b"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show "\<S>\<C>\<F>_result.electoral_module n \<and> profile V A p \<and>
              profile V A q \<and> b \<in> A \<and>
              (b \<in> elect n V A p \<longrightarrow> b \<in> elect n V A q) \<and>
              (b \<in> reject n V A p \<longrightarrow> b \<in> reject n V A q) \<and>
              (b \<in> defer n V A p \<longrightarrow> b \<in> defer n V A q)"
      proof (safe)
        show "\<S>\<C>\<F>_result.electoral_module n"
          using monotone_n
          unfolding defer_lift_invariance_def
          by metis
      next
        show
          "profile V A p" and
          "profile V A q" and
          "b \<in> A"
          using f_profs b_in_A
          by (simp, simp, simp)
      next
        show
          "b \<in> elect n V A p \<Longrightarrow> b \<in> elect n V A q" and
          "b \<in> reject n V A p \<Longrightarrow> b \<in> reject n V A q" and
          "b \<in> defer n V A p \<Longrightarrow> b \<in> defer n V A q"
          using alts a_in_set_diff lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by (metis, metis, metis)
      qed
    qed
  moreover have "\<forall> b \<in> B. mod_contains_result n (m \<parallel>\<^sub>\<up> n) V A q b"
    using alts compatible max_agg_rej_snd_imp_seq_contained f_profs
    unfolding disjoint_compatibility_def
    by metis
  ultimately have prof_contains_result_of_comps_for_elems_in_B:
    "\<forall> b \<in> B. prof_contains_result (m \<parallel>\<^sub>\<up> n) V A p q b"
      unfolding mod_contains_result_def mod_contains_result_sym_def
                prof_contains_result_def
    by simp
  have "\<forall> b \<in> A - B. mod_contains_result_sym (m \<parallel>\<^sub>\<up> n) m V A p b"
    using alts max_agg_rej_fst_equiv_seq_contained monotone_m monotone_n f_profs
    unfolding defer_lift_invariance_def
    by metis
  moreover have "\<forall> b \<in> A. prof_contains_result m V A p q b"
  proof (unfold prof_contains_result_def, clarify)
    fix b :: "'a"
    assume b_in_A: "b \<in> A"
    show "\<S>\<C>\<F>_result.electoral_module m \<and> profile V A p
        \<and> profile V A q \<and> b \<in> A
        \<and> (b \<in> elect m V A p \<longrightarrow> b \<in> elect m V A q)
        \<and> (b \<in> reject m V A p \<longrightarrow> b \<in> reject m V A q)
        \<and> (b \<in> defer m V A p \<longrightarrow> b \<in> defer m V A q)"
    proof (safe)
      show "\<S>\<C>\<F>_result.electoral_module m"
        using monotone_m
        unfolding defer_lift_invariance_def
        by simp
    next
      show
        "profile V A p" and
        "profile V A q" and
        "b \<in> A"
        using f_profs b_in_A
        by (simp, simp, simp)
    next
      show
        "b \<in> elect m V A p \<Longrightarrow> b \<in> elect m V A q" and
        "b \<in> reject m V A p \<Longrightarrow> b \<in> reject m V A q" and
        "b \<in> defer m V A p \<Longrightarrow> b \<in> defer m V A q"
        using defer_m lifted_a monotone_m
        unfolding defer_lift_invariance_def
        by (metis, metis, metis)
    qed
  qed
  moreover have "\<forall> x \<in> A - B. mod_contains_result m (m \<parallel>\<^sub>\<up> n) V A q x"
    using alts max_agg_rej_fst_imp_seq_contained monotone_m monotone_n f_profs
    unfolding defer_lift_invariance_def
    by metis
  ultimately have "\<forall> x \<in> A - B. prof_contains_result (m \<parallel>\<^sub>\<up> n) V A p q x"
    unfolding mod_contains_result_def mod_contains_result_sym_def
              prof_contains_result_def
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
    m n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    c :: "nat"
  assumes
    compatible: "disjoint_compatibility m n" and
    prof: "profile V A p" and
    fin_A: "finite A" and
    reject_sum: "card (reject m V A p) + card (reject n V A p) = card A + c"
  shows "card (reject (m \<parallel>\<^sub>\<up> n) V A p) = c"
proof -
  obtain B :: "'a set" where
    alt_set: "B \<subseteq> A
      \<and> (\<forall> a \<in> B. indep_of_alt m V A a \<and>
            (\<forall> q. profile V A q \<longrightarrow> a \<in> reject m V A q))
      \<and> (\<forall> a \<in> A - B. indep_of_alt n V A a \<and>
            (\<forall> q. profile V A q \<longrightarrow> a \<in> reject n V A q))"
    using compatible prof
    unfolding disjoint_compatibility_def
    by metis
  have reject_representation:
    "reject (m \<parallel>\<^sub>\<up> n) V A p = (reject m V A p) \<inter> (reject n V A p)"
    using prof fin_A compatible max_agg_rej_intersect
    unfolding disjoint_compatibility_def
    by metis
  have "\<S>\<C>\<F>_result.electoral_module m \<and> \<S>\<C>\<F>_result.electoral_module n"
    using compatible
    unfolding disjoint_compatibility_def
    by simp
  hence subsets: "(reject m V A p) \<subseteq> A \<and> (reject n V A p) \<subseteq> A"
    using prof
    by (simp add: reject_in_alts)
  hence "finite (reject m V A p) \<and> finite (reject n V A p)"
    using rev_finite_subset prof fin_A
    by metis
  hence card_difference:
    "card (reject (m \<parallel>\<^sub>\<up> n) V A p)
      = card A + c - card ((reject m V A p) \<union> (reject n V A p))"
    using card_Un_Int reject_representation reject_sum
    by fastforce
  have "\<forall> a \<in> A. a \<in> (reject m V A p) \<or> a \<in> (reject n V A p)"
    using alt_set prof fin_A
    by blast
  hence "A = reject m V A p \<union> reject n V A p"
    using subsets
    by force
  thus "card (reject (m \<parallel>\<^sub>\<up> n) V A p) = c"
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
  fixes m n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    defers_m_one: "defers 1 m" and
    non_elec_m: "non_electing m" and
    rejec_n_two: "rejects 2 n" and
    disj_comp: "disjoint_compatibility m n"
  shows "eliminates 1 (m \<parallel>\<^sub>\<up> n)"
proof (unfold eliminates_def, safe)
  have "\<S>\<C>\<F>_result.electoral_module m"
    using non_elec_m
    unfolding non_electing_def
    by simp
  moreover have "\<S>\<C>\<F>_result.electoral_module n"
    using rejec_n_two
    unfolding rejects_def
    by simp
  ultimately show "\<S>\<C>\<F>_result.electoral_module (m \<parallel>\<^sub>\<up> n)"
    using max_par_comp_sound
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    min_card_two: "1 < card A" and
    prof: "profile V A p"
  hence card_geq_one: "card A \<ge> 1"
    by presburger
  have fin_A: "finite A"
    using min_card_two card.infinite not_one_less_zero
    by metis
  have module: "\<S>\<C>\<F>_result.electoral_module m"
    using non_elec_m
    unfolding non_electing_def
    by simp
  have elect_card_zero: "card (elect m V A p) = 0"
    using prof non_elec_m card_eq_0_iff
    unfolding non_electing_def
    by simp
  moreover from card_geq_one
  have def_card_one: "card (defer m V A p) = 1"
    using defers_m_one module prof fin_A
    unfolding defers_def
    by blast
  ultimately have card_reject_m: "card (reject m V A p) = card A - 1"
  proof -
    have "well_formed_\<S>\<C>\<F> A (elect m V A p, reject m V A p, defer m V A p)"
      using prof module
      unfolding \<S>\<C>\<F>_result.electoral_module.simps
      by simp
    hence "card A =
        card (elect m V A p) + card (reject m V A p) + card (defer m V A p)"
      using result_count fin_A
      by blast
    thus ?thesis
      using def_card_one elect_card_zero
      by simp
  qed
  have "card A \<ge> 2"
    using min_card_two
    by simp
  hence "card (reject n V A p) = 2"
    using prof rejec_n_two fin_A
    unfolding rejects_def
    by blast
  moreover from this
  have "card (reject m V A p) + card (reject n V A p) = card A + 1"
    using card_reject_m card_geq_one
    by linarith
  ultimately show "card (reject (m \<parallel>\<^sub>\<up> n) V A p) = 1"
    using disj_comp prof card_reject_m par_comp_rej_card fin_A
    by blast
qed

end
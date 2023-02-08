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

fun maximum_parallel_composition :: "'a Electoral_Module \<Rightarrow>
        'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "maximum_parallel_composition m n =
    (let a = max_aggregator in (m \<parallel>\<^sub>a n))"

abbreviation max_parallel :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Electoral_Module" (infix "\<parallel>\<^sub>\<up>" 50) where
  "m \<parallel>\<^sub>\<up> n == maximum_parallel_composition m n"

subsection \<open>Soundness\<close>

theorem max_par_comp_sound:
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n"
  shows "electoral_module (m \<parallel>\<^sub>\<up> n)"
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
    "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p x \<or>
      mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p x"
proof (cases)
  assume a1: "x \<in> elect (m \<parallel>\<^sub>\<up> n) A p"
    have mod_contains_inst:
      "\<forall> p_mod q_mod a_set prof a.
        mod_contains_result p_mod q_mod a_set prof (a::'a) =
          (electoral_module p_mod \<and> electoral_module q_mod \<and>
            finite a_set \<and> profile a_set prof \<and> a \<in> a_set \<and>
            (a \<notin> elect p_mod a_set prof \<or> a \<in> elect q_mod a_set prof) \<and>
            (a \<notin> reject p_mod a_set prof \<or> a \<in> reject q_mod a_set prof) \<and>
            (a \<notin> defer p_mod a_set prof \<or> a \<in> defer q_mod a_set prof))"
      unfolding mod_contains_result_def
      by simp
    have module_mn: "electoral_module (m \<parallel>\<^sub>\<up> n)"
      using module_m module_n
      by simp
  have not_defer_mn: "x \<notin> defer (m \<parallel>\<^sub>\<up> n) A p"
    using module_mn IntI a1 empty_iff f_prof result_disj
    by (metis (no_types))
  have not_reject_mn: "x \<notin> reject (m \<parallel>\<^sub>\<up> n) A p"
    using module_mn IntI a1 empty_iff f_prof result_disj
    by (metis (no_types))
  from a1 have
    "let (e1, r1, d1) = m A p;
        (e2, r2, d2) = n A p in
      x \<in> e1 \<union> e2"
    by auto
  hence union_mn: "x \<in> (elect m A p) \<union> (elect n A p)"
    by auto
  thus ?thesis
    using f_prof in_A module_m module_mn module_n
          not_defer_mn not_reject_mn union_mn
          mod_contains_inst
      by blast
next
  assume not_a1: "x \<notin> elect (m \<parallel>\<^sub>\<up> n) A p"
  thus ?thesis
  proof (cases)
    assume x_in_def: "x \<in> defer (m \<parallel>\<^sub>\<up> n) A p"
    thus ?thesis
    proof (safe)
      assume not_mod_cont_mn:
        "\<not> mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p x"
      have par_emod:
        "\<forall> f g.
          (electoral_module (f::'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<and>
            electoral_module g) \<longrightarrow>
              electoral_module (f \<parallel>\<^sub>\<up> g)"
        using max_par_comp_sound
        by blast
      hence "electoral_module (m \<parallel>\<^sub>\<up> n)"
        using module_m module_n
        by blast
      hence max_par_emod:
        "electoral_module (m \<parallel>\<^sub>max_aggregator n)"
        by simp
      have set_intersect:
        "\<forall>(a::'a) A B. (a \<in> A \<inter> B) = (a \<in> A \<and> a \<in> B)"
        by blast
      obtain
        s_func :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> 'a set" and
        p_func :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> 'a Profile" where
        well_f:
        "\<forall> f.
          (\<not> electoral_module f \<or>
            (\<forall> A prof. (finite A \<and> profile A prof) \<longrightarrow> well_formed A (f A prof))) \<and>
          (electoral_module f \<or> finite (s_func f) \<and> profile (s_func f) (p_func f) \<and>
            \<not> well_formed (s_func f) (f (s_func f) (p_func f)))"
        unfolding electoral_module_def
        by moura
      hence wf_n: "well_formed A (n A p)"
        using f_prof module_n
        by blast
      have wf_m: "well_formed A (m A p)"
        using well_f f_prof module_m
        by blast
      have a_exists: "\<forall>(a::'a). a \<notin> {}"
        by blast
      have e_mod_par: "electoral_module (m \<parallel>\<^sub>\<up> n)"
        using par_emod module_m module_n
        by blast
      hence "electoral_module (m \<parallel>\<^sub>max_aggregator n)"
        by simp
      hence result_disj_max:
        "elect (m \<parallel>\<^sub>max_aggregator n) A p \<inter> reject (m \<parallel>\<^sub>max_aggregator n) A p = {} \<and>
          elect (m \<parallel>\<^sub>max_aggregator n) A p \<inter> defer (m \<parallel>\<^sub>max_aggregator n) A p = {} \<and>
          reject (m \<parallel>\<^sub>max_aggregator n) A p \<inter> defer (m \<parallel>\<^sub>max_aggregator n) A p = {}"
        using f_prof result_disj
        by metis
      have x_not_elect:
        "x \<notin> elect (m \<parallel>\<^sub>max_aggregator n) A p"
        using result_disj_max x_in_def
        by force
      have result_m:
        "(elect m A p, reject m A p, defer m A p) = m A p"
        by auto
      have result_n:
        "(elect n A p, reject n A p, defer n A p) = n A p"
        by auto
      have max_pq:
        "\<forall>(A::'a set) p q.
          elect_r (max_aggregator A p q) = elect_r p \<union> elect_r q"
        by force
      have
        "x \<notin> elect (m \<parallel>\<^sub>max_aggregator n) A p"
        using x_not_elect
        by blast
      with max_pq
      have "x \<notin> elect m A p \<union> elect n A p"
        by (simp add: max_pq)
      hence x_not_elect_mn:
        "x \<notin> elect m A p \<and> x \<notin> elect n A p"
        by blast
      have x_not_mpar_rej:
        "x \<notin> reject (m \<parallel>\<^sub>max_aggregator n) A p"
        using result_disj_max x_in_def
        by fastforce
      hence x_not_par_rej:
        "x \<notin> reject (m \<parallel>\<^sub>\<up> n) A p"
        by auto
      have mod_cont_res_fg:
        "\<forall> f g A prof (a::'a).
          mod_contains_result f g A prof a =
            (electoral_module f \<and> electoral_module g \<and>
              finite A \<and> profile A prof \<and> a \<in> A \<and>
                (a \<notin> elect f A prof \<or> a \<in> elect g A prof) \<and>
                (a \<notin> reject f A prof \<or> a \<in> reject g A prof) \<and>
                (a \<notin> defer f A prof \<or> a \<in> defer g A prof))"
        by (simp add: mod_contains_result_def)
      have max_agg_res:
        "max_aggregator A (elect m A p, reject m A p, defer m A p)
          (elect n A p, reject n A p, defer n A p) = (m \<parallel>\<^sub>max_aggregator n) A p"
        by simp
      have well_f_max:
        "\<forall> r2 r1 e2 e1 d2 d1 A.
          well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2) \<longrightarrow>
            reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
        using max_agg_rej_set
        by metis
      have e_mod_disj:
        "\<forall> f (A::'a set) prof.
          (electoral_module f \<and> finite (A::'a set) \<and> profile A prof) \<longrightarrow>
            elect f A prof \<union> reject f A prof \<union> defer f A prof = A"
        using result_presv_alts
        by blast
      hence e_mod_disj_n:
        "elect n A p \<union> reject n A p \<union> defer n A p = A"
        using f_prof module_n
        by metis
      have
        "\<forall> f g A prof (a::'a).
          mod_contains_result f g A prof a =
            (electoral_module f \<and> electoral_module g \<and>
              finite A \<and> profile A prof \<and> a \<in> A \<and>
              (a \<notin> elect f A prof \<or> a \<in> elect g A prof) \<and>
              (a \<notin> reject f A prof \<or> a \<in> reject g A prof) \<and>
              (a \<notin> defer f A prof \<or> a \<in> defer g A prof))"
        by (simp add: mod_contains_result_def)
      with e_mod_disj_n
      have "x \<in> reject n A p"
        using e_mod_par f_prof in_A module_n not_mod_cont_mn
              x_not_elect x_not_elect_mn x_not_mpar_rej
        by auto
      hence "x \<notin> reject m A p"
        using well_f_max max_agg_res result_m result_n
              set_intersect wf_m wf_n x_not_mpar_rej
        by (metis (no_types))
      with max_agg_res
      have
        "x \<notin> defer (m \<parallel>\<^sub>\<up> n) A p \<or> x \<in> defer m A p"
          using e_mod_disj f_prof in_A module_m x_not_elect_mn
          by blast
      with x_not_mpar_rej
      show "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p x"
        using mod_cont_res_fg x_not_par_rej e_mod_par f_prof
              in_A module_m x_not_elect
        by auto
    qed
  next
    assume not_a2: "x \<notin> defer (m \<parallel>\<^sub>\<up> n) A p"
    have el_rej_defer:
      "(elect m A p, reject m A p, defer m A p) = m A p"
      by auto
    from not_a1 not_a2 have a3:
      "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
      using electoral_mod_defer_elem in_A module_m module_n
            f_prof max_par_comp_sound
      by metis
    hence
      "case snd (m A p) of (Aa, Ab) \<Rightarrow>
        case n A p of (Ac, Ad, Ae) \<Rightarrow>
          x \<in> reject_r
            (max_aggregator A
              (elect m A p, Aa, Ab) (Ac, Ad, Ae))"
      using el_rej_defer
      by force
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> fst (snd (max_aggregator A
          (e1, r1, d1) (e2, r2, d2)))"
      by (simp add: case_prod_unfold)
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    hence "x \<notin> elect m A p \<union> (defer n A p \<union> defer m A p)"
      by force
    thus ?thesis
      using mod_contains_result_comm mod_contains_result_def Un_iff
            a3 f_prof in_A module_m module_n max_par_comp_sound
      by (metis (no_types))
  qed
qed

lemma max_agg_rej_iff_both_reject:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n"
  shows
    "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p \<longleftrightarrow>
      (x \<in> reject m A p \<and> x \<in> reject n A p)"
proof
  assume a: "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
  hence
    "case n A p of (Aa, Ab, Ac) \<Rightarrow>
      x \<in> reject_r (max_aggregator A
        (elect m A p, reject m A p, defer m A p) (Aa, Ab, Ac))"
    by auto
  hence
    "case snd (m A p) of (Aa, Ab) \<Rightarrow>
      case n A p of (Ac, Ad, Ae) \<Rightarrow>
        x \<in> reject_r (max_aggregator A
          (elect m A p, Aa, Ab) (Ac, Ad, Ae))"
    by force
  with a have
    "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
      x \<in> fst (snd (max_aggregator A (e1, r1, d1) (e2, r2, d2)))"
    by (simp add: prod.case_eq_if)
  hence
    "let (e1, r1, d1) = m A p;
        (e2, r2, d2) = n A p in
      x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
    by simp
  hence
    "x \<in> A - (elect m A p \<union> elect n A p \<union> defer m A p \<union> defer n A p)"
    by auto
  thus "x \<in> reject m A p \<and> x \<in> reject n A p"
    using Diff_iff Un_iff electoral_mod_defer_elem
          f_prof module_m module_n
    by metis
next
  assume a: "x \<in> reject m A p \<and> x \<in> reject n A p"
  hence
    "x \<notin> elect m A p \<and> x \<notin> defer m A p \<and>
      x \<notin> elect n A p \<and> x \<notin> defer n A p"
    using IntI empty_iff module_m module_n f_prof result_disj
    by metis
  thus "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
    using DiffD1 a f_prof max_agg_eq_result module_m module_n
          mod_contains_result_comm mod_contains_result_def
          reject_not_elec_or_def
      by (metis (no_types))
qed

lemma max_agg_rej1:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject n A p"
  shows "mod_contains_result m (m \<parallel>\<^sub>\<up> n) A p x"
proof (unfold mod_contains_result_def, safe)
  show "electoral_module m"
    using module_m
    by simp
next
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n
    by simp
next
  show "finite A"
    using f_prof
    by simp
next
  show "profile A p"
    using f_prof
    by simp
next
  show "x \<in> A"
    using f_prof module_n reject_in_alts rejected
    by auto
next
  assume x_in_elect: "x \<in> elect m A p"
  hence x_not_reject:
    "x \<notin> reject m A p"
    using disjoint_iff_not_equal f_prof module_m result_disj
    by metis
  have rej_in_A:
    "reject n A p \<subseteq> A"
    using f_prof module_n
    by (simp add: reject_in_alts)
  have x_in_A: "x \<in> A"
    using rej_in_A in_mono rejected
    by metis
  with x_in_elect x_not_reject
  show "x \<in> elect (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_eq_result module_m module_n rejected
          max_agg_rej_iff_both_reject mod_contains_result_comm
          mod_contains_result_def
      by metis
next
  assume "x \<in> reject m A p"
  hence
    "x \<in> reject m A p \<and> x \<in> reject n A p"
    using rejected
    by simp
  thus "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_rej_iff_both_reject module_m module_n
    by (metis (no_types))
next
  assume x_in_defer: "x \<in> defer m A p"
  hence defer_a:
    "\<exists> a. a \<in> defer m A p \<and> x = a"
    by simp
  then obtain x_inst :: 'a where
    inst_x: "x = x_inst \<and> x_inst \<in> defer m A p"
    by metis
  hence x_not_rej:
    "x \<notin> reject m A p"
    using disjoint_iff_not_equal f_prof inst_x module_m result_disj
    by (metis (no_types))
  have
    "\<forall> f A prof.
      (electoral_module f \<and> finite (A::'a set) \<and> profile A prof) \<longrightarrow>
        elect f A prof \<union> reject f A prof \<union> defer f A prof = A"
    using result_presv_alts
    by metis
  with x_in_defer
  have "x \<in> A"
    using f_prof module_m
    by blast
  with inst_x x_not_rej
  show "x \<in> defer (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_eq_result
          max_agg_rej_iff_both_reject
          mod_contains_result_comm
          mod_contains_result_def
          module_m module_n rejected
    by metis
qed

lemma max_agg_rej2:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject n A p"
  shows "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p x"
  using mod_contains_result_comm max_agg_rej1
        module_m module_n f_prof rejected
  by metis

lemma max_agg_rej3:
  assumes
    f_prof:  "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject m A p"
  shows "mod_contains_result n (m \<parallel>\<^sub>\<up> n) A p x"
proof (unfold mod_contains_result_def, safe)
  show "electoral_module n"
    using module_n
    by simp
next
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n
    by simp
next
  show "finite A"
    using f_prof
    by simp
next
  show "profile A p"
    using f_prof
    by simp
next
  show "x \<in> A"
    using f_prof in_mono module_m reject_in_alts rejected
    by (metis (no_types))
next
  assume "x \<in> elect n A p"
  thus "x \<in> elect (m \<parallel>\<^sub>\<up> n) A p"
    using Un_iff combine_ele_rej_def fst_conv
          maximum_parallel_composition.simps
          max_aggregator.simps
    unfolding parallel_composition.simps
    by (metis (mono_tags, lifting))
next
  assume "x \<in> reject n A p"
  thus "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_rej_iff_both_reject module_m module_n rejected
    by metis
next
  assume x_in_def: "x \<in> defer n A p"
  have "x \<in> A"
    using f_prof max_agg_rej1 mod_contains_result_def module_m rejected
    by metis
  thus "x \<in> defer (m \<parallel>\<^sub>\<up> n) A p"
    using x_in_def disjoint_iff_not_equal f_prof
          max_agg_eq_result max_agg_rej_iff_both_reject
          mod_contains_result_comm mod_contains_result_def
          module_m module_n rejected result_disj
      by metis
qed

lemma max_agg_rej4:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject m A p"
  shows "mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p x"
  using mod_contains_result_comm max_agg_rej3
        module_m module_n f_prof rejected
  by metis

lemma max_agg_rej_intersect:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows "reject (m \<parallel>\<^sub>\<up> n) A p = (reject m A p) \<inter> (reject n A p)"
proof -
  have
    "A = (elect m A p) \<union> (reject m A p) \<union> (defer m A p) \<and>
      A = (elect n A p) \<union> (reject n A p) \<union> (defer n A p)"
    using module_m module_n f_prof result_presv_alts
    by metis
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
    "(\<forall> p. finite_profile A p \<longrightarrow>
          mod_contains_result m (m \<parallel>\<^sub>\<up> n) A p x) \<or>
        (\<forall> p. finite_profile A p \<longrightarrow>
          mod_contains_result n (m \<parallel>\<^sub>\<up> n) A p x)"
  using DiffI compatible in_A max_agg_rej1 max_agg_rej3
  unfolding disjoint_compatibility_def
  by metis

subsection \<open>Composition Rules\<close>

text \<open>
  Using a conservative aggregator, the parallel composition
  preserves the property non-electing.
\<close>

theorem conserv_max_agg_presv_non_electing[simp]:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n"
  shows "non_electing (m \<parallel>\<^sub>\<up> n)"
  using non_electing_m non_electing_n
  by simp

text \<open>
  Using the max aggregator, composing two compatible
  electoral modules in parallel preserves defer-lift-invariance.
\<close>

theorem par_comp_def_lift_inv[simp]:
  assumes
    compatible: "disjoint_compatibility m n" and
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<parallel>\<^sub>\<up> n)"
proof (unfold defer_lift_invariance_def, safe)
  have electoral_mod_m: "electoral_module m"
    using monotone_m
    unfolding defer_lift_invariance_def
    by simp
  have electoral_mod_n: "electoral_module n"
    using monotone_n
    unfolding defer_lift_invariance_def
    by simp
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    S :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    x :: "'a"
  assume
    defer_x: "x \<in> defer (m \<parallel>\<^sub>\<up> n) S p" and
    lifted_x: "Profile.lifted S p q x"
  hence f_profs: "finite_profile S p \<and> finite_profile S q"
    unfolding lifted_def
    by simp
  from compatible
  obtain A :: "'a set" where A:
    "A \<subseteq> S \<and> (\<forall> x \<in> A. indep_of_alt m S x \<and>
      (\<forall> p. finite_profile S p \<longrightarrow> x \<in> reject m S p)) \<and>
        (\<forall> x \<in> S - A. indep_of_alt n S x \<and>
      (\<forall> p. finite_profile S p \<longrightarrow> x \<in> reject n S p))"
    using f_profs
    unfolding disjoint_compatibility_def
    by (metis (no_types, lifting))
  have "\<forall> x \<in> S. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
  proof (cases)
    assume a0: "x \<in> A"
    hence "x \<in> reject m S p"
      using A f_profs
      by blast
    with defer_x
    have defer_n: "x \<in> defer n S p"
      using compatible f_profs max_agg_rej4
      unfolding disjoint_compatibility_def mod_contains_result_def
      by metis
    have "\<forall> x \<in> A. mod_contains_result (m \<parallel>\<^sub>\<up> n) n S p x"
      using A compatible max_agg_rej4 f_profs
      unfolding disjoint_compatibility_def
      by metis
    moreover have "\<forall> x \<in> S. prof_contains_result n S p q x"
    proof (unfold prof_contains_result_def, clarify)
      fix x :: "'a"
      assume x_in_S: "x \<in> S"
      show
        "electoral_module n \<and>
         finite_profile S p \<and>
         finite_profile S q \<and>
         x \<in> S \<and>
         (x \<in> elect n S p \<longrightarrow> x \<in> elect n S q) \<and>
         (x \<in> reject n S p \<longrightarrow> x \<in> reject n S q) \<and>
         (x \<in> defer n S p \<longrightarrow> x \<in> defer n S q)"
      proof (safe)
        show "electoral_module n"
          using monotone_n
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S p"
          using f_profs
          by simp
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S q"
          using f_profs
          by simp
      next
        show "x \<in> S"
          using x_in_S
          by simp
      next
        assume "x \<in> elect n S p"
        thus "x \<in> elect n S q"
          using defer_n lifted_x monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      next
        assume "x \<in> reject n S p"
        thus "x \<in> reject n S q"
          using defer_n lifted_x monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      next
        assume "x \<in> defer n S p"
        thus "x \<in> defer n S q"
          using defer_n lifted_x monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      qed
    qed
    moreover have
      "\<forall> x \<in> A. mod_contains_result n (m \<parallel>\<^sub>\<up> n) S q x"
      using A compatible max_agg_rej3 f_profs
      unfolding disjoint_compatibility_def
      by metis
    ultimately have 00:
      "\<forall> x \<in> A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
      unfolding mod_contains_result_def prof_contains_result_def
      by simp
    have
      "\<forall> x \<in> S - A. mod_contains_result (m \<parallel>\<^sub>\<up> n) m S p x"
      using A max_agg_rej2 monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    moreover have "\<forall> x \<in> S. prof_contains_result m S p q x"
    proof (unfold prof_contains_result_def, clarify)
      fix x :: "'a"
      assume x_in_S: "x \<in> S"
      show
        "electoral_module m \<and>
         finite_profile S p \<and>
         finite_profile S q \<and>
         x \<in> S \<and>
         (x \<in> elect m S p \<longrightarrow> x \<in> elect m S q) \<and>
         (x \<in> reject m S p \<longrightarrow> x \<in> reject m S q) \<and>
         (x \<in> defer m S p \<longrightarrow> x \<in> defer m S q)"
      proof (safe)
        show "electoral_module m"
          using monotone_m
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S p"
          using f_profs
          by simp
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S q"
          using f_profs
          by simp
      next
        show "x \<in> S"
          using x_in_S
          by simp
      next
        assume "x \<in> elect m S p"
        thus "x \<in> elect m S q"
          using A a0 lifted_x lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "x \<in> reject m S p"
        thus "x \<in> reject m S q"
          using A a0 lifted_x lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "x \<in> defer m S p"
        thus "x \<in> defer m S q"
          using A a0 lifted_x lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      qed
    qed
    moreover have
      "\<forall> x \<in> S - A. mod_contains_result m (m \<parallel>\<^sub>\<up> n) S q x"
      using A max_agg_rej1 monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    ultimately have 01:
      "\<forall> x \<in> S - A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
      unfolding mod_contains_result_def prof_contains_result_def
      by simp
    from 00 01
    show ?thesis
      by blast
  next
    assume "x \<notin> A"
    hence a1: "x \<in> S - A"
      using DiffI lifted_x compatible f_profs
      unfolding Profile.lifted_def
      by (metis (no_types, lifting))
    hence "x \<in> reject n S p"
      using A f_profs
      by blast
    with defer_x
    have defer_m: "x \<in> defer m S p"
      using DiffD1 DiffD2 compatible dcompat_dec_by_one_mod f_profs
            defer_not_elec_or_rej max_agg_sound par_comp_sound
            disjoint_compatibility_def not_rej_imp_elec_or_def
            mod_contains_result_def
      unfolding maximum_parallel_composition.simps
      by metis
    have
      "\<forall> x \<in> A. mod_contains_result (m \<parallel>\<^sub>\<up> n) n S p x"
      using A compatible max_agg_rej4 f_profs
      unfolding disjoint_compatibility_def
      by metis
    moreover have "\<forall> x \<in> S. prof_contains_result n S p q x"
    proof (unfold prof_contains_result_def, clarify)
      fix x :: "'a"
      assume x_in_S: "x \<in> S"
      show
        "electoral_module n \<and>
         finite_profile S p \<and>
         finite_profile S q \<and>
         x \<in> S \<and>
         (x \<in> elect n S p \<longrightarrow> x \<in> elect n S q) \<and>
         (x \<in> reject n S p \<longrightarrow> x \<in> reject n S q) \<and>
         (x \<in> defer n S p \<longrightarrow> x \<in> defer n S q)"
      proof (safe)
        show "electoral_module n"
          using monotone_n
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S p"
          using f_profs
          by simp
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S q"
          using f_profs
          by simp
      next
        show "x \<in> S"
          using x_in_S
          by simp
      next
        assume "x \<in> elect n S p"
        thus "x \<in> elect n S q"
          using A a1 lifted_x lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "x \<in> reject n S p"
        thus "x \<in> reject n S q"
          using A a1 lifted_x lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "x \<in> defer n S p"
        thus "x \<in> defer n S q"
          using A a1 lifted_x lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      qed
  qed
  moreover have "\<forall> x \<in> A. mod_contains_result n (m \<parallel>\<^sub>\<up> n) S q x"
    using A compatible max_agg_rej3 f_profs
    unfolding disjoint_compatibility_def
    by metis
  ultimately have 10:
    "\<forall> x \<in> A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
    unfolding mod_contains_result_def prof_contains_result_def
    by simp
  have "\<forall> x \<in> S - A. mod_contains_result (m \<parallel>\<^sub>\<up> n) m S p x"
    using A max_agg_rej2 monotone_m monotone_n f_profs
    unfolding defer_lift_invariance_def
    by metis
  moreover have "\<forall> x \<in> S. prof_contains_result m S p q x"
  proof (unfold prof_contains_result_def, clarify)
    fix x :: "'a"
    assume x_in_S: "x \<in> S"
    show
      "electoral_module m \<and>
        finite_profile S p \<and>
        finite_profile S q \<and>
        x \<in> S \<and>
        (x \<in> elect m S p \<longrightarrow> x \<in> elect m S q) \<and>
        (x \<in> reject m S p \<longrightarrow> x \<in> reject m S q) \<and>
        (x \<in> defer m S p \<longrightarrow> x \<in> defer m S q)"
    proof (safe)
      show "electoral_module m"
        using monotone_m
        unfolding defer_lift_invariance_def
        by simp
    next
      show "finite S"
        using f_profs
        by simp
    next
      show "profile S p"
        using f_profs
        by simp
    next
      show "finite S"
        using f_profs
        by simp
    next
      show "profile S q"
        using f_profs
        by simp
    next
      show "x \<in> S"
        using x_in_S
        by simp
    next
      assume "x \<in> elect m S p"
      thus "x \<in> elect m S q"
        using defer_m lifted_x monotone_m
        unfolding defer_lift_invariance_def
        by metis
    next
      assume "x \<in> reject m S p"
      thus "x \<in> reject m S q"
        using defer_m lifted_x monotone_m
        unfolding defer_lift_invariance_def
        by metis
    next
      assume "x \<in> defer m S p"
      thus "x \<in> defer m S q"
        using defer_m lifted_x monotone_m
        unfolding defer_lift_invariance_def
        by metis
    qed
  qed
  moreover have
    "\<forall> x \<in> S - A. mod_contains_result m (m \<parallel>\<^sub>\<up> n) S q x"
    using A max_agg_rej1 monotone_m monotone_n f_profs
    unfolding defer_lift_invariance_def
    by metis
  ultimately have 11:
    "\<forall> x \<in> S - A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
    using electoral_mod_defer_elem
    unfolding mod_contains_result_def prof_contains_result_def
    by simp
  from 10 11
  show ?thesis
    by blast
  qed
  thus "(m \<parallel>\<^sub>\<up> n) S p = (m \<parallel>\<^sub>\<up> n) S q"
    using compatible f_profs eq_alts_in_profs_imp_eq_results
          max_par_comp_sound
    unfolding disjoint_compatibility_def
    by metis
qed

lemma par_comp_rej_card:
  assumes
    compatible: "disjoint_compatibility x y" and
    f_prof: "finite_profile S p" and
    reject_sum: "card (reject x S p) + card (reject y S p) = card S + n"
  shows "card (reject (x \<parallel>\<^sub>\<up> y) S p) = n"
proof -
  from compatible obtain A where A:
    "A \<subseteq> S \<and>
      (\<forall> a \<in> A. indep_of_alt x S a \<and>
          (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject x S p)) \<and>
      (\<forall> a \<in> S - A. indep_of_alt y S a \<and>
          (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject y S p))"
    using f_prof
    unfolding disjoint_compatibility_def
    by metis
  from f_prof compatible have reject_representation:
    "reject (x \<parallel>\<^sub>\<up> y) S p = (reject x S p) \<inter> (reject y S p)"
    using max_agg_rej_intersect
    unfolding disjoint_compatibility_def
    by metis
  have "electoral_module x \<and> electoral_module y"
    using compatible
    unfolding disjoint_compatibility_def
    by simp
  hence subsets: "(reject x S p) \<subseteq> S \<and> (reject y S p) \<subseteq> S"
    by (simp add: f_prof reject_in_alts)
  hence "finite (reject x S p) \<and> finite (reject y S p)"
    using rev_finite_subset f_prof
    by metis
  hence 0:
    "card (reject (x \<parallel>\<^sub>\<up> y) S p) =
        card S + n -
          card ((reject x S p) \<union> (reject y S p))"
    using card_Un_Int reject_representation reject_sum
    by fastforce
  have "\<forall> a \<in> S. a \<in> (reject x S p) \<or> a \<in> (reject y S p)"
    using A f_prof
    by blast
  hence "S = reject x S p \<union> reject y S p"
    using subsets
    by force
  hence 1: "card ((reject x S p) \<union> (reject y S p)) = card S"
    by presburger
  from 0 1
  show "card (reject (x \<parallel>\<^sub>\<up> y) S p) = n"
    by simp
qed

text \<open>
  Using the max-aggregator for composing two compatible modules in parallel,
  whereof the first one is non-electing and defers exactly one alternative,
  and the second one rejects exactly two alternatives, the composition
  results in an electoral module that eliminates exactly one alternative.
\<close>

theorem par_comp_elim_one[simp]:
  assumes
    defers_m_1: "defers 1 m" and
    non_elec_m: "non_electing m" and
    rejec_n_2: "rejects 2 n" and
    disj_comp: "disjoint_compatibility m n"
  shows "eliminates 1 (m \<parallel>\<^sub>\<up> n)"
proof (unfold eliminates_def, safe)
  have electoral_mod_m: "electoral_module m"
    using non_elec_m
    unfolding non_electing_def
    by simp
  have electoral_mod_n: "electoral_module n"
    using rejec_n_2
    unfolding rejects_def
    by simp
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    min_2_card: "1 < card A" and
    fin_A: "finite A" and
    prof_A: "profile A p"
  have card_geq_1: "card A \<ge> 1"
    using min_2_card dual_order.strict_trans2 less_imp_le_nat
    by blast
  have module: "electoral_module m"
    using non_elec_m
    unfolding non_electing_def
    by simp
  have elec_card_0: "card (elect m A p) = 0"
    using fin_A prof_A non_elec_m card_eq_0_iff
    unfolding non_electing_def
    by simp
  moreover
  from card_geq_1 have def_card_1:
    "card (defer m A p) = 1"
    using defers_m_1 module fin_A prof_A
    unfolding defers_def
    by simp
  ultimately have card_reject_m:
    "card (reject m A p) = card A - 1"
  proof -
    have "finite A"
      using fin_A
      by simp
    moreover have
      "well_formed A
        (elect m A p, reject m A p, defer m A p)"
      using fin_A prof_A module
      unfolding electoral_module_def
      by simp
    ultimately have
      "card A =
        card (elect m A p) + card (reject m A p) +
          card (defer m A p)"
      using result_count
      by blast
    thus ?thesis
      using def_card_1 elec_card_0
      by simp
  qed
  have case1: "card A \<ge> 2"
    using min_2_card
    by simp
  from case1
  have card_reject_n: "card (reject n A p) = 2"
    using fin_A prof_A rejec_n_2
    unfolding rejects_def
    by blast
  from card_reject_m card_reject_n
  have "card (reject m A p) + card (reject n A p) = card A + 1"
    using card_geq_1
    by linarith
  with disj_comp prof_A fin_A card_reject_m card_reject_n
  show "card (reject (m \<parallel>\<^sub>\<up> n) A p) = 1"
    using par_comp_rej_card
    by blast
qed

end

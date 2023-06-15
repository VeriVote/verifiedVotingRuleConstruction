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
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n"
  shows "electoral_module (m \<parallel>\<^sub>\<up> n)"
  using mod_m mod_n
  by simp

subsection \<open>Lemmas\<close>

lemma max_agg_eq_result:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    in_A: "a \<in> A"
  shows
    "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p a \<or>
      mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p a"
proof (cases)
  assume a_elect: "a \<in> elect (m \<parallel>\<^sub>\<up> n) A p"
    have mod_contains_inst:
      "\<forall> p_mod q_mod a_set prof b.
        mod_contains_result p_mod q_mod a_set prof (b::'a) =
          (electoral_module p_mod \<and> electoral_module q_mod \<and>
            finite a_set \<and> profile a_set prof \<and> b \<in> a_set \<and>
            (b \<notin> elect p_mod a_set prof \<or> b \<in> elect q_mod a_set prof) \<and>
            (b \<notin> reject p_mod a_set prof \<or> b \<in> reject q_mod a_set prof) \<and>
            (b \<notin> defer p_mod a_set prof \<or> b \<in> defer q_mod a_set prof))"
      unfolding mod_contains_result_def
      by simp
    have module_mn: "electoral_module (m \<parallel>\<^sub>\<up> n)"
      using module_m module_n
      by simp
  have not_defer_mn: "a \<notin> defer (m \<parallel>\<^sub>\<up> n) A p"
    using module_mn IntI a_elect empty_iff f_prof result_disj
    by (metis (no_types))
  have not_reject_mn: "a \<notin> reject (m \<parallel>\<^sub>\<up> n) A p"
    using module_mn IntI a_elect empty_iff f_prof result_disj
    by (metis (no_types))
  from a_elect
  have "let (e1, r1, d1) = m A p;
           (e2, r2, d2) = n A p in
         a \<in> e1 \<union> e2"
    by auto
  hence union_mn: "a \<in> (elect m A p) \<union> (elect n A p)"
    by auto
  thus ?thesis
    using f_prof in_A module_m module_mn module_n
          not_defer_mn not_reject_mn union_mn
          mod_contains_inst
      by blast
next
  assume not_a_elect: "a \<notin> elect (m \<parallel>\<^sub>\<up> n) A p"
  thus ?thesis
  proof (cases)
    assume a_in_def: "a \<in> defer (m \<parallel>\<^sub>\<up> n) A p"
    thus ?thesis
    proof (safe)
      assume not_mod_cont_mn:
        "\<not> mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p a"
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
        "\<forall> (b::'a) A B. (b \<in> A \<inter> B) = (b \<in> A \<and> b \<in> B)"
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
      have a_not_elect:
        "a \<notin> elect (m \<parallel>\<^sub>max_aggregator n) A p"
        using result_disj_max a_in_def
        by force
      have result_m:
        "(elect m A p, reject m A p, defer m A p) = m A p"
        by auto
      have result_n:
        "(elect n A p, reject n A p, defer n A p) = n A p"
        by auto
      have max_pq:
        "\<forall> (B::'a set) p q.
          elect_r (max_aggregator B p q) = elect_r p \<union> elect_r q"
        by force
      have
        "a \<notin> elect (m \<parallel>\<^sub>max_aggregator n) A p"
        using a_not_elect
        by blast
      with max_pq
      have "a \<notin> elect m A p \<union> elect n A p"
        by (simp add: max_pq)
      hence b_not_elect_mn:
        "a \<notin> elect m A p \<and> a \<notin> elect n A p"
        by blast
      have b_not_mpar_rej:
        "a \<notin> reject (m \<parallel>\<^sub>max_aggregator n) A p"
        using result_disj_max a_in_def
        by fastforce
      hence b_not_par_rej:
        "a \<notin> reject (m \<parallel>\<^sub>\<up> n) A p"
        by auto
      have mod_cont_res_fg:
        "\<forall> f g B prof (b::'a).
          mod_contains_result f g B prof b =
            (electoral_module f \<and> electoral_module g \<and>
              finite B \<and> profile B prof \<and> b \<in> B \<and>
                (b \<notin> elect f B prof \<or> b \<in> elect g B prof) \<and>
                (b \<notin> reject f B prof \<or> b \<in> reject g B prof) \<and>
                (b \<notin> defer f B prof \<or> b \<in> defer g B prof))"
        by (simp add: mod_contains_result_def)
      have max_agg_res:
        "max_aggregator A (elect m A p, reject m A p, defer m A p)
          (elect n A p, reject n A p, defer n A p) = (m \<parallel>\<^sub>max_aggregator n) A p"
        by simp
      have well_f_max:
        "\<forall> r2 r1 e2 e1 d2 d1 B.
          well_formed B (e1, r1, d1) \<and> well_formed B (e2, r2, d2) \<longrightarrow>
            reject_r (max_aggregator B (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
        using max_agg_rej_set
        by metis
      have e_mod_disj:
        "\<forall> f (B::'a set) prof.
          (electoral_module f \<and> finite (B::'a set) \<and> profile B prof) \<longrightarrow>
            elect f B prof \<union> reject f B prof \<union> defer f B prof = B"
        using result_presv_alts
        by blast
      hence e_mod_disj_n:
        "elect n A p \<union> reject n A p \<union> defer n A p = A"
        using f_prof module_n
        by metis
      have
        "\<forall> f g B prof (b::'a).
          mod_contains_result f g B prof b =
            (electoral_module f \<and> electoral_module g \<and>
              finite B \<and> profile B prof \<and> b \<in> B \<and>
              (b \<notin> elect f B prof \<or> b \<in> elect g B prof) \<and>
              (b \<notin> reject f B prof \<or> b \<in> reject g B prof) \<and>
              (b \<notin> defer f B prof \<or> b \<in> defer g B prof))"
        by (simp add: mod_contains_result_def)
      with e_mod_disj_n
      have "a \<in> reject n A p"
        using e_mod_par f_prof in_A module_n not_mod_cont_mn
              a_not_elect b_not_elect_mn b_not_mpar_rej
        by auto
      hence "a \<notin> reject m A p"
        using well_f_max max_agg_res result_m result_n
              set_intersect wf_m wf_n b_not_mpar_rej
        by (metis (no_types))
      with max_agg_res
      have "a \<notin> defer (m \<parallel>\<^sub>\<up> n) A p \<or> a \<in> defer m A p"
          using e_mod_disj f_prof in_A module_m b_not_elect_mn
          by blast
      with b_not_mpar_rej
      show "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p a"
        using mod_cont_res_fg b_not_par_rej e_mod_par f_prof
              in_A module_m a_not_elect
        by auto
    qed
  next
    assume not_a_defer: "a \<notin> defer (m \<parallel>\<^sub>\<up> n) A p"
    have el_rej_defer:
      "(elect m A p, reject m A p, defer m A p) = m A p"
      by auto
    from not_a_elect not_a_defer
    have a_reject: "a \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
      using electoral_mod_defer_elem in_A module_m module_n
            f_prof max_par_comp_sound
      by metis
    hence
      "case snd (m A p) of (Aa, Ab) \<Rightarrow>
        case n A p of (Ac, Ad, Ae) \<Rightarrow>
          a \<in> reject_r (max_aggregator A (elect m A p, Aa, Ab) (Ac, Ad, Ae))"
      using el_rej_defer
      by force
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        a \<in> reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2))"
      by (simp add: case_prod_unfold)
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        a \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    hence "a \<notin> elect m A p \<union> (defer n A p \<union> defer m A p)"
      by force
    thus ?thesis
      using mod_contains_result_comm mod_contains_result_def Un_iff
            a_reject f_prof in_A module_m module_n max_par_comp_sound
      by (metis (no_types))
  qed
qed

lemma max_agg_rej_iff_both_reject:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n"
  shows
    "(a \<in> reject (m \<parallel>\<^sub>\<up> n) A p) =
      (a \<in> reject m A p \<and> a \<in> reject n A p)"
proof
  assume rej_a: "a \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
  hence
    "case n A p of (Aa, Ab, Ac) \<Rightarrow>
      a \<in> reject_r (max_aggregator A
        (elect m A p, reject m A p, defer m A p) (Aa, Ab, Ac))"
    by auto
  hence
    "case snd (m A p) of (Aa, Ab) \<Rightarrow>
      case n A p of (Ac, Ad, Ae) \<Rightarrow>
        a \<in> reject_r (max_aggregator A
          (elect m A p, Aa, Ab) (Ac, Ad, Ae))"
    by force
  with rej_a have
    "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
      a \<in> reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2))"
    by (simp add: prod.case_eq_if)
  hence
    "let (e1, r1, d1) = m A p;
        (e2, r2, d2) = n A p in
      a \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
    by simp
  hence
    "a \<in> A - (elect m A p \<union> elect n A p \<union> defer m A p \<union> defer n A p)"
    by auto
  thus "a \<in> reject m A p \<and> a \<in> reject n A p"
    using Diff_iff Un_iff electoral_mod_defer_elem
          f_prof module_m module_n
    by metis
next
  assume a: "a \<in> reject m A p \<and> a \<in> reject n A p"
  hence
    "a \<notin> elect m A p \<and> a \<notin> defer m A p \<and>
      a \<notin> elect n A p \<and> a \<notin> defer n A p"
    using IntI empty_iff module_m module_n f_prof result_disj
    by metis
  thus "a \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
    using DiffD1 a f_prof max_agg_eq_result module_m module_n
          mod_contains_result_comm mod_contains_result_def
          reject_not_elec_or_def
      by (metis (no_types))
qed

lemma max_agg_rej_1:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "a \<in> reject n A p"
  shows "mod_contains_result m (m \<parallel>\<^sub>\<up> n) A p a"
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
  show "a \<in> A"
    using f_prof module_n reject_in_alts rejected
    by auto
next
  assume a_in_elect: "a \<in> elect m A p"
  hence a_not_reject: "a \<notin> reject m A p"
    using disjoint_iff_not_equal f_prof module_m result_disj
    by metis
  have rej_in_A: "reject n A p \<subseteq> A"
    using f_prof module_n
    by (simp add: reject_in_alts)
  have a_in_A: "a \<in> A"
    using rej_in_A in_mono rejected
    by metis
  with a_in_elect a_not_reject
  show "a \<in> elect (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_eq_result module_m module_n rejected
          max_agg_rej_iff_both_reject mod_contains_result_comm
          mod_contains_result_def
      by metis
next
  assume "a \<in> reject m A p"
  hence "a \<in> reject m A p \<and> a \<in> reject n A p"
    using rejected
    by simp
  thus "a \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_rej_iff_both_reject module_m module_n
    by (metis (no_types))
next
  assume a_in_defer: "a \<in> defer m A p"
  hence defer_a:
    "\<exists> b. b \<in> defer m A p \<and> b = a"
    by simp
  then obtain a_inst :: 'a where
    inst_a: "a = a_inst \<and> a_inst \<in> defer m A p"
    by metis
  hence a_not_rej: "a \<notin> reject m A p"
    using disjoint_iff_not_equal f_prof inst_a module_m result_disj
    by (metis (no_types))
  have
    "\<forall> f A prof.
      (electoral_module f \<and> finite (A::'a set) \<and> profile A prof) \<longrightarrow>
        elect f A prof \<union> reject f A prof \<union> defer f A prof = A"
    using result_presv_alts
    by metis
  with a_in_defer
  have "a \<in> A"
    using f_prof module_m
    by blast
  with inst_a a_not_rej
  show "a \<in> defer (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_eq_result max_agg_rej_iff_both_reject
          mod_contains_result_comm mod_contains_result_def
          module_m module_n rejected
    by metis
qed

lemma max_agg_rej_2:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "a \<in> reject n A p"
  shows "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p a"
  using mod_contains_result_comm max_agg_rej_1
        module_m module_n f_prof rejected
  by metis

lemma max_agg_rej_3:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    f_prof:  "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "a \<in> reject m A p"
  shows "mod_contains_result n (m \<parallel>\<^sub>\<up> n) A p a"
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
  show "a \<in> A"
    using f_prof in_mono module_m reject_in_alts rejected
    by (metis (no_types))
next
  assume "a \<in> elect n A p"
  thus "a \<in> elect (m \<parallel>\<^sub>\<up> n) A p"
    using Un_iff combine_ele_rej_def fst_conv
          maximum_parallel_composition.simps
          max_aggregator.simps
    unfolding parallel_composition.simps
    by (metis (mono_tags, lifting))
next
  assume "a \<in> reject n A p"
  thus "a \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
    using f_prof max_agg_rej_iff_both_reject module_m module_n rejected
    by metis
next
  assume a_in_def: "a \<in> defer n A p"
  have "a \<in> A"
    using f_prof max_agg_rej_1 mod_contains_result_def module_m rejected
    by metis
  thus "a \<in> defer (m \<parallel>\<^sub>\<up> n) A p"
    using a_in_def disjoint_iff_not_equal f_prof
          max_agg_eq_result max_agg_rej_iff_both_reject
          mod_contains_result_comm mod_contains_result_def
          module_m module_n rejected result_disj
      by metis
qed

lemma max_agg_rej_4:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "a \<in> reject m A p"
  shows "mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p a"
  using mod_contains_result_comm max_agg_rej_3
        module_m module_n f_prof rejected
  by metis

lemma max_agg_rej_intersect:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
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
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    a :: "'a"
  assumes
    compatible: "disjoint_compatibility m n" and
    in_A: "a \<in> A"
  shows
    "(\<forall> p. finite_profile A p \<longrightarrow>
          mod_contains_result m (m \<parallel>\<^sub>\<up> n) A p a) \<or>
        (\<forall> p. finite_profile A p \<longrightarrow>
          mod_contains_result n (m \<parallel>\<^sub>\<up> n) A p a)"
  using DiffI compatible in_A max_agg_rej_1 max_agg_rej_3
  unfolding disjoint_compatibility_def
  by metis

subsection \<open>Composition Rules\<close>

text \<open>
  Using a conservative aggregator, the parallel composition
  preserves the property non-electing.
\<close>

theorem conserv_max_agg_presv_non_electing[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
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
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
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
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume
    defer_a: "a \<in> defer (m \<parallel>\<^sub>\<up> n) A p" and
    lifted_a: "Profile.lifted A p q a"
  hence f_profs: "finite_profile A p \<and> finite_profile A q"
    unfolding lifted_def
    by simp
  from compatible
  obtain B :: "'a set" where
    alts: "B \<subseteq> A \<and> (\<forall> x \<in> B. indep_of_alt m A x \<and>
            (\<forall> p. finite_profile A p \<longrightarrow> x \<in> reject m A p)) \<and>
              (\<forall> x \<in> A - B. indep_of_alt n A x \<and>
            (\<forall> p. finite_profile A p \<longrightarrow> x \<in> reject n A p))"
    using f_profs
    unfolding disjoint_compatibility_def
    by (metis (no_types, lifting))
  have "\<forall> x \<in> A. prof_contains_result (m \<parallel>\<^sub>\<up> n) A p q x"
  proof (cases)
    assume a0: "a \<in> B"
    hence "a \<in> reject m A p"
      using alts f_profs
      by blast
    with defer_a
    have defer_n: "a \<in> defer n A p"
      using compatible f_profs max_agg_rej_4
      unfolding disjoint_compatibility_def mod_contains_result_def
      by metis
    have "\<forall> x \<in> B. mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p x"
      using alts compatible max_agg_rej_4 f_profs
      unfolding disjoint_compatibility_def
      by metis
    moreover have "\<forall> x \<in> A. prof_contains_result n A p q x"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show
        "electoral_module n \<and>
         finite_profile A p \<and>
         finite_profile A q \<and>
         b \<in> A \<and>
         (b \<in> elect n A p \<longrightarrow> b \<in> elect n A q) \<and>
         (b \<in> reject n A p \<longrightarrow> b \<in> reject n A q) \<and>
         (b \<in> defer n A p \<longrightarrow> b \<in> defer n A q)"
      proof (safe)
        show "electoral_module n"
          using monotone_n
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "profile A p"
          using f_profs
          by simp
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "profile A q"
          using f_profs
          by simp
      next
        show "b \<in> A"
          using b_in_A
          by simp
      next
        assume "b \<in> elect n A p"
        thus "b \<in> elect n A q"
          using defer_n lifted_a monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      next
        assume "b \<in> reject n A p"
        thus "b \<in> reject n A q"
          using defer_n lifted_a monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      next
        assume "b \<in> defer n A p"
        thus "b \<in> defer n A q"
          using defer_n lifted_a monotone_n f_profs
          unfolding defer_lift_invariance_def
          by metis
      qed
    qed
    moreover have
      "\<forall> x \<in> B. mod_contains_result n (m \<parallel>\<^sub>\<up> n) A q x"
      using alts compatible max_agg_rej_3 f_profs
      unfolding disjoint_compatibility_def
      by metis
    ultimately have 00:
      "\<forall> x \<in> B. prof_contains_result (m \<parallel>\<^sub>\<up> n) A p q x"
      unfolding mod_contains_result_def prof_contains_result_def
      by simp
    have
      "\<forall> x \<in> A - B. mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p x"
      using alts max_agg_rej_2 monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    moreover have "\<forall> x \<in> A. prof_contains_result m A p q x"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show
        "electoral_module m \<and>
         finite_profile A p \<and>
         finite_profile A q \<and>
         b \<in> A \<and>
         (b \<in> elect m A p \<longrightarrow> b \<in> elect m A q) \<and>
         (b \<in> reject m A p \<longrightarrow> b \<in> reject m A q) \<and>
         (b \<in> defer m A p \<longrightarrow> b \<in> defer m A q)"
      proof (safe)
        show "electoral_module m"
          using monotone_m
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "profile A p"
          using f_profs
          by simp
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "profile A q"
          using f_profs
          by simp
      next
        show "b \<in> A"
          using b_in_A
          by simp
      next
        assume "b \<in> elect m A p"
        thus "b \<in> elect m A q"
          using alts a0 lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "b \<in> reject m A p"
        thus "b \<in> reject m A q"
          using alts a0 lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "b \<in> defer m A p"
        thus "b \<in> defer m A q"
          using alts a0 lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      qed
    qed
    moreover have
      "\<forall> x \<in> A - B. mod_contains_result m (m \<parallel>\<^sub>\<up> n) A q x"
      using alts max_agg_rej_1 monotone_m monotone_n f_profs
      unfolding defer_lift_invariance_def
      by metis
    ultimately have 01:
      "\<forall> x \<in> A - B. prof_contains_result (m \<parallel>\<^sub>\<up> n) A p q x"
      unfolding mod_contains_result_def prof_contains_result_def
      by simp
    from 00 01
    show ?thesis
      by blast
  next
    assume "a \<notin> B"
    hence a_in_set_diff: "a \<in> A - B"
      using DiffI lifted_a compatible f_profs
      unfolding Profile.lifted_def
      by (metis (no_types, lifting))
    hence "a \<in> reject n A p"
      using alts f_profs
      by blast
    with defer_a
    have defer_m: "a \<in> defer m A p"
      using DiffD1 DiffD2 compatible dcompat_dec_by_one_mod f_profs
            defer_not_elec_or_rej max_agg_sound par_comp_sound
            disjoint_compatibility_def not_rej_imp_elec_or_def
            mod_contains_result_def
      unfolding maximum_parallel_composition.simps
      by metis
    have
      "\<forall> x \<in> B. mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p x"
      using alts compatible max_agg_rej_4 f_profs
      unfolding disjoint_compatibility_def
      by metis
    moreover have "\<forall> x \<in> A. prof_contains_result n A p q x"
    proof (unfold prof_contains_result_def, clarify)
      fix b :: "'a"
      assume b_in_A: "b \<in> A"
      show
        "electoral_module n \<and>
         finite_profile A p \<and>
         finite_profile A q \<and>
         b \<in> A \<and>
         (b \<in> elect n A p \<longrightarrow> b \<in> elect n A q) \<and>
         (b \<in> reject n A p \<longrightarrow> b \<in> reject n A q) \<and>
         (b \<in> defer n A p \<longrightarrow> b \<in> defer n A q)"
      proof (safe)
        show "electoral_module n"
          using monotone_n
          unfolding defer_lift_invariance_def
          by metis
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "profile A p"
          using f_profs
          by simp
      next
        show "finite A"
          using f_profs
          by simp
      next
        show "profile A q"
          using f_profs
          by simp
      next
        show "b \<in> A"
          using b_in_A
          by simp
      next
        assume "b \<in> elect n A p"
        thus "b \<in> elect n A q"
          using alts a_in_set_diff lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "b \<in> reject n A p"
        thus "b \<in> reject n A q"
          using alts a_in_set_diff lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      next
        assume "b \<in> defer n A p"
        thus "b \<in> defer n A q"
          using alts a_in_set_diff lifted_a lifted_imp_equiv_prof_except_a
          unfolding indep_of_alt_def
          by metis
      qed
  qed
  moreover have "\<forall> x \<in> B. mod_contains_result n (m \<parallel>\<^sub>\<up> n) A q x"
    using alts compatible max_agg_rej_3 f_profs
    unfolding disjoint_compatibility_def
    by metis
  ultimately have 10:
    "\<forall> x \<in> B. prof_contains_result (m \<parallel>\<^sub>\<up> n) A p q x"
    unfolding mod_contains_result_def prof_contains_result_def
    by simp
  have "\<forall> x \<in> A - B. mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p x"
    using alts max_agg_rej_2 monotone_m monotone_n f_profs
    unfolding defer_lift_invariance_def
    by metis
  moreover have "\<forall> x \<in> A. prof_contains_result m A p q x"
  proof (unfold prof_contains_result_def, clarify)
    fix b :: "'a"
    assume b_in_A: "b \<in> A"
    show
      "electoral_module m \<and>
        finite_profile A p \<and>
        finite_profile A q \<and>
        b \<in> A \<and>
        (b \<in> elect m A p \<longrightarrow> b \<in> elect m A q) \<and>
        (b \<in> reject m A p \<longrightarrow> b \<in> reject m A q) \<and>
        (b \<in> defer m A p \<longrightarrow> b \<in> defer m A q)"
    proof (safe)
      show "electoral_module m"
        using monotone_m
        unfolding defer_lift_invariance_def
        by simp
    next
      show "finite A"
        using f_profs
        by simp
    next
      show "profile A p"
        using f_profs
        by simp
    next
      show "finite A"
        using f_profs
        by simp
    next
      show "profile A q"
        using f_profs
        by simp
    next
      show "b \<in> A"
        using b_in_A
        by simp
    next
      assume "b \<in> elect m A p"
      thus "b \<in> elect m A q"
        using defer_m lifted_a monotone_m
        unfolding defer_lift_invariance_def
        by metis
    next
      assume "b \<in> reject m A p"
      thus "b \<in> reject m A q"
        using defer_m lifted_a monotone_m
        unfolding defer_lift_invariance_def
        by metis
    next
      assume "b \<in> defer m A p"
      thus "b \<in> defer m A q"
        using defer_m lifted_a monotone_m
        unfolding defer_lift_invariance_def
        by metis
    qed
  qed
  moreover have
    "\<forall> x \<in> A - B. mod_contains_result m (m \<parallel>\<^sub>\<up> n) A q x"
    using alts max_agg_rej_1 monotone_m monotone_n f_profs
    unfolding defer_lift_invariance_def
    by metis
  ultimately have 11:
    "\<forall> x \<in> A - B. prof_contains_result (m \<parallel>\<^sub>\<up> n) A p q x"
    using electoral_mod_defer_elem
    unfolding mod_contains_result_def prof_contains_result_def
    by simp
  from 10 11
  show ?thesis
    by blast
  qed
  thus "(m \<parallel>\<^sub>\<up> n) A p = (m \<parallel>\<^sub>\<up> n) A q"
    using compatible f_profs eq_alts_in_profs_imp_eq_results
          max_par_comp_sound
    unfolding disjoint_compatibility_def
    by metis
qed

lemma par_comp_rej_card:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    c :: nat
  assumes
    compatible: "disjoint_compatibility m n" and
    f_prof: "finite_profile A p" and
    reject_sum: "card (reject m A p) + card (reject n A p) = card A + c"
  shows "card (reject (m \<parallel>\<^sub>\<up> n) A p) = c"
proof -
  from compatible
  obtain B where
    alt_set: "B \<subseteq> A \<and>
         (\<forall> a \<in> B. indep_of_alt m A a \<and>
             (\<forall> q. finite_profile A q \<longrightarrow> a \<in> reject m A q)) \<and>
         (\<forall> a \<in> A - B. indep_of_alt n A a \<and>
             (\<forall> q. finite_profile A q \<longrightarrow> a \<in> reject n A q))"
    using f_prof
    unfolding disjoint_compatibility_def
    by metis
  from f_prof compatible
  have reject_representation:
    "reject (m \<parallel>\<^sub>\<up> n) A p = (reject m A p) \<inter> (reject n A p)"
    using max_agg_rej_intersect
    unfolding disjoint_compatibility_def
    by metis
  have "electoral_module m \<and> electoral_module n"
    using compatible
    unfolding disjoint_compatibility_def
    by simp
  hence subsets: "(reject m A p) \<subseteq> A \<and> (reject n A p) \<subseteq> A"
    by (simp add: f_prof reject_in_alts)
  hence "finite (reject m A p) \<and> finite (reject n A p)"
    using rev_finite_subset f_prof
    by metis
  hence 0:
    "card (reject (m \<parallel>\<^sub>\<up> n) A p) =
        card A + c -
          card ((reject m A p) \<union> (reject n A p))"
    using card_Un_Int reject_representation reject_sum
    by fastforce
  have "\<forall> a \<in> A. a \<in> (reject m A p) \<or> a \<in> (reject n A p)"
    using alt_set f_prof
    by blast
  hence "A = reject m A p \<union> reject n A p"
    using subsets
    by force
  hence 1: "card ((reject m A p) \<union> (reject n A p)) = card A"
    by presburger
  from 0 1
  show "card (reject (m \<parallel>\<^sub>\<up> n) A p) = c"
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
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes
    defers_m_one: "defers 1 m" and
    non_elec_m: "non_electing m" and
    rejec_n_two: "rejects 2 n" and
    disj_comp: "disjoint_compatibility m n"
  shows "eliminates 1 (m \<parallel>\<^sub>\<up> n)"
proof (unfold eliminates_def, safe)
  have electoral_mod_m: "electoral_module m"
    using non_elec_m
    unfolding non_electing_def
    by simp
  have electoral_mod_n: "electoral_module n"
    using rejec_n_two
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
    min_card_two: "1 < card A" and
    fin_A: "finite A" and
    prof_A: "profile A p"
  have card_geq_one: "card A \<ge> 1"
    using min_card_two dual_order.strict_trans2 less_imp_le_nat
    by blast
  have module: "electoral_module m"
    using non_elec_m
    unfolding non_electing_def
    by simp
  have elec_card_zero: "card (elect m A p) = 0"
    using fin_A prof_A non_elec_m card_eq_0_iff
    unfolding non_electing_def
    by simp
  moreover from card_geq_one
  have def_card_one: "card (defer m A p) = 1"
    using defers_m_one module fin_A prof_A
    unfolding defers_def
    by simp
  ultimately have card_reject_m:
    "card (reject m A p) = card A - 1"
  proof -
    have "finite A"
      using fin_A
      by simp
    moreover have "well_formed A (elect m A p, reject m A p, defer m A p)"
      using fin_A prof_A module
      unfolding electoral_module_def
      by simp
    ultimately have
      "card A = card (elect m A p) + card (reject m A p) + card (defer m A p)"
      using result_count
      by blast
    thus ?thesis
      using def_card_one elec_card_zero
      by simp
  qed
  have case_1: "card A \<ge> 2"
    using min_card_two
    by simp
  from case_1
  have card_reject_n: "card (reject n A p) = 2"
    using fin_A prof_A rejec_n_two
    unfolding rejects_def
    by blast
  from card_reject_m card_reject_n
  have "card (reject m A p) + card (reject n A p) = card A + 1"
    using card_geq_one
    by linarith
  with disj_comp prof_A fin_A card_reject_m card_reject_n
  show "card (reject (m \<parallel>\<^sub>\<up> n) A p) = 1"
    using par_comp_rej_card
    by blast
qed

end

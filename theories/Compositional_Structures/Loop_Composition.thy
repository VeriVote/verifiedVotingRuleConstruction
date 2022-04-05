(*  File:       Loop_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Loop Composition\<close>

theory Loop_Composition
  imports "Basic_Modules/Component_Types/Termination_Condition"
          "Basic_Modules/Defer_Module"
          Sequential_Composition
begin

text \<open>
  The loop composition uses the same module in sequence,
  combined with a termination condition, until either
  (1) the termination condition is met or
  (2) no new decisions are made (i.e., a fixed point is reached).
\<close>

subsection \<open>Definition\<close>

lemma loop_termination_helper:
  assumes
    not_term: "\<not>t (acc A p)" and
    subset: "defer (acc \<triangleright> m) A p \<subset> defer acc A p" and
    not_inf: "\<not>infinite (defer acc A p)"
  shows
    "((acc \<triangleright> m, m, t, A, p), (acc, m, t, A, p)) \<in>
        measure (\<lambda>(acc, m, t, A, p). card (defer acc A p))"
  using assms psubset_card_mono
  by simp

text \<open>
  This function handles the accumulator for the following loop composition
  function.
\<close>

function loop_comp_helper ::
    "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Termination_Condition \<Rightarrow> 'a Electoral_Module" where
  "t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
    infinite (defer acc A p) \<Longrightarrow>
      loop_comp_helper acc m t A p = acc A p" |
  "\<not>(t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
    infinite (defer acc A p)) \<Longrightarrow>
      loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
proof -
  fix
    P :: bool and
    x :: "('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
          ('a Termination_Condition) \<times> 'a set \<times> 'a Profile"
  assume
    a1: "\<And> t acc A p m.
          \<lbrakk>t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
              infinite (defer acc A p);
            x = (acc, m, t, A, p)\<rbrakk> \<Longrightarrow> P" and
    a2: "\<And> t acc A p m.
          \<lbrakk>\<not> (t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
              infinite (defer acc A p));
            x = (acc, m, t, A, p)\<rbrakk> \<Longrightarrow> P"
  have "\<exists> f A p p2 g. (g, f, p, A, p2) = x"
    using prod_cases5
    by metis
  thus P
    using a2 a1
    by (metis (no_types))
next
  show
    "\<And> t acc A p m ta acca Aa pa ma.
       t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
        infinite (defer acc A p) \<Longrightarrow>
          ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
          infinite (defer acca Aa pa) \<Longrightarrow>
           (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
              acc A p = acca Aa pa"
    by fastforce
next
  show
    "\<And> t acc A p m ta acca Aa pa ma.
       t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
        infinite (defer acc A p) \<Longrightarrow>
          \<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
          infinite (defer acca Aa pa)) \<Longrightarrow>
           (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
              acc A p = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
  proof -
    fix
      t :: "'a Termination_Condition" and
      acc :: "'a Electoral_Module" and
      A :: "'a set" and
      p :: "'a Profile" and
      m :: "'a Electoral_Module" and
      ta :: "'a Termination_Condition" and
      acca :: "'a Electoral_Module" and
      Aa :: "'a set" and
      pa :: "'a Profile" and
      ma :: "'a Electoral_Module"
    assume
      a1: "t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
            infinite (defer acc A p)" and
      a2: "\<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
            infinite (defer acca Aa pa))" and
      "(acc, m, t, A, p) = (acca, ma, ta, Aa, pa)"
    hence False
      using a2 a1
      by force
  thus "acc A p = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
    by auto
qed
next
  show
    "\<And> t acc A p m ta acca Aa pa ma.
       \<not> (t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
          infinite (defer acc A p)) \<Longrightarrow>
           \<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
            infinite (defer acca Aa pa)) \<Longrightarrow>
             (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
                loop_comp_helper_sumC (acc \<triangleright> m, m, t, A, p) =
                  loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
    by force
qed
termination
proof -
  have func_term:
    "\<exists> r. wf r \<and>
        (\<forall>p f (A::'a set) prof g.
          p (f A prof) \<or>
          \<not> defer (f \<triangleright> g) A prof \<subset> defer f A prof \<or>
          infinite (defer f A prof) \<or>
          ((f \<triangleright> g, g, p, A, prof), (f, g, p, A, prof)) \<in> r)"
    using loop_termination_helper wf_measure "termination"
    by (metis (no_types))
  hence
    "\<forall> r p.
      Ex ((\<lambda> ra. \<forall> f (A::'a set) prof pa g.
            \<exists> prof2 pb p_rel pc pd h (B::'a set) prof3 i pe.
        \<not> wf r \<or>
          loop_comp_helper_dom
            (p::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
              (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
          infinite (defer f A prof) \<or>
          pa (f A prof) \<and>
            wf
              (prof2::((
                ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
                ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times> _) set) \<and>
            \<not> loop_comp_helper_dom (pb::
                ('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
          wf p_rel \<and> \<not> defer (f \<triangleright> g) A prof \<subset> defer f A prof \<and>
            \<not> loop_comp_helper_dom
                (pc::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                  (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
            ((f \<triangleright> g, g, pa, A, prof), f, g, pa, A, prof) \<in> p_rel \<and> wf p_rel \<and>
            \<not> loop_comp_helper_dom
                (pd::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                  (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
            finite (defer h B prof3) \<and>
            defer (h \<triangleright> i) B prof3 \<subset> defer h B prof3 \<and>
            \<not> pe (h B prof3) \<and>
            ((h \<triangleright> i, i, pe, B, prof3), h, i, pe, B, prof3) \<notin> r)::
          ((('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
            ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times>
            ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
            ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) set \<Rightarrow> bool)"
    by metis
  obtain
    p_rel ::  "((('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
               ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times>
               ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
               ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) set" where
      "wf p_rel \<and>
        (\<forall> p f A prof g. p (f A prof) \<or>
          \<not> defer (f \<triangleright> g) A prof \<subset> defer f A prof \<or>
          infinite (defer f A prof) \<or>
          ((f \<triangleright> g, g, p, A, prof), f, g, p, A, prof) \<in> p_rel)"
    using func_term
    by presburger
  thus ?thesis
    using "termination"
    by metis
qed

lemma loop_comp_code_helper[code]:
  "loop_comp_helper acc m t A p =
    (if (t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
      infinite (defer acc A p))
    then (acc A p) else (loop_comp_helper (acc \<triangleright> m) m t A p))"
  by simp

function loop_composition ::
    "'a Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow>
        'a Electoral_Module" where
  "t ({}, {}, A) \<Longrightarrow>
    loop_composition m t A p = defer_module A p" |
  "\<not>(t ({}, {}, A)) \<Longrightarrow>
    loop_composition m t A p = (loop_comp_helper m m t) A p"
  by (fastforce, simp_all)
termination
  using "termination" wf_empty
  by blast

abbreviation loop ::
  "'a Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow> 'a Electoral_Module"
    ("_ \<circlearrowleft>\<^sub>_" 50) where
  "m \<circlearrowleft>\<^sub>t \<equiv> loop_composition m t"

lemma loop_comp_code[code]:
  "loop_composition m t A p =
    (if (t ({},{},A))
    then (defer_module A p) else (loop_comp_helper m m t) A p)"
  by simp

lemma loop_comp_helper_imp_partit:
  assumes
    module_m: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "electoral_module acc \<and> (n = card (defer acc A p)) \<Longrightarrow>
        well_formed A (loop_comp_helper acc m t A p)"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  have
    "\<forall> (f::'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) g.
      (electoral_module f \<and> electoral_module g) \<longrightarrow>
        electoral_module (f \<triangleright> g)"
    by auto
  hence "electoral_module (acc \<triangleright> m)"
    using less.prems module_m
    by metis
  hence wf_acc:
    "\<not> t (acc A p) \<and> \<not> t (acc A p) \<and>
      defer (acc \<triangleright> m) A p \<subset> defer acc A p \<and>
      finite (defer acc A p) \<longrightarrow>
        well_formed A (loop_comp_helper acc m t A p)"
    using less.hyps less.prems loop_comp_helper.simps(2)
          psubset_card_mono
  by metis
  have "well_formed A (acc A p)"
    using less.prems profile
    unfolding electoral_module_def
    by blast
  thus ?case
    using wf_acc loop_comp_helper.simps(1)
    by (metis (no_types))
qed

subsection \<open>Soundness\<close>

theorem loop_comp_sound:
  assumes "electoral_module m"
  shows "electoral_module (m \<circlearrowleft>\<^sub>t)"
  using def_mod_sound loop_composition.simps(1) loop_composition.simps(2)
        loop_comp_helper_imp_partit assms
  unfolding electoral_module_def
  by metis

lemma loop_comp_helper_imp_no_def_incr:
  assumes
    module_m: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "(electoral_module acc \<and> n = card (defer acc A p)) \<Longrightarrow>
        defer (loop_comp_helper acc m t) A p \<subseteq> defer acc A p"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  have emod_acc_m: "electoral_module (acc \<triangleright> m)"
    using less.prems module_m
    by simp
  have "\<forall> A A'. infinite (A::'a set) \<or> \<not> A' \<subset> A \<or> card A' < card A"
    using psubset_card_mono
    by metis
  hence
    "\<not> t (acc A p) \<and> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<and>
      finite (defer acc A p) \<longrightarrow>
        defer (loop_comp_helper (acc \<triangleright> m) m t) A p \<subseteq> defer acc A p"
    using emod_acc_m less.hyps less.prems
    by blast
  hence
    "\<not> t (acc A p) \<and> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<and>
        finite (defer acc A p) \<longrightarrow>
          defer (loop_comp_helper acc m t) A p \<subseteq> defer acc A p"
    using loop_comp_helper.simps(2)
    by (metis (no_types))
  thus ?case
    using eq_iff loop_comp_helper.simps(1)
    by (metis (no_types))
qed

subsection \<open>Lemmata\<close>

lemma loop_comp_helper_def_lift_inv_helper:
  assumes
    monotone_m: "defer_lift_invariance m" and
    f_prof: "finite_profile A p"
  shows
    "(defer_lift_invariance acc \<and> n = card (defer acc A p)) \<longrightarrow>
        (\<forall> q a.
          (a \<in> (defer (loop_comp_helper acc m t) A p) \<and>
            lifted A p q a) \<longrightarrow>
                (loop_comp_helper acc m t) A p =
                  (loop_comp_helper acc m t) A q)"
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have defer_card_comp:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall> q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc \<triangleright> m) A p) = card (defer (acc \<triangleright> m) A q))"
    using monotone_m def_lift_inv_seq_comp_help
    by metis
  have defer_card_acc:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall> q a. (a \<in> (defer (acc) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc) A p) = card (defer (acc) A q))"
    unfolding defer_lift_invariance_def
    by simp
  hence defer_card_acc_2:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall> q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc) A p) = card (defer (acc) A q))"
    using monotone_m f_prof seq_comp_def_set_trans
    unfolding defer_lift_invariance_def
    by metis
  thus ?case
  proof cases
    assume card_unchanged: "card (defer (acc \<triangleright> m) A p) = card (defer acc A p)"
    with defer_card_comp defer_card_acc monotone_m
    have
      "defer_lift_invariance (acc) \<longrightarrow>
          (\<forall> q a. (a \<in> (defer (acc) A p) \<and> lifted A p q a) \<longrightarrow>
              (loop_comp_helper acc m t) A q = acc A q)"
    proof (safe)
      fix
        q :: "'a Profile" and
        a :: "'a"
      assume
        def_card_eq:
        "card (defer (acc \<triangleright> m) A p) = card (defer acc A p)" and
        dli_acc: "defer_lift_invariance acc" and
        def_seq_lift_card:
        "\<forall> q a. a \<in> defer (acc \<triangleright> m) A p \<and> Profile.lifted A p q a \<longrightarrow>
          card (defer (acc \<triangleright> m) A p) = card (defer (acc \<triangleright> m) A q)" and
        a_in_def_acc: "a \<in> defer acc A p" and
        lifted_A: "Profile.lifted A p q a"
      have emod_m: "electoral_module m"
        using monotone_m
        unfolding defer_lift_invariance_def
        by simp
      have emod_acc: "electoral_module acc"
        using dli_acc
        unfolding defer_lift_invariance_def
        by simp
      have acc_eq_pq: "acc A q = acc A p"
        using a_in_def_acc dli_acc lifted_A
        unfolding defer_lift_invariance_def
        by (metis (full_types))
      with emod_acc emod_m
      have
        "finite (defer acc A p) \<longrightarrow>
          loop_comp_helper acc m t A q = acc A q"
        using a_in_def_acc def_card_eq def_seq_lift_card
              dual_order.strict_iff_order f_prof lifted_A
              loop_comp_code_helper psubset_card_mono
              seq_comp_def_set_bounded
        by (metis (no_types))
      thus "loop_comp_helper acc m t A q = acc A q"
        using acc_eq_pq loop_comp_code_helper
        by (metis (full_types))
    qed
    moreover from card_unchanged
    have "(loop_comp_helper acc m t) A p = acc A p"
      using loop_comp_helper.simps(1) order.strict_iff_order
            psubset_card_mono
      by metis
    ultimately have
      "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc) \<longrightarrow>
          (\<forall> q a. (a \<in> (defer (loop_comp_helper acc m t) A p) \<and>
              lifted A p q a) \<longrightarrow>
                  (loop_comp_helper acc m t) A p =
                    (loop_comp_helper acc m t) A q)"
      unfolding defer_lift_invariance_def
      by metis
    thus ?thesis
      using monotone_m seq_comp_presv_def_lift_inv
      by blast
  next
    assume card_changed:
      "\<not> (card (defer (acc \<triangleright> m) A p) = card (defer acc A p))"
    with f_prof seq_comp_def_card_bounded
    have card_smaller_for_p:
      "electoral_module (acc) \<longrightarrow>
          (card (defer (acc \<triangleright> m) A p) < card (defer acc A p))"
      using monotone_m order.not_eq_order_implies_strict
      unfolding defer_lift_invariance_def
      by (metis (full_types))
    with defer_card_acc_2 defer_card_comp
    have card_changed_for_q:
      "defer_lift_invariance (acc) \<longrightarrow>
          (\<forall> q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
              (card (defer (acc \<triangleright> m) A q) < card (defer acc A q)))"
      unfolding defer_lift_invariance_def
      by (metis (no_types, lifting))
    thus ?thesis
    proof cases
      assume t_not_satisfied_for_p: "\<not> t (acc A p)"
      hence t_not_satisfied_for_q:
        "defer_lift_invariance (acc) \<longrightarrow>
            (\<forall> q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                \<not> t (acc A q))"
        using monotone_m f_prof seq_comp_def_set_trans
        unfolding defer_lift_invariance_def
        by metis
      from card_changed defer_card_comp defer_card_acc
      have dli_card_def:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall> q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> Profile.lifted A p q a) \<longrightarrow>
                card (defer (acc \<triangleright> m) A q) \<noteq> (card (defer acc A q)))"
      proof -
        have
          "\<forall> f.
            (defer_lift_invariance f \<or>
              (\<exists> A prof prof2 (a::'a).
                f A prof \<noteq> f A prof2 \<and>
                  Profile.lifted A prof prof2 a \<and>
                  a \<in> defer f A prof) \<or> \<not> electoral_module f) \<and>
                  ((\<forall> A p1 p2 b. f A p1 = f A p2 \<or> \<not> Profile.lifted A p1 p2 b \<or>
                    b \<notin> defer f A p1) \<and>
                  electoral_module f \<or> \<not> defer_lift_invariance f)"
          unfolding defer_lift_invariance_def
          by blast
        thus ?thesis
          using card_changed monotone_m f_prof seq_comp_def_set_trans
          by (metis (no_types, opaque_lifting))
      qed
      hence dli_def_subset:
        "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc) \<longrightarrow>
            (\<forall> q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                defer (acc \<triangleright> m) A q \<subset> defer acc A q)"
      proof -
        {
          fix
            alt :: 'a and
            prof :: "'a Profile"
          have
            "(\<not> defer_lift_invariance (acc \<triangleright> m) \<or> \<not> defer_lift_invariance acc) \<or>
              (alt \<notin> defer (acc \<triangleright> m) A p \<or> \<not> lifted A p prof alt) \<or>
              defer (acc \<triangleright> m) A prof \<subset> defer acc A prof"
            using Profile.lifted_def dli_card_def defer_lift_invariance_def
                  monotone_m psubsetI seq_comp_def_set_bounded
            by (metis (no_types))
        }
        thus ?thesis
          by metis
      qed
      with t_not_satisfied_for_p
      have rec_step_q:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall> q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                loop_comp_helper acc m t A q =
                  loop_comp_helper (acc \<triangleright> m) m t A q)"
      proof (safe)
        fix
          q :: "'a Profile" and
          a :: "'a"
        assume
          a_in_def_impl_def_subset:
          "\<forall> q a. a \<in> defer (acc \<triangleright> m) A p \<and> lifted A p q a \<longrightarrow>
            defer (acc \<triangleright> m) A q \<subset> defer acc A q" and
          dli_acc: "defer_lift_invariance acc" and
          a_in_def_seq_acc_m: "a \<in> defer (acc \<triangleright> m) A p" and
          lifted_pq_a: "lifted A p q a"
        have defer_subset_acc:
          "defer (acc \<triangleright> m) A q \<subset> defer acc A q"
          using a_in_def_impl_def_subset lifted_pq_a
                a_in_def_seq_acc_m
          by metis
        have "electoral_module acc"
          using dli_acc
          unfolding defer_lift_invariance_def
          by simp
        hence "finite (defer acc A q) \<and> \<not> t (acc A q)"
          using lifted_def dli_acc a_in_def_seq_acc_m
                lifted_pq_a def_presv_fin_prof
                t_not_satisfied_for_q
          by metis
        with defer_subset_acc
        show
          "loop_comp_helper acc m t A q =
            loop_comp_helper (acc \<triangleright> m) m t A q"
          using loop_comp_code_helper
          by metis
      qed
      have rec_step_p:
        "electoral_module acc \<longrightarrow>
            loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
      proof (safe)
        assume emod_acc: "electoral_module acc"
        have emod_implies_defer_subset:
          "electoral_module m \<longrightarrow> defer (acc \<triangleright> m) A p \<subseteq> defer acc A p"
          using emod_acc f_prof seq_comp_def_set_bounded
          by blast
        have card_ineq: "card (defer (acc \<triangleright> m) A p) < card (defer acc A p)"
          using card_smaller_for_p emod_acc
          by force
        have fin_def_limited_acc:
          "finite_profile (defer acc A p) (limit_profile (defer acc A p) p)"
          using def_presv_fin_prof emod_acc f_prof
          by metis
        have "defer (acc \<triangleright> m) A p \<subseteq> defer acc A p"
          using emod_implies_defer_subset defer_lift_invariance_def monotone_m
          by blast
        hence "defer (acc \<triangleright> m) A p \<subset> defer acc A p"
          using fin_def_limited_acc card_ineq card_psubset
          by metis
        with fin_def_limited_acc
        show "loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
          using loop_comp_code_helper t_not_satisfied_for_p
          by (metis (no_types))
      qed
      show ?thesis
      proof (safe)
        fix
          q :: "'a Profile" and
          a :: "'a"
        assume
          dli_acc: "defer_lift_invariance acc" and
          n_card_acc: "n = card (defer acc A p)" and
          a_in_defer_lch: "a \<in> defer (loop_comp_helper acc m t) A p" and
          a_lifted: "Profile.lifted A p q a"
        hence emod_acc: "electoral_module acc"
          unfolding defer_lift_invariance_def
          by metis
        have "defer_lift_invariance (acc \<triangleright> m) \<and> a \<in> defer (acc \<triangleright> m) A p"
          using a_in_defer_lch defer_lift_invariance_def dli_acc
                f_prof loop_comp_helper_imp_no_def_incr monotone_m
                rec_step_p seq_comp_presv_def_lift_inv subsetD
          by (metis (no_types))
        with emod_acc
        show "loop_comp_helper acc m t A p = loop_comp_helper acc m t A q"
          using a_in_defer_lch a_lifted card_smaller_for_p dli_acc
                less.hyps n_card_acc rec_step_p rec_step_q
          by (metis (full_types))
      qed
    next
      assume "\<not> \<not>t (acc A p)"
      thus ?thesis
        using loop_comp_helper.simps(1)
        unfolding defer_lift_invariance_def
        by metis
    qed
  qed
qed

lemma loop_comp_helper_def_lift_inv:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc" and
    profile: "finite_profile A p"
  shows
    "\<forall> q a. (lifted A p q a \<and> a \<in> (defer (loop_comp_helper acc m t) A p)) \<longrightarrow>
        (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q"
  using loop_comp_helper_def_lift_inv_helper
        monotone_m monotone_acc profile
  by blast

lemma loop_comp_helper_def_lift_inv2:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc" and
    finite_A_p: "finite_profile A p" and
    lifted_A_pq: "lifted A p q a" and
    a_in_defer_acc: "a \<in> defer (loop_comp_helper acc m t) A p"
  shows "(loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q"
  using finite_A_p lifted_A_pq a_in_defer_acc
        loop_comp_helper_def_lift_inv
        monotone_acc monotone_m
  by blast

lemma lifted_imp_fin_prof:
  assumes "lifted A p q a"
  shows "finite_profile A p"
  using assms
  unfolding Profile.lifted_def
  by simp

lemma loop_comp_helper_presv_def_lift_inv:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc"
  shows "defer_lift_invariance (loop_comp_helper acc m t)"
proof (unfold defer_lift_invariance_def, safe)
  show "electoral_module (loop_comp_helper acc m t)"
    using electoral_modI loop_comp_helper_imp_partit monotone_acc monotone_m
    unfolding defer_lift_invariance_def
    by (metis (no_types))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume
    defer_a: "a \<in> defer (loop_comp_helper acc m t) A p" and
    lift_a: "Profile.lifted A p q a"
  show "loop_comp_helper acc m t A p = loop_comp_helper acc m t A q"
    using defer_a lift_a lifted_imp_fin_prof loop_comp_helper_def_lift_inv
          monotone_acc monotone_m
    by (metis (full_types))
qed

lemma loop_comp_presv_non_electing_helper:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_acc: "non_electing acc" and
    f_prof: "finite_profile A p" and
    acc_defer_card: "n = card (defer acc A p)"
  shows "elect (loop_comp_helper acc m t) A p = {}"
  using acc_defer_card non_electing_acc
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  thus ?case
  proof (safe)
    fix x :: "'a"
    assume
      y_acc_no_elect:
      "(\<And> y acc'. y < card (defer acc A p) \<Longrightarrow>
        y = card (defer acc' A p) \<Longrightarrow> non_electing acc' \<Longrightarrow>
          elect (loop_comp_helper acc' m t) A p = {})" and
      acc_non_elect: "non_electing acc" and
      x_in_acc_elect: "x \<in> elect (loop_comp_helper acc m t) A p"
    have
      "\<forall> (f::'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) g.
        (non_electing f \<and> non_electing g) \<longrightarrow>
          non_electing (f \<triangleright> g)"
      by simp
    hence seq_acc_m_non_elect: "non_electing (acc \<triangleright> m)"
      using acc_non_elect non_electing_m
      by blast
    have "\<forall> A B. (finite (A::'a set) \<and> B \<subset> A) \<longrightarrow> card B < card A"
      using psubset_card_mono
      by metis
    hence card_ineq:
      "\<forall> A B. (finite (A::'a set) \<and> B \<subset> A) \<longrightarrow> card B < card A"
      by presburger
    have no_elect_acc: "elect acc A p = {}"
      using acc_non_elect f_prof non_electing_def
      by auto
    have card_n_no_elect:
      "\<forall> n f.
        (n < card (defer acc A p) \<and> n = card (defer f A p) \<and> non_electing f) \<longrightarrow>
          elect (loop_comp_helper f m t) A p = {}"
      using y_acc_no_elect
      by blast
    have
      "\<And> f.
        (finite (defer acc A p) \<and> defer f A p \<subset> defer acc A p \<and> non_electing f) \<longrightarrow>
          elect (loop_comp_helper f m t) A p = {}"
      using card_n_no_elect psubset_card_mono
      by metis
    hence loop_helper_term:
      "(\<not> t (acc A p) \<and> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<and>
            finite (defer acc A p)) \<and>
          \<not> t (acc A p) \<longrightarrow>
        elect (loop_comp_helper acc m t) A p = {}"
      using loop_comp_code_helper seq_acc_m_non_elect
      by (metis (no_types))
    obtain set_func :: "'a set \<Rightarrow> 'a" where
      "\<forall> A. (A = {} \<longrightarrow> (\<forall> a. a \<notin> A)) \<and> (A \<noteq> {} \<longrightarrow> set_func A \<in> A)"
      using all_not_in_conv
      by (metis (no_types))
    thus "x \<in> {}"
      using loop_comp_code_helper no_elect_acc x_in_acc_elect loop_helper_term
      by (metis (no_types))
  qed
qed

lemma loop_comp_helper_iter_elim_def_n_helper:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    n_acc_defer_card: "n = card (defer acc A p)" and
    n_ge_x: "n \<ge> x" and
    def_card_gt_one: "card (defer acc A p) > 1" and
    acc_nonelect: "non_electing acc"
  shows "card (defer (loop_comp_helper acc m t) A p) = x"
  using n_ge_x def_card_gt_one acc_nonelect n_acc_defer_card
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have subset:
    "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> electoral_module acc) \<longrightarrow>
        defer (acc \<triangleright> m) A p \<subset> defer acc A p"
    using seq_comp_elim_one_red_def_set single_elimination
    by metis
  hence step_reduces_defer_set:
    "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> non_electing acc) \<longrightarrow>
        defer (acc \<triangleright> m) A p \<subset> defer acc A p"
    unfolding non_electing_def
    by metis
  thus ?case
  proof cases
    assume term_satisfied: "t (acc A p)"
    have "card (defer_r (loop_comp_helper acc m t A p)) = x"
      using loop_comp_helper.simps(1) term_satisfied terminate_if_n_left
      by metis
    thus ?case
      by blast
  next
    assume term_not_satisfied: "\<not>(t (acc A p))"
    hence card_not_eq_x: "card (defer acc A p) \<noteq> x"
      using terminate_if_n_left
      by simp
    have rec_step:
      "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> non_electing acc) \<longrightarrow>
          loop_comp_helper acc m t A p =
              loop_comp_helper (acc \<triangleright> m) m t A p"
      using def_presv_fin_prof loop_comp_helper.simps(2)
            step_reduces_defer_set term_not_satisfied
      unfolding non_electing_def
      by metis
    thus ?case
    proof cases
      assume card_too_small:
        "card (defer acc A p) < x"
      thus ?thesis
        using not_le card_too_small less.prems(1) less.prems(4) not_le
        by (metis (no_types))
    next
      assume old_card_at_least_x: "\<not>(card (defer acc A p) < x)"
      obtain i where i_is_new_card: "i = card (defer (acc \<triangleright> m) A p)"
        by simp
      with card_not_eq_x
      have card_too_big:
        "card (defer acc A p) > x"
        using nat_neq_iff old_card_at_least_x
        by simp
      hence enough_leftover:
        "card (defer acc A p) > 1"
        using x_greater_zero
        by simp
      have "electoral_module acc \<longrightarrow> (defer acc A p) \<subseteq> A"
        by (simp add: defer_in_alts f_prof)
      hence step_profile:
        "electoral_module acc \<longrightarrow>
            finite_profile (defer acc A p)
              (limit_profile (defer acc A p) p)"
        using f_prof limit_profile_sound
        by metis
      hence
        "electoral_module acc \<longrightarrow>
            card (defer m (defer acc A p)
              (limit_profile (defer acc A p) p)) =
                card (defer acc A p) - 1"
        using non_electing_m single_elimination
              single_elim_decr_def_card2 enough_leftover
        by metis
      hence "electoral_module acc \<longrightarrow> i = card (defer acc A p) - 1"
        using snd_conv i_is_new_card
        unfolding sequential_composition.simps
        by metis
      hence "electoral_module acc \<longrightarrow> i \<ge> x"
        using card_too_big
        by linarith
      hence new_card_still_big_enough: "electoral_module acc \<longrightarrow> x \<le> i"
        by simp
      have
        "electoral_module acc \<and> electoral_module m \<longrightarrow>
            defer (acc \<triangleright> m) A p \<subseteq> defer acc A p"
        using enough_leftover f_prof subset
        by blast
      hence
        "electoral_module acc \<and> electoral_module m \<longrightarrow>
            i \<le> card (defer acc A p)"
        using card_mono i_is_new_card step_profile
        by metis
      hence i_geq_x:
        "electoral_module acc \<and> electoral_module m \<longrightarrow> (i = x \<or> i > x)"
        using nat_less_le new_card_still_big_enough
        by metis
      thus ?thesis
      proof cases
        assume new_card_greater_x: "electoral_module acc \<longrightarrow> i > x"
        hence "electoral_module acc \<longrightarrow> 1 < card (defer (acc \<triangleright> m) A p)"
          using x_greater_zero i_is_new_card
          by linarith
        moreover have new_card_still_big_enough2_step:
          "electoral_module acc \<longrightarrow> x \<le> i"
          using i_is_new_card new_card_still_big_enough
          by metis
        moreover have n_card_then_i_lt_n_step:
          "n = card (defer acc A p) \<longrightarrow>
              (electoral_module acc \<longrightarrow> i < n)"
          using subset step_profile enough_leftover f_prof psubset_card_mono
                i_is_new_card
          by metis
        moreover have acc_mod_then_acc_seq_m_mod_step:
          "electoral_module acc \<longrightarrow>
              electoral_module (acc \<triangleright> m)"
          using non_electing_m seq_comp_sound
          unfolding non_electing_def
          by simp
        moreover have non_electing_new:
          "non_electing acc \<longrightarrow> non_electing (acc \<triangleright> m)"
          using non_electing_m
          by simp
        ultimately have card_x:
          "(n = card (defer acc A p) \<and> non_electing acc \<and>
              electoral_module acc) \<longrightarrow>
                  card (defer (loop_comp_helper (acc \<triangleright> m) m t) A p) = x"
          using less.hyps i_is_new_card new_card_greater_x
          by metis
        have f1: "loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
          using enough_leftover f_prof less.prems(3) rec_step
          by metis
        have "electoral_module acc"
          using less.prems(3)
          unfolding non_electing_def
          by simp
        thus ?thesis
          using f1 card_x less.prems(3) less.prems(4)
          by presburger
      next
        assume i_not_gt_x: "\<not>(electoral_module acc \<longrightarrow> i > x)"
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> i = x"
          using i_geq_x
          by simp
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> t ((acc \<triangleright> m) A p)"
          using i_is_new_card terminate_if_n_left
          by metis
        hence
          "electoral_module acc \<and> electoral_module m \<longrightarrow>
              card (defer_r (loop_comp_helper (acc \<triangleright> m) m t A p)) = x"
          using loop_comp_helper.simps(1) terminate_if_n_left
          by metis
        thus ?thesis
          using i_not_gt_x dual_order.strict_iff_order i_is_new_card
                loop_comp_helper.simps(1) new_card_still_big_enough
                f_prof rec_step terminate_if_n_left
                enough_leftover less.prems(3)
          by metis
      qed
    qed
  qed
qed

lemma loop_comp_helper_iter_elim_def_n:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    acc_defers_enough: "card (defer acc A p) \<ge> x" and
    non_electing_acc: "non_electing acc"
  shows "card (defer (loop_comp_helper acc m t) A p) = x"
  using acc_defers_enough gr_implies_not0 le_neq_implies_less
        less_one linorder_neqE_nat loop_comp_helper.simps(1)
        loop_comp_helper_iter_elim_def_n_helper non_electing_acc
        non_electing_m f_prof single_elimination nat_neq_iff
        terminate_if_n_left x_greater_zero less_le
  by (metis (no_types, lifting))

lemma iter_elim_def_n_helper:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    enough_alternatives: "card A \<ge> x"
  shows "card (defer (m \<circlearrowleft>\<^sub>t) A p) = x"
proof cases
  assume "card A = x"
  thus ?thesis
    by (simp add: terminate_if_n_left)
next
  assume card_not_x: "\<not> card A = x"
  thus ?thesis
  proof cases
    assume "card A < x"
    thus ?thesis
      using enough_alternatives not_le
      by blast
  next
    assume "\<not>card A < x"
    hence card_big_enough_A: "card A > x"
      using card_not_x
      by linarith
    hence card_m: "card (defer m A p) = card A - 1"
      using non_electing_m f_prof single_elimination
            single_elim_decr_def_card2 x_greater_zero
      by fastforce
    hence card_big_enough_m: "card (defer m A p) \<ge> x"
      using card_big_enough_A
      by linarith
    hence "(m \<circlearrowleft>\<^sub>t) A p = (loop_comp_helper m m t) A p"
      by (simp add: card_not_x terminate_if_n_left)
    thus ?thesis
      using card_big_enough_m non_electing_m f_prof single_elimination
            terminate_if_n_left x_greater_zero
            loop_comp_helper_iter_elim_def_n
      by metis
  qed
qed

subsection \<open>Composition Rules\<close>

text \<open>
  The loop composition preserves defer-lift-invariance.
\<close>

theorem loop_comp_presv_def_lift_inv[simp]:
  assumes "defer_lift_invariance m"
  shows "defer_lift_invariance (m \<circlearrowleft>\<^sub>t)"
proof (unfold defer_lift_invariance_def, safe)
  from assms
  have "electoral_module m"
    unfolding defer_lift_invariance_def
    by simp
  thus "electoral_module (m \<circlearrowleft>\<^sub>t)"
    by (simp add: loop_comp_sound)
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume
    a_in_loop_defer: "a \<in> defer (m \<circlearrowleft>\<^sub>t) A p" and
    lifted_a: "Profile.lifted A p q a"
  have defer_lift_loop:
    "\<forall> p q a. (a \<in> (defer (m \<circlearrowleft>\<^sub>t) A p) \<and> lifted A p q a) \<longrightarrow>
        (m \<circlearrowleft>\<^sub>t) A p = (m \<circlearrowleft>\<^sub>t) A q"
    using assms lifted_imp_fin_prof loop_comp_helper_def_lift_inv2
          loop_composition.simps defer_module.simps
    by (metis (full_types))
  show "(m \<circlearrowleft>\<^sub>t) A p = (m \<circlearrowleft>\<^sub>t) A q"
    using a_in_loop_defer lifted_a defer_lift_loop
    by metis
qed

text \<open>
  The loop composition preserves the property non-electing.
\<close>

theorem loop_comp_presv_non_electing[simp]:
  assumes non_electing_m: "non_electing m"
  shows "non_electing (m \<circlearrowleft>\<^sub>t)"
proof (unfold non_electing_def, safe, simp_all)
  show "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound non_electing_m
    unfolding non_electing_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    "finite A" and
    "profile A p" and
    "x \<in> elect (m \<circlearrowleft>\<^sub>t) A p"
  thus False
    using def_mod_non_electing loop_comp_presv_non_electing_helper
          non_electing_m empty_iff loop_comp_code
    unfolding non_electing_def
    by (metis (no_types))
qed

theorem iter_elim_def_n[simp]:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = n))" and
    x_greater_zero: "n > 0"
  shows "defers n (m \<circlearrowleft>\<^sub>t)"
proof (unfold defers_def, safe)
  show "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound non_electing_m
    unfolding non_electing_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    "n \<le> card A" and
    "finite A" and
    "profile A p"
  thus "card (defer (m \<circlearrowleft>\<^sub>t) A p) = n"
    using iter_elim_def_n_helper non_electing_m single_elimination
          terminate_if_n_left x_greater_zero
    by metis
qed

end

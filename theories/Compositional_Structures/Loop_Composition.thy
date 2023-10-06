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
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<not> t (acc V A p)" and
    "defer V (acc \<triangleright> m) A p \<subset> defer V acc A p" and
    "\<not> infinite (defer V acc A p)"
  shows "((acc \<triangleright> m, m, t, V, A, p), (acc, m, t, V, A, p)) \<in>
            measure (\<lambda> (acc, m, t, V, A, p). card (defer V acc A p))"
  using assms psubset_card_mono
  by simp

text \<open>
  This function handles the accumulator for the following loop composition
  function.
\<close>

function loop_comp_helper ::
    "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        'a Termination_Condition \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "t (acc V A p) \<or> \<not> ((defer V (acc \<triangleright> m) A p) \<subset> (defer V acc A p)) \<or>
    infinite (defer V acc A p) \<Longrightarrow>
      loop_comp_helper acc m t V A p = acc V A p" |
  "\<not> (t (acc V A p) \<or> \<not> ((defer V (acc \<triangleright> m) A p) \<subset> (defer V acc A p)) \<or>
        infinite (defer V acc A p)) \<Longrightarrow>
      loop_comp_helper acc m t V A p = loop_comp_helper (acc \<triangleright> m) m t V A p"
proof -
  fix
    P :: bool and
    accum ::
    "('a, 'v, 'a Result) Electoral_Module \<times> ('a, 'v, 'a Result) Electoral_Module 
        \<times> 'a Termination_Condition \<times> 'v set \<times> 'a set \<times> ('a, 'v) Profile"
  have accum_exists: "\<exists> m n t V A p. (m, n, t, V, A, p) = accum"
    using prod_cases5
    by metis
  assume
    "\<And> t acc V A p m.
      t (acc V A p) \<or> \<not> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p \<or>
          \<not> finite (defer V acc A p) \<Longrightarrow>
        accum = (acc, m, t, V, A, p) \<Longrightarrow> P" and
    "\<And> t acc V A p m.
      \<not> (t (acc V A p) \<or> \<not> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p \<or>
          \<not> finite (defer V acc A p)) \<Longrightarrow>
        accum = (acc, m, t, V, A, p) \<Longrightarrow> P"
  thus P
    using accum_exists
    by (metis (no_types))
next
  show "\<And>t acc V A p m ta acc' V' A' p' m'.
       t (acc (V::'v set) A p) \<or> \<not> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p 
        \<or> infinite (defer V acc A p) \<Longrightarrow>
       ta (acc' V' A' p') \<or>
        \<not> defer V' (acc' \<triangleright> m') A' p' \<subset> defer V' acc' A' p' \<or> infinite (defer V' acc' A' p') \<Longrightarrow>
       (acc, m, t, V, A, p) = (acc', m', ta, V', A', p') \<Longrightarrow> acc V A p = acc' V' A' p'"
    by fastforce
next
  show
    "\<And>t acc V A p m ta acca Va Aa pa ma.
       t (acc V A p) \<or> \<not> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p \<or> infinite (defer V acc A p) \<Longrightarrow>
       \<not> (ta (acca Va Aa pa) \<or>
           \<not> defer Va (acca \<triangleright> ma) Aa pa \<subset> defer Va acca Aa pa \<or> infinite (defer Va acca Aa pa)) \<Longrightarrow>
       (acc, m, t, V, A, p) = (acca, ma, ta, Va, Aa, pa) \<Longrightarrow>
       acc V A p = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Va, Aa, pa)"
    by force
next
  show
    "\<And>t acc V A p m ta acca Va Aa pa ma.
       \<not> (t (acc V A p) \<or>
           \<not> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p \<or> infinite (defer V acc A p)) \<Longrightarrow>
       \<not> (ta (acca Va Aa pa) \<or>
           \<not> defer Va (acca \<triangleright> ma) Aa pa \<subset> defer Va acca Aa pa \<or> infinite (defer Va acca Aa pa)) \<Longrightarrow>
       (acc, m, t, V, A, p) = (acca, ma, ta, Va, Aa, pa) \<Longrightarrow>
       loop_comp_helper_sumC (acc \<triangleright> m, m, t, V, A, p) =
       loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Va, Aa, pa)"
    by force
qed
termination
proof (safe)
  fix
    m :: "('b, 'a, 'b Result) Electoral_Module" and
    n :: "('b, 'a, 'b Result) Electoral_Module" and
    t :: "'b Termination_Condition" and
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile"
  have term_rel:
    "\<exists> R. wf R \<and>
        (t (m V A p) \<or> \<not> defer V (m \<triangleright> n) A p \<subset> defer V m A p \<or> infinite (defer V m A p) \<or>
          ((m \<triangleright> n, n, t, V, A, p), (m, n, t, V, A, p)) \<in> R)"
    using loop_termination_helper wf_measure "termination"
    by (metis (no_types))
  obtain
    R ::  "(((('b, 'a, 'b Result) Electoral_Module) \<times> (('b, 'a, 'b Result) Electoral_Module) \<times>
            ('b Termination_Condition) \<times> 'a set \<times> 'b set \<times> ('b, 'a) Profile) \<times>
            (('b, 'a, 'b Result) Electoral_Module) \<times> (('b, 'a, 'b Result) Electoral_Module) \<times>
            ('b Termination_Condition) \<times> 'a set \<times> 'b set \<times> ('b, 'a) Profile) set" where
    "wf R \<and>
      (t (m V A p) \<or>
        \<not> defer V (m \<triangleright> n) A p \<subset> defer V m A p \<or> infinite (defer V m A p) \<or>
          ((m \<triangleright> n, n, t, V, A, p), m, n, t, V, A, p) \<in> R)"
    using term_rel
    by presburger
  have "\<forall> R'. All
    (loop_comp_helper_dom::
      ('b, 'a, 'b Result) Electoral_Module \<times> ('b, 'a, 'b Result) Electoral_Module 
          \<times> 'b Termination_Condition \<times> 'a set \<times> 'b set \<times> ('b, 'a) Profile \<Rightarrow> bool) \<or>
      (\<exists> t' m' V' A' p' n'. wf R' \<longrightarrow>
        ((m' \<triangleright> n', n', t', V'::'a set, A'::'b set, p'), m', n', t', V', A', p') \<notin> R' \<and>
          finite (defer V' m' A' p') \<and> defer V' (m' \<triangleright> n') A' p' \<subset> defer V' m' A' p' \<and>
            \<not> t' (m' V' A' p'))"
    using "termination"
    by metis
  thus "loop_comp_helper_dom (m, n, t, V, A, p)"
    using loop_termination_helper wf_measure
    by metis
qed

lemma loop_comp_code_helper[code]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows
    "loop_comp_helper acc m t V A p =
      (if (t (acc V A p) \<or> \<not> ((defer V (acc \<triangleright> m) A p) \<subset> (defer V acc A p)) \<or>
        infinite (defer V acc A p))
      then (acc V A p) else (loop_comp_helper (acc \<triangleright> m) m t V A p))"
  by simp

function loop_composition ::
  "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a Termination_Condition 
    \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "t ({}, {}, A) \<Longrightarrow> loop_composition m t V A p = defer_module V A p" |
  "\<not>(t ({}, {}, A)) \<Longrightarrow> loop_composition m t V A p = (loop_comp_helper m m t) V A p"
  by (fastforce, simp_all)
termination
  using "termination" wf_empty
  by blast

abbreviation loop ::
  "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a Termination_Condition 
    \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module"
    ("_ \<circlearrowleft>\<^sub>_" 50) where
  "m \<circlearrowleft>\<^sub>t \<equiv> loop_composition m t"

lemma loop_comp_code[code]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "loop_composition m t V A p =
          (if (t ({},{},A))
            then (defer_module V A p) else (loop_comp_helper m m t) V A p)"
  by simp

lemma loop_comp_helper_imp_partit:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n :: nat
  assumes
    module_m: "social_choice_result.electoral_module m" and
    profile: "finite_profile V A p" and
    module_acc: "social_choice_result.electoral_module acc" and
    defer_card_n: "n = card (defer V acc A p)"
  shows "well_formed A (loop_comp_helper acc m t V A p)"
  using assms
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  have "\<forall> m' n'.
    (social_choice_result.electoral_module m' \<and> social_choice_result.electoral_module n') 
      \<longrightarrow> social_choice_result.electoral_module (m' \<triangleright> n')"
    by auto
  hence "social_choice_result.electoral_module (acc \<triangleright> m)"
    using less.prems module_m
    by metis
  hence "\<not> t (acc V A p) \<and> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p \<and>
            finite (defer V acc A p) \<longrightarrow>
          well_formed A (loop_comp_helper acc m t V A p)"
    using less.hyps less.prems loop_comp_helper.simps(2)
          psubset_card_mono
  by metis
  moreover have "well_formed A (acc V A p)"
    using less.prems profile
    unfolding social_choice_result.electoral_module_def
    by blast
  ultimately show ?case
    using loop_comp_helper.simps(1)
    by (metis (no_types))
qed

subsection \<open>Soundness\<close>

theorem loop_comp_sound:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition"
  assumes "social_choice_result.electoral_module m"
  shows "social_choice_result.electoral_module (m \<circlearrowleft>\<^sub>t)"
  using def_mod_sound loop_composition.simps(1, 2)
        loop_comp_helper_imp_partit assms
  unfolding social_choice_result.electoral_module_def
  by metis

lemma loop_comp_helper_imp_no_def_incr:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n :: nat
  assumes
    module_m: "social_choice_result.electoral_module m" and
    profile: "finite_profile V A p" and
    mod_acc: "social_choice_result.electoral_module acc" and
    card_n_defer_acc: "n = card (defer V acc A p)"
  shows "defer V (loop_comp_helper acc m t) A p \<subseteq> defer V acc A p"
  using assms
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  have emod_acc_m: "social_choice_result.electoral_module (acc \<triangleright> m)"
    using less.prems module_m seq_comp_sound 
    by blast
  have "\<forall> A A'. (finite A \<and> A' \<subset> A) \<longrightarrow> card A' < card A"
    using psubset_card_mono
    by metis
  hence "\<not> t (acc V A p) \<and> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p \<and>
            finite (defer V acc A p) \<longrightarrow>
          defer V (loop_comp_helper (acc \<triangleright> m) m t) A p \<subseteq> defer V acc A p"
    using emod_acc_m less.hyps less.prems
    by blast
  hence "\<not> t (acc V A p) \<and> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p \<and>
            finite (defer V acc A p) \<longrightarrow>
          defer V (loop_comp_helper acc m t) A p \<subseteq> defer V acc A p"
    using loop_comp_helper.simps(2)
    by (metis (no_types))
  thus ?case
    using eq_iff loop_comp_helper.simps(1)
    by (metis (no_types))
qed

subsection \<open>Lemmas\<close>

lemma loop_comp_helper_def_lift_inv_helper:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    monotone_m: "defer_lift_invariance m" and
    f_prof: "finite_profile V A p" and
    dli_acc: "defer_lift_invariance acc" and
    card_n_defer: "n = card (defer V acc A p)" and
    only_voters_vote: "only_voters_vote m"
  shows
    "\<forall> q a. (a \<in> (defer V (loop_comp_helper acc m t) A p) \<and> lifted V A p q a) \<longrightarrow>
        (loop_comp_helper acc m t) V A p = (loop_comp_helper acc m t) V A q"
  using assms
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have defer_card_comp:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall> q a. (a \<in> (defer V (acc \<triangleright> m) A p) \<and> lifted V A p q a) \<longrightarrow>
            card (defer V (acc \<triangleright> m) A p) = card (defer V (acc \<triangleright> m) A q))"
    using monotone_m def_lift_inv_seq_comp_help only_voters_vote
    by metis
  have "defer_lift_invariance acc \<longrightarrow>
          (\<forall> q a. (a \<in> (defer V (acc) A p) \<and> lifted V A p q a) \<longrightarrow>
            card (defer V (acc) A p) = card (defer V (acc) A q))"
    unfolding defer_lift_invariance_def
    by simp
  hence defer_card_acc:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall> q a. (a \<in> (defer V (acc \<triangleright> m) A p) \<and> lifted V A p q a) \<longrightarrow>
            card (defer V (acc) A p) = card (defer V (acc) A q))"
    using assms seq_comp_def_set_trans
    unfolding defer_lift_invariance_def
    by metis
  thus ?case
  proof (cases)
    assume card_unchanged: "card (defer V (acc \<triangleright> m) A p) = card (defer V acc A p)"
    have "defer_lift_invariance (acc) \<longrightarrow>
            (\<forall> q a. (a \<in> (defer V (acc) A p) \<and> lifted V A p q a) \<longrightarrow>
              (loop_comp_helper acc m t) V A q = acc V A q)"
    proof (safe)
      fix
        q :: "('a, 'v) Profile" and
        a :: "'a"
      assume
        dli_acc: "defer_lift_invariance acc" and
        a_in_def_acc: "a \<in> defer V acc A p" and
        lifted_A: "Profile.lifted V A p q a"
      have emod_m: "social_choice_result.electoral_module m"
        using monotone_m
        unfolding defer_lift_invariance_def
        by simp
      have emod_acc: "social_choice_result.electoral_module acc"
        using dli_acc
        unfolding defer_lift_invariance_def
        by simp
      have acc_eq_pq: "acc V A q = acc V A p"
        using a_in_def_acc dli_acc lifted_A
        unfolding defer_lift_invariance_def
        by (metis (full_types))
      with emod_acc emod_m
      have "finite (defer V acc A p) \<longrightarrow> loop_comp_helper acc m t V A q = acc V A q"
        using a_in_def_acc card_unchanged defer_card_comp f_prof lifted_A
              loop_comp_code_helper psubset_card_mono dual_order.strict_iff_order
              seq_comp_def_set_bounded less.prems(3)
        by (metis (mono_tags, lifting))
      thus "loop_comp_helper acc m t V A q = acc V A q"
        using acc_eq_pq loop_comp_code_helper
        by (metis (full_types))
    qed
    moreover from card_unchanged
    have "(loop_comp_helper acc m t) V A p = acc V A p"
      using loop_comp_helper.simps(1) order.strict_iff_order psubset_card_mono
      by metis
    ultimately have
      "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc) \<longrightarrow>
          (\<forall> q a. (a \<in> (defer V (loop_comp_helper acc m t) A p) \<and> lifted V A p q a) \<longrightarrow>
                  (loop_comp_helper acc m t) V A p = (loop_comp_helper acc m t) V A q)"
      unfolding defer_lift_invariance_def
      by metis
    thus ?thesis
      using monotone_m seq_comp_presv_def_lift_inv less.prems(3) only_voters_vote
      by blast
  next
    assume card_changed: "\<not> (card (defer V (acc \<triangleright> m) A p) = card (defer V acc A p))"
    with f_prof seq_comp_def_card_bounded
    have card_smaller_for_p:
      "social_choice_result.electoral_module (acc) \<longrightarrow>
        (card (defer V (acc \<triangleright> m) A p) < card (defer V acc A p))"
      using monotone_m order.not_eq_order_implies_strict
      unfolding defer_lift_invariance_def
      by (metis (full_types))
    with defer_card_acc defer_card_comp
    have card_changed_for_q:
     "defer_lift_invariance (acc) \<longrightarrow>
        (\<forall> q a. (a \<in> (defer V (acc \<triangleright> m) A p) \<and> lifted V A p q a) \<longrightarrow>
          (card (defer V (acc \<triangleright> m) A q) < card (defer V acc A q)))"
      unfolding defer_lift_invariance_def
      by metis  
    thus ?thesis
    proof (cases)
      assume t_not_satisfied_for_p: "\<not> t (acc V A p)"
      hence t_not_satisfied_for_q:
        "defer_lift_invariance (acc) \<longrightarrow>
            (\<forall> q a. (a \<in> (defer V (acc \<triangleright> m) A p) \<and> lifted V A p q a) \<longrightarrow> \<not> t (acc V A q))"
        using monotone_m f_prof seq_comp_def_set_trans
        unfolding defer_lift_invariance_def
        by metis
      have dli_card_def:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall> q a. (a \<in> (defer V (acc \<triangleright> m) A p) \<and> Profile.lifted V A p q a) \<longrightarrow>
                card (defer V (acc \<triangleright> m) A q) \<noteq> (card (defer V acc A q)))"
      proof -
        have
          "\<forall> m'.
            (\<not> defer_lift_invariance m' \<and> social_choice_result.electoral_module m' \<longrightarrow>
              (\<exists> A' V' p' q' a.
                m' V' A' p' \<noteq> m' V' A' q' \<and> Profile.lifted V' A' p' q' a 
                  \<and> a \<in> defer V' m' A' p')) \<and>
            (defer_lift_invariance m' \<longrightarrow>
              social_choice_result.electoral_module m' \<and>
                (\<forall> A' V' p' q' a.
                  m' V' A' p' \<noteq> m' V' A' q' \<longrightarrow> Profile.lifted V' A' p' q' a \<longrightarrow>
                    a \<notin> defer V' m' A' p'))"
          unfolding defer_lift_invariance_def
          by blast
        thus ?thesis
          using card_changed monotone_m f_prof seq_comp_def_set_trans
          by (metis (no_types, opaque_lifting))
      qed
      hence dli_def_subset:
        "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc) \<longrightarrow>
            (\<forall> p' a. (a \<in> (defer V (acc \<triangleright> m) A p) \<and> lifted V A p p' a) \<longrightarrow>
                defer V (acc \<triangleright> m) A p' \<subset> defer V acc A p')"
      proof -
        {
          fix
            a :: 'a and
            p' :: "('a, 'v) Profile"
          have "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc \<and>
                  (a \<in> defer V (acc \<triangleright> m) A p \<and> lifted V A p p' a)) \<longrightarrow>
                    defer V (acc \<triangleright> m) A p' \<subset> defer V acc A p'"
            using Profile.lifted_def dli_card_def defer_lift_invariance_def
                  monotone_m psubsetI seq_comp_def_set_bounded
            by (metis (no_types))
        }
        thus ?thesis
          by simp
      qed
      with t_not_satisfied_for_p
      have rec_step_q:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall> q a. (a \<in> (defer V (acc \<triangleright> m) A p) \<and> lifted V A p q a) \<longrightarrow>
                loop_comp_helper acc m t V A q =
                  loop_comp_helper (acc \<triangleright> m) m t V A q)"
      proof (safe)
        fix
          q :: "('a, 'v) Profile" and
          a :: "'a"
        assume
          a_in_def_impl_def_subset:
          "\<forall> q' a'. a' \<in> defer V (acc \<triangleright> m) A p \<and> lifted V A p q' a' \<longrightarrow>
            defer V (acc \<triangleright> m) A q' \<subset> defer V acc A q'" and
          dli_acc: "defer_lift_invariance acc" and
          a_in_def_seq_acc_m: "a \<in> defer V (acc \<triangleright> m) A p" and
          lifted_pq_a: "lifted V A p q a"
        have defer_subset_acc: "defer V (acc \<triangleright> m) A q \<subset> defer V acc A q"
          using a_in_def_impl_def_subset lifted_pq_a a_in_def_seq_acc_m
          by metis
        have "social_choice_result.electoral_module acc"
          using dli_acc
          unfolding defer_lift_invariance_def
          by simp
        hence "finite (defer V acc A q) \<and> \<not> t (acc V A q)"
          using lifted_def dli_acc a_in_def_seq_acc_m lifted_pq_a def_presv_fin_prof
                t_not_satisfied_for_q
          by metis
        with defer_subset_acc
        show "loop_comp_helper acc m t V A q = loop_comp_helper (acc \<triangleright> m) m t V A q"
          using loop_comp_code_helper
          by metis
      qed
      have rec_step_p:
        "social_choice_result.electoral_module acc \<longrightarrow>
            loop_comp_helper acc m t V A p = loop_comp_helper (acc \<triangleright> m) m t V A p"
      proof (safe)
        assume emod_acc: "social_choice_result.electoral_module acc"
        have sound_imp_defer_subset:
          "social_choice_result.electoral_module m \<longrightarrow> defer V (acc \<triangleright> m) A p \<subseteq> defer V acc A p"
          using emod_acc f_prof seq_comp_def_set_bounded
          by blast
        have card_ineq: "card (defer V (acc \<triangleright> m) A p) < card (defer V acc A p)"
          using card_smaller_for_p emod_acc
          by force
        have fin_def_limited_acc:
          "finite_profile V (defer V acc A p) (limit_profile (defer V acc A p) p)"
          using def_presv_fin_prof emod_acc f_prof
          by metis
        have "defer V (acc \<triangleright> m) A p \<subseteq> defer V acc A p"
          using sound_imp_defer_subset defer_lift_invariance_def monotone_m
          by blast
        hence "defer V (acc \<triangleright> m) A p \<subset> defer V acc A p"
          using fin_def_limited_acc card_ineq card_psubset
          by metis
        with fin_def_limited_acc
        show "loop_comp_helper acc m t V A p = loop_comp_helper (acc \<triangleright> m) m t V A p"
          using loop_comp_code_helper t_not_satisfied_for_p
          by (metis (no_types))
      qed
      show ?thesis
      proof (safe)
        fix
          q :: "('a, 'v) Profile" and
          a :: "'a"
        assume
          a_in_defer_lch: "a \<in> defer V (loop_comp_helper acc m t) A p" and
          a_lifted: "Profile.lifted V A p q a"
        have "social_choice_result.electoral_module acc"
          using defer_lift_invariance_def less.prems(3)
          by blast
        moreover have "defer_lift_invariance (acc \<triangleright> m) \<and> a \<in> defer V (acc \<triangleright> m) A p"
          using a_in_defer_lch defer_lift_invariance_def dli_acc f_prof rec_step_p subsetD
                loop_comp_helper_imp_no_def_incr monotone_m seq_comp_presv_def_lift_inv
                less.prems(3)
          sorry
        ultimately show
          "loop_comp_helper acc m t V A p = loop_comp_helper acc m t V A q"
          using a_in_defer_lch a_lifted card_smaller_for_p dli_acc f_prof
                less.hyps rec_step_p rec_step_q less.prems(1, 3, 4) only_voters_vote
          by metis
      qed
    next
      assume "\<not> \<not>t (acc V A p)"
      thus ?thesis
        using loop_comp_helper.simps(1) less.prems(3)
        unfolding defer_lift_invariance_def
        by metis
    qed
  qed
qed

lemma loop_comp_helper_def_lift_inv:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "defer_lift_invariance m" and
    "only_voters_vote m" and
    "defer_lift_invariance acc" and
    "finite_profile V A p"
  shows
    "\<forall> q a. (lifted V A p q a \<and> a \<in> (defer V (loop_comp_helper acc m t) A p)) \<longrightarrow>
        (loop_comp_helper acc m t) V A p = (loop_comp_helper acc m t) V A q"
  using loop_comp_helper_def_lift_inv_helper assms
  by blast

lemma loop_comp_helper_def_lift_inv_2:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and 
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "defer_lift_invariance m" and
    "only_voters_vote m" and
    "defer_lift_invariance acc" and
    "finite_profile V A p" and
    "lifted V A p q a" and
    "a \<in> defer V (loop_comp_helper acc m t) A p"
  shows "(loop_comp_helper acc m t) V A p = (loop_comp_helper acc m t) V A q"
  using loop_comp_helper_def_lift_inv assms
  by blast

lemma lifted_imp_fin_prof:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "lifted V A p q a"
  shows "finite_profile V A p"
  using assms
  unfolding Profile.lifted_def
  by simp

lemma loop_comp_helper_presv_def_lift_inv:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    "defer_lift_invariance m" and
    "only_voters_vote m" and
    "defer_lift_invariance acc"
  shows "defer_lift_invariance (loop_comp_helper acc m t)"
proof (unfold defer_lift_invariance_def, safe)
  show "social_choice_result.electoral_module (loop_comp_helper acc m t)"
    using social_choice_result.electoral_modI loop_comp_helper_imp_partit assms
    unfolding defer_lift_invariance_def
    by (metis (no_types))
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    "a \<in> defer V (loop_comp_helper acc m t) A p" and
    "Profile.lifted V A p q a"
  thus "loop_comp_helper acc m t V A p = loop_comp_helper acc m t V A q"
    using lifted_imp_fin_prof loop_comp_helper_def_lift_inv assms
    by metis
qed

lemma loop_comp_presv_non_electing_helper:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n :: nat
  assumes
    non_electing_m: "non_electing m" and
    non_electing_acc: "non_electing acc" and
    f_prof: "finite_profile V A p" and
    acc_defer_card: "n = card (defer V acc A p)"
  shows "elect V (loop_comp_helper acc m t) A p = {}"
  using acc_defer_card non_electing_acc
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  thus ?case
  proof (safe)
    fix x :: "'a"
    assume
      acc_no_elect:
      "(\<And> i acc'. i < card (defer V acc A p) \<Longrightarrow>
        i = card (defer V acc' A p) \<Longrightarrow> non_electing acc' \<Longrightarrow>
          elect V (loop_comp_helper acc' m t) A p = {})" and
      acc_non_elect: "non_electing acc" and
      x_in_acc_elect: "x \<in> elect V (loop_comp_helper acc m t) A p"
    have "\<forall> m' n'. (non_electing m' \<and> non_electing n') \<longrightarrow> non_electing (m' \<triangleright> n')"
      by simp
    hence seq_acc_m_non_elect: "non_electing (acc \<triangleright> m)"
      using acc_non_elect non_electing_m
      by blast
    have "\<forall> i m'.
            (i < card (defer V acc A p) \<and> i = card (defer V m' A p) \<and>
                non_electing m') \<longrightarrow>
              elect V (loop_comp_helper m' m t) A p = {}"
      using acc_no_elect
      by blast
    hence "\<And> m'.
            (finite (defer V acc A p) \<and> defer V m' A p \<subset> defer V acc A p \<and>
                non_electing m') \<longrightarrow>
              elect V (loop_comp_helper m' m t) A p = {}"
      using psubset_card_mono
      by metis
    hence "(\<not> t (acc V A p) \<and> defer V (acc \<triangleright> m) A p \<subset> defer V acc A p \<and>
                finite (defer V acc A p)) \<longrightarrow>
              elect V (loop_comp_helper acc m t) A p = {}"
      using loop_comp_code_helper seq_acc_m_non_elect
      by (metis (no_types))
    moreover have "elect V acc A p = {}"
      using acc_non_elect f_prof non_electing_def
      by blast
    ultimately show "x \<in> {}"
      using loop_comp_code_helper x_in_acc_elect
      by (metis (no_types))
  qed
qed

lemma loop_comp_helper_iter_elim_def_n_helper:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n :: nat and
    x :: nat
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) = (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile V A p" and
    n_acc_defer_card: "n = card (defer V acc A p)" and
    n_ge_x: "n \<ge> x" and
    def_card_gt_one: "card (defer V acc A p) > 1" and
    acc_nonelect: "non_electing acc"
  shows "card (defer V (loop_comp_helper acc m t) A p) = x"
  using n_ge_x def_card_gt_one acc_nonelect n_acc_defer_card
proof (induct n arbitrary: acc rule: less_induct)
  (* Likely, this induction here makes little sense, as it is over the size
     of the defer set. The expectation is going forward as in (acc \<triangleright> m),
     but that would imply that the defer set is shrinking with each step.
     It might be worth revising this proof at some point in the future. *)
  case (less n)
  have mod_acc: "social_choice_result.electoral_module acc"
    using less.prems(3) non_electing_def
    by metis
  hence step_reduces_defer_set: "defer V (acc \<triangleright> m) A p \<subset> defer V acc A p"
    using seq_comp_elim_one_red_def_set single_elimination
          f_prof less.prems(2)
    by metis
  thus ?case
  proof (cases "t (acc V A p)")
    case True
    assume term_satisfied: "t (acc V A p)"
    thus "card (defer_r (loop_comp_helper acc m t V A p)) = x"
      using loop_comp_helper.simps(1) term_satisfied terminate_if_n_left
      by metis
  next
    case False (* Termination condition not met *)
    hence card_not_eq_x: "card (defer V acc A p) \<noteq> x"
      using terminate_if_n_left
      by metis
    have "\<not> infinite (defer V acc A p)"
      using def_presv_fin_prof f_prof mod_acc
      by (metis (full_types))
    hence rec_step:
      "loop_comp_helper acc m t V A p = loop_comp_helper (acc \<triangleright> m) m t V A p"
      using False loop_comp_helper.simps(2) step_reduces_defer_set
      by metis
    have card_too_big: "card (defer V acc A p) > x"
      using card_not_eq_x dual_order.order_iff_strict less.prems(1, 4)
      by simp
    hence enough_leftover: "card (defer V acc A p) > 1"
      using x_greater_zero
      by simp
    obtain k where
      new_card_k: "k = card (defer V (acc \<triangleright> m) A p)"
      by metis
    have "defer V acc A p \<subseteq> A"
      using defer_in_alts f_prof mod_acc
      by metis
    hence step_profile: "finite_profile V (defer V acc A p) (limit_profile (defer V acc A p) p)"
      using f_prof limit_profile_sound
      by metis
    hence
      "card (defer V m (defer V acc A p) (limit_profile (defer V acc A p) p)) =
        card (defer V acc A p) - 1"
      using enough_leftover non_electing_m single_elim_decr_def_card_2
            single_elimination
      by metis
    hence k_card: "k = card (defer V acc A p) - 1"
      using mod_acc f_prof new_card_k non_electing_m seq_comp_defers_def_set
      by metis
    hence new_card_still_big_enough: "x \<le> k"
      using card_too_big
      by linarith
    show ?thesis
    proof (cases "x < k")
      case True
      hence "1 < card (defer V (acc \<triangleright> m) A p)"
        using new_card_k x_greater_zero
        by linarith
      moreover have "k < n"
        using step_reduces_defer_set step_profile psubset_card_mono
              new_card_k less.prems(4)
        by blast
      moreover have "social_choice_result.electoral_module (acc \<triangleright> m)"
        using mod_acc eliminates_def seq_comp_sound
              single_elimination
        by metis
      moreover have "non_electing (acc \<triangleright> m)"
        using less.prems(3) non_electing_m
        by simp
      ultimately have "card (defer V (loop_comp_helper (acc \<triangleright> m) m t) A p) = x"
        using new_card_k new_card_still_big_enough less.hyps
        by metis
      thus ?thesis
        using rec_step
        by presburger
    next
      case False (* k \<le> x (but actually, we can show k = x) *)
      thus ?thesis
        using dual_order.strict_iff_order new_card_k
              new_card_still_big_enough rec_step
              terminate_if_n_left
        by simp
    qed
  qed
qed

lemma loop_comp_helper_iter_elim_def_n:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    acc :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x :: nat
  assumes
    "non_electing m" and
    "eliminates 1 m" and
    "\<forall> r. ((t r) = (card (defer_r r) = x))" and
    "x > 0" and
    "finite_profile V A p" and
    "card (defer V acc A p) \<ge> x" and
    "non_electing acc"
  shows "card (defer V (loop_comp_helper acc m t) A p) = x"
  using assms gr_implies_not0 le_neq_implies_less less_one linorder_neqE_nat nat_neq_iff
        less_le loop_comp_helper_iter_elim_def_n_helper loop_comp_helper.simps(1)
  by (metis (no_types, lifting))

lemma iter_elim_def_n_helper:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x :: nat
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) = (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile V A p" and
    enough_alternatives: "card A \<ge> x"
  shows "card (defer V (m \<circlearrowleft>\<^sub>t) A p) = x"
proof (cases)
  assume "card A = x"
  thus ?thesis
    using terminate_if_n_left
    by simp
next
  assume card_not_x: "\<not> card A = x"
  thus ?thesis
  proof (cases)
    assume "card A < x"
    thus ?thesis
      using enough_alternatives not_le
      by blast
  next
    assume "\<not> card A < x"
    hence "card A > x"
      using card_not_x
      by linarith
    moreover from this
    have "card (defer V m A p) = card A - 1"
      using non_electing_m single_elimination single_elim_decr_def_card_2
            f_prof x_greater_zero
      by fastforce
    ultimately have "card (defer V m A p) \<ge> x"
      by linarith
    moreover have "(m \<circlearrowleft>\<^sub>t) V A p = (loop_comp_helper m m t) V A p"
      using card_not_x terminate_if_n_left
      by simp
    ultimately show ?thesis
      using non_electing_m f_prof single_elimination terminate_if_n_left x_greater_zero
            loop_comp_helper_iter_elim_def_n
      by metis
  qed
qed

subsection \<open>Composition Rules\<close>

text \<open>
  The loop composition preserves defer-lift-invariance.
\<close>

theorem loop_comp_presv_def_lift_inv[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition"
  assumes "defer_lift_invariance m" and "only_voters_vote m"
  shows "defer_lift_invariance (m \<circlearrowleft>\<^sub>t)"
proof (unfold defer_lift_invariance_def, safe)
  have "social_choice_result.electoral_module m"
    using assms
    unfolding defer_lift_invariance_def
    by simp
  thus "social_choice_result.electoral_module (m \<circlearrowleft>\<^sub>t)"
    by (simp add: loop_comp_sound)
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    "a \<in> defer V (m \<circlearrowleft>\<^sub>t) A p" and
    "Profile.lifted V A p q a"
  moreover have
    "\<forall> p' q' a'. (a' \<in> (defer V (m \<circlearrowleft>\<^sub>t) A p') \<and> lifted V A p' q' a') \<longrightarrow>
        (m \<circlearrowleft>\<^sub>t) V A p' = (m \<circlearrowleft>\<^sub>t) V A q'"
    using assms lifted_imp_fin_prof loop_comp_helper_def_lift_inv_2
          loop_composition.simps defer_module.simps
    by (metis (full_types))
  ultimately show "(m \<circlearrowleft>\<^sub>t) V A p = (m \<circlearrowleft>\<^sub>t) V A q"
    by metis
qed

text \<open>
  The loop composition preserves the property non-electing.
\<close>

theorem loop_comp_presv_non_electing[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition"
  assumes "non_electing m"
  shows "non_electing (m \<circlearrowleft>\<^sub>t)"
proof (unfold non_electing_def, safe)
  show "social_choice_result.electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound assms
    unfolding non_electing_def
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    "finite A" and
    "finite V" and
    "profile V A p" and
    "a \<in> elect V (m \<circlearrowleft>\<^sub>t) A p"
  thus "a \<in> {}"
    using def_mod_non_electing loop_comp_presv_non_electing_helper
          assms empty_iff loop_comp_code
    unfolding non_electing_def
    by (metis (no_types))
qed

theorem iter_elim_def_n[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    n :: nat
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) = (card (defer_r r) = n))" and
    x_greater_zero: "n > 0"
  shows "defers n (m \<circlearrowleft>\<^sub>t)"
proof (unfold defers_def, safe)
  show "social_choice_result.electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound non_electing_m
    unfolding non_electing_def
    by metis
next
  fix
    A :: "'a set" and 
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    "n \<le> card A" and
    "finite A" and
    "finite V" and
    "profile V A p"
  thus "card (defer V (m \<circlearrowleft>\<^sub>t) A p) = n"
    using iter_elim_def_n_helper assms
    by metis
qed

end

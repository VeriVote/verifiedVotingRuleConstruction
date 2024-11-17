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
  \<^item> the termination condition is met or
  \<^item> no new decisions are made (i.e., a fixed point is reached).
\<close>

subsection \<open>Definition\<close>

lemma loop_termination_helper:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<not> t (acc V A p)" and
    "defer (acc \<triangleright> m) V A p \<subset> defer acc V A p" and
    "finite (defer acc V A p)"
  shows "((acc \<triangleright> m, m, t, V, A, p), (acc, m, t, V, A, p)) \<in>
            measure (\<lambda> (acc, m, t, V, A, p). card (defer acc V A p))"
  using assms psubset_card_mono
  by simp

text \<open>
  This function handles the accumulator for the following loop composition
  function.
\<close>

function loop_comp_helper :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" where
    loop_comp_helper_finite:
    "finite (defer acc V A p) \<and> (defer (acc \<triangleright> m) V A p) \<subset> (defer acc V A p)
        \<longrightarrow> t (acc V A p) \<Longrightarrow>
    loop_comp_helper acc m t V A p = acc V A p" |
    loop_comp_helper_infinite:
    "\<not> (finite (defer acc V A p) \<and> (defer (acc \<triangleright> m) V A p) \<subset> (defer acc V A p)
        \<longrightarrow> t (acc V A p)) \<Longrightarrow>
    loop_comp_helper acc m t V A p = loop_comp_helper (acc \<triangleright> m) m t V A p"
proof -
  fix
    P :: "bool" and
    accum ::
    "('a, 'v, 'a Result) Electoral_Module \<times> ('a, 'v, 'a Result) Electoral_Module
        \<times> 'a Termination_Condition \<times> 'v set \<times> 'a set \<times> ('a, 'v) Profile"
  have accum_exists: "\<exists> m n t V A p. (m, n, t, V, A, p) = accum"
    using prod_cases5
    by metis
  assume
    "\<And> acc V A p m t.
      finite (defer acc V A p) \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p
          \<longrightarrow> t (acc V A p) \<Longrightarrow> accum = (acc, m, t, V, A, p) \<Longrightarrow> P" and
    "\<And> acc V A p m t.
      \<not> (finite (defer acc V A p) \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p
          \<longrightarrow> t (acc V A p)) \<Longrightarrow> accum = (acc, m, t, V, A, p) \<Longrightarrow> P"
  thus "P"
    using accum_exists
    by metis
next
  fix
    t t' :: "'a Termination_Condition" and
    acc acc' :: "('a, 'v, 'a Result) Electoral_Module" and
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    m m' :: "('a, 'v, 'a Result) Electoral_Module"
  assume
    "finite (defer acc V A p)
    \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p
        \<longrightarrow> t (acc V A p)" and
    "finite (defer acc' V' A' p')
    \<and> defer (acc' \<triangleright> m') V' A' p' \<subset> defer acc' V' A' p'
        \<longrightarrow> t' (acc' V' A' p')" and
    "(acc, m, t, V, A, p) = (acc', m', t', V', A', p')"
  thus "acc V A p = acc' V' A' p'"
    by fastforce
next
  fix
    t t' :: "'a Termination_Condition" and
    acc acc' :: "('a, 'v, 'a Result) Electoral_Module" and
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    m m' :: "('a, 'v, 'a Result) Electoral_Module"
  assume
    "finite (defer acc V A p)
    \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p
          \<longrightarrow> t (acc V A p)" and
    "\<not> (finite (defer acc' V' A' p')
    \<and> defer (acc' \<triangleright> m') V' A' p' \<subset> defer acc' V' A' p'
          \<longrightarrow> t' (acc' V' A' p'))" and
    "(acc, m, t, V, A, p) = (acc', m', t', V', A', p')"
  thus "acc V A p = loop_comp_helper_sumC (acc' \<triangleright> m', m', t', V', A', p')"
    by force
next
  fix
    t t' :: "'a Termination_Condition" and
    acc acc' :: "('a, 'v, 'a Result) Electoral_Module" and
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    m m' :: "('a, 'v, 'a Result) Electoral_Module"
  assume
    "\<not> (finite (defer acc V A p)
    \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p
          \<longrightarrow> t (acc V A p))" and
    "\<not> (finite (defer acc' V' A' p')
    \<and> defer (acc' \<triangleright> m') V' A' p' \<subset> defer acc' V' A' p'
          \<longrightarrow> t' (acc' V' A' p'))" and
    "(acc, m, t, V, A, p) = (acc', m', t', V', A', p')"
  thus "loop_comp_helper_sumC (acc \<triangleright> m, m, t, V, A, p) =
                  loop_comp_helper_sumC (acc' \<triangleright> m', m', t', V', A', p')"
    by force
qed
termination
proof (safe)
  fix
    m n :: "('b, 'a, 'b Result) Electoral_Module" and
    t :: "'b Termination_Condition" and
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile"
  have term_rel:
    "\<exists> R. wf R \<and>
        (finite (defer m V A p)
        \<and> defer (m \<triangleright> n) V A p \<subset> defer m V A p
      \<longrightarrow> t (m V A p)
        \<or> ((m \<triangleright> n, n, t, V, A, p), (m, n, t, V, A, p)) \<in> R)"
    using loop_termination_helper wf_measure "termination"
    by (metis (no_types))
  obtain
    R :: "((('b, 'a, 'b Result) Electoral_Module
              \<times> ('b, 'a, 'b Result) Electoral_Module
              \<times> ('b Termination_Condition) \<times> 'a set \<times> 'b set
              \<times> ('b, 'a) Profile)
          \<times> ('b, 'a, 'b Result) Electoral_Module
              \<times> ('b, 'a, 'b Result) Electoral_Module
              \<times> ('b Termination_Condition) \<times> 'a set \<times> 'b set
              \<times> ('b, 'a) Profile) set" where
    "wf R \<and>
      (finite (defer m V A p)
        \<and> defer (m \<triangleright> n) V A p \<subset> defer m V A p
      \<longrightarrow> t (m V A p)
        \<or> ((m \<triangleright> n, n, t, V, A, p), m, n, t, V, A, p) \<in> R)"
    using term_rel
    by presburger
  have "\<forall> R'.
    All (loop_comp_helper_dom ::
      ('b, 'a, 'b Result) Electoral_Module \<times> ('b, 'a, 'b Result) Electoral_Module
      \<times> 'b Termination_Condition \<times> 'a set \<times> 'b set \<times> ('b, 'a) Profile \<Rightarrow> bool) \<or>
      (\<exists> t' m' A' V' p' n'. wf R' \<longrightarrow>
        ((m' \<triangleright> n', n', t', V' :: 'a set, A' :: 'b set, p'), m', n', t', V', A', p') \<notin> R'
        \<and> finite (defer m' V' A' p') \<and> defer (m' \<triangleright> n') V' A' p' \<subset> defer m' V' A' p'
        \<and> \<not> t' (m' V' A' p'))"
    using "termination"
    by metis
  thus "loop_comp_helper_dom (m, n, t, V, A, p)"
    using loop_termination_helper wf_measure
    by metis
qed

lemma loop_comp_code_helper[code]:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows
    "loop_comp_helper acc m t V A p =
      (if (t (acc V A p) \<or> \<not> ((defer (acc \<triangleright> m) V A p) \<subset> (defer acc V A p))
      \<or> infinite (defer acc V A p))
      then (acc V A p) else (loop_comp_helper (acc \<triangleright> m) m t V A p))"
  using loop_comp_helper.simps
  by (metis (no_types))

function loop_composition :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        'a Termination_Condition \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "t ({}, {}, A)
    \<Longrightarrow> loop_composition m t V A p = defer_module V A p" |
  "\<not>(t ({}, {}, A))
    \<Longrightarrow> loop_composition m t V A p = (loop_comp_helper m m t) V A p"
  by (fastforce, simp_all)
termination
  using "termination" wf_empty
  by blast

abbreviation loop :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
        'a Termination_Condition \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module"
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
          (if (t ({}, {}, A))
            then (defer_module V A p) else (loop_comp_helper m m t) V A p)"
  by simp

lemma loop_comp_helper_imp_partit:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n :: "nat"
  assumes
    module_m: "\<S>\<C>\<F>_result.electoral_module m" and
    profile: "profile V A p" and
    module_acc: "\<S>\<C>\<F>_result.electoral_module acc" and
    defer_card_n: "n = card (defer acc V A p)"
  shows "well_formed_\<S>\<C>\<F> A (loop_comp_helper acc m t V A p)"
  using assms
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  have "\<forall> m' n'.
    (\<S>\<C>\<F>_result.electoral_module m' \<and> \<S>\<C>\<F>_result.electoral_module n')
      \<longrightarrow> \<S>\<C>\<F>_result.electoral_module (m' \<triangleright> n')"
    using seq_comp_sound
    by metis
  hence "\<S>\<C>\<F>_result.electoral_module (acc \<triangleright> m)"
    using less.prems module_m
    by blast
  hence "\<not> t (acc V A p) \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p \<and>
            finite (defer acc V A p) \<longrightarrow>
          well_formed_\<S>\<C>\<F> A (loop_comp_helper acc m t V A p)"
    using less.hyps less.prems loop_comp_helper_infinite
          psubset_card_mono
  by metis
  moreover have "well_formed_\<S>\<C>\<F> A (acc V A p)"
    using less.prems profile
    unfolding \<S>\<C>\<F>_result.electoral_module.simps
    by metis
  ultimately show ?case
    using loop_comp_code_helper
    by (metis (no_types))
qed

subsection \<open>Soundness\<close>

theorem loop_comp_sound:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition"
  assumes "\<S>\<C>\<F>_result.electoral_module m"
  shows "\<S>\<C>\<F>_result.electoral_module (m \<circlearrowleft>\<^sub>t)"
  using def_mod_sound loop_composition.simps
        loop_comp_helper_imp_partit assms
  unfolding \<S>\<C>\<F>_result.electoral_module.simps
  by metis

lemma loop_comp_helper_imp_no_def_incr:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n :: "nat"
  assumes
    module_m: "\<S>\<C>\<F>_result.electoral_module m" and
    profile: "profile V A p" and
    mod_acc: "\<S>\<C>\<F>_result.electoral_module acc" and
    card_n_defer_acc: "n = card (defer acc V A p)"
  shows "defer (loop_comp_helper acc m t) V A p \<subseteq> defer acc V A p"
  using assms
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  have emod_acc_m: "\<S>\<C>\<F>_result.electoral_module (acc \<triangleright> m)"
    using less.prems module_m seq_comp_sound
    by blast
  have "\<forall> A A'. (finite A \<and> A' \<subset> A) \<longrightarrow> card A' < card A"
    using psubset_card_mono
    by metis
  hence "\<not> t (acc V A p) \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p \<and>
            finite (defer acc V A p) \<longrightarrow>
          defer (loop_comp_helper (acc \<triangleright> m) m t) V A p \<subseteq> defer acc V A p"
    using emod_acc_m less.hyps less.prems
    by blast
  hence "\<not> t (acc V A p) \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p \<and>
            finite (defer acc V A p) \<longrightarrow>
          defer (loop_comp_helper acc m t) V A p \<subseteq> defer acc V A p"
    using loop_comp_helper_infinite
    by (metis (no_types))
  thus ?case
    using eq_iff loop_comp_code_helper
    by (metis (no_types))
qed

subsection \<open>Lemmas\<close>

lemma loop_comp_helper_def_lift_inv_helper:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n :: "nat"
  assumes
    monotone_m: "defer_lift_invariance m" and
    prof: "profile V A p" and
    dli_acc: "defer_lift_invariance acc" and
    card_n_defer: "n = card (defer acc V A p)" and
    defer_finite: "finite (defer acc V A p)" and
    voters_determine_m: "voters_determine_election m"
  shows
    "\<forall> q a. a \<in> (defer (loop_comp_helper acc m t) V A p) \<and> lifted V A p q a \<longrightarrow>
        (loop_comp_helper acc m t) V A p = (loop_comp_helper acc m t) V A q"
  using assms
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have defer_card_comp:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall> q a. a \<in> (defer (acc \<triangleright> m) V A p) \<and> lifted V A p q a \<longrightarrow>
            card (defer (acc \<triangleright> m) V A p) = card (defer (acc \<triangleright> m) V A q))"
    using monotone_m def_lift_inv_seq_comp_help voters_determine_m
    by metis
  have "defer_lift_invariance acc \<longrightarrow>
          (\<forall> q a. a \<in> (defer acc V A p) \<and> lifted V A p q a \<longrightarrow>
            card (defer acc V A p) = card (defer acc V A q))"
    unfolding defer_lift_invariance_def
    by simp
  hence defer_card_acc:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall> q a. (a \<in> (defer (acc \<triangleright> m) V A p) \<and> lifted V A p q a) \<longrightarrow>
            card (defer acc V A p) = card (defer acc V A q))"
    using assms seq_comp_def_set_trans
    unfolding defer_lift_invariance_def
    by metis
  thus ?case
  proof (cases)
    assume card_unchanged:
      "card (defer (acc \<triangleright> m) V A p) = card (defer acc V A p)"
    have "defer_lift_invariance acc \<longrightarrow>
            (\<forall> q a. a \<in> (defer acc V A p) \<and> lifted V A p q a \<longrightarrow>
              (loop_comp_helper acc m t) V A q = acc V A q)"
    proof (safe)
      fix
        q :: "('a, 'v) Profile" and
        a :: "'a"
      assume
        dli_acc: "defer_lift_invariance acc" and
        a_in_def_acc: "a \<in> defer acc V A p" and
        lifted_A: "Profile.lifted V A p q a"
      moreover have "\<S>\<C>\<F>_result.electoral_module m"
        using monotone_m
        unfolding defer_lift_invariance_def
        by simp
      moreover have emod_acc: "\<S>\<C>\<F>_result.electoral_module acc"
        using dli_acc
        unfolding defer_lift_invariance_def
        by simp
      moreover have acc_eq_pq: "acc V A q = acc V A p"
        using a_in_def_acc dli_acc lifted_A
        unfolding defer_lift_invariance_def
        by (metis (full_types))
      ultimately have "finite (defer acc V A p)
                        \<longrightarrow> loop_comp_helper acc m t V A q = acc V A q"
        using card_unchanged defer_card_comp prof loop_comp_code_helper
              psubset_card_mono dual_order.strict_iff_order
              seq_comp_def_set_bounded less
        by (metis (mono_tags, lifting))
      thus "loop_comp_helper acc m t V A q = acc V A q"
        using acc_eq_pq loop_comp_code_helper
        by (metis (full_types))
    qed
    moreover from card_unchanged
    have "(loop_comp_helper acc m t) V A p = acc V A p"
      using loop_comp_code_helper order.strict_iff_order psubset_card_mono
      by metis
    ultimately have
      "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc
      \<longrightarrow> (\<forall> q a. a \<in> (defer (loop_comp_helper acc m t) V A p)
                  \<and> lifted V A p q a
            \<longrightarrow> (loop_comp_helper acc m t) V A p =
                  (loop_comp_helper acc m t) V A q)"
      unfolding defer_lift_invariance_def
      by metis
    moreover have "defer_lift_invariance (acc \<triangleright> m)"
      using less monotone_m seq_comp_presv_def_lift_inv
      by safe
    ultimately show ?thesis
      using less monotone_m
      by metis
  next
    assume card_changed:
      "\<not> (card (defer (acc \<triangleright> m) V A p) = card (defer acc V A p))"
    with prof
    have card_smaller_for_p:
      "\<S>\<C>\<F>_result.electoral_module acc \<and> finite A \<longrightarrow>
        card (defer (acc \<triangleright> m) V A p) < card (defer acc V A p)"
      using monotone_m order.not_eq_order_implies_strict
            card_mono less.prems seq_comp_def_set_bounded
      unfolding defer_lift_invariance_def
      by metis
    with defer_card_acc defer_card_comp
    have card_changed_for_q:
      "defer_lift_invariance acc \<longrightarrow>
          (\<forall> q a. a \<in> (defer (acc \<triangleright> m) V A p) \<and> lifted V A p q a \<longrightarrow>
              card (defer (acc \<triangleright> m) V A q) < card (defer acc V A q))"
      using lifted_def less
      unfolding defer_lift_invariance_def
      by (metis (no_types, lifting))
    thus ?thesis
    proof (cases)
      assume t_not_satisfied_for_p: "\<not> t (acc V A p)"
      hence t_not_satisfied_for_q:
        "defer_lift_invariance acc \<longrightarrow>
            (\<forall> q a. a \<in> (defer (acc \<triangleright> m) V A p) \<and> lifted V A p q a
              \<longrightarrow> \<not> t (acc V A q))"
        using monotone_m prof seq_comp_def_set_trans
        unfolding defer_lift_invariance_def
        by metis
      have dli_card_defer:
        "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc
          \<longrightarrow> (\<forall> q a. a \<in> (defer (acc \<triangleright> m) V A p) \<and> Profile.lifted V A p q a
                \<longrightarrow> card (defer (acc \<triangleright> m) V A q) \<noteq> (card (defer acc V A q)))"
      proof -
        have
          "\<forall> m'.
            (\<not> defer_lift_invariance m' \<and> \<S>\<C>\<F>_result.electoral_module m'
            \<longrightarrow> (\<exists> V' A' p' q' a.
                  m' V' A' p' \<noteq> m' V' A' q' \<and> lifted V' A' p' q' a
                \<and> a \<in> defer m' V' A' p'))
            \<and> (defer_lift_invariance m'
              \<longrightarrow> \<S>\<C>\<F>_result.electoral_module m'
                \<and> (\<forall> V' A' p' q' a.
                  m' V' A' p' \<noteq> m' V' A' q'
                \<longrightarrow> lifted V' A' p' q' a \<longrightarrow> a \<notin> defer m' V' A' p'))"
          unfolding defer_lift_invariance_def
          by blast
        thus ?thesis
          using card_changed monotone_m prof seq_comp_def_set_trans
          by (metis (no_types, opaque_lifting))
      qed
      hence dli_def_subset:
        "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc
          \<longrightarrow> (\<forall> p' a. a \<in> (defer (acc \<triangleright> m) V A p) \<and> lifted V A p p' a
              \<longrightarrow> defer (acc \<triangleright> m) V A p' \<subset> defer acc V A p')"
        using Profile.lifted_def dli_card_defer defer_lift_invariance_def
              monotone_m psubsetI seq_comp_def_set_bounded
        by (metis (no_types, opaque_lifting))
      with t_not_satisfied_for_p
      have rec_step_q:
        "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc
          \<longrightarrow> (\<forall> q a. a \<in> (defer (acc \<triangleright> m) V A p) \<and> lifted V A p q a
              \<longrightarrow> loop_comp_helper acc m t V A q =
                    loop_comp_helper (acc \<triangleright> m) m t V A q)"
      proof (safe)
        fix
          q :: "('a, 'v) Profile" and
          a :: "'a"
        assume
          a_in_def_imp_def_subset:
          "\<forall> q' a'. a' \<in> defer (acc \<triangleright> m) V A p \<and> lifted V A p q' a' \<longrightarrow>
            defer (acc \<triangleright> m) V A q' \<subset> defer acc V A q'" and
          dli_acc: "defer_lift_invariance acc" and
          a_in_def_seq_acc_m: "a \<in> defer (acc \<triangleright> m) V A p" and
          lifted_pq_a: "lifted V A p q a"
        hence "defer (acc \<triangleright> m) V A q \<subset> defer acc V A q"
          by metis
        moreover have "\<S>\<C>\<F>_result.electoral_module acc"
          using dli_acc
          unfolding defer_lift_invariance_def
          by simp
        moreover have "\<not> t (acc V A q)"
          using dli_acc a_in_def_seq_acc_m lifted_pq_a t_not_satisfied_for_q
          by metis
        ultimately show "loop_comp_helper acc m t V A q
                          = loop_comp_helper (acc \<triangleright> m) m t V A q"
          using loop_comp_code_helper defer_in_alts finite_subset lifted_pq_a
          unfolding lifted_def
          by (metis (mono_tags, lifting))
      qed
      have rec_step_p:
        "\<S>\<C>\<F>_result.electoral_module acc \<longrightarrow>
            loop_comp_helper acc m t V A p = loop_comp_helper (acc \<triangleright> m) m t V A p"
      proof (safe)
        assume emod_acc: "\<S>\<C>\<F>_result.electoral_module acc"
        have sound_imp_defer_subset:
          "\<S>\<C>\<F>_result.electoral_module m
            \<longrightarrow> defer (acc \<triangleright> m) V A p \<subseteq> defer acc V A p"
          using emod_acc prof seq_comp_def_set_bounded
          by blast
        hence card_ineq: "card (defer (acc \<triangleright> m) V A p) < card (defer acc V A p)"
          using card_changed card_mono less order_neq_le_trans
          unfolding defer_lift_invariance_def
          by metis
        have def_limited_acc:
          "profile V (defer acc V A p) (limit_profile (defer acc V A p) p)"
          using def_presv_prof emod_acc prof
          by metis
        have "defer (acc \<triangleright> m) V A p \<subseteq> defer acc V A p"
          using sound_imp_defer_subset defer_lift_invariance_def monotone_m
          by blast
        hence "defer (acc \<triangleright> m) V A p \<subset> defer acc V A p"
          using def_limited_acc card_ineq card_psubset less
          by metis
        with def_limited_acc
        show "loop_comp_helper acc m t V A p =
                loop_comp_helper (acc \<triangleright> m) m t V A p"
          using loop_comp_code_helper t_not_satisfied_for_p less
          by (metis (no_types))
      qed
      show ?thesis
      proof (safe)
        fix
          q :: "('a, 'v) Profile" and
          a :: "'a"
        assume
          a_in_defer_lch: "a \<in> defer (loop_comp_helper acc m t) V A p" and
          a_lifted: "Profile.lifted V A p q a"
        have mod_acc: "\<S>\<C>\<F>_result.electoral_module acc"
          using less.prems
          unfolding defer_lift_invariance_def
          by simp
        hence loop_comp_equiv:
          "loop_comp_helper acc m t V A p = loop_comp_helper (acc \<triangleright> m) m t V A p"
          using rec_step_p
          by blast
        hence "a \<in> defer (loop_comp_helper (acc \<triangleright> m) m t) V A p"
          using a_in_defer_lch
          by presburger
        moreover have l_inv: "defer_lift_invariance (acc \<triangleright> m)"
          using less.prems monotone_m voters_determine_m
                seq_comp_presv_def_lift_inv
          by blast
        ultimately have "a \<in> defer (acc \<triangleright> m) V A p"
          using prof monotone_m in_mono loop_comp_helper_imp_no_def_incr
          unfolding defer_lift_invariance_def
          by (metis (no_types, lifting))
        with l_inv loop_comp_equiv show
          "loop_comp_helper acc m t V A p = loop_comp_helper acc m t V A q"
        proof -
          assume
            dli_acc_seq_m: "defer_lift_invariance (acc \<triangleright> m)" and
            a_in_def_seq: "a \<in> defer (acc \<triangleright> m) V A p"
          moreover from this have "\<S>\<C>\<F>_result.electoral_module (acc \<triangleright> m)"
            unfolding defer_lift_invariance_def
            by blast
          moreover have "a \<in> defer (loop_comp_helper (acc \<triangleright> m) m t) V A p"
            using loop_comp_equiv a_in_defer_lch
            by presburger
          ultimately have
            "loop_comp_helper (acc \<triangleright> m) m t V A p
              = loop_comp_helper (acc \<triangleright> m) m t V A q"
            using monotone_m mod_acc less a_lifted card_smaller_for_p
                  defer_in_alts infinite_super less
            unfolding lifted_def
            by (metis (no_types))
          moreover have "loop_comp_helper acc m t V A q
                          = loop_comp_helper (acc \<triangleright> m) m t V A q"
            using dli_acc_seq_m a_in_def_seq less a_lifted rec_step_q
            by blast
          ultimately show ?thesis
            using loop_comp_equiv
            by presburger
        qed
      qed
    next
      assume "\<not> \<not>t (acc V A p)"
      thus ?thesis
        using loop_comp_code_helper less
        unfolding defer_lift_invariance_def
        by metis
    qed
  qed
qed

lemma loop_comp_helper_def_lift_inv:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "defer_lift_invariance m" and
    "voters_determine_election m" and
    "defer_lift_invariance acc" and
    "profile V A p" and
    "lifted V A p q a" and
    "a \<in> defer (loop_comp_helper acc m t) V A p"
  shows "(loop_comp_helper acc m t) V A p = (loop_comp_helper acc m t) V A q"
  using assms loop_comp_helper_def_lift_inv_helper lifted_def
        defer_in_alts defer_lift_invariance_def finite_subset
  by metis

lemma lifted_imp_fin_prof:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "lifted V A p q a"
  shows "finite_profile V A p"
  using assms
  unfolding lifted_def
  by simp

lemma loop_comp_helper_presv_def_lift_inv:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition"
  assumes
    "defer_lift_invariance m" and
    "voters_determine_election m" and
    "defer_lift_invariance acc"
  shows "defer_lift_invariance (loop_comp_helper acc m t)"
proof (unfold defer_lift_invariance_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (loop_comp_helper acc m t)"
    using loop_comp_helper_imp_partit assms
    unfolding \<S>\<C>\<F>_result.electoral_module.simps
              defer_lift_invariance_def
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    "a \<in> defer (loop_comp_helper acc m t) V A p" and
    "lifted V A p q a"
  thus "loop_comp_helper acc m t V A p = loop_comp_helper acc m t V A q"
    using lifted_imp_fin_prof loop_comp_helper_def_lift_inv assms
    by metis
qed

lemma loop_comp_presv_non_electing_helper:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n :: "nat"
  assumes
    non_electing_m: "non_electing m" and
    non_electing_acc: "non_electing acc" and
    prof: "profile V A p" and
    acc_defer_card: "n = card (defer acc V A p)"
  shows "elect (loop_comp_helper acc m t) V A p = {}"
  using acc_defer_card non_electing_acc
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  thus ?case
  proof (safe)
    fix x :: "'a"
    assume
      acc_no_elect:
      "(\<And> i acc'. i < card (defer acc V A p) \<Longrightarrow>
        i = card (defer acc' V A p) \<Longrightarrow> non_electing acc' \<Longrightarrow>
          elect (loop_comp_helper acc' m t) V A p = {})" and
      acc_non_elect: "non_electing acc" and
      x_in_acc_elect: "x \<in> elect (loop_comp_helper acc m t) V A p"
    have "\<forall> m' n'. non_electing m' \<and> non_electing n' \<longrightarrow> non_electing (m' \<triangleright> n')"
      by simp
    hence seq_acc_m_non_elect: "non_electing (acc \<triangleright> m)"
      using acc_non_elect non_electing_m
      by blast
    have "\<forall> i m'.
            i < card (defer acc V A p) \<and> i = card (defer m' V A p) \<and>
                non_electing m' \<longrightarrow>
              elect (loop_comp_helper m' m t) V A p = {}"
      using acc_no_elect
      by blast
    hence "\<forall> m'.
            finite (defer acc V A p) \<and> defer m' V A p \<subset> defer acc V A p \<and>
                non_electing m' \<longrightarrow>
              elect (loop_comp_helper m' m t) V A p = {}"
      using psubset_card_mono
      by metis
    hence "\<not> t (acc V A p) \<and> defer (acc \<triangleright> m) V A p \<subset> defer acc V A p \<and>
                finite (defer acc V A p) \<longrightarrow>
              elect (loop_comp_helper acc m t) V A p = {}"
      using loop_comp_code_helper seq_acc_m_non_elect
      by (metis (no_types))
    moreover have "elect acc V A p = {}"
      using acc_non_elect prof non_electing_def
      by blast
    ultimately show "x \<in> {}"
      using loop_comp_code_helper x_in_acc_elect
      by (metis (no_types))
  qed
qed

(* Likely, this induction here makes little sense, as it is over the size
   of the defer set. The expectation is going forward as in (acc \<triangleright> m),
   but that would imply that the defer set is shrinking with each step.
   It might be worth revising this proof at some point in the future. *)
lemma loop_comp_helper_iter_elim_def_n_helper:
  fixes
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    n x :: "nat"
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. t r = (card (defer_r r) = x)" and
    x_greater_zero: "x > 0" and
    prof: "profile V A p" and
    n_acc_defer_card: "n = card (defer acc V A p)" and
    n_ge_x: "n \<ge> x" and
    def_card_gt_one: "card (defer acc V A p) > 1" and
    acc_nonelect: "non_electing acc"
  shows "card (defer (loop_comp_helper acc m t) V A p) = x"
  using n_ge_x def_card_gt_one acc_nonelect n_acc_defer_card
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have mod_acc: "\<S>\<C>\<F>_result.electoral_module acc"
    using less
    unfolding non_electing_def
    by metis
  hence step_reduces_defer_set: "defer (acc \<triangleright> m) V A p \<subset> defer acc V A p"
    using seq_comp_elim_one_red_def_set single_elimination prof less
    by metis
  thus ?case
  proof (cases "t (acc V A p)")
    case True
    assume term_satisfied: "t (acc V A p)"
    thus "card (defer_r (loop_comp_helper acc m t V A p)) = x"
      using loop_comp_code_helper term_satisfied terminate_if_n_left
      by metis
  next
    case False
    hence card_not_eq_x: "card (defer acc V A p) \<noteq> x"
      using terminate_if_n_left
      by metis
    have fin_def_acc: "finite (defer acc V A p)"
      using prof mod_acc less card.infinite not_one_less_zero
      by metis
    hence rec_step:
      "loop_comp_helper acc m t V A p = loop_comp_helper (acc \<triangleright> m) m t V A p"
      using False step_reduces_defer_set
      by simp
    have card_too_big: "card (defer acc V A p) > x"
      using card_not_eq_x dual_order.order_iff_strict less
      by simp
    hence enough_leftover: "card (defer acc V A p) > 1"
      using x_greater_zero
      by simp
    obtain k :: "nat" where
      new_card_k: "k = card (defer (acc \<triangleright> m) V A p)"
      by metis
    have "defer acc V A p \<subseteq> A"
      using defer_in_alts prof mod_acc
      by metis
    hence step_profile:
      "profile V (defer acc V A p) (limit_profile (defer acc V A p) p)"
      using prof limit_profile_sound
      by metis
    hence
      "card (defer m V (defer acc V A p) (limit_profile (defer acc V A p) p)) =
        card (defer acc V A p) - 1"
      using enough_leftover non_electing_m
            single_elimination single_elim_decr_def_card'
      by blast
    hence k_card: "k = card (defer acc V A p) - 1"
      using mod_acc prof new_card_k non_electing_m seq_comp_defers_def_set
      by metis
    hence new_card_still_big_enough: "x \<le> k"
      using card_too_big
      by linarith
    show ?thesis
    proof (cases "x < k")
      case True
      hence "1 < card (defer (acc \<triangleright> m) V A p)"
        using new_card_k x_greater_zero
        by linarith
      moreover have "k < n"
        using step_reduces_defer_set step_profile psubset_card_mono
              new_card_k less fin_def_acc
        by metis
      moreover have "\<S>\<C>\<F>_result.electoral_module (acc \<triangleright> m)"
        using mod_acc eliminates_def seq_comp_sound single_elimination
        by metis
      moreover have "non_electing (acc \<triangleright> m)"
        using less non_electing_m
        by simp
      ultimately have "card (defer (loop_comp_helper (acc \<triangleright> m) m t) V A p) = x"
        using new_card_k new_card_still_big_enough less
        by metis
      thus ?thesis
        using rec_step
        by presburger
    next
      case False
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
    m acc :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x :: "nat"
  assumes
    "non_electing m" and
    "eliminates 1 m" and
    "\<forall> r. (t r) = (card (defer_r r) = x)" and
    "x > 0" and
    "profile V A p" and
    "card (defer acc V A p) \<ge> x" and
    "non_electing acc"
  shows "card (defer (loop_comp_helper acc m t) V A p) = x"
  using assms gr_implies_not0 le_neq_implies_less less_one linorder_neqE_nat nat_neq_iff
        less_le loop_comp_helper_iter_elim_def_n_helper loop_comp_code_helper
  by (metis (no_types, lifting))

lemma iter_elim_def_n_helper:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x :: "nat"
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. (t r) = (card (defer_r r) = x)" and
    x_greater_zero: "x > 0" and
    prof: "profile V A p" and
    enough_alternatives: "card A \<ge> x"
  shows "card (defer (m \<circlearrowleft>\<^sub>t) V A p) = x"
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
    have "card (defer m V A p) = card A - 1"
      using non_electing_m single_elimination single_elim_decr_def_card'
            prof x_greater_zero
      by fastforce
    ultimately have "card (defer m V A p) \<ge> x"
      by linarith
    moreover have "(m \<circlearrowleft>\<^sub>t) V A p = (loop_comp_helper m m t) V A p"
      using card_not_x terminate_if_n_left
      by simp
    ultimately show ?thesis
      using non_electing_m prof single_elimination terminate_if_n_left x_greater_zero
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
  assumes
    "defer_lift_invariance m" and
    "voters_determine_election m"
  shows "defer_lift_invariance (m \<circlearrowleft>\<^sub>t)"
proof (unfold defer_lift_invariance_def, safe)
  have "\<S>\<C>\<F>_result.electoral_module m"
    using assms
    unfolding defer_lift_invariance_def
    by simp
  thus "\<S>\<C>\<F>_result.electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound
    by blast
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    "a \<in> defer (m \<circlearrowleft>\<^sub>t) V A p" and
    "lifted V A p q a"
  moreover have
    "\<forall> p' q' a'. a' \<in> (defer (m \<circlearrowleft>\<^sub>t) V A p') \<and> lifted V A p' q' a' \<longrightarrow>
        (m \<circlearrowleft>\<^sub>t) V A p' = (m \<circlearrowleft>\<^sub>t) V A q'"
    using assms lifted_imp_fin_prof loop_comp_helper_def_lift_inv
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
  show "\<S>\<C>\<F>_result.electoral_module (m \<circlearrowleft>\<^sub>t)"
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
    "profile V A p" and
    "a \<in> elect (m \<circlearrowleft>\<^sub>t) V A p"
  thus "a \<in> {}"
    using def_mod_non_electing loop_comp_presv_non_electing_helper
          assms empty_iff loop_comp_code
    unfolding non_electing_def
    by (metis (no_types, lifting))
qed

theorem iter_elim_def_n[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    t :: "'a Termination_Condition" and
    n :: "nat"
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. t r = (card (defer_r r) = n)" and
    x_greater_zero: "n > 0"
  shows "defers n (m \<circlearrowleft>\<^sub>t)"
proof (unfold defers_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (m \<circlearrowleft>\<^sub>t)"
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
    "profile V A p"
  thus "card (defer (m \<circlearrowleft>\<^sub>t) V A p) = n"
    using iter_elim_def_n_helper assms
    by metis
qed

end
(*  File:       Plurality_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Plurality Module\<close>

theory Plurality_Module
  imports "Component_Types/Elimination_Module"
begin

text \<open>
  The plurality module implements the plurality voting rule.
  The plurality rule elects all modules with the maximum amount of top
  preferences among all alternatives, and rejects all the other alternatives.
  It is electing and induces the classical plurality (voting) rule
  from social-choice theory.
\<close>

subsection \<open>Definition\<close>

fun plurality_score :: "('a, 'v) Evaluation_Function" where
  "plurality_score V x A p = win_count V p x"

fun plurality :: "('a, 'v, 'a Result) Electoral_Module" where
  "plurality V A p = max_eliminator plurality_score V A p"

fun plurality' :: "('a, 'v, 'a Result) Electoral_Module" where
  "plurality' V A p =
      (if finite A
        then ({},
              {a \<in> A. \<exists> x \<in> A. win_count V p x > win_count V p a},
              {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})
        else ({}, {}, A))"

lemma enat_leq_enat_set_max:
  fixes
    x :: "enat" and
    X :: "enat set"
  assumes
    "x \<in> X" and
    "finite X"
  shows "x \<le> Max X"
  using assms
  by simp

lemma plurality_mod_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "plurality V A p = plurality' V A p"
proof (unfold plurality'.simps)
  have no_winners_or_in_domain:
    "finite {win_count V p a | a. a \<in> A} \<longrightarrow>
      {win_count V p a | a. a \<in> A} = {} \<or>
        Max {win_count V p a | a. a \<in> A} \<in> {win_count V p a | a. a \<in> A}"
    using Max_in
    by blast
  moreover have only_one_max:
    "finite A \<longrightarrow>
      {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x} =
        {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}}"
  proof
    assume fin_A: "finite A"
    hence "finite {win_count V p x | x. x \<in> A}"
      by simp
    hence
      "\<forall> a \<in> A. \<forall> b \<in> A. win_count V p a < win_count V p b \<longrightarrow>
        win_count V p a < Max {win_count V p x | x. x \<in> A}"
      using CollectI Max_gr_iff empty_Collect_eq
      by (metis (mono_tags, lifting))
    hence
      "{a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x}
        \<subseteq> {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}}"
      by blast
    moreover have
      "{a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}}
        \<subseteq> {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x}"
      using fin_A no_winners_or_in_domain
      by fastforce
    ultimately show
      "{a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x} =
        {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}}"
      by fastforce
  qed
  ultimately have
    "finite A \<longrightarrow>
      reject plurality V A p = {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x}"
    by force
  moreover have
    "finite A \<longrightarrow>
      defer plurality V A p = {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a}"
  proof
    assume fin_A: "finite A"
    have "{a \<in> A. \<exists> x \<in> A. win_count V p x > win_count V p a}
          \<inter> {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a} = {}"
      by force
    moreover have
      "{a \<in> A. \<exists> x \<in> A. win_count V p x > win_count V p a}
        \<union> {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a} = A"
      by force
    ultimately have
      "{a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a} =
          A - {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}}"
      using fin_A only_one_max Diff_cancel Int_Diff_Un Un_Diff inf_commute
      by (metis (no_types, lifting))
    moreover have
      "{a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}} = A \<longrightarrow>
      {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a} = A"
      using fin_A no_winners_or_in_domain
      by fastforce
    ultimately show
      "defer plurality V A p = {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a}"
      using fin_A
      by force
  qed
  moreover have "elect plurality V A p = {}"
    unfolding max_eliminator.simps less_eliminator.simps elimination_module.simps
    by force
  ultimately have
    "finite A \<longrightarrow>
      plurality V A p =
        ({}, {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x},
          {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})"
    using split_pairs
    by (metis (no_types, lifting))
  thus "plurality V A p =
    (if finite A
     then ({}, {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x},
           {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})
     else ({}, {}, A))"
    by force
qed

subsection \<open>Soundness\<close>

theorem plurality_sound[simp]: "\<S>\<C>\<F>_result.electoral_module plurality"
  unfolding plurality.simps
  using max_elim_sound
  by metis

theorem plurality'_sound[simp]: "\<S>\<C>\<F>_result.electoral_module plurality'"
proof (unfold \<S>\<C>\<F>_result.electoral_module.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  have "disjoint3 (
      {},
      {a \<in> A. \<exists> a' \<in> A. win_count V p a < win_count V p a'},
      {a \<in> A. \<forall> a' \<in> A. win_count V p a' \<le> win_count V p a})"
    by auto
  moreover have
    "{a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x} \<union>
      {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a} = A"
    using not_le_imp_less
    by blast
  ultimately show "well_formed_\<S>\<C>\<F> A (plurality' V A p)"
    by simp
qed

lemma voters_determine_plurality_score: "voters_determine_evaluation plurality_score"
proof (unfold plurality_score.simps voters_determine_evaluation.simps, safe)
  fix
    A :: "'b set" and
    V :: "'a set" and
    p p' :: "('b, 'a) Profile" and
    a :: "'b"
  assume
    "\<forall> v \<in> V. p v = p' v" and
    "a \<in> A"
  hence "finite V \<longrightarrow>
    card {v \<in> V. above (p v) a = {a}} = card {v \<in> V. above (p' v) a = {a}}"
    using Collect_cong
    by (metis (no_types, lifting))
  thus "win_count V p a = win_count V p' a"
    unfolding win_count.simps
    by presburger
qed

lemma voters_determine_plurality: "voters_determine_election plurality"
  unfolding plurality.simps
  using voters_determine_max_elim voters_determine_plurality_score
  by blast

lemma voters_determine_plurality': "voters_determine_election plurality'"
proof (unfold voters_determine_election.simps, safe)
  fix
    A :: "'k set" and
    V :: "'v set" and
    p p' :: "('k, 'v) Profile"
  assume "\<forall> v \<in> V. p v = p' v"
  thus "plurality' V A p = plurality' V A p'"
    using voters_determine_plurality plurality_mod_equiv
    unfolding voters_determine_election.simps
    by (metis (full_types))
qed

subsection \<open>Non-Blocking\<close>

text \<open>
  The plurality module is non-blocking.
\<close>

theorem plurality_mod_non_blocking[simp]: "non_blocking plurality"
  unfolding plurality.simps
  using max_elim_non_blocking
  by metis

theorem plurality'_mod_non_blocking[simp]: "non_blocking plurality'"
  using plurality_mod_non_blocking plurality_mod_equiv plurality'_sound
  unfolding non_blocking_def
  by metis

subsection \<open>Non-Electing\<close>

text \<open>
  The plurality module is non-electing.
\<close>

theorem plurality_non_electing[simp]: "non_electing plurality"
  using max_elim_non_electing
  unfolding plurality.simps non_electing_def
  by metis

theorem plurality'_non_electing[simp]: "non_electing plurality'"
  unfolding non_electing_def
  using plurality'_sound
  by simp

subsection \<open>Property\<close>

lemma plurality_def_inv_mono_alts:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    defer_a: "a \<in> defer plurality V A p" and
    lift_a: "lifted V A p q a"
  shows "defer plurality V A q = defer plurality V A p
          \<or> defer plurality V A q = {a}"
proof -
  have set_disj: "\<forall> b c. b \<notin> {c} \<or> b = c"
    by blast
  have lifted_winner: "\<forall> b \<in> A. \<forall> i \<in> V.
      above (p i) b = {b} \<longrightarrow> (above (q i) b = {b} \<or> above (q i) a = {a})"
    using lift_a lifted_above_winner_alts
    unfolding Profile.lifted_def
    by metis
  hence "\<forall> i \<in> V. (above (p i) a = {a} \<longrightarrow> above (q i) a = {a})"
    using defer_a lift_a
    unfolding Profile.lifted_def
    by metis
  hence a_win_subset:
    "{i \<in> V. above (p i) a = {a}} \<subseteq> {i \<in> V. above (q i) a = {a}}"
    by blast
  moreover have lifted_prof: "profile V A q"
    using lift_a
    unfolding Profile.lifted_def
    by metis
  ultimately have win_count_a: "win_count V p a \<le> win_count V q a"
    by (simp add: card_mono)
  have fin_A: "finite A"
    using lift_a
    unfolding Profile.lifted_def
    by blast
  hence "\<forall> b \<in> A - {a}.
          \<forall> i \<in> V. (above (q i) a = {a} \<longrightarrow> above (q i) b \<noteq> {b})"
    using DiffE above_one lift_a insertCI insert_absorb insert_not_empty
    unfolding Profile.lifted_def profile_def
    by metis
  with lifted_winner
  have above_QtoP:
    "\<forall> b \<in> A - {a}.
      \<forall> i \<in> V. (above (q i) b = {b} \<longrightarrow> above (p i) b = {b})"
    using lifted_above_winner_other lift_a
    unfolding Profile.lifted_def
    by metis
  hence "\<forall> b \<in> A - {a}.
          {i \<in> V. above (q i) b = {b}} \<subseteq> {i \<in> V. above (p i) b = {b}}"
    by (simp add: Collect_mono)
  hence win_count_other: "\<forall> b \<in> A - {a}. win_count V p b \<ge> win_count V q b"
    by (simp add: card_mono)
  show "defer plurality V A q = defer plurality V A p
        \<or> defer plurality V A q = {a}"
  proof (cases)
    assume "win_count V p a = win_count V q a"
    hence "card {i \<in> V. above (p i) a = {a}} = card {i \<in> V. above (q i) a = {a}}"
      using win_count.simps Profile.lifted_def enat.inject lift_a
      by (metis (mono_tags, lifting))
    moreover have "finite {i \<in> V. above (q i) a = {a}}"
      using Collect_mem_eq Profile.lifted_def finite_Collect_conjI lift_a
      by (metis (mono_tags))
    ultimately have "{i \<in> V. above (p i) a = {a}} = {i \<in> V. above (q i) a = {a}}"
      using a_win_subset
      by (simp add: card_subset_eq)
    hence above_pq: "\<forall> i \<in> V. (above (p i) a = {a}) = (above (q i) a = {a})"
      by blast
    moreover have
      "\<forall> b \<in> A - {a}. \<forall> i \<in> V.
          (above (p i) b = {b} \<longrightarrow> (above (q i) b = {b} \<or> above (q i) a = {a}))"
      using lifted_winner
      by auto
    moreover have
      "\<forall> b \<in> A - {a}. \<forall> i \<in> V. (above (p i) b = {b} \<longrightarrow> above (p i) a \<noteq> {a})"
    proof (intro ballI impI, safe)
      fix
        b :: "'a" and
        i :: "'v"
      assume
        "b \<in> A" and
        "i \<in> V"
      moreover from this have A_not_empty: "A \<noteq> {}"
        by blast
      ultimately have "linear_order_on A (p i)"
        using lift_a
        unfolding lifted_def profile_def
        by metis
      moreover assume
        b_neq_a: "b \<noteq> a" and
        abv_b: "above (p i) b = {b}" and
        abv_a: "above (p i) a = {a}"
      ultimately show False
        using above_one_eq A_not_empty fin_A
        by (metis (no_types))
    qed
    ultimately have above_PtoQ:
      "\<forall> b \<in> A - {a}. \<forall> i \<in> V. (above (p i) b = {b} \<longrightarrow> above (q i) b = {b})"
      by simp
    hence "\<forall> b \<in> A.
            card {i \<in> V. above (p i) b = {b}} =
              card {i \<in> V. above (q i) b = {b}}"
    proof (safe)
      fix b :: "'a"
      assume "b \<in> A"
      thus "card {i \<in> V. above (p i) b = {b}} =
              card {i \<in> V. above (q i) b = {b}}"
        using DiffI set_disj above_PtoQ above_QtoP above_pq
        by (metis (no_types, lifting))
    qed
    hence "{b \<in> A. \<forall> c \<in> A. win_count V p c \<le> win_count V p b} =
              {b \<in> A. \<forall> c \<in> A. win_count V q c \<le> win_count V q b}"
      by auto
    hence "defer plurality' V A q = defer plurality' V A p
            \<or> defer plurality' V A q = {a}"
      by simp
    hence "defer plurality V A q = defer plurality V A p
            \<or> defer plurality V A q = {a}"
      using plurality_mod_equiv lift_a
      unfolding Profile.lifted_def
      by (metis (no_types, opaque_lifting))
    thus ?thesis
      by simp
  next
    assume "win_count V p a \<noteq> win_count V q a"
    hence strict_less: "win_count V p a < win_count V q a"
      using win_count_a
      by simp
    have "a \<in> defer plurality V A p"
      using defer_a plurality.elims
      by (metis (no_types))
    moreover have non_empty_A: "A \<noteq> {}"
      using lift_a equals0D equiv_prof_except_a_def
            lifted_imp_equiv_prof_except_a
      by metis
    moreover have fin_A: "finite_profile V A p"
      using lift_a
      unfolding Profile.lifted_def
      by simp
    ultimately have "a \<in> defer plurality' V A p"
      using plurality_mod_equiv
      by metis
    hence a_in_win_p:
      "a \<in> {b \<in> A. \<forall> c \<in> A. win_count V p c \<le> win_count V p b}"
      using fin_A
      by simp
    hence "\<forall> b \<in> A. win_count V p b \<le> win_count V p a"
      by simp
    hence less: "\<forall> b \<in> A - {a}. win_count V q b < win_count V q a"
      using DiffD1 antisym dual_order.trans not_le_imp_less
            win_count_a strict_less win_count_other
      by metis
    hence "\<forall> b \<in> A - {a}. \<not> (\<forall> c \<in> A. win_count V q c \<le> win_count V q b)"
      using lift_a not_le
      unfolding Profile.lifted_def
      by metis
    hence "\<forall> b \<in> A - {a}.
            b \<notin> {c \<in> A. \<forall> b \<in> A. win_count V q b \<le> win_count V q c}"
      by blast
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality' V A q"
      using fin_A
      by simp
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality V A q"
      using lift_a non_empty_A plurality_mod_equiv
      unfolding Profile.lifted_def
      by (metis (no_types, lifting))
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality V A q"
      by simp
    moreover have "a \<in> defer plurality V A q"
    proof -
      have "\<forall> b \<in> A - {a}. win_count V q b \<le> win_count V q a"
        using less less_imp_le
        by metis
      moreover have "win_count V q a \<le> win_count V q a"
        by simp
      ultimately have "\<forall> b \<in> A. win_count V q b \<le> win_count V q a"
        by auto
      moreover have "a \<in> A"
        using a_in_win_p
        by simp
      ultimately have
        "a \<in> {b \<in> A. \<forall> c \<in> A. win_count V q c \<le> win_count V q b}"
        by simp
      hence "a \<in> defer plurality' V A q"
        by simp
      hence "a \<in> defer plurality V A q"
        using plurality_mod_equiv non_empty_A fin_A lift_a non_empty_A
        unfolding Profile.lifted_def
        by (metis (no_types))
      thus ?thesis
        by simp
    qed
    moreover have "defer plurality V A q \<subseteq> A"
      by simp
    ultimately show ?thesis
      by blast
  qed
qed

lemma plurality'_def_inv_mono_alts:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "a \<in> defer plurality' V A p" and
    "lifted V A p q a"
  shows "defer plurality' V A q = defer plurality' V A p
          \<or> defer plurality' V A q = {a}"
  using assms plurality_def_inv_mono_alts plurality_mod_equiv
  by (metis (no_types))

text \<open>
  The plurality rule is invariant-monotone.
\<close>

theorem plurality_mod_def_inv_mono[simp]: "defer_invariant_monotonicity plurality"
proof (unfold defer_invariant_monotonicity_def, intro conjI impI allI)
  show "\<S>\<C>\<F>_result.electoral_module plurality"
    using plurality_sound
    by metis
next
  show "non_electing plurality"
    by simp
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p q :: "('b, 'a) Profile" and
    a :: "'b"
  assume "a \<in> defer plurality V A p \<and> Profile.lifted V A p q a"
  hence "defer plurality V A q = defer plurality V A p
          \<or> defer plurality V A q = {a}"
    using plurality_def_inv_mono_alts
    by metis
  thus "defer plurality V A q = defer plurality V A p
          \<or> defer plurality V A q = {a}"
    by simp
qed

theorem plurality'_mod_def_inv_mono[simp]: "defer_invariant_monotonicity plurality'"
  using plurality_mod_def_inv_mono plurality_mod_equiv
        plurality'_non_electing plurality'_sound
  unfolding defer_invariant_monotonicity_def
  by metis

end
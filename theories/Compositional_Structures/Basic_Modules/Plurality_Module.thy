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
    ({},
     {a \<in> A. \<exists> x \<in> A. win_count V p x > win_count V p a},
     {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})"

lemma enat_leq_enat_set_max:
  fixes
    x :: enat and
    X :: "enat set"
  assumes 
    "x \<in> X" and 
    "finite X"
  shows "x \<le> Max X"
  by (simp add: assms)

lemma plurality_mod_elim_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    non_empty_A: "A \<noteq> {}" and
    fin_A: "finite A" and
    prof: "profile V A p"
  shows "plurality V A p = plurality' V A p"
proof (unfold plurality.simps plurality'.simps plurality_score.simps, standard)
  have "fst (max_eliminator (\<lambda>V x A p. win_count V p x) V A p) = {}"
    by simp
  also have "... = fst ({},
             {a \<in> A. \<exists> b \<in> A. win_count V p a < win_count V p b},
             {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a})"
    by simp
  finally show 
    "fst (max_eliminator (\<lambda>V x A p. win_count V p x) V A p) =
      fst ({}, 
            {a \<in> A. \<exists>b\<in>A. win_count V p a < win_count V p b}, 
            {a \<in> A. \<forall>b\<in>A. win_count V p b \<le> win_count V p a})"
    by simp
next
  let ?no_max = "{a \<in> A. win_count V p a < Max {win_count V p x |x. x \<in> A}} = A"
  have "?no_max \<Longrightarrow> {win_count V p x |x. x \<in> A} \<noteq> {}"
    using non_empty_A
    by blast
  moreover have "finite {win_count V p x |x. x \<in> A}"
    using fin_A
    by simp
  ultimately have exists_max: "?no_max \<Longrightarrow> False"
    using Max_in
    by fastforce
  have rej_eq:
    "snd (max_eliminator (\<lambda> V b A p. win_count V p b) V A p) =
      snd ({}, 
            {a \<in> A. \<exists>x\<in>A. win_count V p a < win_count V p x}, 
            {a \<in> A. \<forall>x\<in>A. win_count V p x \<le> win_count V p a})"
  proof (simp del: win_count.simps, safe)
    fix
      a :: "'a" and
      b :: "'a"
    assume
      "b \<in> A" and
      "win_count V p a < Max {win_count V p a' | a'. a' \<in> A}" and
      "\<not> win_count V p b < Max {win_count V p a' | a'. a' \<in> A}"
    thus "\<exists> b \<in> A. win_count V p a < win_count V p b"
      using dual_order.strict_trans1 not_le_imp_less
      by blast
  next
    fix
      a :: "'a" and
      b :: "'a"
    assume
      a_in_A: "a \<in> A" and
      b_in_A: "b \<in> A" and
      wc_a_lt_wc_b: "win_count V p a < win_count V p b"
    moreover have "\<forall> t. t b \<le> Max {n. \<exists> a'. (n::enat) = t a' \<and> a' \<in> A}"
    proof (safe)
      fix 
        t :: "'a \<Rightarrow> enat"
      have "t b \<in> {t a' |a'. a' \<in> A}"
        using b_in_A
        by auto
      thus "t b \<le> Max {t a' |a'. a' \<in> A}"
        using enat_leq_enat_set_max fin_A
        by auto
    qed
    ultimately show "win_count V p a < Max {win_count V p a' | a'. a' \<in> A}"
      using dual_order.strict_trans1
      by blast
  next
    fix
      a :: 'a and
      b :: 'a
    assume 
      a_in_A: "a \<in> A" and
      b_in_A: "b \<in> A" and
      wc_a_max: "\<not> win_count V p a < Max {win_count V p x |x. x \<in> A}"
    have "win_count V p b \<in> {win_count V p x |x. x \<in> A}"
      using b_in_A
      by auto
    hence "win_count V p b \<le> Max {win_count V p x |x. x \<in> A}"
      using b_in_A fin_A enat_leq_enat_set_max
      by auto
    thus "win_count V p b \<le> win_count V p a"
      using wc_a_max
      by (meson dual_order.strict_trans1 linorder_le_less_linear)
  next
    fix
      a :: 'a and
      b :: 'a
    assume 
      a_in_A: "a \<in> A" and
      b_in_A: "b \<in> A" and
      wc_a_max: "\<forall>x\<in>A. win_count V p x \<le> win_count V p a" and
      wc_a_not_max: "win_count V p a < Max {win_count V p x |x. x \<in> A}"
    have "win_count V p b \<le> win_count V p a"
      using b_in_A wc_a_max
      by auto
    thus "win_count V p b < Max {win_count V p x |x. x \<in> A}"
      using wc_a_not_max
      by simp
  next
    assume ?no_max
    thus "False"
      by (rule exists_max)
  next
    fix
      a :: 'a and
      b :: 'a
    assume 
      ?no_max
    thus "win_count V p a \<le> win_count V p b"
      using exists_max
      by simp
  qed
  thus "snd (max_eliminator (\<lambda> V b A p. win_count V p b) V A p) =
    snd ({},
         {a \<in> A. \<exists> b \<in> A. win_count V p a < win_count V p b},
         {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a})"
    using rej_eq snd_conv
    by metis
qed

subsection \<open>Soundness\<close>

theorem plurality_sound[simp]: "social_choice_result.electoral_module plurality"
  unfolding plurality.simps
  using max_elim_sound
  by metis

theorem plurality'_sound[simp]: "social_choice_result.electoral_module plurality'"
proof (unfold social_choice_result.electoral_module_def, safe)
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
    by auto
  ultimately show "well_formed A (plurality' V A p)"
    by simp
qed

subsection \<open>Non-Blocking\<close>

text \<open>
  The plurality module is non-blocking.
\<close>

theorem plurality_mod_non_blocking[simp]: "non_blocking plurality"
  unfolding plurality.simps
  using max_elim_non_blocking
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
  by (simp add: non_electing_def) 

subsection \<open>Property\<close>

lemma plurality_def_inv_mono_2:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    defer_a: "a \<in> defer V plurality A p" and
    lift_a: "lifted V A p q a"
  shows "defer V plurality A q = defer V plurality A p \<or> defer V plurality A q = {a}"
proof -
  have set_disj: "\<forall> b c. (b::'a) \<notin> {c} \<or> b = c"
    by force
  have lifted_winner:
    "\<forall> b \<in> A.
      \<forall> i \<in> V. (above (p i) b = {b} \<longrightarrow> (above (q i) b = {b} \<or> above (q i) a = {a}))"
    using lift_a lifted_above_winner
    unfolding Profile.lifted_def
    by metis
  hence "\<forall> i \<in> V. (above (p i) a = {a} \<longrightarrow> above (q i) a = {a})"
    using defer_a lift_a
    unfolding Profile.lifted_def
    by metis
  hence a_win_subset:
    "{i\<in>V. above (p i) a = {a}} \<subseteq> {i\<in>V. above (q i) a = {a}}"
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
  hence
    "\<forall> b \<in> A - {a}.
      \<forall> i \<in> V. (above (q i) a = {a} \<longrightarrow> above (q i) b \<noteq> {b})"
    using DiffE above_one_2 lift_a insertCI insert_absorb insert_not_empty
    unfolding Profile.lifted_def profile_def
    by metis
  with lifted_winner
  have above_QtoP:
    "\<forall> b \<in> A - {a}.
      \<forall> i \<in> V. (above (q i) b = {b} \<longrightarrow> above (p i) b = {b})"
    using lifted_above_winner_3 lift_a
    unfolding Profile.lifted_def
    by metis
  hence "\<forall> b \<in> A - {a}.
          {i \<in> V. above (q i) b = {b}} \<subseteq> {i \<in> V. above (p i) b = {b}}"
    by (simp add: Collect_mono)
  hence win_count_other: "\<forall> b \<in> A - {a}. win_count V p b \<ge> win_count V q b"
    by (simp add: card_mono)
  show "defer V plurality A q = defer V plurality A p \<or> defer V plurality A q = {a}"
  proof (cases)
    assume "win_count V p a = win_count V q a"
    hence "card {i \<in> V. above (p i) a = {a}} = card {i \<in> V. above (q i) a = {a}}"
      using win_count.simps Profile.lifted_def enat.inject lift_a
      by (metis (mono_tags, lifting))
    moreover have "finite {i \<in> V. above (q i) a = {a}}"
      by (metis (mono_tags) Collect_mem_eq Profile.lifted_def finite_Collect_conjI lift_a)
    ultimately have
      "{i \<in> V. above (p i) a = {a}} = {i \<in> V. above (q i) a = {a}}"
      using a_win_subset
      by (simp add: card_subset_eq)
    hence above_pq:
      "\<forall> i \<in> V. (above (p i) a = {a}) = (above (q i) a = {a})"
      by blast
    moreover have
      "\<forall> b \<in> A - {a}.
        \<forall> i \<in> V.
          (above (p i) b = {b} \<longrightarrow> (above (q i) b = {b} \<or> above (q i) a = {a}))"
      using lifted_winner
      by auto
    moreover have
      "\<forall> b \<in> A - {a}.
        \<forall> i \<in> V. (above (p i) b = {b} \<longrightarrow> above (p i) a \<noteq> {a})"
    proof (rule ccontr, simp, safe, simp)
      fix
        b :: "'a" and
        i :: "'v"
      assume
        b_in_A: "b \<in> A" and
        i_is_voter: "i \<in> V" and
        abv_b: "above (p i) b = {b}" and
        abv_a: "above (p i) a = {a}"
      moreover from b_in_A
      have "A \<noteq> {}"
        by auto
      moreover from i_is_voter
      have "linear_order_on A (p i)"
        using lift_a
        unfolding Profile.lifted_def profile_def
        by simp
      ultimately show "b = a"
        using fin_A above_one_2
        by metis
    qed
    ultimately have above_PtoQ:
      "\<forall> b \<in> A - {a}. \<forall> i \<in> V. (above (p i) b = {b} \<longrightarrow> above (q i) b = {b})"
      by simp
    hence "\<forall> b \<in> A.
            card {i \<in> V. above (p i) b = {b}} =
              card {i \<in> V. above (q i) b = {b}}"
    proof (safe)
      fix b :: "'a"
      assume
        above_c:
          "\<forall> c \<in> A - {a}. \<forall> i \<in> V. above (p i) c = {c} \<longrightarrow> above (q i) c = {c}" and
        b_in_A: "b \<in> A"
      show "card {i \<in> V. above (p i) b = {b}} =
              card {i \<in> V. above (q i) b = {b}}"
        using DiffI b_in_A set_disj above_PtoQ above_QtoP above_pq
        by (metis (no_types, lifting))
    qed
    hence "{b \<in> A. \<forall> c \<in> A. win_count V p c \<le> win_count V p b} =
              {b \<in> A. \<forall> c \<in> A. win_count V q c \<le> win_count V q b}"
      by auto
    hence "defer V plurality' A q = defer V plurality' A p \<or> defer V plurality' A q = {a}"
      by simp
    hence "defer V plurality A q = defer V plurality A p \<or> defer V plurality A q = {a}"
      using plurality_mod_elim_equiv empty_not_insert insert_absorb lift_a
      unfolding Profile.lifted_def
      by (metis (no_types, opaque_lifting))
    thus ?thesis
      by simp
  next
    assume "win_count V p a \<noteq> win_count V q a"
    hence strict_less: "win_count V p a < win_count V q a"
      using win_count_a
      by simp
    have "a \<in> defer V plurality A p"
      using defer_a plurality.elims
      by (metis (no_types))
    moreover have non_empty_A: "A \<noteq> {}"
      using lift_a equals0D equiv_prof_except_a_def lifted_imp_equiv_prof_except_a
      by metis
    moreover have fin_A: "finite_profile V A p"
      using lift_a
      unfolding Profile.lifted_def
      by simp
    ultimately have "a \<in> defer V plurality' A p"
      using plurality_mod_elim_equiv
      by metis
    hence a_in_win_p: "a \<in> {b \<in> A. \<forall> c \<in> A. win_count V p c \<le> win_count V p b}"
      by simp
    hence "\<forall> b \<in> A. win_count V p b \<le> win_count V p a"
      by simp
    hence less: "\<forall> b \<in> A - {a}. win_count V q b < win_count V q a"
      using DiffD1 antisym dual_order.trans not_le_imp_less win_count_a strict_less
            win_count_other
      by metis
    hence "\<forall> b \<in> A - {a}. \<not> (\<forall> c \<in> A. win_count V q c \<le> win_count V q b)"
      using lift_a not_le
      unfolding Profile.lifted_def
      by metis
    hence "\<forall> b \<in> A - {a}. b \<notin> {c \<in> A. \<forall> b \<in> A. win_count V q b \<le> win_count V q c}"
      by blast
    hence "\<forall> b \<in> A - {a}. b \<notin> defer V plurality' A q"
      by simp
    hence "\<forall> b \<in> A - {a}. b \<notin> defer V plurality A q"
      using lift_a non_empty_A plurality_mod_elim_equiv
      unfolding Profile.lifted_def
      by (metis (no_types, lifting))
    hence "\<forall> b \<in> A - {a}. b \<notin> defer V plurality A q"
      by simp
    moreover have "a \<in> defer V plurality A q"
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
      ultimately have "a \<in> {b \<in> A. \<forall> c \<in> A. win_count V q c \<le> win_count V q b}"
        by simp
      hence "a \<in> defer V plurality' A q"
        by simp
      hence "a \<in> defer V plurality A q"
        using plurality_mod_elim_equiv non_empty_A fin_A lift_a non_empty_A
        unfolding Profile.lifted_def
        by (metis (no_types))
      thus ?thesis
        by simp
    qed
    moreover have "defer V plurality A q \<subseteq> A"
      by simp
    ultimately show ?thesis
      by blast
  qed
qed

text \<open>
  The plurality rule is invariant-monotone.
\<close>

theorem plurality_mod_def_inv_mono[simp]: "defer_invariant_monotonicity plurality"
proof (unfold defer_invariant_monotonicity_def, intro conjI impI allI)
  show "social_choice_result.electoral_module plurality"
    by simp
next
  show "non_electing plurality"
    by simp
next
  fix
    A :: "'b set" and 
    V :: "'a set" and 
    p :: "('b, 'a) Profile" and 
    q :: "('b, 'a) Profile" and
    a :: 'b
  assume "a \<in> snd (snd (plurality V A p)) \<and> Profile.lifted V A p q a"
  hence "defer V plurality A q = defer V plurality A p \<or> defer V plurality A q = {a}"
    using plurality_def_inv_mono_2
    by metis
  thus "snd (snd (plurality V A q)) = snd (snd (plurality V A p)) \<or> snd (snd (plurality V A q)) = {a}"
    by auto
qed

end

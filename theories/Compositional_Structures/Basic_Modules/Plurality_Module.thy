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

fun plurality_score :: "'a Evaluation_Function" where
  "plurality_score x A p = win_count p x"

fun plurality :: "'a Electoral_Module" where
  "plurality A p = max_eliminator plurality_score A p"

fun plurality' :: "'a Electoral_Module" where
  "plurality' A p =
    ({},
     {a \<in> A. \<exists> x \<in> A. win_count p x > win_count p a},
     {a \<in> A. \<forall> x \<in> A. win_count p x \<le> win_count p a})"

lemma plurality_mod_elim_equiv:
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    non_empty_A: "A \<noteq> {}" and
    fin_prof_A: "finite_profile A p"
  shows "plurality A p = plurality' A p"
proof (unfold plurality.simps plurality'.simps plurality_score.simps, standard)
  show "elect (max_eliminator (\<lambda> x A p. win_count p x)) A p =
    elect_r ({},
             {a \<in> A. \<exists> b \<in> A. win_count p a < win_count p b},
             {a \<in> A. \<forall> b \<in> A. win_count p b \<le> win_count p a})"
    using max_elim_non_electing fin_prof_A
    by simp
next
  have rej_eq:
    "reject (max_eliminator (\<lambda> b A p. win_count p b)) A p =
      {a \<in> A. \<exists> b \<in> A. win_count p a < win_count p b}"
  proof (simp del: win_count.simps, safe)
    fix
      a :: "'a" and
      b :: "'a"
    assume
      "b \<in> A" and
      "win_count p a < Max {win_count p a' | a'. a' \<in> A}" and
      "\<not> win_count p b < Max {win_count p a' | a'. a' \<in> A}"
    thus "\<exists> b \<in> A. win_count p a < win_count p b"
      using dual_order.strict_trans1 not_le_imp_less
      by blast
  next
    fix
      a :: "'a" and
      b :: "'a"
    assume
      b_in_A: "b \<in> A" and
      wc_a_lt_wc_b: "win_count p a < win_count p b"
    moreover have "\<forall> t. t b \<le> Max {n. \<exists> a'. (n::nat) = t a' \<and> a' \<in> A}"
      using fin_prof_A b_in_A
      by (simp add: score_bounded)
    ultimately show "win_count p a < Max {win_count p a' | a'. a' \<in> A}"
      using dual_order.strict_trans1
      by blast
  next
    assume "{a \<in> A. win_count p a < Max {win_count p b | b. b \<in> A}} = A"
    hence "A = {}"
      using max_score_contained[where A=A and e="(\<lambda> a. win_count p a)"]
            fin_prof_A nat_less_le
      by blast
    thus "False"
      using non_empty_A
      by simp
  qed
  have "defer (max_eliminator (\<lambda> x A p. win_count p x)) A p =
    {a \<in> A. \<forall> a' \<in> A. win_count p a' \<le> win_count p a}"
  proof (auto simp del: win_count.simps)
    fix
      a :: "'a" and
      b :: "'a"
    assume
      "a \<in> A" and
      "b \<in> A" and
      "\<not> win_count p a < Max {win_count p a' | a'. a' \<in> A}"
    moreover from this
    have "win_count p a = Max {win_count p a' | a'. a' \<in> A}"
      using score_bounded[where A=A and e ="(\<lambda> a'. win_count p a')"] fin_prof_A
            order_le_imp_less_or_eq
      by blast
    ultimately show "win_count p b \<le> win_count p a"
      using score_bounded[where A= A and e = "(\<lambda> x. win_count p x)"] fin_prof_A
      by presburger
  next
    fix
      a :: "'a" and
      b :: "'a"
    assume "{a' \<in> A. win_count p a' < Max {win_count p b' | b'. b' \<in> A}} = A"
    hence "A = {}"
      using max_score_contained[where A= A and e = "(\<lambda> x. win_count p x)"]
            fin_prof_A nat_less_le
      by auto
    thus "win_count p a \<le> win_count p b"
      using non_empty_A
      by simp
  qed
  thus "snd (max_eliminator (\<lambda> b A p. win_count p b) A p) =
    snd ({},
         {a \<in> A. \<exists> b \<in> A. win_count p a < win_count p b},
         {a \<in> A. \<forall> b \<in> A. win_count p b \<le> win_count p a})"
    using rej_eq prod.collapse snd_conv
    by metis
qed

subsection \<open>Soundness\<close>

theorem plurality_sound[simp]: "electoral_module plurality"
  unfolding plurality.simps
  using max_elim_sound
  by metis

theorem plurality'_sound[simp]: "electoral_module plurality'"
proof (unfold electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  have "disjoint3 (
      {},
      {a \<in> A. \<exists> a' \<in> A. win_count p a < win_count p a'},
      {a \<in> A. \<forall> a' \<in> A. win_count p a' \<le> win_count p a})"
    by auto
  moreover have
    "{a \<in> A. \<exists> x \<in> A. win_count p a < win_count p x} \<union>
      {a \<in> A. \<forall> x \<in> A. win_count p x \<le> win_count p a} = A"
    using not_le_imp_less
    by auto
  ultimately show "well_formed A (plurality' A p)"
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
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assumes
    defer_a: "a \<in> defer plurality A p" and
    lift_a: "lifted A p q a"
  shows "defer plurality A q = defer plurality A p \<or> defer plurality A q = {a}"
proof -
  have set_disj: "\<forall> b c. (b::'a) \<notin> {c} \<or> b = c"
    by force
  have lifted_winner:
    "\<forall> b \<in> A.
      \<forall> i::nat. i < length p \<longrightarrow>
        (above (p!i) b = {b} \<longrightarrow> (above (q!i) b = {b} \<or> above (q!i) a = {a}))"
    using lift_a lifted_above_winner
    unfolding Profile.lifted_def
    by (metis (no_types, lifting))
  hence "\<forall> i::nat. i < length p \<longrightarrow> (above (p!i) a = {a} \<longrightarrow> above (q!i) a = {a})"
    using defer_a lift_a
    unfolding Profile.lifted_def
    by metis
  hence a_win_subset:
    "{i::nat. i < length p \<and> above (p!i) a = {a}} \<subseteq>
        {i::nat. i < length p \<and> above (q!i) a = {a}}"
    by blast
  moreover have sizes: "length p = length q"
    using lift_a
    unfolding Profile.lifted_def
    by metis
  ultimately have win_count_a: "win_count p a \<le> win_count q a"
    by (simp add: card_mono)
  have fin_A: "finite A"
    using lift_a
    unfolding Profile.lifted_def
    by metis
  hence
    "\<forall> b \<in> A - {a}.
      \<forall> i::nat. i < length p \<longrightarrow> (above (q!i) a = {a} \<longrightarrow> above (q!i) b \<noteq> {b})"
    using DiffE above_one_2 lift_a insertCI insert_absorb insert_not_empty sizes
    unfolding Profile.lifted_def profile_def
    by metis
  with lifted_winner
  have above_QtoP:
    "\<forall> b \<in> A - {a}.
      \<forall> i::nat. i < length p \<longrightarrow> (above (q!i) b = {b} \<longrightarrow> above (p!i) b = {b})"
    using lifted_above_winner_3 lift_a
    unfolding Profile.lifted_def
    by metis
  hence "\<forall> b \<in> A - {a}.
          {i::nat. i < length p \<and> above (q!i) b = {b}} \<subseteq>
            {i::nat. i < length p \<and> above (p!i) b = {b}}"
    by (simp add: Collect_mono)
  hence win_count_other: "\<forall> b \<in> A - {a}. win_count p b \<ge> win_count q b"
    by (simp add: card_mono sizes)
  show "defer plurality A q = defer plurality A p \<or> defer plurality A q = {a}"
  proof (cases)
    assume "win_count p a = win_count q a"
    hence "card {i::nat. i < length p \<and> above (p!i) a = {a}} =
            card {i::nat. i < length p \<and> above (q!i) a = {a}}"
      using sizes
      by simp
    moreover have "finite {i::nat. i < length p \<and> above (q!i) a = {a}}"
      by simp
    ultimately have
      "{i::nat. i < length p \<and> above (p!i) a = {a}} =
        {i::nat. i < length p \<and> above (q!i) a = {a}}"
      using a_win_subset
      by (simp add: card_subset_eq)
    hence above_pq:
      "\<forall> i::nat. i < length p \<longrightarrow> (above (p!i) a = {a}) = (above (q!i) a = {a})"
      by blast
    moreover have
      "\<forall> b \<in> A - {a}.
        \<forall> i::nat. i < length p \<longrightarrow>
          (above (p!i) b = {b} \<longrightarrow> (above (q!i) b = {b} \<or> above (q!i) a = {a}))"
      using lifted_winner
      by auto
    moreover have
      "\<forall> b \<in> A - {a}.
        \<forall> i::nat. i < length p \<longrightarrow> (above (p!i) b = {b} \<longrightarrow> above (p!i) a \<noteq> {a})"
    proof (rule ccontr, simp, safe, simp)
      fix
        b :: "'a" and
        i :: "nat"
      assume
        b_in_A: "b \<in> A" and
        i_in_range: "i < length p" and
        abv_b: "above (p!i) b = {b}" and
        abv_a: "above (p!i) a = {a}"
      moreover from b_in_A
      have "A \<noteq> {}"
        by auto
      moreover from i_in_range
      have "linear_order_on A (p!i)"
        using lift_a
        unfolding Profile.lifted_def profile_def
        by simp
      ultimately show "b = a"
        using fin_A above_one_2
        by metis
    qed
    ultimately have above_PtoQ:
      "\<forall> b \<in> A - {a}. \<forall> i::nat.
        i < length p \<longrightarrow> (above (p!i) b = {b} \<longrightarrow> above (q!i) b = {b})"
      by simp
    hence "\<forall> b \<in> A.
            card {i::nat. i < length p \<and> above (p!i) b = {b}} =
              card {i::nat. i < length q \<and> above (q!i) b = {b}}"
    proof (safe)
      fix b :: "'a"
      assume
        above_c:
          "\<forall> c \<in> A - {a}. \<forall> i < length p.
            above (p!i) c = {c} \<longrightarrow> above (q!i) c = {c}" and
        b_in_A: "b \<in> A"
      show "card {i. i < length p \<and> above (p!i) b = {b}} =
              card {i. i < length q \<and> above (q!i) b = {b}}"
        using DiffI b_in_A set_disj above_PtoQ above_QtoP above_pq sizes
        by (metis (no_types, lifting))
    qed
    hence "{b \<in> A. \<forall> c \<in> A. win_count p c \<le> win_count p b} =
              {b \<in> A. \<forall> c \<in> A. win_count q c \<le> win_count q b}"
      by auto
    hence "defer plurality' A q = defer plurality' A p \<or> defer plurality' A q = {a}"
      by simp
    hence "defer plurality A q = defer plurality A p \<or> defer plurality A q = {a}"
      using plurality_mod_elim_equiv empty_not_insert insert_absorb lift_a
      unfolding Profile.lifted_def
      by (metis (no_types, opaque_lifting))
    thus ?thesis
      by simp
  next
    assume "win_count p a \<noteq> win_count q a"
    hence strict_less: "win_count p a < win_count q a"
      using win_count_a
      by simp
    have "a \<in> defer plurality A p"
      using defer_a plurality.elims
      by (metis (no_types))
    moreover have non_empty_A: "A \<noteq> {}"
      using lift_a equals0D equiv_prof_except_a_def lifted_imp_equiv_prof_except_a
      by metis
    moreover have fin_A: "finite_profile A p"
      using lift_a
      unfolding Profile.lifted_def
      by simp
    ultimately have "a \<in> defer plurality' A p"
      using plurality_mod_elim_equiv
      by metis
    hence a_in_win_p: "a \<in> {b \<in> A. \<forall> c \<in> A. win_count p c \<le> win_count p b}"
      by simp
    hence "\<forall> b \<in> A. win_count p b \<le> win_count p a"
      by simp
    hence less: "\<forall> b \<in> A - {a}. win_count q b < win_count q a"
      using DiffD1 antisym dual_order.trans not_le_imp_less win_count_a strict_less
            win_count_other
      by metis
    hence "\<forall> b \<in> A - {a}. \<not> (\<forall> c \<in> A. win_count q c \<le> win_count q b)"
      using lift_a not_le
      unfolding Profile.lifted_def
      by metis
    hence "\<forall> b \<in> A - {a}. b \<notin> {c \<in> A. \<forall> b \<in> A. win_count q b \<le> win_count q c}"
      by blast
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality' A q"
      by simp
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality A q"
      using lift_a non_empty_A plurality_mod_elim_equiv
      unfolding Profile.lifted_def
      by (metis (no_types, lifting))
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality A q"
      by simp
    moreover have "a \<in> defer plurality A q"
    proof -
      have "\<forall> b \<in> A - {a}. win_count q b \<le> win_count q a"
        using less less_imp_le
        by metis
      moreover have "win_count q a \<le> win_count q a"
        by simp
      ultimately have "\<forall> b \<in> A. win_count q b \<le> win_count q a"
        by auto
      moreover have "a \<in> A"
        using a_in_win_p
        by simp
      ultimately have "a \<in> {b \<in> A. \<forall> c \<in> A. win_count q c \<le> win_count q b}"
        by simp
      hence "a \<in> defer plurality' A q"
        by simp
      hence "a \<in> defer plurality A q"
        using plurality_mod_elim_equiv non_empty_A fin_A lift_a non_empty_A
        unfolding Profile.lifted_def
        by (metis (no_types))
      thus ?thesis
        by simp
    qed
    moreover have "defer plurality A q \<subseteq> A"
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
  show "electoral_module plurality"
    by simp
next
  show "non_electing plurality"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume "a \<in> defer plurality A p \<and> Profile.lifted A p q a"
  thus "defer plurality A q = defer plurality A p \<or> defer plurality A q = {a}"
    using plurality_def_inv_mono_2
    by metis
qed

end

(*  File:       Plurality_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Plurality Module\<close>

theory Plurality_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  The plurality module implements the plurality voting rule.
  The plurality rule elects all modules with the maximum amount of top
  preferences among all alternatives, and rejects all the other alternatives.
  It is electing and induces the classical plurality (voting) rule
  from social-choice theory.
\<close>

subsection \<open>Definition\<close>

fun plurality :: "'a Electoral_Module" where
  "plurality A p =
    ({a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a},
     {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a},
     {})"

subsection \<open>Soundness\<close>

theorem plurality_sound[simp]: "electoral_module plurality"
proof (unfold electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  have disjoint:
    "let elect = {a \<in> (A::'a set). \<forall> x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists> x \<in> A. win_count p a < win_count p x} in
    disjoint3 (elect, reject, {})"
    by auto
  have
    "let elect = {a \<in> (A::'a set). \<forall> x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists> x \<in> A. win_count p a < win_count p x} in
    elect \<union> reject = A"
    using not_le_imp_less
    by auto
  with disjoint
  show "well_formed A (plurality A p)"
    by simp
qed

subsection \<open>Electing\<close>

lemma plurality_electing2: "\<forall> A p.
                              (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow>
                                elect plurality A p \<noteq> {}"
proof (clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    A_non_empty: "A \<noteq> {}" and
    fin_A: "finite A" and
    prof_p: "profile A p" and
    plurality_elect_none: "elect plurality A p = {}"
  obtain max where
    max: "max = Max (win_count p ` A)"
    by simp
  then obtain a where
    a: "win_count p a = max \<and> a \<in> A"
    using Max_in A_non_empty fin_A empty_is_image
          finite_imageI imageE
    by (metis (no_types, lifting))
  hence "\<forall> x \<in> A. win_count p x \<le> win_count p a"
    using A_non_empty fin_A max
    by simp
  moreover have "a \<in> A"
    using a
    by simp
  ultimately have
    "a \<in> {a \<in> A. \<forall> x \<in> A. win_count p x \<le> win_count p a}"
    by blast
  hence "a \<in> elect plurality A p"
    by simp
  thus False
    using plurality_elect_none all_not_in_conv
    by metis
qed

text \<open>
  The plurality module is electing.
\<close>

theorem plurality_electing[simp]: "electing plurality"
proof (unfold electing_def, safe)
  show "electoral_module plurality"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    elect_none: "elect plurality A p = {}" and
    x_in_A: "x \<in> A"
  have "\<forall> A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect plurality A p \<noteq> {}"
    using plurality_electing2
    by simp
  hence empty_A: "A = {}"
    using fin_A prof_p elect_none
    by (metis (no_types))
  thus "x \<in> {}"
    using x_in_A
    by simp
qed

subsection \<open>Property\<close>

lemma plurality_inv_mono2: "\<forall> A p q a.
                              (a \<in> elect plurality A p \<and> lifted A p q a) \<longrightarrow>
                                (elect plurality A q = elect plurality A p \<or>
                                    elect plurality A q = {a})"
proof (intro allI impI)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume elect_and_lift_a: "a \<in> elect plurality A p \<and> lifted A p q a"
  have ab1: "\<forall> a b. (a::'a) \<notin> {b} \<or> a = b"
    by force
  have lifted_winner:
    "\<forall> x \<in> A.
      \<forall> i::nat. i < length p \<longrightarrow>
        (above (p!i) x = {x} \<longrightarrow>
          (above (q!i) x = {x} \<or> above (q!i) a = {a}))"
    using elect_and_lift_a lifted_above_winner
    unfolding Profile.lifted_def
    by (metis (no_types, lifting))
  hence
    "\<forall> i::nat. i < length p \<longrightarrow>
      (above (p!i) a = {a} \<longrightarrow> above (q!i) a = {a})"
    using elect_and_lift_a
    by auto
  hence a_win_subset:
    "{i::nat. i < length p \<and> above (p!i) a = {a}} \<subseteq>
      {i::nat. i < length p \<and> above (q!i) a = {a}}"
    by blast
  moreover have sizes: "length p = length q"
    using elect_and_lift_a
    unfolding Profile.lifted_def
    by metis
  ultimately have win_count_a:
    "win_count p a \<le> win_count q a"
    by (simp add: card_mono)
  have fin_A: "finite A"
    using elect_and_lift_a
    unfolding Profile.lifted_def
    by metis
  hence
    "\<forall> x \<in> A - {a}.
      \<forall> i::nat. i < length p \<longrightarrow>
        (above (q!i) a = {a} \<longrightarrow> above (q!i) x \<noteq> {x})"
    using DiffE above_one2 elect_and_lift_a insertCI insert_absorb insert_not_empty sizes
    unfolding Profile.lifted_def profile_def
    by metis
  with lifted_winner
  have above_QtoP:
    "\<forall> x \<in> A - {a}.
      \<forall> i::nat. i < length p \<longrightarrow>
        (above (q!i) x = {x} \<longrightarrow> above (p!i) x = {x})"
    using lifted_above_winner3 elect_and_lift_a
    unfolding Profile.lifted_def
    by metis
  hence
    "\<forall> x \<in> A - {a}.
      {i::nat. i < length p \<and> above (q!i) x = {x}} \<subseteq>
        {i::nat. i < length p \<and> above (p!i) x = {x}}"
    by (simp add: Collect_mono)
  hence win_count_other:
    "\<forall> x \<in> A - {a}. win_count p x \<ge> win_count q x"
    by (simp add: card_mono sizes)
  show
    "elect plurality A q = elect plurality A p \<or>
      elect plurality A q = {a}"
  proof cases
    assume "win_count p a = win_count q a"
    hence
      "card {i::nat. i < length p \<and> above (p!i) a = {a}} =
        card {i::nat. i < length p \<and> above (q!i) a = {a}}"
      using sizes
      by simp
    moreover have
      "finite {i::nat. i < length p \<and> above (q!i) a = {a}}"
      by simp
    ultimately have
      "{i::nat. i < length p \<and> above (p!i) a = {a}} =
        {i::nat. i < length p \<and> above (q!i) a = {a}}"
      using a_win_subset
      by (simp add: card_subset_eq)
    hence above_pq:
      "\<forall> i::nat. i < length p \<longrightarrow>
        above (p!i) a = {a} \<longleftrightarrow> above (q!i) a = {a}"
      by blast
    hence above_pq2:
      "\<forall> n. \<not> n < length p \<or>
        (above (p!n) a = {a}) = (above (q!n) a = {a})"
      by presburger
    moreover have
      "\<forall> x \<in> A - {a}.
        \<forall> i::nat. i < length p \<longrightarrow>
          (above (p!i) x = {x} \<longrightarrow>
            (above (q!i) x = {x} \<or> above (q!i) a = {a}))"
      using lifted_winner
      by auto
    moreover have
      "\<forall> x \<in> A - {a}.
        \<forall> i::nat. i < length p \<longrightarrow>
          (above (p!i) x = {x} \<longrightarrow> above (p!i) a \<noteq> {a})"
    proof (rule ccontr, simp, safe, simp)
      fix
        x :: "'a" and
        i :: "nat"
      assume
        x_in_A: "x \<in> A" and
        i_in_range: "i < length p" and
        abv_x: "above (p!i) x = {x}" and
        abv_a: "above (p!i) a = {a}"
      have not_empty: "A \<noteq> {}"
        using x_in_A
        by auto
      have "linear_order_on A (p!i)"
        using elect_and_lift_a i_in_range
        unfolding Profile.lifted_def profile_def
        by simp
      thus "x = a"
        using not_empty abv_a abv_x fin_A above_one2
        by metis
    qed
    ultimately have above_PtoQ:
      "\<forall> x \<in> A - {a}.
        \<forall> i::nat. i < length p \<longrightarrow>
          (above (p!i) x = {x} \<longrightarrow> above (q!i) x = {x})"
      by simp
    hence
      "\<forall> x \<in> A.
        card {i::nat. i < length p \<and> above (p!i) x = {x}} =
          card {i::nat. i < length q \<and> above (q!i) x = {x}}"
    proof (safe)
      fix x :: "'a"
      assume
        "\<forall> y \<in> A - {a}. \<forall> i < length p.
          above (p!i) y = {y} \<longrightarrow> above (q!i) y = {y}" and
        x_in_A: "x \<in> A"
      show
        "card {i. i < length p \<and> above (p!i) x = {x}} =
          card {i. i < length q \<and> above (q!i) x = {x}}"
        using DiffI x_in_A ab1 above_PtoQ above_QtoP above_pq2 sizes
        by (metis (no_types, lifting))
    qed
    hence "\<forall> x \<in> A. win_count p x = win_count q x"
      by simp
    hence
      "{a \<in> A. \<forall> x \<in> A. win_count p x \<le> win_count p a} =
        {a \<in> A. \<forall> x \<in> A. win_count q x \<le> win_count q a}"
      by auto
    thus ?thesis
      by simp
  next
    assume "win_count p a \<noteq> win_count q a"
    hence strict_less:
      "win_count p a < win_count q a"
      using win_count_a
      by simp
    have a_in_win_p:
      "a \<in> {a \<in> A. \<forall> x \<in> A. win_count p x \<le> win_count p a}"
      using elect_and_lift_a
      by simp
    hence "\<forall> x \<in> A. win_count p x \<le> win_count p a"
      by simp
    with strict_less win_count_other
    have less:
      "\<forall> x \<in> A - {a}. win_count q x < win_count q a"
      using DiffD1 antisym dual_order.trans
            not_le_imp_less win_count_a
      by metis
    hence
      "\<forall> x \<in> A - {a}. \<not>(\<forall>y \<in> A. win_count q y \<le> win_count q x)"
      using elect_and_lift_a not_le
      unfolding Profile.lifted_def
      by metis
    hence
      "\<forall> x \<in> A - {a}.
        x \<notin> {a \<in> A. \<forall> x \<in> A. win_count q x \<le> win_count q a}"
      by blast
    hence
      "\<forall> x \<in> A - {a}. x \<notin> elect plurality A q"
      by simp
    moreover have
      "a \<in> elect plurality A q"
    proof -
      from less
      have
        "\<forall> x \<in> A - {a}. win_count q x \<le> win_count q a"
        using less_imp_le
        by metis
      moreover have
        "win_count q a \<le> win_count q a"
        by simp
      ultimately have
        "\<forall> x \<in> A. win_count q x \<le> win_count q a"
        by auto
      moreover have
        "a \<in> A"
        using a_in_win_p
        by simp
      ultimately have
        "a \<in> {a \<in> A.
            \<forall> x \<in> A. win_count q x \<le> win_count q a}"
        by simp
      thus ?thesis
        by simp
    qed
    moreover have
      "elect plurality A q \<subseteq> A"
      by simp
    ultimately show ?thesis
      by auto
  qed
qed

text \<open>
  The plurality rule is invariant-monotone.
\<close>

theorem plurality_inv_mono[simp]: "invariant_monotonicity plurality"
proof (unfold invariant_monotonicity_def, intro conjI impI allI)
  show "electoral_module plurality"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume "a \<in> elect plurality A p \<and> Profile.lifted A p q a"
  thus "elect plurality A q = elect plurality A p \<or> elect plurality A q = {a}"
    using plurality_inv_mono2
    by metis
qed

end

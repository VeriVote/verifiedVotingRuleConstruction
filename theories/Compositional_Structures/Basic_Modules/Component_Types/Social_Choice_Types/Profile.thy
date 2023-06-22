(*  File:       Profile.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Preference Profile\<close>

theory Profile
  imports Preference_Relation
begin

text \<open>
  Preference profiles denote the decisions made by the individual voters on
  the eligible alternatives. They are represented in the form of one preference
  relation (e.g., selected on a ballot) per voter, collectively captured in a
  list of such preference relations.
  Unlike a the common preference profiles in the social-choice sense, the
  profiles described here considers only the (sub-)set of alternatives that are
  received.
\<close>

subsection \<open>Definition\<close>

text \<open>
  A profile contains one ballot for each voter.
\<close>

type_synonym 'a Profile = "('a Preference_Relation) list"

type_synonym 'a Election = "'a set \<times> 'a Profile"

text \<open>
  A profile on a finite set of alternatives A contains only ballots that are
  linear orders on A.
\<close>

definition profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "profile A p \<equiv> \<forall> i::nat. i < length p \<longrightarrow> linear_order_on A (p!i)"

lemma profile_set :
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  shows "profile A p \<equiv> (\<forall> b \<in> (set p). linear_order_on A b)"
  unfolding profile_def all_set_conv_all_nth
  by simp

abbreviation finite_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "finite_profile A p \<equiv> finite A \<and> profile A p"

subsection \<open>Preference Counts and Comparisons\<close>

text \<open>
  The win count for an alternative a in a profile p is
  the amount of ballots in p that rank alternative a in first position.
\<close>

fun win_count :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count p a =
    card {i::nat. i < length p \<and> above (p!i) a = {a}}"

fun win_count_code :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count_code Nil a = 0" |
  "win_count_code (p#ps) a =
      (if (above p a = {a}) then 1 else 0) + win_count_code ps a"

lemma win_count_equiv[code]:
  fixes
    p :: "'a Profile" and
    x :: "'a"
  shows "win_count p x = win_count_code p x"
proof (induction p rule: rev_induct, simp)
  case (snoc a p)
  fix
    a :: "'a Preference_Relation" and
    p :: "'a Profile"
  assume base_case: "win_count p x = win_count_code p x"
  have size_one: "length [a] = 1"
    by simp
  have p_pos_in_ps: "\<forall> i < length p. p!i = (p@[a])!i"
    by (simp add: nth_append)
  have
    "win_count [a] x =
      (let q = [a] in
        card {i::nat. i < length q \<and>
              (let r = (q!i) in (above r x = {x}))})"
    by simp
  hence one_ballot_equiv: "win_count [a] x = win_count_code [a] x"
    using size_one
    by (simp add: nth_Cons')
  have pref_count_induct:
    "win_count (p@[a]) x =
      win_count p x + win_count [a] x"
  proof (simp)
    have
      "{i. i = 0 \<and> (above ([a]!i) x = {x})} =
        (if (above a x = {x}) then {0} else {})"
      by (simp add: Collect_conv_if)
    hence shift_idx_a:
      "card {i. i = length p \<and> (above ([a]!0) x = {x})} =
        card {i. i = 0 \<and> (above ([a]!i) x = {x})}"
      by simp
    have set_prof_eq:
      "{i. i < Suc (length p) \<and> (above ((p@[a])!i) x = {x})} =
        {i. i < length p \<and> (above (p!i) x = {x})} \<union>
          {i. i = length p \<and> (above ([a]!0) x = {x})}"
    proof (safe, simp_all)
      fix
        n :: nat and
        n' :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[a])!n) x = {x}" and
        "n \<noteq> length p" and
        "n' \<in> above (p!n) x"
      thus "n' = x"
        using less_antisym p_pos_in_ps singletonD
        by metis
    next
      fix n :: nat
      assume
        "n < Suc (length p)" and
        "above ((p@[a])!n) x = {x}" and
        "n \<noteq> length p"
      thus "x \<in> above (p!n) x"
        using less_antisym insertI1 p_pos_in_ps
        by metis
    next
      fix
        n :: nat and
        b :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[a])!n) x = {x}" and
        "b \<in> above a x" and
        "b \<noteq> x"
      thus "n < length p"
        using less_antisym nth_append_length
              p_pos_in_ps singletonD
        by metis
    next
      fix
        n :: nat and
        b :: "'a" and
        b' :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[a])!n) x = {x}" and
        "b \<in> above a x" and
        "b \<noteq> x" and
        "b' \<in> above (p!n) x"
      thus "b' = x"
        using less_antisym p_pos_in_ps
              nth_append_length singletonD
        by metis
    next
      fix
        n :: nat and
        b :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[a])!n) x = {x}" and
        "b \<in> above a x" and
        "b \<noteq> x"
      thus "x \<in> above (p!n) x"
        using insertI1 less_antisym nth_append
              nth_append_length singletonD
        by metis
    next
      fix n :: nat
      assume
        "n < Suc (length p)" and
        "above ((p@[a])!n) x = {x}" and
        "x \<notin> above a x"
      thus "n < length p"
        using insertI1 less_antisym nth_append_length
        by metis
    next
      fix
        n :: nat and
        b :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[a])!n) x = {x}" and
        "x \<notin> above a x" and
        "b \<in> above (p!n) x"
      thus "b = x"
        using insertI1 less_antisym nth_append_length
              p_pos_in_ps singletonD
        by metis
    next
      fix n :: nat
      assume
        "n < Suc (length p)" and
        "above ((p@[a])!n) x = {x}" and
        "x \<notin> above a x"
      thus "x \<in> above (p!n) x"
        using insertI1 less_antisym nth_append_length p_pos_in_ps
        by metis
    next
      fix
        n :: nat and
        b :: "'a"
      assume
        "n < length p" and
        "above (p!n) x = {x}" and
        "b \<in> above ((p@[a])!n) x"
      thus "b = x"
        by (simp add: nth_append)
    next
      fix n :: nat
      assume
        "n < length p" and
        "above (p!n) x = {x}"
      thus "x \<in> above ((p@[a])!n) x"
        by (simp add: nth_append)
    qed
    have fin_len_p:
      "finite {n. n < length p \<and> (above (p!n) x = {x})}"
      by simp
    have fin_len_a_0:
      "finite {n. n = length p \<and> (above ([a]!0) x = {x})}"
      by simp
    have
      "card ({i. i < length p \<and> (above (p!i) x = {x})} \<union>
        {i. i = length p \<and> (above ([a]!0) x = {x})}) =
          card {i. i < length p \<and> (above (p!i) x = {x})} +
            card {i. i = length p \<and> (above ([a]!0) x = {x})}"
      using fin_len_p fin_len_a_0 card_Un_disjoint
      by blast
    thus
      "card {i. i < Suc (length p) \<and> (above ((p@[a])!i) x = {x})} =
        card {i. i < length p \<and> (above (p!i) x = {x})} +
          card {i. i = 0 \<and> (above ([a]!i) x = {x})}"
      using set_prof_eq shift_idx_a
      by auto
  qed
  have "win_count_code (p@[a]) x = win_count_code p x + win_count_code [a] x"
  proof (induction p, simp)
    fix
      r :: "'a Preference_Relation" and
      q :: "'a Profile"
    assume
      "win_count_code (q@[a]) x =
        win_count_code q x + win_count_code [a] x"
    thus
      "win_count_code ((r#q)@[a]) x =
        win_count_code (r#q) x + win_count_code [a] x"
      by simp
  qed
  thus "win_count (p@[a]) x = win_count_code (p@[a]) x"
    using pref_count_induct base_case one_ballot_equiv
    by presburger
qed

fun prefer_count :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count p x y =
      card {i::nat. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"

fun prefer_count_code :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count_code Nil x y = 0" |
  "prefer_count_code (p#ps) x y =
      (if y \<preceq>\<^sub>p x then 1 else 0) + prefer_count_code ps x y"

lemma pref_count_equiv[code]:
  fixes
    p :: "'a Profile" and
    x :: "'a" and
    y :: "'a"
  shows "prefer_count p x y = prefer_count_code p x y"
proof (induction p rule: rev_induct, simp)
  case (snoc a p)
  fix
    a :: "'a Preference_Relation" and
    p :: "'a Profile"
  assume base_case: "prefer_count p x y = prefer_count_code p x y"
  have size_one: "length [a] = 1"
    by simp
  have p_pos_in_ps:
    "\<forall> i < length p. p!i = (p@[a])!i"
    by (simp add: nth_append)
  have
    "prefer_count [a] x y =
      (let q = [a] in
        card {i::nat. i < length q \<and>
              (let r = (q!i) in (y \<preceq>\<^sub>r x))})"
    by simp
  hence one_ballot_equiv:
    "prefer_count [a] x y = prefer_count_code [a] x y"
    using size_one
    by (simp add: nth_Cons')
  have pref_count_induct:
    "prefer_count (p@[a]) x y =
      prefer_count p x y + prefer_count [a] x y"
  proof (simp)
    have
      "{i. i = 0 \<and> (y, x) \<in> [a]!i} =
        (if ((y, x) \<in> a) then {0} else {})"
      by (simp add: Collect_conv_if)
    hence shift_idx_a:
      "card {i. i = length p \<and> (y, x) \<in> [a]!0} =
        card {i. i = 0 \<and> (y, x) \<in> [a]!i}"
      by simp
    have set_prof_eq:
      "{i. i < Suc (length p) \<and> (y, x) \<in> (p@[a])!i} =
        {i. i < length p \<and> (y, x) \<in> p!i} \<union>
          {i. i = length p \<and> (y, x) \<in> [a]!0}"
    proof (safe, simp_all)
      fix xa :: nat
      assume
        "xa < Suc (length p)" and
        "(y, x) \<in> (p@[a])!xa" and
        "xa \<noteq> length p"
      thus "(y, x) \<in> p!xa"
        using less_antisym p_pos_in_ps
        by metis
    next
      fix xa :: nat
      assume
        "xa < Suc (length p)" and
        "(y, x) \<in> (p@[a])!xa" and
        "(y, x) \<notin> a"
      thus "xa < length p"
        using less_antisym nth_append_length
        by metis
    next
      fix xa :: nat
      assume
        "xa < Suc (length p)" and
        "(y, x) \<in> (p@[a])!xa" and
        "(y, x) \<notin> a"
      thus "(y, x) \<in> p!xa"
        using less_antisym nth_append_length p_pos_in_ps
        by metis
    next
      fix xa :: nat
      assume
        "xa < length p" and
        "(y, x) \<in> p!xa"
      thus "(y, x) \<in> (p@[a])!xa"
        using less_antisym p_pos_in_ps
        by metis
    qed
    have fin_len_p: "finite {n. n < length p \<and> (y, x) \<in> p!n}"
      by simp
    have fin_len_a_0: "finite {n. n = length p \<and> (y, x) \<in> [a]!0}"
      by simp
    have
      "card ({i. i < length p \<and> (y, x) \<in> p!i} \<union>
        {i. i = length p \<and> (y, x) \<in> [a]!0}) =
          card {i. i < length p \<and> (y, x) \<in> p!i} +
            card {i. i = length p \<and> (y, x) \<in> [a]!0}"
      using fin_len_p fin_len_a_0 card_Un_disjoint
      by blast
    thus
      "card {i. i < Suc (length p) \<and> (y, x) \<in> (p@[a])!i} =
        card {i. i < length p \<and> (y, x) \<in> p!i} +
          card {i. i = 0 \<and> (y, x) \<in> [a]!i}"
      using set_prof_eq shift_idx_a
      by simp
  qed
  have pref_count_code_induct:
    "prefer_count_code (p@[a]) x y =
      prefer_count_code p x y + prefer_count_code [a] x y"
  proof (simp, safe)
    assume y_pref_x: "(y, x) \<in> a"
    show "prefer_count_code (p@[a]) x y = Suc (prefer_count_code p x y)"
    proof (induction p, simp_all)
      show "(y, x) \<in> a"
        using y_pref_x
        by simp
    qed
  next
    assume not_y_pref_x: "(y, x) \<notin> a"
    show "prefer_count_code (p@[a]) x y = prefer_count_code p x y"
    proof (induction p, simp_all, safe)
      assume "(y, x) \<in> a"
      thus False
        using not_y_pref_x
        by simp
    qed
  qed
  show "prefer_count (p@[a]) x y = prefer_count_code (p@[a]) x y"
    using pref_count_code_induct pref_count_induct
          base_case one_ballot_equiv
    by presburger
qed

lemma set_compr:
  fixes
    S :: "'a set" and
    f :: "'a \<Rightarrow> 'a set"
  shows "{ f x | x. x \<in> S } = f ` S"
  by auto

lemma pref_count_set_compr:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  shows "{prefer_count p x y | y. y \<in> A - {x}} = (prefer_count p x) ` (A - {x})"
  by auto

lemma pref_count:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a" and
    y :: "'a"
  assumes
    prof: "profile A p" and
    x_in_A: "x \<in> A" and
    y_in_A: "y \<in> A" and
    neq: "x \<noteq> y"
  shows "prefer_count p x y = (length p) - (prefer_count p y x)"
proof -
  have "\<forall> i::nat. i < length p \<longrightarrow> connex A (p!i)"
    using prof
    unfolding profile_def
    by (simp add: lin_ord_imp_connex)
  hence asym: "\<forall> i::nat. i < length p \<longrightarrow>
              \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x)) \<longrightarrow> (let r = (p!i) in (x \<preceq>\<^sub>r y))"
    using x_in_A y_in_A
    unfolding connex_def
    by metis
  have "\<forall> i::nat. i < length p \<longrightarrow> ((y, x) \<in> (p!i) \<longrightarrow> (x, y) \<notin> (p!i))"
    using antisymD neq lin_imp_antisym prof
    unfolding profile_def
    by metis
  hence "{i::nat. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))} =
            {i::nat. i < length p} -
              {i::nat. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))}"
    using asym
    by auto
  thus ?thesis
    by (simp add: card_Diff_subset Collect_mono)
qed

lemma pref_count_sym:
  fixes
    p :: "'a Profile" and
    x :: "'a" and
    a :: "'a" and
    b :: "'a"
  assumes
    pref_count_ineq: "prefer_count p a x \<ge> prefer_count p x b" and
    prof: "profile A p" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    x_in_A: "x \<in> A" and
    a_neq_x: "a \<noteq> x" and
    x_neq_b: "x \<noteq> b"
  shows "prefer_count p b x \<ge> prefer_count p x a"
proof -
  have "prefer_count p a x = (length p) - (prefer_count p x a)"
    using pref_count prof a_in_A x_in_A a_neq_x
    by metis
  moreover have pref_count_b_eq: "prefer_count p x b = (length p) - (prefer_count p b x)"
    using pref_count prof x_in_A b_in_A x_neq_b
    by (metis (mono_tags, lifting))
  hence "(length p) - (prefer_count p b x) \<le> (length p) - (prefer_count p x a)"
    using calculation pref_count_ineq
    by simp
  hence "(prefer_count p x a) - (length p) \<le> (prefer_count p b x) - (length p)"
    using a_in_A diff_is_0_eq diff_le_self a_neq_x
          pref_count prof x_in_A
    by (metis (no_types))
  thus ?thesis
    using pref_count_b_eq calculation pref_count_ineq
    by linarith
qed

lemma empty_prof_imp_zero_pref_count:
  fixes p :: "'a Profile"
  assumes "p = []"
  shows "\<forall> x y. prefer_count p x y = 0"
  using assms
  by simp

lemma empty_prof_imp_zero_pref_count_code:
  fixes p :: "'a Profile"
  assumes "p = []"
  shows "\<forall> x y. prefer_count_code p x y = 0"
  using assms
  by simp

lemma pref_count_code_incr:
  fixes
    ps :: "'a Profile" and
    p :: "'a Preference_Relation" and
    x :: "'a" and
    y :: "'a" and
    n :: nat
  assumes
    "prefer_count_code ps x y = n" and
    "y \<preceq>\<^sub>p x"
  shows "prefer_count_code (p#ps) x y = n+1"
  using assms
  by simp

lemma pref_count_code_not_smaller_imp_constant:
  fixes
    ps :: "'a Profile" and
    p :: "'a Preference_Relation" and
    x :: "'a" and
    y :: "'a" and
    n :: nat
  assumes
    "prefer_count_code ps x y = n" and
    "\<not>(y \<preceq>\<^sub>p x)"
  shows "prefer_count_code (p#ps) x y = n"
  using assms
  by simp

fun wins :: "'a \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins x p y =
    (prefer_count p x y > prefer_count p y x)"

text \<open>
  Alternative a wins against b implies that b does not win against a.
\<close>

lemma wins_antisym:
  fixes
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  assumes "wins a p b"
  shows "\<not> wins b p a"
  using assms
  by simp

lemma wins_irreflex:
  fixes
    p :: "'a Profile" and
    a :: "'a"
  shows "\<not> wins a p a"
  using wins_antisym
  by metis

subsection \<open>Condorcet Winner\<close>

fun condorcet_winner :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner A p w =
      (finite_profile A p \<and>  w \<in> A \<and> (\<forall> x \<in> A - {w}. wins w p x))"

lemma cond_winner_unique:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    winner_a: "condorcet_winner A p a" and
    winner_b: "condorcet_winner A p b"
  shows "b = a"
proof (rule ccontr)
  assume b_neq_a: "b \<noteq> a"
  from winner_b
  have "wins b p a"
    using b_neq_a insert_Diff insert_iff winner_a
    by simp
  hence "\<not> wins a p b"
    by (simp add: wins_antisym)
  moreover from winner_a
  have
    a_wins_against_b: "wins a p b"
    using Diff_iff b_neq_a
          singletonD winner_b
    by simp
  ultimately show False
    by simp
qed

lemma cond_winner_unique_2:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    winner: "condorcet_winner A p a" and
    not_a:  "b \<noteq> a"
  shows "\<not> condorcet_winner A p b"
  using not_a cond_winner_unique winner
  by metis

lemma cond_winner_unique_3:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes "condorcet_winner A p a"
  shows "{b \<in> A. condorcet_winner A p b} = {a}"
proof (safe, simp_all, safe)
  fix b :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    b_in_A: "b \<in> A" and
    b_wins:
      "\<forall> x \<in> A - {b}.
        card {i. i < length p \<and> (b, x) \<in> p!i} <
          card {i. i < length p \<and> (x, b) \<in> p!i}"
  from assms
  have assm:
    "finite_profile A p \<and>  a \<in> A \<and>
      (\<forall> x \<in> A - {a}.
        card {i::nat. i < length p \<and> (a, x) \<in> p!i} <
          card {i::nat. i < length p \<and> (x, a) \<in> p!i})"
    by simp
  hence
    "(\<forall> x \<in> A - {a}.
      card {i::nat. i < length p \<and> (a, x) \<in> p!i} <
        card {i::nat. i < length p \<and> (x, a) \<in> p!i})"
    by simp
  hence a_beats_b:
    "b \<noteq> a \<Longrightarrow>
      card {i::nat. i < length p \<and> (a, b) \<in> p!i} <
        card {i::nat. i < length p \<and> (b, a) \<in> p!i}"
    using b_in_A
    by simp
  also from assm
  have "finite_profile A p"
    by simp
  moreover from assm
  have "a \<in> A"
    by simp
  hence b_beats_a:
    "b \<noteq> a \<Longrightarrow>
      card {i. i < length p \<and> (b, a) \<in> p!i} <
        card {i. i < length p \<and> (a, b) \<in> p!i}"
    using b_wins
    by simp
  from a_beats_b b_beats_a
  show "b = a"
    by linarith
next
  from assms
  show "a \<in> A"
    by simp
next
  from assms
  show "finite A"
    by simp
next
  from assms
  show "profile A p"
    by simp
next
  from assms
  show "a \<in> A"
    by simp
next
  fix b :: "'a"
  assume
    b_in_A: "b \<in> A" and
    a_wins:
      "\<not> card {i. i < length p \<and> (a, b) \<in> p!i} <
        card {i. i < length p \<and> (b, a) \<in> p!i}"
  from assms
  have
    "finite_profile A p \<and> a \<in> A \<and>
      (\<forall> x \<in> A - {a}.
        card {i::nat. i < length p \<and> (a, x) \<in> p!i} <
          card {i::nat. i < length p \<and> (x, a) \<in> p!i})"
    by simp
  thus "b = a"
    using b_in_A a_wins insert_Diff insert_iff
    by (metis (no_types, lifting))
qed

subsection \<open>Limited Profile\<close>

text \<open>
  This function restricts a profile p to a set A and
  keeps all of A's preferences.
\<close>

fun limit_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile" where
  "limit_profile A p = map (limit A) p"

lemma limit_prof_trans:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    C :: "'a set" and
    p :: "'a Profile"
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B" and
    "finite_profile A p"
  shows "limit_profile C p = limit_profile C (limit_profile B p)"
  using assms
  by auto

lemma limit_profile_sound:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    p :: "'a Profile"
  assumes
    profile: "finite_profile B p" and
    subset: "A \<subseteq> B"
  shows "finite_profile A (limit_profile A p)"
proof (safe)
  have "finite B \<longrightarrow> A \<subseteq> B \<longrightarrow> finite A"
    using rev_finite_subset
    by metis
  with profile
  show "finite A"
    using subset
    by metis
next
  have prof_is_lin_ord:
    "\<forall> C q.
      (profile (C::'a set) q \<longrightarrow> (\<forall> n < length q. linear_order_on C (q!n))) \<and>
      ((\<forall> n < length q. linear_order_on C (q!n)) \<longrightarrow> profile C q)"
    unfolding profile_def
    by simp
  have limit_prof_simp: "limit_profile A p = map (limit A) p"
    by simp
  obtain n :: nat where
    prof_limit_n: "(n < length (limit_profile A p) \<longrightarrow>
            linear_order_on A (limit_profile A p!n)) \<longrightarrow>
          profile A (limit_profile A p)"
    using prof_is_lin_ord
    by metis
  have prof_n_lin_ord: "\<forall> n < length p. linear_order_on B (p!n)"
    using prof_is_lin_ord profile
    by simp
  have prof_length: "length p = length (map (limit A) p)"
    by simp
  have "n < length p \<longrightarrow> linear_order_on B (p!n)"
    using prof_n_lin_ord
    by simp
  thus "profile A (limit_profile A p)"
    using prof_length prof_limit_n limit_prof_simp limit_presv_lin_ord nth_map subset
    by (metis (no_types))
qed

lemma limit_prof_presv_size:
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  shows "length p = length (limit_profile A p)"
  by simp

subsection \<open>Lifting Property\<close>

definition equiv_prof_except_a :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv_prof_except_a A p q a \<equiv>
    finite_profile A p \<and> finite_profile A q \<and>
      a \<in> A \<and> length p = length q \<and>
      (\<forall> i::nat.
        i < length p \<longrightarrow>
          equiv_rel_except_a A (p!i) (q!i) a)"

text \<open>
  An alternative gets lifted from one profile to another iff
  its ranking increases in at least one ballot, and nothing else changes.
\<close>

definition lifted :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A p q a \<equiv>
    finite_profile A p \<and> finite_profile A q \<and>
      a \<in> A \<and> length p = length q \<and>
      (\<forall> i::nat.
        (i < length p \<and> \<not>Preference_Relation.lifted A (p!i) (q!i) a) \<longrightarrow>
          (p!i) = (q!i)) \<and>
      (\<exists> i::nat. i < length p \<and> Preference_Relation.lifted A (p!i) (q!i) a)"

lemma lifted_imp_equiv_prof_except_a:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assumes "lifted A p q a"
  shows "equiv_prof_except_a A p q a"
proof (unfold equiv_prof_except_a_def, safe)
  from assms
  show "finite A"
    unfolding lifted_def
    by metis
next
  from assms
  show "profile A p"
    unfolding lifted_def
    by metis
next
  from assms
  show "finite A"
    unfolding lifted_def
    by metis
next
  from assms
  show "profile A q"
    unfolding lifted_def
    by metis
next
  from assms
  show "a \<in> A"
    unfolding lifted_def
    by metis
next
  from assms
  show "length p = length q"
    unfolding lifted_def
    by metis
next
  fix i :: nat
  assume "i < length p"
  with assms
  show "equiv_rel_except_a A (p!i) (q!i) a"
    using lifted_imp_equiv_rel_except_a trivial_equiv_rel
    unfolding lifted_def profile_def
    by (metis (no_types))
qed

lemma negl_diff_imp_eq_limit_prof:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assumes
    change: "equiv_prof_except_a B p q a" and
    subset: "A \<subseteq> B" and
    not_in_A: "a \<notin> A"
  shows "limit_profile A p = limit_profile A q"
proof (simp)
  have
    "\<forall> i::nat. i < length p \<longrightarrow>
      equiv_rel_except_a B (p!i) (q!i) a"
    using change equiv_prof_except_a_def
    by metis
  hence "\<forall> i::nat. i < length p \<longrightarrow> limit A (p!i) = limit A (q!i)"
    using not_in_A negl_diff_imp_eq_limit subset
    by metis
  thus "map (limit A) p = map (limit A) q"
    using change equiv_prof_except_a_def
          length_map nth_equalityI nth_map
    by (metis (mono_tags, lifting))
qed

lemma limit_prof_eq_or_lifted:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assumes
    lifted_a: "lifted B p q a" and
    subset: "A \<subseteq> B"
  shows
    "limit_profile A p = limit_profile A q \<or>
        lifted A (limit_profile A p) (limit_profile A q) a"
proof (cases)
  assume a_in_A: "a \<in> A"
  have
    "\<forall> i::nat. i < length p \<longrightarrow>
        (Preference_Relation.lifted B (p!i) (q!i) a \<or> (p!i) = (q!i))"
    using lifted_a
    unfolding lifted_def
    by metis
  hence one:
    "\<forall> i::nat. i < length p \<longrightarrow>
         (Preference_Relation.lifted A (limit A (p!i)) (limit A (q!i)) a \<or>
           (limit A (p!i)) = (limit A (q!i)))"
    using limit_lifted_imp_eq_or_lifted subset
    by metis
  thus ?thesis
  proof (cases)
    assume "\<forall> i::nat. i < length p \<longrightarrow> (limit A (p!i)) = (limit A (q!i))"
    thus ?thesis
      using length_map lifted_a nth_equalityI nth_map
            limit_profile.simps
      unfolding lifted_def
      by (metis (mono_tags, lifting))
  next
    assume forall_limit_p_q: "\<not>(\<forall> i::nat. i < length p \<longrightarrow> (limit A (p!i)) = (limit A (q!i)))"
    let ?p = "limit_profile A p"
    let ?q = "limit_profile A q"
    have "profile A ?p \<and> profile A ?q"
      using lifted_a limit_profile_sound subset
      unfolding lifted_def
      by metis
    moreover have "length ?p = length ?q"
      using lifted_a
      unfolding lifted_def
      by fastforce
    moreover have "\<exists> i::nat. i < length ?p \<and> Preference_Relation.lifted A (?p!i) (?q!i) a"
      using forall_limit_p_q length_map lifted_a limit_profile.simps nth_map one
      unfolding lifted_def
      by (metis (no_types, lifting))
    moreover have
      "\<forall> i::nat.
        (i < length ?p \<and> \<not>Preference_Relation.lifted A (?p!i) (?q!i) a) \<longrightarrow>
          (?p!i) = (?q!i)"
      using length_map lifted_a limit_profile.simps nth_map one
      unfolding lifted_def
      by metis
    ultimately have "lifted A ?p ?q a"
      using a_in_A lifted_a rev_finite_subset subset
      unfolding lifted_def
      by (metis (no_types, lifting))
    thus ?thesis
      by simp
  qed
next
  assume "a \<notin> A"
  thus ?thesis
    using lifted_a negl_diff_imp_eq_limit_prof subset
          lifted_imp_equiv_prof_except_a
    by metis
qed

end

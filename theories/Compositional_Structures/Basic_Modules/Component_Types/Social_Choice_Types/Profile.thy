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

text
\<open>Preference profiles denote the decisions made by the individual voters on
the eligible alternatives. They are represented in the form of one preference
relation (e.g., selected on a ballot) per voter, collectively captured in a
list of such preference relations.
Unlike a the common preference profiles in the social-choice sense, the
profiles described here considers only the (sub-)set of alternatives that are
received.\<close>

subsection \<open>Definition\<close>

(*A profile contains one ballot for each voter.*)
type_synonym 'a Profile = "('a Preference_Relation) list"

(*
   A profile on a finite set of alternatives A contains only ballots that are
   linear orders on A.
*)
definition profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "profile A p \<equiv> \<forall>i::nat. i < length p \<longrightarrow> linear_order_on A (p!i)"

lemma profile_set : "profile A p \<equiv> (\<forall>b \<in> (set p). linear_order_on A b)"
  by (simp add: all_set_conv_all_nth profile_def)

abbreviation finite_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "finite_profile A p \<equiv> finite A \<and> profile A p"

subsection \<open>Preference Counts and Comparisons\<close>

(*
   The win count for an alternative a in a profile p is
   the amount of ballots in p that rank alternative a in first position.
*)
fun win_count :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count p a =
    card {i::nat. i < length p \<and> above (p!i) a = {a}}"

fun win_count_code :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count_code Nil a = 0" |
  "win_count_code (p#ps) a =
      (if (above p a = {a}) then 1 else 0) + win_count_code ps a"

lemma win_count_equiv[code]: "win_count p x = win_count_code p x"
proof (induction p rule: rev_induct, simp)
  case (snoc a p)
  fix
    a :: "'a Preference_Relation" and
    p :: "'a Profile"
  assume
    base_case:
    "win_count p x = win_count_code p x"
  have size_one: "length [a] = 1"
    by simp
  have p_pos_in_ps:
    "\<forall>i<length p. p!i = (p@[a])!i"
    by (simp add: nth_append)
  have
    "win_count [a] x =
      (let q = [a] in
        card {i::nat. i < length q \<and>
              (let r = (q!i) in (above r x = {x}))})"
    by simp
  hence one_ballot_equiv:
    "win_count [a] x = win_count_code [a] x"
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
        xa :: nat and
        xaa :: "'a"
      assume
        "xa < Suc (length p)" and
        "above ((p@[a])!xa) x = {x}" and
        "xa \<noteq> length p" and
        "xaa \<in> above (p!xa) x"
      thus "xaa = x"
        using less_antisym p_pos_in_ps singletonD
        by metis
    next
      fix
        xa :: nat
      assume
        "xa < Suc (length p)" and
        "above ((p@[a])!xa) x = {x}" and
        "xa \<noteq> length p"
      thus "x \<in> above (p!xa) x"
        using less_antisym insertI1 p_pos_in_ps
        by metis
    next
      fix
        xa :: nat and
        xaa :: "'a"
      assume
        "xa < Suc (length p)" and
        "above ((p@[a])!xa) x = {x}" and
        "xaa \<in> above a x" and
        "xaa \<noteq> x"
      thus "xa < length p"
        using less_antisym nth_append_length
              p_pos_in_ps singletonD
        by metis
    next
      fix
        xa :: nat and
        xaa :: "'a" and
        xb :: "'a"
      assume
        "xa < Suc (length p)" and
        "above ((p@[a])!xa) x = {x}" and
        "xaa \<in> above a x" and
        "xaa \<noteq> x" and
        "xb \<in> above (p!xa) x"
      thus "xb = x"
        using less_antisym p_pos_in_ps
              nth_append_length singletonD
        by metis
    next
      fix
        xa :: nat and
        xaa :: "'a"
      assume
        "xa < Suc (length p)" and
        "above ((p@[a])!xa) x = {x}" and
        "xaa \<in> above a x" and
        "xaa \<noteq> x"
      thus "x \<in> above (p!xa) x"
        using insertI1 less_antisym nth_append
              nth_append_length singletonD
        by metis
    next
      fix
        xa :: nat
      assume
        "xa < Suc (length p)" and
        "above ((p@[a])!xa) x = {x}" and
        "x \<notin> above a x"
      thus "xa < length p"
        using insertI1 less_antisym nth_append_length
        by metis
    next
      fix
        xa :: nat and
        xb :: "'a"
      assume
        "xa < Suc (length p)" and
        "above ((p@[a])!xa) x = {x}" and
        "x \<notin> above a x" and
        "xb \<in> above (p!xa) x"
      thus "xb = x"
        using insertI1 less_antisym nth_append_length
              p_pos_in_ps singletonD
        by metis
    next
      fix
        xa :: nat
      assume
        "xa < Suc (length p)" and
        "above ((p@[a])!xa) x = {x}" and
        "x \<notin> above a x"
      thus "x \<in> above (p!xa) x"
        using insertI1 less_antisym nth_append_length p_pos_in_ps
        by metis
    next
      fix
        xa :: nat and
        xaa :: "'a"
      assume
        "xa < length p" and
        "above (p!xa) x = {x}" and
        "xaa \<in> above ((p@[a])!xa) x"
      thus "xaa = x"
        by (simp add: nth_append)
    next
      fix
        xa :: nat
      assume
        "xa < length p" and
        "above (p!xa) x = {x}"
      thus "x \<in> above ((p@[a])!xa) x"
        by (simp add: nth_append)
    qed
    have f1:
      "finite {n. n < length p \<and> (above (p!n) x = {x})}"
      by simp
    have f2:
      "finite {n. n = length p \<and> (above ([a]!0) x = {x})}"
      by simp
    have
      "card ({i. i < length p \<and> (above (p!i) x = {x})} \<union>
        {i. i = length p \<and> (above ([a]!0) x = {x})}) =
          card {i. i < length p \<and> (above (p!i) x = {x})} +
            card {i. i = length p \<and> (above ([a]!0) x = {x})}"
      using f1 f2 card_Un_disjoint
      by blast
    thus
      "card {i. i < Suc (length p) \<and> (above ((p@[a])!i) x = {x})} =
        card {i. i < length p \<and> (above (p!i) x = {x})} +
          card {i. i = 0 \<and> (above ([a]!i) x = {x})}"
      using set_prof_eq shift_idx_a
      by auto
  qed
  have pref_count_code_induct:
    "win_count_code (p@[a]) x =
      win_count_code p x + win_count_code [a] x"
  proof (induction p, simp)
    fix
      aa :: "'a Preference_Relation" and
      p :: "'a Profile"
    assume
      "win_count_code (p@[a]) x =
        win_count_code p x + win_count_code [a] x"
    thus
      "win_count_code ((aa#p)@[a]) x =
        win_count_code (aa#p) x + win_count_code [a] x"
      by simp
  qed
  show "win_count (p@[a]) x = win_count_code (p@[a]) x"
    using pref_count_code_induct pref_count_induct
          base_case one_ballot_equiv
    by presburger
qed

fun prefer_count :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count p x y =
      card {i::nat. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"

fun prefer_count_code :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count_code Nil x y = 0" |
  "prefer_count_code (p#ps) x y =
      (if y \<preceq>\<^sub>p x then 1 else 0) + prefer_count_code ps x y"

lemma pref_count_equiv[code]: "prefer_count p x y = prefer_count_code p x y"
proof (induction p rule: rev_induct, simp)
  case (snoc a p)
  fix
    a :: "'a Preference_Relation" and
    p :: "'a Profile"
  assume
    base_case:
    "prefer_count p x y = prefer_count_code p x y"
  have size_one: "length [a] = 1"
    by simp
  have p_pos_in_ps:
    "\<forall>i<length p. p!i = (p@[a])!i"
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
      fix
        xa :: nat
      assume
        "xa < Suc (length p)" and
        "(y, x) \<in> (p@[a])!xa" and
        "xa \<noteq> length p"
      thus "(y, x) \<in> p!xa"
        using less_antisym p_pos_in_ps
        by metis
    next
      fix
        xa :: nat
      assume
        "xa < Suc (length p)" and
        "(y, x) \<in> (p@[a])!xa" and
        "(y, x) \<notin> a"
      thus "xa < length p"
        using less_antisym nth_append_length
        by metis
    next
      fix
        xa :: nat
      assume
        "xa < Suc (length p)" and
        "(y, x) \<in> (p@[a])!xa" and
        "(y, x) \<notin> a"
      thus "(y, x) \<in> p!xa"
        using less_antisym nth_append_length p_pos_in_ps
        by metis
    next
      fix
        xa :: nat
      assume
        "xa < length p" and
        "(y, x) \<in> p!xa"
      thus "(y, x) \<in> (p@[a])!xa"
        using less_antisym p_pos_in_ps
        by metis
    qed
    have f1:
      "finite {n. n < length p \<and> (y, x) \<in> p!n}"
      by simp
    have f2:
      "finite {n. n = length p \<and> (y, x) \<in> [a]!0}"
      by simp
    have
      "card ({i. i < length p \<and> (y, x) \<in> p!i} \<union>
        {i. i = length p \<and> (y, x) \<in> [a]!0}) =
          card {i. i < length p \<and> (y, x) \<in> p!i} +
            card {i. i = length p \<and> (y, x) \<in> [a]!0}"
      using f1 f2 card_Un_disjoint
      by blast
    thus
      "card {i. i < Suc (length p) \<and> (y, x) \<in> (p@[a])!i} =
        card {i. i < length p \<and> (y, x) \<in> p!i} +
          card {i. i = 0 \<and> (y, x) \<in> [a]!i}"
      using set_prof_eq shift_idx_a
      by auto
  qed
  have pref_count_code_induct:
    "prefer_count_code (p@[a]) x y =
      prefer_count_code p x y + prefer_count_code [a] x y"
  proof (simp, safe)
    assume
      assm: "(y, x) \<in> a"
    show
      "prefer_count_code (p@[a]) x y = Suc (prefer_count_code p x y)"
    proof (induction p, simp_all)
      show "(y, x) \<in> a"
        using assm
        by simp
    qed
  next
    assume
      assm: "(y, x) \<notin> a"
    show
      "prefer_count_code (p@[a]) x y = prefer_count_code p x y"
    proof (induction p, simp_all, safe)
      assume
        "(y, x) \<in> a"
      thus "False"
        using assm
        by simp
    qed
  qed
  show "prefer_count (p@[a]) x y = prefer_count_code (p@[a]) x y"
    using pref_count_code_induct pref_count_induct
          base_case one_ballot_equiv
    by presburger
qed

lemma set_compr: "{ f x | x . x \<in> S } = f ` S"
  by auto

lemma pref_count_set_compr: "{prefer_count p x y | y . y \<in> A-{x}} =
          (prefer_count p x) ` (A-{x})"
  by auto

lemma pref_count:
  assumes prof: "profile A p"
  assumes x_in_A: "x \<in> A"
  assumes y_in_A: "y \<in> A"
  assumes neq: "x \<noteq> y"
  shows "prefer_count p x y = (length p) - (prefer_count p y x)"
proof -
  have 00: "card {i::nat. i < length p} = length p"
    by simp
  have 10:
    "{i::nat. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))} =
        {i::nat. i < length p} -
          {i::nat. i < length p \<and> \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"
    by auto
  have 0: "\<forall> i::nat . i < length p \<longrightarrow> linear_order_on A (p!i)"
    using prof profile_def
    by metis
  hence "\<forall> i::nat . i < length p \<longrightarrow> connex A (p!i)"
    by (simp add: lin_ord_imp_connex)
  hence 1: "\<forall> i::nat . i < length p \<longrightarrow>
              \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x)) \<longrightarrow> (let r = (p!i) in (x \<preceq>\<^sub>r y))"
    using connex_def x_in_A y_in_A
    by metis
  from 0 have
    "\<forall> i::nat . i < length p \<longrightarrow> antisym  (p!i)"
    using lin_imp_antisym
    by metis
  hence "\<forall> i::nat . i < length p \<longrightarrow> ((y, x) \<in> (p!i) \<longrightarrow> (x, y) \<notin> (p!i))"
    using antisymD neq
    by metis
  hence "\<forall> i::nat . i < length p \<longrightarrow>
          ((let r = (p!i) in (y \<preceq>\<^sub>r x)) \<longrightarrow> \<not> (let r = (p!i) in (x \<preceq>\<^sub>r y)))"
    by simp
  with 1 have
    "\<forall> i::nat . i < length p \<longrightarrow>
      \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x)) = (let r = (p!i) in (x \<preceq>\<^sub>r y))"
    by metis
  hence 2:
    "{i::nat. i < length p \<and> \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x))} =
        {i::nat. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))}"
    by metis
  hence 20:
    "{i::nat. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))} =
        {i::nat. i < length p} -
          {i::nat. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))}"
    using "10" "2"
    by simp
  have
    "{i::nat. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))} \<subseteq>
        {i::nat. i < length p}"
    by (simp add: Collect_mono)
  hence 30:
    "card ({i::nat. i < length p} -
        {i::nat. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))}) =
      (card {i::nat. i < length p}) -
        card({i::nat. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))})"
    by (simp add: card_Diff_subset)
  have "prefer_count p x y =
          card {i::nat. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"
    by simp
  also have
    "... = card({i::nat. i < length p} -
            {i::nat. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))})"
    using "20"
    by simp
  also have
    "... = (card {i::nat. i < length p}) -
              card({i::nat. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))})"
    using "30"
    by metis
  also have
    "... = length p - (prefer_count p y x)"
    by simp
  finally show ?thesis
    by (simp add: "20" "30")
qed

lemma pref_count_sym:
    assumes p1: "prefer_count p a x \<ge> prefer_count p x b"
    assumes prof: "profile A p"
    assumes a_in_A: "a \<in> A"
    assumes b_in_A: "b \<in> A"
    assumes x_in_A: "x \<in> A"
    assumes neq1: "a \<noteq> x"
    assumes neq2: "x \<noteq> b"
    shows "prefer_count p b x \<ge> prefer_count p x a"
proof -
  from prof a_in_A x_in_A neq1 have 0:
    "prefer_count p a x = (length p) - (prefer_count p x a)"
    using pref_count
    by metis
  moreover from prof x_in_A b_in_A neq2 have 1:
    "prefer_count p x b = (length p) - (prefer_count p b x)"
    using pref_count
    by (metis (mono_tags, lifting))
  hence 2: "(length p) - (prefer_count p x a) \<ge>
              (length p) - (prefer_count p b x)"
    using calculation p1
    by auto
  hence 3: "(prefer_count p x a) - (length p) \<le>
              (prefer_count p b x) - (length p)"
    using a_in_A diff_is_0_eq diff_le_self neq1
          pref_count prof x_in_A
    by (metis (no_types))
  hence "(prefer_count p x a) \<le> (prefer_count p b x)"
    using "1" "3" calculation p1
    by linarith
  thus ?thesis
    by linarith
qed

lemma empty_prof_imp_zero_pref_count:
  assumes "p = []"
  shows "\<forall> x y. prefer_count p x y = 0"
  using assms
  by simp

lemma empty_prof_imp_zero_pref_count_code:
  assumes "p = []"
  shows "\<forall> x y. prefer_count_code p x y = 0"
  using assms
  by simp

lemma pref_count_code_incr:
  assumes
    "prefer_count_code ps x y = n" and
    "y \<preceq>\<^sub>p x"
  shows "prefer_count_code (p#ps) x y = n+1"
  using assms
  by simp

lemma pref_count_code_not_smaller_imp_constant:
  assumes
    "prefer_count_code ps x y = n" and
    "\<not>(y \<preceq>\<^sub>p x)"
  shows "prefer_count_code (p#ps) x y = n"
  using assms
  by simp

fun wins :: "'a \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins x p y =
    (prefer_count p x y > prefer_count p y x)"

(* Alternative a wins against b implies that b does not win against a. *)
lemma wins_antisym:
  assumes "wins a p b"
  shows "\<not> wins b p a"
  using assms
  by simp

lemma wins_irreflex: "\<not> wins w p w"
  using wins_antisym
  by metis

subsection \<open>Condorcet Winner\<close>

fun condorcet_winner :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner A p w =
      (finite_profile A p \<and>  w \<in> A \<and> (\<forall>x \<in> A - {w} . wins w p x))"

lemma cond_winner_unique:
  assumes winner_c: "condorcet_winner A p c" and
          winner_w: "condorcet_winner A p w"
  shows "w = c"
proof (rule ccontr)
  assume
    assumption: "w \<noteq> c"
  from winner_w
  have "wins w p c"
    using assumption insert_Diff insert_iff winner_c
    by simp
  hence "\<not> wins c p w"
    by (simp add: wins_antisym)
  moreover from winner_c
  have
    c_wins_against_w: "wins c p w"
    using Diff_iff assumption
          singletonD winner_w
    by simp
  ultimately show False
    by simp
qed

lemma cond_winner_unique2:
  assumes winner: "condorcet_winner A p w" and
          not_w:  "x \<noteq> w" and
          in_A:   "x \<in> A"
        shows "\<not> condorcet_winner A p x"
  using not_w cond_winner_unique winner
  by metis

lemma cond_winner_unique3:
  assumes "condorcet_winner A p w"
  shows "{a \<in> A. condorcet_winner A p a} = {w}"
proof (safe, simp_all, safe)
  fix
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    x_in_A: "x \<in> A" and
    x_wins:
      "\<forall>xa \<in> A - {x}.
        card {i. i < length p \<and> (x, xa) \<in> p!i} <
          card {i. i < length p \<and> (xa, x) \<in> p!i}"
  from assms have assm:
    "finite_profile A p \<and>  w \<in> A \<and>
      (\<forall>x \<in> A - {w}.
        card {i::nat. i < length p \<and> (w, x) \<in> p!i} <
          card {i::nat. i < length p \<and> (x, w) \<in> p!i})"
    by simp
  hence
    "(\<forall>x \<in> A - {w}.
      card {i::nat. i < length p \<and> (w, x) \<in> p!i} <
        card {i::nat. i < length p \<and> (x, w) \<in> p!i})"
    by simp
  hence w_beats_x:
    "x \<noteq> w \<Longrightarrow>
      card {i::nat. i < length p \<and> (w, x) \<in> p!i} <
        card {i::nat. i < length p \<and> (x, w) \<in> p!i}"
    using x_in_A
    by simp
  also from assm have
    "finite_profile A p"
    by simp
  moreover from assm have
    "w \<in> A"
    by simp
  hence x_beats_w:
    "x \<noteq> w \<Longrightarrow>
      card {i. i < length p \<and> (x, w) \<in> p!i} <
        card {i. i < length p \<and> (w, x) \<in> p!i}"
    using x_wins
    by simp
  from w_beats_x x_beats_w show
    "x = w"
    by linarith
next
  fix
    x :: "'a"
  from assms show "w \<in> A"
    by simp
next
  fix
    x :: "'a"
  from assms show "finite A"
    by simp
next
  fix
    x :: "'a"
  from assms show "profile A p"
    by simp
next
  fix
    x :: "'a"
  from assms show "w \<in> A"
    by simp
next
  fix
    x :: "'a" and
    xa :: "'a"
  assume
    xa_in_A: "xa \<in> A" and
    w_wins:
      "\<not> card {i. i < length p \<and> (w, xa) \<in> p!i} <
        card {i. i < length p \<and> (xa, w) \<in> p!i}"
  from assms have
    "finite_profile A p \<and>  w \<in> A \<and>
      (\<forall>x \<in> A - {w} .
        card {i::nat. i < length p \<and> (w, x) \<in> p!i} <
          card {i::nat. i < length p \<and> (x, w) \<in> p!i})"
    by simp
  thus "xa = w"
    using xa_in_A w_wins insert_Diff insert_iff
    by (metis (no_types, lifting))
qed

subsection \<open>Limited Profile\<close>

(*
   This function restricts a profile p to a set A and
   keeps all of A's preferences.
*)
fun limit_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile" where
  "limit_profile A p = map (limit A) p"

lemma limit_prof_trans:
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B" and
    "finite_profile A p"
  shows "limit_profile C p = limit_profile C (limit_profile B p)"
  using assms
  by auto

lemma limit_profile_sound:
  assumes
    profile: "finite_profile S p" and
    subset: "A \<subseteq> S"
  shows "finite_profile A (limit_profile A p)"
proof (simp)
  from profile
  show "finite_profile A (map (limit A) p)"
    using length_map limit_presv_lin_ord nth_map
          profile_def subset infinite_super
    by metis
qed

lemma limit_prof_presv_size:
  assumes f_prof: "finite_profile S p" and
          subset:  "A \<subseteq> S"
  shows "length p = length (limit_profile A p)"
  by simp

subsection \<open>Lifting Property\<close>

definition equiv_prof_except_a :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow>
                                        'a \<Rightarrow> bool" where
  "equiv_prof_except_a A p q a \<equiv>
    finite_profile A p \<and> finite_profile A q \<and>
      a \<in> A \<and> length p = length q \<and>
      (\<forall>i::nat.
        i < length p \<longrightarrow>
          equiv_rel_except_a A (p!i) (q!i) a)"

(*
   An alternative gets lifted from one profile to another iff
   its ranking increases in at least one ballot, and nothing else changes.
*)
definition lifted :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A p q a \<equiv>
    finite_profile A p \<and> finite_profile A q \<and>
      a \<in> A \<and> length p = length q \<and>
      (\<forall>i::nat.
        (i < length p \<and> \<not>Preference_Relation.lifted A (p!i) (q!i) a) \<longrightarrow>
          (p!i) = (q!i)) \<and>
      (\<exists>i::nat. i < length p \<and> Preference_Relation.lifted A (p!i) (q!i) a)"

lemma lifted_imp_equiv_prof_except_a:
  assumes lifted: "lifted A p q a"
  shows "equiv_prof_except_a A p q a"
proof -
  have
    "\<forall>i::nat. i < length p \<longrightarrow>
      equiv_rel_except_a A (p!i) (q!i) a"
  proof
    fix i :: nat
    show
      "i < length p \<longrightarrow>
        equiv_rel_except_a A (p!i) (q!i) a"
    proof
      assume i_ok: "i < length p"
      show "equiv_rel_except_a A (p!i) (q!i) a"
        using lifted_def i_ok lifted profile_def trivial_equiv_rel
              lifted_imp_equiv_rel_except_a
        by metis
    qed
  qed
  thus ?thesis
    using lifted_def lifted equiv_prof_except_a_def
    by metis
qed

lemma negl_diff_imp_eq_limit_prof:
  assumes
    change: "equiv_prof_except_a S p q a" and
    subset: "A \<subseteq> S" and
    notInA: "a \<notin> A"
  shows "limit_profile A p = limit_profile A q"
proof -
  have
    "\<forall>i::nat. i < length p \<longrightarrow>
      equiv_rel_except_a S (p!i) (q!i) a"
    using change equiv_prof_except_a_def
    by metis
  hence "\<forall>i::nat. i < length p \<longrightarrow> limit A (p!i) = limit A (q!i)"
    using notInA negl_diff_imp_eq_limit subset
    by metis
  hence "map (limit A) p = map (limit A) q"
    using change equiv_prof_except_a_def
          length_map nth_equalityI nth_map
    by (metis (mono_tags, lifting))
  thus ?thesis
    by simp
qed

lemma limit_prof_eq_or_lifted:
  assumes
    lifted: "lifted S p q a" and
    subset: "A \<subseteq> S"
  shows
    "limit_profile A p = limit_profile A q \<or>
        lifted A (limit_profile A p) (limit_profile A q) a"
proof cases
  assume inA: "a \<in> A"
  have
    "\<forall>i::nat. i < length p \<longrightarrow>
        (Preference_Relation.lifted S (p!i) (q!i) a \<or> (p!i) = (q!i))"
    using lifted_def lifted
    by metis
  hence one:
    "\<forall>i::nat. i < length p \<longrightarrow>
         (Preference_Relation.lifted A (limit A (p!i)) (limit A (q!i)) a \<or>
           (limit A (p!i)) = (limit A (q!i)))"
    using limit_lifted_imp_eq_or_lifted subset
    by metis
  thus ?thesis
  proof cases
    assume "\<forall>i::nat. i < length p \<longrightarrow> (limit A (p!i)) = (limit A (q!i))"
    thus ?thesis
      using lifted_def length_map lifted
            limit_profile.simps nth_equalityI nth_map
      by (metis (mono_tags, lifting))
  next
    assume assm:
      "\<not>(\<forall>i::nat. i < length p \<longrightarrow> (limit A (p!i)) = (limit A (q!i)))"
    let ?p = "limit_profile A p"
    let ?q = "limit_profile A q"
    have "profile A ?p \<and> profile A ?q"
      using lifted_def lifted limit_profile_sound subset
      by metis
    moreover have "length ?p = length ?q"
      using lifted_def lifted
      by fastforce
    moreover have
      "\<exists>i::nat. i < length ?p \<and> Preference_Relation.lifted A (?p!i) (?q!i) a"
      using assm lifted_def length_map lifted
            limit_profile.simps nth_map one
      by (metis (no_types, lifting))
    moreover have
      "\<forall>i::nat.
        (i < length ?p \<and> \<not>Preference_Relation.lifted A (?p!i) (?q!i) a) \<longrightarrow>
          (?p!i) = (?q!i)"
      using lifted_def length_map lifted
            limit_profile.simps nth_map one
      by metis
    ultimately have "lifted A ?p ?q a"
      using lifted_def inA lifted rev_finite_subset subset
      by (metis (no_types, lifting))
    thus ?thesis
      by simp
  qed
next
  assume "a \<notin> A"
  thus ?thesis
    using lifted negl_diff_imp_eq_limit_prof subset
          lifted_imp_equiv_prof_except_a
    by metis
qed

end

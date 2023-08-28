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
          "HOL.Finite_Set"
          "HOL-Library.Extended_Nat"
begin

text \<open>
  Preference profiles denote the decisions made by the individual voters on
  the eligible alternatives. They are represented in the form of one preference
  relation (e.g., selected on a ballot) per voter, collectively captured in a
  mapping of voters onto their respective preference relations.
  If there are finitely many voters, they can be enumerated and the mapping can
  be interpreted as a list of preference relations.
  Unlike the common preference profiles in the social-choice sense, the
  profiles described here consider only the (sub-)set of alternatives that are
  received.
\<close>

subsection \<open>Definition\<close>

text \<open>
  A profile contains one ballot for each voter.
  An election consists of a set of participating voters,
  a set of eligible alternatives and a corresponding profile.
\<close>

type_synonym ('a, 'v) Profile = "'v \<Rightarrow> ('a Preference_Relation)"

type_synonym ('a, 'v) Election = "'a set \<times> 'v set \<times> ('a, 'v) Profile"

fun alts_\<E> :: "('a, 'v) Election \<Rightarrow> 'a set" where "alts_\<E> E = fst E"

fun votrs_\<E> :: "('a, 'v) Election \<Rightarrow> 'v set" where "votrs_\<E> E = fst (snd E)"

fun prof_\<E> :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Profile" where "prof_\<E> E = snd (snd E)"

text \<open>
  A profile on a set of alternatives A and a voter set V, per voter from V,
  only ballots that are linear orders on A.
  A finite profile is one where V and A are finite.
  A profile where the voters are the first n from a globally fixed, 
  enumerable ground set of voters can analogously be interpreted as a list of 
  length n of ballots.
\<close>

definition profile :: "'a set \<Rightarrow> 'v set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> bool" where
  "profile A V p \<equiv> \<forall> v \<in> V. linear_order_on A (p v)"

type_synonym 'a Fixed_Voter_Profile = "('a Preference_Relation) list"

function fixed_voter_profile_to_profile :: "'a Fixed_Voter_Profile \<Rightarrow> ('a, nat) Profile" where
  "fixed_voter_profile_to_profile p v = p!v" if "v < length p" |
  "fixed_voter_profile_to_profile p v = {}" if "v \<ge> length p"
  apply atomize_elim
  apply auto
  done
termination by lexicographic_order

(*
fun profile_to_fixed_aggregator :: 
"('a, nat) Profile \<Rightarrow> nat \<Rightarrow> (('a Preference_Relation) list) \<Rightarrow> 'a Fixed_Voter_Profile" where
  "profile_to_fixed_aggregator p 0 xs = rev xs" |
  "profile_to_fixed_aggregator p n xs = profile_to_fixed_aggregator p (n-1) ((p (n-1))#xs)"
*)

fun profile_to_fixed_voter_profile :: "('a, nat) Profile \<Rightarrow> nat \<Rightarrow> 'a Fixed_Voter_Profile" where
  "profile_to_fixed_voter_profile p 0 = []" |
  "profile_to_fixed_voter_profile p n = (profile_to_fixed_voter_profile p (n-1)) @ [p (n-1)]"

(*
lemma fixed_profile_aggregator_length [simp]: 
"length (profile_to_fixed_aggregator p n xs) = n + length xs"
  apply (induction n arbitrary: xs)
  apply (auto)
  done

lemma fixed_profile_aggregator_values [simp]: 
  fixes
    xs::"('a Preference_Relation) list" and
    n::nat and
    v::nat
  assumes "length xs \<le> v \<and> v < n + length xs"
  shows "(profile_to_fixed_aggregator p n xs)!v = p v"
proof
*)

lemma fixed_profile_length [simp]: "n = length (profile_to_fixed_voter_profile p n)"
  apply (induction n)
   apply (auto)
  done
  
theorem profile_fixed_profile_equiv [simp]:
  fixes
    n::nat and
    v::nat and
    p::"('a, nat) Profile"
  assumes 0: "v < n"
  shows "(profile_to_fixed_voter_profile p n)!v = p v"
  sorry (*TODO*)

abbreviation finite_profile :: "'a set \<Rightarrow> 'v set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> bool" where
  "finite_profile A V p \<equiv> finite A \<and> finite V \<and> profile A V p"

(*
lemma profile_set :
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  shows "profile A p \<equiv> (\<forall> b \<in> (set p). linear_order_on A b)"
  unfolding profile_def all_set_conv_all_nth
  by simp
*)

subsection \<open>Preference Counts and Comparisons\<close>

text \<open>
  The win count for an alternative a with respect to a finite voter set V in a profile p is
  the amount of ballots from V in p that rank alternative a in first position.
  If the voter set is infinite, counting is not generally possible.
\<close>

definition win_count :: "'a Fixed_Voter_Profile \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count p a = card {n \<in> \<nat>. (n < length p) \<longrightarrow> above (p!n) a = {a}}"

(*function win_count1 :: "('a, 'v) Profile \<Rightarrow> 'v set \<Rightarrow> 'a \<Rightarrow> enat"
  where
    "win_count p V a = card {v\<in>V. above (p v) a = {a}}" if "finite V" |
    "win_count p V a = infinity" if "\<not>(finite V)"
  apply atomize_elim
  apply auto
  done
termination by lexicographic_order*)

fun win_count_code :: "'a Fixed_Voter_Profile \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count_code Nil a = 0" |
  "win_count_code (r#p) a =
      (if (above r a = {a}) then 1 else 0) + win_count_code p a"

lemma win_count_equiv[code]:
  fixes
    p :: "'a Fixed_Voter_Profile" and
    a :: "'a"
  shows "win_count p a = win_count_code p a"
proof (induction p rule: rev_induct, simp)
  case (snoc r p)
  fix
    r :: "'a Preference_Relation" and
    p :: "'a Fixed_Voter_Profile"
  assume base_case: "win_count p a = win_count_code p a"
  have size_one: "length [r] = 1"
    by simp
  have p_pos: "\<forall> i < length p. p!i = (p@[r])!i"
    by (simp add: nth_append)
  have
    "win_count [r] a =
      (let q = [r] in
        card {i::nat. i < length q \<and> (let r' = (q!i) in (above r' a = {a}))})"
    by simp
  hence one_ballot_equiv: "win_count [r] a = win_count_code [r] a"
    using size_one
    by (simp add: nth_Cons')
  have pref_count_induct: "win_count (p@[r]) a = win_count p a + win_count [r] a"
  proof (simp)
    have "{i. i = 0 \<and> (above ([r]!i) a = {a})} =
            (if (above r a = {a}) then {0} else {})"
      by (simp add: Collect_conv_if)
    hence shift_idx_a:
      "card {i. i = length p \<and> (above ([r]!0) a = {a})} =
        card {i. i = 0 \<and> (above ([r]!i) a = {a})}"
      by simp
    have set_prof_eq:
      "{i. i < Suc (length p) \<and> (above ((p@[r])!i) a = {a})} =
        {i. i < length p \<and> (above (p!i) a = {a})} \<union>
          {i. i = length p \<and> (above ([r]!0) a = {a})}"
    proof (safe, simp_all)
      fix
        n :: nat and
        a' :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[r])!n) a = {a}" and
        "n \<noteq> length p" and
        "a' \<in> above (p!n) a"
      thus "a' = a"
        using less_antisym p_pos singletonD
        by metis
    next
      fix n :: nat
      assume
        "n < Suc (length p)" and
        "above ((p@[r])!n) a = {a}" and
        "n \<noteq> length p"
      thus "a \<in> above (p!n) a"
        using less_antisym insertI1 p_pos
        by metis
    next
      fix
        n :: nat and
        a' :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[r])!n) a = {a}" and
        "a' \<in> above r a" and
        "a' \<noteq> a"
      thus "n < length p"
        using less_antisym nth_append_length p_pos singletonD
        by metis
    next
      fix
        n :: nat and
        a' :: "'a" and
        a'' :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[r])!n) a = {a}" and
        "a' \<in> above r a" and
        "a' \<noteq> a" and
        "a'' \<in> above (p!n) a"
      thus "a'' = a"
        using less_antisym p_pos nth_append_length singletonD
        by metis
    next
      fix
        n :: nat and
        a' :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[r])!n) a = {a}" and
        "a' \<in> above r a" and
        "a' \<noteq> a"
      thus "a \<in> above (p!n) a"
        using insertI1 less_antisym nth_append nth_append_length singletonD
        by metis
    next
      fix n :: nat
      assume
        "n < Suc (length p)" and
        "above ((p@[r])!n) a = {a}" and
        "a \<notin> above r a"
      thus "n < length p"
        using insertI1 less_antisym nth_append_length
        by metis
    next
      fix
        n :: nat and
        a' :: "'a"
      assume
        "n < Suc (length p)" and
        "above ((p@[r])!n) a = {a}" and
        "a \<notin> above r a" and
        "a' \<in> above (p!n) a"
      thus "a' = a"
        using insertI1 less_antisym nth_append_length p_pos singletonD
        by metis
    next
      fix n :: nat
      assume
        "n < Suc (length p)" and
        "above ((p@[r])!n) a = {a}" and
        "a \<notin> above r a"
      thus "a \<in> above (p!n) a"
        using insertI1 less_antisym nth_append_length p_pos
        by metis
    next
      fix
        n :: nat and
        a' :: "'a"
      assume
        "n < length p" and
        "above (p!n) a = {a}" and
        "a' \<in> above ((p@[r])!n) a"
      thus "a' = a"
        by (simp add: nth_append)
    next
      fix n :: nat
      assume
        "n < length p" and
        "above (p!n) a = {a}"
      thus "a \<in> above ((p@[r])!n) a"
        by (simp add: nth_append)
    qed
    have "finite {n. n < length p \<and> (above (p!n) a = {a})}"
      by simp
    moreover have "finite {n. n = length p \<and> (above ([r]!0) a = {a})}"
      by simp
    ultimately have
      "card ({i. i < length p \<and> (above (p!i) a = {a})} \<union>
        {i. i = length p \<and> (above ([r]!0) a = {a})}) =
          card {i. i < length p \<and> (above (p!i) a = {a})} +
            card {i. i = length p \<and> (above ([r]!0) a = {a})}"
      using card_Un_disjoint
      by blast
    thus
      "card {i. i < Suc (length p) \<and> (above ((p@[r])!i) a = {a})} =
        card {i. i < length p \<and> (above (p!i) a = {a})} +
          card {i. i = 0 \<and> (above ([r]!i) a = {a})}"
      using set_prof_eq shift_idx_a
      by auto
  qed
  have "win_count_code (p@[r]) a = win_count_code p a + win_count_code [r] a"
  proof (induction p, simp)
    case (Cons r' q)
    fix
      r :: "'a Preference_Relation" and
      r' :: "'a Preference_Relation" and
      q :: "'a Profile"
    assume "win_count_code (q@[r']) a =
              win_count_code q a + win_count_code [r'] a"
    thus "win_count_code ((r#q)@[r']) a =
            win_count_code (r#q) a + win_count_code [r'] a"
      by simp
  qed
  thus "win_count (p@[r]) a = win_count_code (p@[r]) a"
    using pref_count_induct base_case one_ballot_equiv
    by presburger
qed

fun prefer_count :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count p x y =
      card {i::nat. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"

fun prefer_count_code :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count_code Nil x y = 0" |
  "prefer_count_code (r#p) x y =
      (if y \<preceq>\<^sub>r x then 1 else 0) + prefer_count_code p x y"

lemma pref_count_equiv[code]:
  fixes
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  shows "prefer_count p a b = prefer_count_code p a b"
proof (induction p rule: rev_induct, simp)
  case (snoc r p)
  fix
    r :: "'a Preference_Relation" and
    p :: "'a Profile"
  assume base_case: "prefer_count p a b = prefer_count_code p a b"
  have size_one: "length [r] = 1"
    by simp
  have p_pos_in_ps: "\<forall> i < length p. p!i = (p@[r])!i"
    by (simp add: nth_append)
  have "prefer_count [r] a b =
          (let q = [r] in
            card {i::nat. i < length q \<and> (let r = (q!i) in (b \<preceq>\<^sub>r a))})"
    by simp
  hence one_ballot_equiv: "prefer_count [r] a b = prefer_count_code [r] a b"
    using size_one
    by (simp add: nth_Cons')
  have pref_count_induct:
    "prefer_count (p@[r]) a b = prefer_count p a b + prefer_count [r] a b"
  proof (simp)
    have "{i. i = 0 \<and> (b, a) \<in> [r]!i} = (if ((b, a) \<in> r) then {0} else {})"
      by (simp add: Collect_conv_if)
    hence shift_idx_a:
      "card {i. i = length p \<and> (b, a) \<in> [r]!0} = card {i. i = 0 \<and> (b, a) \<in> [r]!i}"
      by simp
    have set_prof_eq:
      "{i. i < Suc (length p) \<and> (b, a) \<in> (p@[r])!i} =
        {i. i < length p \<and> (b, a) \<in> p!i} \<union> {i. i = length p \<and> (b, a) \<in> [r]!0}"
    proof (safe, simp_all)
      fix i :: nat
      assume
        "i < Suc (length p)" and
        "(b, a) \<in> (p@[r])!i" and
        "i \<noteq> length p"
      thus "(b, a) \<in> p!i"
        using less_antisym p_pos_in_ps
        by metis
    next
      fix i :: nat
      assume
        "i < Suc (length p)" and
        "(b, a) \<in> (p@[r])!i" and
        "(b, a) \<notin> r"
      thus "i < length p"
        using less_antisym nth_append_length
        by metis
    next
      fix i :: nat
      assume
        "i < Suc (length p)" and
        "(b, a) \<in> (p@[r])!i" and
        "(b, a) \<notin> r"
      thus "(b, a) \<in> p!i"
        using less_antisym nth_append_length p_pos_in_ps
        by metis
    next
      fix i :: nat
      assume
        "i < length p" and
        "(b, a) \<in> p!i"
      thus "(b, a) \<in> (p@[r])!i"
        using less_antisym p_pos_in_ps
        by metis
    qed
    have fin_len_p: "finite {n. n < length p \<and> (b, a) \<in> p!n}"
      by simp
    have "finite {n. n = length p \<and> (b, a) \<in> [r]!0}"
      by simp
    hence
      "card ({i. i < length p \<and> (b, a) \<in> p!i} \<union> {i. i = length p \<and> (b, a) \<in> [r]!0}) =
          card {i. i < length p \<and> (b, a) \<in> p!i} +
            card {i. i = length p \<and> (b, a) \<in> [r]!0}"
      using fin_len_p card_Un_disjoint
      by blast
    thus
      "card {i. i < Suc (length p) \<and> (b, a) \<in> (p@[r])!i} =
        card {i. i < length p \<and> (b, a) \<in> p!i} + card {i. i = 0 \<and> (b, a) \<in> [r]!i}"
      using set_prof_eq shift_idx_a
      by simp
  qed
  have pref_count_code_induct:
    "prefer_count_code (p@[r]) a b =
      prefer_count_code p a b + prefer_count_code [r] a b"
  proof (simp, safe)
    assume y_pref_x: "(b, a) \<in> r"
    show "prefer_count_code (p@[r]) a b = Suc (prefer_count_code p a b)"
    proof (induction p, simp_all)
      show "(b, a) \<in> r"
        using y_pref_x
        by simp
    qed
  next
    assume not_y_pref_x: "(b, a) \<notin> r"
    show "prefer_count_code (p@[r]) a b = prefer_count_code p a b"
    proof (induction p, simp_all, safe)
      assume "(b, a) \<in> r"
      thus False
        using not_y_pref_x
        by simp
    qed
  qed
  show "prefer_count (p@[r]) a b = prefer_count_code (p@[r]) a b"
    using pref_count_code_induct pref_count_induct base_case one_ballot_equiv
    by presburger
qed

lemma set_compr:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> 'a set"
  shows "{f x | x. x \<in> A} = f ` A"
  by auto

lemma pref_count_set_compr:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  shows "{prefer_count p a a' | a'. a' \<in> A - {a}} = (prefer_count p a) ` (A - {a})"
  by auto

lemma pref_count:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    prof: "profile A p" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    neq: "a \<noteq> b"
  shows "prefer_count p a b = (length p) - (prefer_count p b a)"
proof -
  have "\<forall> i::nat. i < length p \<longrightarrow> connex A (p!i)"
    using prof
    unfolding profile_def
    by (simp add: lin_ord_imp_connex)
  hence asym: "\<forall> i::nat. i < length p \<longrightarrow>
              \<not> (let r = (p!i) in (b \<preceq>\<^sub>r a)) \<longrightarrow> (let r = (p!i) in (a \<preceq>\<^sub>r b))"
    using a_in_A b_in_A
    unfolding connex_def
    by metis
  have "\<forall> i::nat. i < length p \<longrightarrow> ((b, a) \<in> (p!i) \<longrightarrow> (a, b) \<notin> (p!i))"
    using antisymD neq lin_imp_antisym prof
    unfolding profile_def
    by metis
  hence "{i::nat. i < length p \<and> (let r = (p!i) in (b \<preceq>\<^sub>r a))} =
            {i::nat. i < length p} -
              {i::nat. i < length p \<and> (let r = (p!i) in (a \<preceq>\<^sub>r b))}"
    using asym
    by auto
  thus ?thesis
    by (simp add: card_Diff_subset Collect_mono)
qed

lemma pref_count_sym:
  fixes
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a" and
    c :: "'a"
  assumes
    pref_count_ineq: "prefer_count p a c \<ge> prefer_count p c b" and
    prof: "profile A p" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    c_in_A: "c \<in> A" and
    a_neq_c: "a \<noteq> c" and
    c_neq_b: "c \<noteq> b"
  shows "prefer_count p b c \<ge> prefer_count p c a"
proof -
  have "prefer_count p a c = (length p) - (prefer_count p c a)"
    using pref_count prof a_in_A c_in_A a_neq_c
    by metis
  moreover have pref_count_b_eq:
    "prefer_count p c b = (length p) - (prefer_count p b c)"
    using pref_count prof c_in_A b_in_A c_neq_b
    by (metis (mono_tags, lifting))
  hence "(length p) - (prefer_count p b c) \<le> (length p) - (prefer_count p c a)"
    using calculation pref_count_ineq
    by simp
  hence "(prefer_count p c a) - (length p) \<le> (prefer_count p b c) - (length p)"
    using a_in_A diff_is_0_eq diff_le_self a_neq_c pref_count prof c_in_A
    by (metis (no_types))
  thus ?thesis
    using pref_count_b_eq calculation pref_count_ineq
    by linarith
qed

lemma empty_prof_imp_zero_pref_count:
  fixes
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  assumes "p = []"
  shows "prefer_count p a b = 0"
  using assms
  by simp

lemma empty_prof_imp_zero_pref_count_code:
  fixes
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  assumes "p = []"
  shows "prefer_count_code p a b = 0"
  using assms
  by simp

lemma pref_count_code_incr:
  fixes
    p :: "'a Profile" and
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a" and
    n :: nat
  assumes
    "prefer_count_code p a b = n" and
    "b \<preceq>\<^sub>r a"
  shows "prefer_count_code (r#p) a b = n + 1"
  using assms
  by simp

lemma pref_count_code_not_smaller_imp_constant:
  fixes
    p :: "'a Profile" and
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a" and
    n :: nat
  assumes
    "prefer_count_code p a b = n" and
    "\<not> (b \<preceq>\<^sub>r a)"
  shows "prefer_count_code (r#p) a b = n"
  using assms
  by simp

fun wins :: "'a \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins a p b =
    (prefer_count p a b > prefer_count p b a)"

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
  "condorcet_winner A p a =
      (finite_profile A p \<and>  a \<in> A \<and> (\<forall> x \<in> A - {a}. wins a p x))"

lemma cond_winner_unique:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    "condorcet_winner A p a" and
    "condorcet_winner A p b"
  shows "b = a"
proof (rule ccontr)
  assume b_neq_a: "b \<noteq> a"
  have "wins b p a"
    using b_neq_a insert_Diff insert_iff assms
    by simp
  hence "\<not> wins a p b"
    by (simp add: wins_antisym)
  moreover have a_wins_against_b: "wins a p b"
    using Diff_iff b_neq_a singletonD assms
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
    "condorcet_winner A p a" and
    "b \<noteq> a"
  shows "\<not> condorcet_winner A p b"
  using cond_winner_unique assms
  by metis

lemma cond_winner_unique_3:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes "condorcet_winner A p a"
  shows "{a' \<in> A. condorcet_winner A p a'} = {a}"
proof (safe)
  fix a' :: "'a"
  assume "condorcet_winner A p a'"
  thus "a' = a"
    using assms cond_winner_unique
    by metis
next
  show "a \<in> A"
    using assms
    unfolding condorcet_winner.simps
    by (metis (no_types))
next
  show "condorcet_winner A p a"
    using assms
    by presburger
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
    "\<forall> A' p'.
      (profile (A'::'a set) p' \<longrightarrow> (\<forall> n < length p'. linear_order_on A' (p'!n))) \<and>
      ((\<forall> n < length p'. linear_order_on A' (p'!n)) \<longrightarrow> profile A' p')"
    unfolding profile_def
    by simp
  have limit_prof_simp: "limit_profile A p = map (limit A) p"
    by simp
  obtain n :: nat where
    prof_limit_n: "(n < length (limit_profile A p) \<longrightarrow>
            linear_order_on A (limit_profile A p!n)) \<longrightarrow> profile A (limit_profile A p)"
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
  "equiv_prof_except_a A p p' a \<equiv>
    finite_profile A p \<and> finite_profile A p' \<and> a \<in> A \<and> length p = length p' \<and>
      (\<forall> i::nat. i < length p \<longrightarrow> equiv_rel_except_a A (p!i) (p'!i) a)"

text \<open>
  An alternative gets lifted from one profile to another iff
  its ranking increases in at least one ballot, and nothing else changes.
\<close>

definition lifted :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A p p' a \<equiv>
    finite_profile A p \<and> finite_profile A p' \<and>
      a \<in> A \<and> length p = length p' \<and>
      (\<forall> i::nat. i < length p \<and> \<not> Preference_Relation.lifted A (p!i) (p'!i) a \<longrightarrow>
          (p!i) = (p'!i)) \<and>
      (\<exists> i::nat. i < length p \<and> Preference_Relation.lifted A (p!i) (p'!i) a)"

lemma lifted_imp_equiv_prof_except_a:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    p' :: "'a Profile" and
    a :: "'a"
  assumes "lifted A p p' a"
  shows "equiv_prof_except_a A p p' a"
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
  show "profile A p'"
    unfolding lifted_def
    by metis
next
  from assms
  show "a \<in> A"
    unfolding lifted_def
    by metis
next
  from assms
  show "length p = length p'"
    unfolding lifted_def
    by metis
next
  fix i :: nat
  assume "i < length p"
  with assms
  show "equiv_rel_except_a A (p!i) (p'!i) a"
    using lifted_imp_equiv_rel_except_a trivial_equiv_rel
    unfolding lifted_def profile_def
    by (metis (no_types))
qed

lemma negl_diff_imp_eq_limit_prof:
  fixes
    A :: "'a set" and
    A' :: "'a set" and
    p :: "'a Profile" and
    p' :: "'a Profile" and
    a :: "'a"
  assumes
    change: "equiv_prof_except_a A' p q a" and
    subset: "A \<subseteq> A'" and
    not_in_A: "a \<notin> A"
  shows "limit_profile A p = limit_profile A q"
proof (simp)
  have "\<forall> i::nat. i < length p \<longrightarrow> equiv_rel_except_a A' (p!i) (q!i) a"
    using change equiv_prof_except_a_def
    by metis
  hence "\<forall> i::nat. i < length p \<longrightarrow> limit A (p!i) = limit A (q!i)"
    using not_in_A negl_diff_imp_eq_limit subset
    by metis
  thus "map (limit A) p = map (limit A) q"
    using change equiv_prof_except_a_def length_map nth_equalityI nth_map
    by (metis (mono_tags, lifting))
qed

lemma limit_prof_eq_or_lifted:
  fixes
    A :: "'a set" and
    A' :: "'a set" and
    p :: "'a Profile" and
    p' :: "'a Profile" and
    a :: "'a"
  assumes
    lifted_a: "lifted A' p p' a" and
    subset: "A \<subseteq> A'"
  shows "limit_profile A p = limit_profile A p' \<or>
            lifted A (limit_profile A p) (limit_profile A p') a"
proof (cases)
  assume a_in_A: "a \<in> A"
  have "\<forall> i::nat. i < length p \<longrightarrow>
          (Preference_Relation.lifted A' (p!i) (p'!i) a \<or> (p!i) = (p'!i))"
    using lifted_a
    unfolding lifted_def
    by metis
  hence one:
    "\<forall> i::nat. i < length p \<longrightarrow>
         (Preference_Relation.lifted A (limit A (p!i)) (limit A (p'!i)) a \<or>
           (limit A (p!i)) = (limit A (p'!i)))"
    using limit_lifted_imp_eq_or_lifted subset
    by metis
  thus ?thesis
  proof (cases)
    assume "\<forall> i::nat. i < length p \<longrightarrow> (limit A (p!i)) = (limit A (p'!i))"
    thus ?thesis
      using length_map lifted_a nth_equalityI nth_map limit_profile.simps
      unfolding lifted_def
      by (metis (mono_tags, lifting))
  next
    assume forall_limit_p_q:
      "\<not> (\<forall> i::nat. i < length p \<longrightarrow> (limit A (p!i)) = (limit A (p'!i)))"
    let ?p = "limit_profile A p"
    let ?q = "limit_profile A p'"
    have "profile A ?p \<and> profile A ?q"
      using lifted_a limit_profile_sound subset
      unfolding lifted_def
      by metis
    moreover have "length ?p = length ?q"
      using lifted_a
      unfolding lifted_def
      by fastforce
    moreover have
      "\<exists> i::nat. i < length ?p \<and> Preference_Relation.lifted A (?p!i) (?q!i) a"
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
    using lifted_a negl_diff_imp_eq_limit_prof subset lifted_imp_equiv_prof_except_a
    by metis
qed

end

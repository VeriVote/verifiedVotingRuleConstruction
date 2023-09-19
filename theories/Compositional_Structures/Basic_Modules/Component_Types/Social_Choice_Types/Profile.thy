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
"HOL-Combinatorics.List_Permutation"
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
  A profile on a set of alternatives A and a voter set V consists of ballots
  that are linear orders on A for all voters in V.
  A finite profile is one where V and A are finite.
\<close>

definition profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> bool" where
  "profile V A p \<equiv> \<forall> v \<in> V. linear_order_on A (p v)"

abbreviation finite_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> bool" where
  "finite_profile V A p \<equiv> finite A \<and> finite V \<and> profile V A p"

text \<open>
  A common action of interest on elections is renaming the voters, 
  e.g. when talking about anonymity.
\<close>

fun rename :: "('v \<Rightarrow> 'v) \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "rename \<pi> (A, V, p) = (let p' = (\<lambda>v. p ((the_inv \<pi>) v)) in (A, \<pi> ` V, p'))"

lemma rename_sound:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes 
    prof: "profile V A p" and
    renamed: "(A, V', q) = rename \<pi> (A, V, p)" and
    bij: "bij \<pi>"
  shows "profile V' A q"
proof (unfold profile_def, safe)
  fix 
    v'::'v
  assume "v' \<in> V'"
  let ?q_img = "(((the_inv) \<pi>) v')"
  have "V' = \<pi> ` V" using renamed by simp
  hence "?q_img \<in> V"
    using UNIV_I \<open>v' \<in> V'\<close> bij bij_is_inj bij_is_surj 
          f_the_inv_into_f inj_image_mem_iff
    by (metis)
  hence "linear_order_on A (p ?q_img)"
    using prof
    by (simp add: profile_def)
  moreover have "q v' = p ?q_img" using renamed bij by simp
  ultimately show "linear_order_on A (q v')" by simp
qed

lemma rename_finite: 
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes 
    prof: "finite_profile V A p" and
    renamed: "(A, V', q) = rename \<pi> (A, V, p)" and
    bij: "bij \<pi>"
  shows "finite_profile V' A q"
proof (safe)
  show "finite A"
    using prof 
    by auto
  show "finite V'" 
    using bij renamed prof 
    by simp
  show "profile V' A q" 
    using assms rename_sound 
    by metis
qed

text \<open>
  A profile on a voter set that has a natural order can be viewed as a list of ballots.
\<close>

fun list_of_preferences :: "'v list \<Rightarrow> ('a, 'v) Profile 
                              \<Rightarrow> ('a Preference_Relation) list" where
  "list_of_preferences [] p = []" |
  "list_of_preferences (x#xs) p = (p x)#(list_of_preferences xs p)"

lemma lop_simps: 
  fixes
    i :: nat
  assumes 
    in_bounds: "i < length l"
  shows length_inv: "length (list_of_preferences l p) = length l" and
        index: "(list_of_preferences l p)!i = p (l!i)"
proof -
  show length_inv: "length (list_of_preferences l p) = length l"
    by (induction rule: list_of_preferences.induct, auto) 
next
  show "list_of_preferences l p ! i = p (l ! i)"
    sorry (* TODO *)
qed

fun to_list :: "'v::linorder set \<Rightarrow> ('a, 'v) Profile 
                  \<Rightarrow> ('a Preference_Relation) list" where
  "to_list V p = (if (finite V) 
                    then (list_of_preferences (sorted_list_of_set V) p)
                    else [])"

lemma to_list_simp: 
  fixes 
    i :: nat and
    V :: "'v::linorder set" and
    p :: "('a, 'v) Profile"
  assumes
    "i < card V"
  shows "(to_list V p)!i = p ((sorted_list_of_set V)!i)"
proof -
  have "(to_list V p)!i = (list_of_preferences (sorted_list_of_set V) p)!i"
    by auto
  also have "... = p ((sorted_list_of_set V)!i)"
    by (simp add: assms index)
  finally show ?thesis by auto
qed

lemma to_list_permutes_under_bij:
  fixes 
    \<pi> :: "'v::linorder \<Rightarrow> 'v" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes "bij \<pi>"
  shows
  "to_list (\<pi> ` V) (\<lambda>x. p ((the_inv \<pi>) x)) <~~> (to_list V p)"
proof -
  show "mset (to_list (\<pi> ` V) (\<lambda>x. p (the_inv \<pi> x))) = mset (to_list V p)"
  proof (cases "finite V")
    let ?q = "(\<lambda>x. p ((the_inv \<pi>) x))" and 
        ?v = "(\<pi> ` V)" and
        ?perm = "(\<lambda>i. (if (i < card V) then (i) else (i)))"
    case True
    have "length (sorted_list_of_set ?v) = card V"
      using assms bij_betw_same_card bij_betw_subset top_greatest
            sorted_list_of_set.length_sorted_key_list_of_set 
      by metis
    hence "i < card V \<Longrightarrow> (to_list ?v ?q)!i = ?q ((sorted_list_of_set ?v)!i)"
      using to_list_simp
      by (metis sorted_list_of_set.length_sorted_key_list_of_set)
    hence "i < card V \<Longrightarrow> (to_list ?v ?q)!i = p ((the_inv \<pi>) ((sorted_list_of_set ?v)!i))"
      by auto
    hence "i < card V \<Longrightarrow> (to_list ?v ?q)!i = p ((sorted_list_of_set V)!(?perm i))"
      sorry
    moreover have "to_list V p = list_of_preferences (sorted_list_of_set V) p"
      by auto
    ultimately have "(to_list ?v ?q) = permute_list ?perm (to_list V p)"
      sorry
    thus ?thesis 
      by simp
  next
    case False
    hence "infinite (\<pi> ` V)" using \<open>bij \<pi>\<close>
      by (meson bij_betw_finite bij_betw_subset top_greatest)
    hence "(to_list (\<pi> ` V) (\<lambda>x. p (the_inv \<pi> x))) = []"
      by simp
    moreover have "to_list V p = []" 
      using \<open>infinite V\<close>
      by simp
    ultimately show ?thesis
      by presburger
  qed
qed
  

subsection \<open>Preference Counts and Comparisons\<close>

text \<open>
  The win count for an alternative a with respect to a finite voter set V in a profile p is
  the amount of ballots from V in p that rank alternative a in first position.
  If the voter set is infinite, counting is not generally possible.
\<close>

fun win_count :: "'v set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> enat" where
  "win_count V p a = (if (finite V) 
    then card {v\<in>V. above (p v) a = {a}} else infinity)"

fun prefer_count :: "'v set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "prefer_count V p x y = (if (finite V)
      then card {v\<in>V. (let r = (p v) in (y \<preceq>\<^sub>r x))} else infinity)"

lemma pref_count_voter_set_card:
  fixes 
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: 'a and
    b :: 'a
  assumes finV: "finite V"
  shows "prefer_count V p a b \<le> card V"
proof (simp)
  have "{v \<in> V. (b, a) \<in> p v} \<subseteq> V" by auto
  hence "card {v \<in> V. (b, a) \<in> p v} \<le> card V"
    using finV Finite_Set.card_mono
    by metis
  thus "(finite V \<longrightarrow> card {v \<in> V. (b, a) \<in> p v} \<le> card V) \<and> finite V"
    by (simp add: finV)
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
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  shows "{prefer_count V p a a' | a'. a' \<in> A - {a}} = (prefer_count V p a) ` (A - {a})"
  by auto

lemma pref_count:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    prof: "profile V A p" and
    fin: "finite V" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    neq: "a \<noteq> b"
  shows "prefer_count V p a b = card V - (prefer_count V p b a)"
proof -
  have "\<forall> v\<in>V. connex A (p v)"
    using prof
    unfolding profile_def
    by (simp add: lin_ord_imp_connex)
  hence asym: "\<forall> v\<in>V. \<not> (let r = (p v) in (b \<preceq>\<^sub>r a)) \<longrightarrow> (let r = (p v) in (a \<preceq>\<^sub>r b))"
    using a_in_A b_in_A
    unfolding connex_def
    by metis
  have "\<forall> v\<in>V. ((b, a) \<in> (p v) \<longrightarrow> (a, b) \<notin> (p v))"
    using antisymD neq lin_imp_antisym prof
    unfolding profile_def
    by metis
  hence "{v\<in>V. (let r = (p v) in (b \<preceq>\<^sub>r a))} =
            V - {v\<in>V. (let r = (p v) in (a \<preceq>\<^sub>r b))}"
    using asym
    by auto
  thus ?thesis
    by (simp add: card_Diff_subset Collect_mono fin)
qed

lemma pref_count_sym:
  fixes
    p :: "('a, 'v) Profile" and
    V :: "'v set" and
    a :: "'a" and
    b :: "'a" and
    c :: "'a"
  assumes
    pref_count_ineq: "prefer_count V p a c \<ge> prefer_count V p c b" and
    prof: "profile V A p" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    c_in_A: "c \<in> A" and
    a_neq_c: "a \<noteq> c" and
    c_neq_b: "c \<noteq> b"
  shows "prefer_count V p b c \<ge> prefer_count V p c a"
proof (cases)
  assume finV: "finite V"
  have nat1: "prefer_count V p c a \<in> \<nat>"
    by (simp add: Nats_def of_nat_eq_enat finV) 
  have nat2: "prefer_count V p b c \<in> \<nat>"
    by (simp add: Nats_def of_nat_eq_enat finV)
  have smaller: "prefer_count V p c a \<le> card V"
    using prof finV pref_count_voter_set_card
    by metis
  have "prefer_count V p a c = card V - (prefer_count V p c a)"
    using pref_count prof a_in_A c_in_A a_neq_c finV
    by (metis (no_types, opaque_lifting))
  moreover have pref_count_b_eq: 
    "prefer_count V p c b = card V - (prefer_count V p b c)"
    using pref_count prof a_in_A c_in_A a_neq_c b_in_A c_neq_b finV
    by metis
  hence ineq: "card V - (prefer_count V p b c) \<le> card V - (prefer_count V p c a)"
    using calculation pref_count_ineq
    by simp
  hence "card V - (prefer_count V p b c) + (prefer_count V p c a) \<le> 
          card V - (prefer_count V p c a) + (prefer_count V p c a)"
    using pref_count_b_eq pref_count_ineq 
    by auto
  hence "card V + (prefer_count V p c a) \<le> card V + (prefer_count V p b c)"
    using nat1 nat2 finV smaller
    by simp
  thus ?thesis by simp
next
  assume infV: "infinite V"
  have "prefer_count V p c a = infinity" 
    using infV 
    by simp
  moreover have "prefer_count V p b c = infinity" 
    using infV 
    by simp
  thus ?thesis by simp
qed

lemma empty_prof_imp_zero_pref_count:
  fixes
    p :: "('a, 'v) Profile" and
    V :: "'v set" and
    a :: "'a" and
    b :: "'a"
  assumes "V = {}"
  shows "prefer_count V p a b = 0"
  by (simp add: zero_enat_def assms)

(* lemma pref_count_code_incr:
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
  by simp *)

fun wins :: "'v set \<Rightarrow> 'a \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins V a p b =
    (prefer_count V p a b > prefer_count V p b a)"

lemma wins_inf_voters:
  fixes
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a" and
    V :: "'v set"
  assumes "infinite V"
  shows "wins V b p a = False"
  using assms
  by simp

text \<open>
  Alternative a wins against b implies that b does not win against a.
\<close>

lemma wins_antisym:
  fixes
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a" and
    V :: "'v set"
  assumes "wins V a p b" (* \<Longrightarrow> finite V *)
  shows "\<not> wins V b p a"
  using assms
  by simp

lemma wins_irreflex:
  fixes
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    V :: "'v set"
  shows "\<not> wins V a p a"
  using wins_antisym
  by metis

subsection \<open>Condorcet Winner\<close>

fun condorcet_winner :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner V A p a =
      (finite_profile V A p \<and> a \<in> A \<and> (\<forall> x \<in> A - {a}. wins V a p x))"

lemma cond_winner_unique:
  fixes
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    "condorcet_winner V A p a" and
    "condorcet_winner V A p b"
  shows "b = a"
proof (rule ccontr)
  assume b_neq_a: "b \<noteq> a"
  have "wins V b p a"
    using b_neq_a insert_Diff insert_iff assms
    by simp
  hence "\<not> wins V a p b"
    by (simp add: wins_antisym)
  moreover have a_wins_against_b: "wins V a p b"
    using Diff_iff b_neq_a singletonD assms
    by auto
  ultimately show False
    by simp
qed

lemma cond_winner_unique_2:
  fixes
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    "condorcet_winner V A p a" and
    "b \<noteq> a"
  shows "\<not> condorcet_winner V A p b"
  using cond_winner_unique assms
  by metis

lemma cond_winner_unique_3:
  fixes
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "condorcet_winner V A p a"
  shows "{a' \<in> A. condorcet_winner V A p a'} = {a}"
proof (safe)
  fix a' :: "'a"
  assume "condorcet_winner V A p a'"
  thus "a' = a"
    using assms cond_winner_unique
    by metis
next
  show "a \<in> A"
    using assms
    unfolding condorcet_winner.simps
    by (metis (no_types))
next
  show "condorcet_winner V A p a"
    using assms
    by presburger
qed

subsection \<open>Limited Profile\<close>

text \<open>
  This function restricts a profile p to a set A of alternatives and
  a set V of voters s.t. voters outside of V don't have any preferences/
  do not cast a vote.
  Keeps all of A's preferences.
\<close>

fun limit_profile :: "'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile" where
  "limit_profile A p = (\<lambda>v. limit A (p v))" 

lemma limit_prof_trans:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    C :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B"
  shows "limit_profile C p = limit_profile C (limit_profile B p)"
  using assms
  by auto

lemma limit_profile_sound:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    profile: "finite_profile V B p" and
    subset: "A \<subseteq> B"
  shows "finite_profile V A (limit_profile A p)"
proof (safe)
  have finA: "finite B \<longrightarrow> A \<subseteq> B \<longrightarrow> finite A"
    using rev_finite_subset
    by metis
  with profile
  show "finite A"
    using subset
    by metis
next
  show finV: "finite V" using profile by auto
next
  have "\<forall> v \<in> V. linear_order_on A (limit A (p v))"
    by (metis profile profile_def subset limit_presv_lin_ord)
  hence "\<forall> v \<in> V. linear_order_on A ((limit_profile A p) v)"
    by simp
  thus "profile V A (limit_profile A p)"
    using profile_def 
    by auto
qed

(* have limit_prof_simp: "limit_profile A p = map (limit A) p"
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
  thus "profile A V (limit_profile A p)"
    using prof_length prof_limit_n limit_prof_simp limit_presv_lin_ord nth_map subset
    by (metis (no_types)) *)


(*
lemma limit_prof_presv_size:
  fixes
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  shows "length p = length (limit_profile A p)"
  by simp
*)

subsection \<open>Lifting Property\<close>

definition equiv_prof_except_a :: 
"'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv_prof_except_a V A p p' a \<equiv>
    profile V A p \<and> profile V A p' \<and> a \<in> A \<and> 
      (\<forall> v\<in>V. equiv_rel_except_a A (p v) (p' v) a)"
(* profile or finite_profile or finite A? *)

text \<open>
  An alternative gets lifted from one profile to another iff
  its ranking increases in at least one ballot, and nothing else changes.
\<close>

definition lifted :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted V A p p' a \<equiv>
    profile V A p \<and> profile V A p' \<and> a \<in> A 
      \<and> (\<forall> v\<in>V. \<not> Preference_Relation.lifted A (p v) (p' v) a \<longrightarrow> (p v) = (p' v)) 
      \<and> (\<exists> v\<in>V. Preference_Relation.lifted A (p v) (p' v) a)"

lemma lifted_imp_equiv_prof_except_a:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "lifted V A p p' a"
  shows "equiv_prof_except_a V A p p' a"
proof (unfold equiv_prof_except_a_def, safe)
  from assms
  show "profile V A p"
    unfolding lifted_def
    by metis
next
  from assms
  show "profile V A p'"
    unfolding lifted_def
    by metis
next
  from assms
  show "a \<in> A"
    unfolding lifted_def
    by metis
next
  fix v::'v
  assume "v \<in> V"
  with assms
  show "equiv_rel_except_a A (p v) (p' v) a"
    using lifted_imp_equiv_rel_except_a trivial_equiv_rel
    unfolding lifted_def profile_def
    by (metis (no_types))
qed

(*
lemma negl_diff_imp_eq_limit_prof:
  fixes
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    change: "equiv_prof_except_a V A' p q a" and
    subset: "A \<subseteq> A'" and
    not_in_A: "a \<notin> A"
  shows "limit_profile A p = limit_profile A q"
proof (simp)
  have "\<forall>v\<in>V. equiv_rel_except_a A' (p v) (q v) a"
    using change equiv_prof_except_a_def
    by metis
  hence "\<forall>v\<in>V. limit A (p v) = limit A (q v)"
    using not_in_A negl_diff_imp_eq_limit subset
    by metis
  fix
    v::'v and
    a::'a and
    b::'a
  assume "a \<in> A \<and> b \<in> B"
  moreover have "(a,b) \<in> p v \<longleftrightarrow> (a,b) \<in> q v"
    using change
    try
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
qed*)

end

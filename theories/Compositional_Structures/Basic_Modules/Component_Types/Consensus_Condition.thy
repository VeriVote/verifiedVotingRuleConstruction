(*  File:       Consensus_Condition.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Consensus Condition\<close>

theory Consensus_Condition
  imports "HOL-Combinatorics.List_Permutation"
          "Social_Choice_Types/Profile"
begin

text \<open>
  TODO.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Consensus_Condition = "'a Election \<Rightarrow> bool"

subsection \<open>Consensus Conditions\<close>

text \<open>
  Nonempty set.
\<close>

fun nonempty_set_condition :: "'a Consensus_Condition" where
  "nonempty_set_condition (A, p) = (A \<noteq> {})"

text \<open>
  Nonempty profile.
\<close>

fun nonempty_profile_condition :: "'a Consensus_Condition" where
  "nonempty_profile_condition (A, p) = (p \<noteq> [])"

text \<open>
  Equal top ranked alternatives.
\<close>

fun equal_top_condition' :: "'a \<Rightarrow> 'a Consensus_Condition" where
  "equal_top_condition' a (A, p) = ((a \<in> A) \<and> (\<forall> i < length p. above (p!i) a = {a}))"

fun equal_top_condition :: "'a Consensus_Condition" where
  "equal_top_condition E = (\<exists> a. equal_top_condition' a E)"

text \<open>
  Equal votes.
\<close>

fun equal_vote_condition' :: "'a Preference_Relation \<Rightarrow> 'a Consensus_Condition" where
  "equal_vote_condition' r (A, p) = (\<forall> i < length p. (p!i) = r)"

fun equal_vote_condition :: "'a Consensus_Condition" where
  "equal_vote_condition E = (\<exists> r. equal_vote_condition' r E)"

text \<open>
  Unanimity condition.
\<close>

fun unanimity_condition :: "'a Consensus_Condition" where
  "unanimity_condition c =
    (nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_top_condition c)"

text \<open>
  Strong unanimity condition.
\<close>

fun strong_unanimity_condition :: "'a Consensus_Condition" where
  "strong_unanimity_condition c =
    (nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_vote_condition c)"


subsection \<open>Properties\<close>

definition consensus_anonymity :: "'a Consensus_Condition \<Rightarrow> bool" where
  "consensus_anonymity c \<equiv>
    \<forall> A p q. finite_profile A p \<and> finite_profile A q \<and> p <~~> q \<longrightarrow> c (A, p) \<longrightarrow> c (A, q)"

subsection \<open>Auxiliary Lemmas\<close>

lemma cons_anon_if_ex_cons_anon:
  fixes
    b :: "'a Consensus_Condition" and
    b':: "'b \<Rightarrow> 'a Consensus_Condition"
  assumes
    general_cond_b: "b = (\<lambda> E. \<exists> x. b' x E)" and
    all_cond_anon: "\<forall> x. consensus_anonymity (b' x)"
  shows "consensus_anonymity b"
proof (unfold consensus_anonymity_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    cond_b: "b (A, p)" and
    fin_C: "finite A" and
    prof_p: "profile A p" and
    prof_q: "profile A q" and
    perm: "p <~~> q"
  have "\<exists> x. b' x (A, p)"
    using cond_b general_cond_b
    by simp
  then obtain x :: 'b where
    "b' x (A, p)"
    by blast
  hence "b' x (A, q)"
    using all_cond_anon perm fin_C prof_p prof_q
    unfolding consensus_anonymity_def
    by blast
  hence "\<exists> x. b' x (A, q)"
    by metis
  thus "b (A, q)"
    using general_cond_b
    by simp
qed

subsection \<open>Theorems\<close>

lemma nonempty_set_cond_anonymous: "consensus_anonymity nonempty_set_condition"
  unfolding consensus_anonymity_def
  by simp

lemma nonempty_profile_cond_anonymous: "consensus_anonymity nonempty_profile_condition"
proof (unfold consensus_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    perm: "p <~~> q" and
    not_empty_p: "nonempty_profile_condition (A, p)"
  have "length q = length p"
    using perm perm_length
    by force
  thus "nonempty_profile_condition (A, q)"
    using not_empty_p length_0_conv
    unfolding nonempty_profile_condition.simps
    by metis
qed

lemma equal_top_cond'_anonymous:
  fixes a :: "'a"
  shows "consensus_anonymity (equal_top_condition' a)"
proof (unfold consensus_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    perm: "p <~~> q" and
    top_cons_a: "equal_top_condition' a (A, p)"
  from perm obtain pi where
    perm_pi: "pi permutes {..< length p}" and
    perm_list_q: "permute_list pi p = q"
    using mset_eq_permutation
    by metis
  have l: "length p = length q"
    using perm perm_length
    by force
  hence "\<forall> i < length q. pi i < length p"
    using perm_pi permutes_in_image
    by fastforce
  moreover have "\<forall> i < length q. q!i = p!(pi i)"
    using perm_list_q
    unfolding permute_list_def
    by auto
  moreover have winner: "\<forall> i < length p. above (p!i) a = {a}"
    using top_cons_a
    by simp
  ultimately have "\<forall> i < length p. above (q!i) a = {a}"
    using l
    by metis
  moreover have "a \<in> A"
    using top_cons_a
    by simp
  ultimately show "equal_top_condition' a (A, q)"
    using l
    unfolding equal_top_condition'.simps
    by metis
qed

lemma eq_top_cond_anon: "consensus_anonymity equal_top_condition"
  using equal_top_cond'_anonymous
        cons_anon_if_ex_cons_anon[of equal_top_condition equal_top_condition']
  by fastforce

lemma eq_vote_cond'_anon:
  fixes r :: "'a Preference_Relation"
  shows "consensus_anonymity (equal_vote_condition' r)"
proof (unfold consensus_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    perm: "p <~~> q" and
    equal_votes_pref: "equal_vote_condition' r (A, p)" 
  from perm obtain pi where
    perm_pi: "pi permutes {..< length p}" and
    perm_list_q: "permute_list pi p = q"
    using mset_eq_permutation
    by metis
  have l: "length p = length q"
    using perm perm_length
    by force
  hence "\<forall> i < length q. pi i < length p"
    using perm_pi permutes_in_image
    by fastforce
  moreover have "\<forall> i < length q. q!i = p!(pi i)"
    using perm_list_q
    unfolding permute_list_def
    by auto
  moreover have winner: "\<forall> i < length p. p!i = r"
    using equal_votes_pref
    by simp
  ultimately have "\<forall> i < length p. q!i = r"
    using l
    by metis
  thus "equal_vote_condition' r (A, q)"
    using l
    unfolding equal_vote_condition'.simps
    by metis
qed

lemma eq_vote_cond_anon: "consensus_anonymity equal_vote_condition"
  unfolding equal_vote_condition.simps
  using eq_vote_cond'_anon cons_anon_if_ex_cons_anon
  by blast

end

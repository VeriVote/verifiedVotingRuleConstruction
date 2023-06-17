(*  File:       Consensus_Condition.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Consensus Condition\<close>

theory Consensus_Condition
  imports "Social_Choice_Types/Profile"
          "HOL-Combinatorics.List_Permutation"
begin

text \<open>
  TODO.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Consensus_Condition = "'a Election \<Rightarrow> bool"

subsection \<open>TODO\<close>

definition consensus_condition_anonymity :: "'a Consensus_Condition \<Rightarrow> bool" where
  "consensus_condition_anonymity cc \<equiv>
    \<forall> A p q. finite_profile A p \<and> finite_profile A q \<and> p <~~> q \<longrightarrow> cc (A, p) \<longrightarrow> cc (A, q)"

lemma cond_anon_if_ex_cond_anon:
  fixes
    b':: "'b \<Rightarrow> 'a Consensus_Condition" and
    b :: "'a Consensus_Condition"
  assumes
    general_cond_b: "b = (\<lambda> E. \<exists> x. b' x E)" and
    all_cond_anon: "\<forall> x. consensus_condition_anonymity (b' x)"
  shows "consensus_condition_anonymity b"
proof (unfold consensus_condition_anonymity_def, safe)
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
  from cond_b general_cond_b
  have "\<exists> x. b' x (A, p)"
    by simp
  then obtain x :: 'b where
    "b' x (A, p)"
    by blast
  with all_cond_anon
  have "b' x (A, q)"
    using perm fin_C prof_p prof_q
    unfolding consensus_condition_anonymity_def
    by blast
  hence "\<exists> x. b' x (A, q)"
    by metis
  thus "b (A, q)"
    using general_cond_b
    by simp
qed

subsection \<open>Consensus Conditions\<close>

text \<open>
  Nonempty set.
\<close>

fun ne_set_cond :: "'a Consensus_Condition" where
  "ne_set_cond (A, p) = (A \<noteq> {})"

lemma ne_set_cond_anon: "consensus_condition_anonymity ne_set_cond"
  unfolding consensus_condition_anonymity_def
  by simp

text \<open>
  Nonempty profile.
\<close>

fun ne_profile_cond :: "'a Consensus_Condition" where
  "ne_profile_cond (A, p) = (p \<noteq> [])"

lemma ne_profile_cond_anon: "consensus_condition_anonymity ne_profile_cond"
proof (unfold consensus_condition_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    perm: "p <~~> q" and
    not_empty_p: "ne_profile_cond (A, p)"
  from perm
  have "length q = length p"
    using perm_length
    by force
  thus "ne_profile_cond (A, q)"
    using not_empty_p length_0_conv
    unfolding ne_profile_cond.simps
    by metis
qed

text \<open>
  Equal top ranked alternatives.
\<close>

fun eq_top_cond' :: "'a \<Rightarrow> 'a Consensus_Condition" where
  "eq_top_cond' a (A, p) = ((a \<in> A) \<and> (\<forall> i < length p. above (p!i) a = {a}))"

fun eq_top_cond :: "'a Consensus_Condition" where
  "eq_top_cond E = (\<exists> a. eq_top_cond' a E)"

lemma eq_top_cond'_anon:
  fixes a :: "'a"
  shows "consensus_condition_anonymity (eq_top_cond' a)"
proof (unfold consensus_condition_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    perm: "p <~~> q" and
    top_cons_a: "eq_top_cond' a (A, p)"
  from perm obtain pi where
    perm_pi: "pi permutes {..< length p}" and
    perm_list_q: "permute_list pi p = q"
    using mset_eq_permutation
    by metis
  from perm
  have l: "length p = length q"
    using perm_length
    by force
  hence "\<forall> i < length q. pi i < length p"
    using perm_pi permutes_in_image
    by fastforce
  moreover from perm_list_q have "\<forall> i < length q. q!i = p!(pi i)"
    unfolding permute_list_def
    by auto
  moreover from top_cons_a have winner: "\<forall> i < length p. above (p!i) a = {a}"
    by simp
  ultimately have "\<forall> i < length p. above (q!i) a = {a}"
    using l
    by metis
  moreover from top_cons_a have "a \<in> A"
    by simp
  ultimately show "eq_top_cond' a (A, q)"
    using l
    unfolding eq_top_cond'.simps
    by metis
qed

lemma eq_top_cond_anon: "consensus_condition_anonymity eq_top_cond"
  using eq_top_cond'_anon cond_anon_if_ex_cond_anon[of eq_top_cond eq_top_cond']
  by fastforce

text \<open>
  Equal votes.
\<close>

fun eq_vote_cond' :: "'a Preference_Relation \<Rightarrow> 'a Consensus_Condition" where
  "eq_vote_cond' pref (A, p) = (\<forall> i < length p. (p!i) = pref)"

fun eq_vote_cond :: "'a Consensus_Condition" where
  "eq_vote_cond E = (\<exists> pref. eq_vote_cond' pref E)"

lemma eq_vote_cond'_anon:
  fixes pref :: "'a Preference_Relation"
  shows "consensus_condition_anonymity (eq_vote_cond' pref)"
proof (unfold consensus_condition_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    pref :: "'a Preference_Relation"
  assume
    perm: "p <~~> q" and
    equal_votes_pref: "eq_vote_cond' pref (A, p)" 
  from perm obtain pi where
    perm_pi: "pi permutes {..< length p}" and
    perm_list_q: "permute_list pi p = q"
    using mset_eq_permutation
    by metis
  from perm
  have l: "length p = length q"
    using perm_length
    by force
  hence "\<forall> i < length q. pi i < length p"
    using perm_pi permutes_in_image
    by fastforce
  moreover from perm_list_q
  have "\<forall> i < length q. q!i = p!(pi i)"
    unfolding permute_list_def
    by auto
  moreover from equal_votes_pref
  have winner: "\<forall> i < length p. p!i = pref"
    by simp
  ultimately have "\<forall> i < length p. q!i = pref"
    using l
    by metis
  thus "eq_vote_cond' pref (A, q)"
    using l
    unfolding eq_vote_cond'.simps
    by metis
qed

lemma eq_vote_cond_anon: "consensus_condition_anonymity eq_vote_cond"
proof (unfold eq_vote_cond.simps)
  show "consensus_condition_anonymity (\<lambda> E. \<exists> x. eq_vote_cond' x E)"
    using eq_vote_cond'_anon cond_anon_if_ex_cond_anon
    by blast
qed

text \<open>
  Unanimity condition.
\<close>

fun unanimity_condition :: "'a Consensus_Condition" where
  "unanimity_condition E = (ne_set_cond E \<and> ne_profile_cond E \<and> eq_top_cond E)"

text \<open>
  Strong unanimity condition.
\<close>

fun strong_unanimity_condition :: "'a Consensus_Condition" where
  "strong_unanimity_condition E =
   (\<lambda> E. ne_set_cond E \<and> ne_profile_cond E \<and> eq_vote_cond E) E"

end

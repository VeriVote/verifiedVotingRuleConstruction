(*  File:       Consensus_Condition.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Consensus Condition\<close>

theory Consensus_Condition
  imports "Social_Choice_Types/Profile"
begin

text \<open>
  TODO.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Consensus_Condition = "'a Election \<Rightarrow> bool"

subsection \<open>TODO\<close>

definition consensus_condition_anonymity :: "'a Consensus_Condition \<Rightarrow> bool" where
  "consensus_condition_anonymity CC \<equiv>
    \<forall> pi A p. finite_profile A p \<longrightarrow> newnameforpermut pi \<longrightarrow> CC (A, p) \<longrightarrow> CC (A, pi p)"

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
    pi::"'a Profile \<Rightarrow> 'a Profile" and
    A :: "'a set" and
    p :: "'a Profile"
  assume
    perm_pi: "newnameforpermut pi" and
    cond_b: "b (A, p)" and
    fin_C: "finite A" and
    prof_p: "profile A p"
  from cond_b general_cond_b
  have "\<exists> x. b' x (A, p)"
    by auto
  then obtain x::'b where
    "b' x (A, p)"
    by blast
  with all_cond_anon
  have "b' x (A, pi p)"
    using perm_pi fin_C prof_p
    unfolding consensus_condition_anonymity_def
    by simp
  hence "\<exists> x. b' x (A, pi p)"
    by auto
  thus "b (A, pi p)"
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
    pi :: "'a Profile \<Rightarrow> 'a Profile" and
    A :: "'a set" and
    p :: "'a Profile"
  assume
    perm_pi: "newnameforpermut pi" and
    not_empty_p: "ne_profile_cond (A, p)"
  from perm_pi
  have "length (pi p) = length p"
    unfolding newnameforpermut_def n_permutation_def
    by simp
  thus "ne_profile_cond (A, pi p)"
    using not_empty_p
    by auto
qed

text \<open>
  Equal top ranked alternatives.
\<close>

fun eq_top_cond' :: "'a \<Rightarrow> 'a Consensus_Condition" where
  "eq_top_cond' a (A, p) = ((a \<in> A) \<and> (\<forall> i < length p. above (p!i) a = {a}))"

fun eq_top_cond :: "'a Consensus_Condition" where
  "eq_top_cond E = (\<exists> a. eq_top_cond' a E)"

lemma eq_top_cond'_anon: "\<forall> a. consensus_condition_anonymity (eq_top_cond' a)"
proof (unfold consensus_condition_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    pi :: "'a Profile \<Rightarrow> 'a Profile" and
    a :: "'a"
  assume
    perm_pi: "newnameforpermut pi" and
    top_cons_a: "eq_top_cond' a (A, p)"
  let ?b = "bij (length p) pi"
  from perm_pi
  have l: "length p = length (pi p)"
    unfolding newnameforpermut_def n_permutation_def
    by simp
  hence "\<forall> i < length (pi p). ?b i < length p"
    using bij_of_perm_is_bij perm_pi
          bij_betw_apply lessThan_iff
    unfolding newnameforpermut_def
    by metis
  moreover from perm_pi
  have "\<forall> i < length (pi p). (pi p)!i = p!(?b i)"
    using bij_of_perm_item_mapping l
    unfolding newnameforpermut_def
    by metis
  moreover from top_cons_a
  have winner: "\<forall> i < length p. above (p!i) a = {a}"
    by simp
  ultimately have "\<forall> i < length p. above (pi p!i) a = {a}"
    using l
    by metis
  moreover from top_cons_a
  have "a \<in> A"
    by simp
  ultimately show "eq_top_cond' a (A, pi p)"
    using l
    by simp
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

lemma eq_vote_cond'_anon: "\<forall> pref. consensus_condition_anonymity (eq_vote_cond' pref)"
proof (unfold consensus_condition_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    pi :: "'a Profile \<Rightarrow> 'a Profile" and
    pref :: "'a Preference_Relation"
  assume
    perm_pi: "newnameforpermut pi" and
    equal_votes_pref: "eq_vote_cond' pref (A, p)"
  let ?b = "bij (length p) pi"
  from perm_pi
  have l: "length p = length (pi p)"
    unfolding newnameforpermut_def n_permutation_def
    by simp
  hence "\<forall> i < length (pi p). ?b i < length p"
    using bij_of_perm_is_bij perm_pi
          bij_betw_apply lessThan_iff
    unfolding newnameforpermut_def
    by metis
  moreover from perm_pi
  have "\<forall> i < length (pi p). (pi p)!i = p!(?b i)"
    using bij_of_perm_item_mapping l
    unfolding newnameforpermut_def
    by metis
  moreover from equal_votes_pref
  have winner: "\<forall> i < length p. (p!i) = pref"
    by simp
  ultimately have "\<forall> i < length p. (pi p!i) = pref"
    using l
    by metis
  thus "eq_vote_cond' pref (A, pi p)"
    using l
    by simp
qed

lemma eq_vote_cond_anon: "consensus_condition_anonymity eq_vote_cond"
proof (unfold eq_vote_cond.simps)
  show "consensus_condition_anonymity (\<lambda> E. \<exists> x. eq_vote_cond' x E)"
    using eq_vote_cond'_anon cond_anon_if_ex_cond_anon
    by auto
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

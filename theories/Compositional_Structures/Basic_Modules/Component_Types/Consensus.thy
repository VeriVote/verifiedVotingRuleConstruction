(*  File:       Consensus.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Consensus\<close>

theory Consensus
  imports "HOL-Combinatorics.List_Permutation"
          "Social_Choice_Types/Profile"
begin

text \<open>
  An election consisting of a set of alternatives and a list of preferential votes (a profile)
  is a consensus if it has an undisputed winner reflecting a certain concept of fairness in the
  society.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Consensus = "'a Election \<Rightarrow> bool"

subsection \<open>Consensus Conditions\<close>

text \<open>
  Nonempty set.
\<close>

fun nonempty_set\<^sub>\<C> :: "'a Consensus" where
  "nonempty_set\<^sub>\<C> (A, p) = (A \<noteq> {})"

text \<open>
  Nonempty profile.
\<close>

fun nonempty_profile\<^sub>\<C> :: "'a Consensus" where
  "nonempty_profile\<^sub>\<C> (A, p) = (p \<noteq> [])"

text \<open>
  Equal top ranked alternatives.
\<close>

fun equal_top\<^sub>\<C>' :: "'a \<Rightarrow> 'a Consensus" where
  "equal_top\<^sub>\<C>' a (A, p) = (a \<in> A \<and> (\<forall> i < length p. above (p!i) a = {a}))"

fun equal_top\<^sub>\<C> :: "'a Consensus" where
  "equal_top\<^sub>\<C> c = (\<exists> a. equal_top\<^sub>\<C>' a c)"

text \<open>
  Equal votes.
\<close>

fun equal_vote\<^sub>\<C>' :: "'a Preference_Relation \<Rightarrow> 'a Consensus" where
  "equal_vote\<^sub>\<C>' r (A, p) = (\<forall> i < length p. (p!i) = r)"

fun equal_vote\<^sub>\<C> :: "'a Consensus" where
  "equal_vote\<^sub>\<C> c = (\<exists> r. equal_vote\<^sub>\<C>' r c)"

text \<open>
  Unanimity condition.
\<close>

fun unanimity\<^sub>\<C> :: "'a Consensus" where
  "unanimity\<^sub>\<C> c = (nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C> c)"

text \<open>
  Strong unanimity condition.
\<close>

fun strong_unanimity\<^sub>\<C> :: "'a Consensus" where
  "strong_unanimity\<^sub>\<C> c = (nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C> c)"


subsection \<open>Properties\<close>

definition consensus_anonymity :: "'a Consensus \<Rightarrow> bool" where
  "consensus_anonymity c \<equiv>
    \<forall> A p q. profile A p \<and> profile A q \<and> p <~~> q \<longrightarrow> c (A, p) \<longrightarrow> c (A, q)"

subsection \<open>Auxiliary Lemmas\<close>

lemma ex_anon_cons_imp_cons_anonymous:
  fixes
    b :: "'a Consensus" and
    b':: "'b \<Rightarrow> 'a Consensus"
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
    using all_cond_anon perm prof_p prof_q
    unfolding consensus_anonymity_def
    by blast
  hence "\<exists> x. b' x (A, q)"
    by metis
  thus "b (A, q)"
    using general_cond_b
    by simp
qed

subsection \<open>Theorems\<close>

lemma nonempty_set_cons_anonymous: "consensus_anonymity nonempty_set\<^sub>\<C>"
  unfolding consensus_anonymity_def
  by simp

lemma nonempty_profile_cons_anonymous: "consensus_anonymity nonempty_profile\<^sub>\<C>"
proof (unfold consensus_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    perm: "p <~~> q" and
    not_empty_p: "nonempty_profile\<^sub>\<C> (A, p)"
  have "length q = length p"
    using perm perm_length
    by force
  thus "nonempty_profile\<^sub>\<C> (A, q)"
    using not_empty_p length_0_conv
    unfolding nonempty_profile\<^sub>\<C>.simps
    by metis
qed

lemma equal_top_cons'_anonymous:
  fixes a :: "'a"
  shows "consensus_anonymity (equal_top\<^sub>\<C>' a)"
proof (unfold consensus_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    perm: "p <~~> q" and
    top_cons_a: "equal_top\<^sub>\<C>' a (A, p)"
  from perm obtain \<pi> where
    perm\<^sub>\<pi>: "\<pi> permutes {..< length p}" and
    list_pq\<^sub>\<pi>: "permute_list \<pi> p = q"
    using mset_eq_permutation
    by metis
  have l: "length p = length q"
    using perm perm_length
    by force
  hence "\<forall> i < length q. \<pi> i < length p"
    using perm\<^sub>\<pi> permutes_in_image
    by fastforce
  moreover have "\<forall> i < length q. q!i = p!(\<pi> i)"
    using list_pq\<^sub>\<pi>
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
  ultimately show "equal_top\<^sub>\<C>' a (A, q)"
    using l
    unfolding equal_top\<^sub>\<C>'.simps
    by metis
qed

lemma eq_top_cons_anon: "consensus_anonymity equal_top\<^sub>\<C>"
  using equal_top_cons'_anonymous
        ex_anon_cons_imp_cons_anonymous[of equal_top\<^sub>\<C> equal_top\<^sub>\<C>']
  by fastforce

lemma eq_vote_cons'_anonymous:
  fixes r :: "'a Preference_Relation"
  shows "consensus_anonymity (equal_vote\<^sub>\<C>' r)"
proof (unfold consensus_anonymity_def, clarify)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    perm: "p <~~> q" and
    equal_votes_pref: "equal_vote\<^sub>\<C>' r (A, p)"
  from perm obtain \<pi> where
    perm\<^sub>\<pi>: "\<pi> permutes {..< length p}" and
    list_pq\<^sub>\<pi>: "permute_list \<pi> p = q"
    using mset_eq_permutation
    by metis
  have l: "length p = length q"
    using perm perm_length
    by force
  hence "\<forall> i < length q. \<pi> i < length p"
    using perm\<^sub>\<pi> permutes_in_image
    by fastforce
  moreover have "\<forall> i < length q. q!i = p!(\<pi> i)"
    using list_pq\<^sub>\<pi>
    unfolding permute_list_def
    by auto
  moreover have winner: "\<forall> i < length p. p!i = r"
    using equal_votes_pref
    by simp
  ultimately have "\<forall> i < length p. q!i = r"
    using l
    by metis
  thus "equal_vote\<^sub>\<C>' r (A, q)"
    using l
    unfolding equal_vote\<^sub>\<C>'.simps
    by metis
qed

lemma eq_vote_cons_anonymous: "consensus_anonymity equal_vote\<^sub>\<C>"
  unfolding equal_vote\<^sub>\<C>.simps
  using eq_vote_cons'_anonymous ex_anon_cons_imp_cons_anonymous
  by blast

end

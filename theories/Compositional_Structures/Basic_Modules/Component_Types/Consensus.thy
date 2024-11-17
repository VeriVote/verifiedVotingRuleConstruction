(*  File:       Consensus.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Consensus\<close>

theory Consensus
  imports "Social_Choice_Types/Voting_Symmetry"
begin

text \<open>
  An election consisting of a set of alternatives and preferential votes for each voter (a profile)
  is a consensus if it has an undisputed winner reflecting a certain concept of fairness in the
  society.
\<close>

subsection \<open>Definition\<close>

type_synonym ('a, 'v) Consensus = "('a, 'v) Election \<Rightarrow> bool"

subsection \<open>Consensus Conditions\<close>

text \<open>
  Nonempty alternative set.
\<close>

fun nonempty_set\<^sub>\<C> :: "('a, 'v) Consensus" where
  "nonempty_set\<^sub>\<C> (A, V, p) = (A \<noteq> {})"

text \<open>
  Nonempty profile, i.e., nonempty voter set.
  Note that this is also true if p(v) = {} holds for all voters v in V.
\<close>

fun nonempty_profile\<^sub>\<C> :: "('a, 'v) Consensus" where
  "nonempty_profile\<^sub>\<C> (A, V, p) = (V \<noteq> {})"

text \<open>
  Equal top ranked alternatives.
\<close>

fun equal_top\<^sub>\<C>' :: "'a \<Rightarrow> ('a, 'v) Consensus" where
  "equal_top\<^sub>\<C>' a (A, V, p) = (a \<in> A \<and> (\<forall> v \<in> V. above (p v) a = {a}))"

fun equal_top\<^sub>\<C> :: "('a, 'v) Consensus" where
  "equal_top\<^sub>\<C> c = (\<exists> a. equal_top\<^sub>\<C>' a c)"

text \<open>
  Equal votes.
\<close>

fun equal_vote\<^sub>\<C>' :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Consensus" where
  "equal_vote\<^sub>\<C>' r (A, V, p) = (\<forall> v \<in> V. (p v) = r)"

fun equal_vote\<^sub>\<C> :: "('a, 'v) Consensus" where
  "equal_vote\<^sub>\<C> c = (\<exists> r. equal_vote\<^sub>\<C>' r c)"

text \<open>
  Unanimity condition.
\<close>

fun unanimity\<^sub>\<C> :: "('a, 'v) Consensus" where
  "unanimity\<^sub>\<C> c = (nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C> c)"

text \<open>
  Strong unanimity condition.
\<close>

fun strong_unanimity\<^sub>\<C> :: "('a, 'v) Consensus" where
  "strong_unanimity\<^sub>\<C> c = (nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C> c)"

subsection \<open>Properties\<close>

definition consensus_anonymity :: "('a, 'v) Consensus \<Rightarrow> bool" where
  "consensus_anonymity c \<equiv>
    (\<forall> A V p \<pi> :: ('v \<Rightarrow> 'v).
        bij \<pi> \<longrightarrow>
          (let (A', V', q) = (rename \<pi> (A, V, p)) in
            profile V A p \<longrightarrow> profile V' A' q
            \<longrightarrow> c (A, V, p) \<longrightarrow> c (A', V', q)))"

fun consensus_neutrality :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Consensus \<Rightarrow> bool" where
  "consensus_neutrality X c = is_symmetry c (Invariance (neutrality\<^sub>\<R> X))"

subsection \<open>Auxiliary Lemmas\<close>

lemma cons_anon_conj:
  fixes c c' :: "('a, 'v) Consensus"
  assumes
    "consensus_anonymity c" and
    "consensus_anonymity c'"
  shows "consensus_anonymity (\<lambda> e. c e \<and> c' e)"
proof (unfold consensus_anonymity_def Let_def, clarify)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij_\<pi>: "bij \<pi>" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and
    prof: "profile V A p"
  hence "profile V' A' q"
    using rename_sound fst_conv rename.simps
    by metis
  moreover assume
    "c (A, V, p)" and
    "c' (A, V, p)"
  ultimately show "c (A', V', q) \<and> c' (A', V', q)"
    using bij_\<pi> renamed assms prof
    unfolding consensus_anonymity_def
    by auto
qed

theorem cons_conjunction_invariant:
  fixes
    \<CC> :: "('a, 'v) Consensus set" and
    rel :: "('a, 'v) Election rel"
  defines "C \<equiv> (\<lambda> E. (\<forall> C' \<in> \<CC>. C' E))"
  assumes "\<forall> C'. C' \<in> \<CC> \<longrightarrow> is_symmetry C' (Invariance rel)"
  shows "is_symmetry C (Invariance rel)"
proof (unfold is_symmetry.simps, intro allI impI)
  fix E E' :: "('a, 'v) Election"
  assume "(E, E') \<in> rel"
  hence "\<forall> C' \<in> \<CC>. C' E = C' E'"
    using assms
    unfolding is_symmetry.simps
    by blast
  thus "C E = C E'"
    unfolding C_def
    by blast
qed

lemma cons_anon_invariant:
  fixes
    c :: "('a, 'v) Consensus" and
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    anon: "consensus_anonymity c" and
    bij_\<pi>: "bij \<pi>" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and
    cond_c: "c (A, V, p)"
  shows "c (A', V', q)"
proof -
  have "profile V' A' q"
    using rename_sound bij_\<pi> renamed prof_p
    by fastforce
  thus ?thesis
    using anon cond_c renamed rename_finite bij_\<pi> prof_p
    unfolding consensus_anonymity_def Let_def
    by auto
qed

lemma ex_anon_cons_imp_cons_anonymous:
  fixes
    b :: "('a, 'v) Consensus" and
    b':: "'b \<Rightarrow> ('a, 'v) Consensus"
  assumes
    general_cond_b: "b = (\<lambda> E. \<exists> x. b' x E)" and
    all_cond_anon: "\<forall> x. consensus_anonymity (b' x)"
  shows "consensus_anonymity b"
proof (unfold consensus_anonymity_def Let_def, safe)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij_\<pi>: "bij \<pi>" and
    cond_b: "b (A, V, p)" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)"
  have "\<exists> x. b' x (A, V, p)"
    using cond_b general_cond_b
    by simp
  then obtain x :: "'b" where
    "b' x (A, V, p)"
    by blast
  moreover have "consensus_anonymity (b' x)"
    using all_cond_anon
    by simp
  moreover have "profile V' A' q"
    using prof_p renamed bij_\<pi> rename_sound
    by fastforce
  ultimately have "b' x (A', V', q)"
    using all_cond_anon bij_\<pi> prof_p renamed
    unfolding consensus_anonymity_def
    by auto
  hence "\<exists> x. b' x (A', V', q)"
    by metis
  thus "b (A', V', q)"
    using general_cond_b
    by simp
qed

subsection \<open>Theorems\<close>

subsubsection \<open>Anonymity\<close>

lemma nonempty_set_cons_anonymous: "consensus_anonymity nonempty_set\<^sub>\<C>"
  unfolding consensus_anonymity_def
  by simp

lemma nonempty_profile_cons_anonymous: "consensus_anonymity nonempty_profile\<^sub>\<C>"
proof (unfold consensus_anonymity_def Let_def, clarify)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij_\<pi>: "bij \<pi>" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)"
  hence "card V = card V'"
    using rename.simps Pair_inject bij_betw_same_card
          bij_betw_subset top_greatest
    by (metis (mono_tags, lifting))
  moreover assume "nonempty_profile\<^sub>\<C> (A, V, p)"
  ultimately show "nonempty_profile\<^sub>\<C> (A', V', q)"
    using length_0_conv renamed
    unfolding nonempty_profile\<^sub>\<C>.simps
    by auto
qed

lemma equal_top_cons'_anonymous:
  fixes a :: "'a"
  shows "consensus_anonymity (equal_top\<^sub>\<C>' a)"
proof (unfold consensus_anonymity_def Let_def, clarify)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij_\<pi>: "bij \<pi>" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and
    top_cons_a: "equal_top\<^sub>\<C>' a (A, V, p)"
  have "\<forall> v' \<in> V'. q v' = p ((the_inv \<pi>) v')"
    using renamed
    by auto
  moreover have "\<forall> v' \<in> V'. (the_inv \<pi>) v' \<in> V"
    using bij_\<pi> renamed rename.simps bij_is_inj
          f_the_inv_into_f_bij_betw inj_image_mem_iff
    by fastforce
  moreover have winner: "\<forall> v \<in> V. above (p v) a = {a}"
    using top_cons_a
    by simp
  ultimately have "\<forall> v' \<in> V'. above (q v') a = {a}"
    by simp
  moreover have "a \<in> A"
    using top_cons_a
    by simp
  ultimately show "equal_top\<^sub>\<C>' a (A', V', q)"
    using renamed
    unfolding equal_top\<^sub>\<C>'.simps
    by simp
qed

lemma eq_top_cons_anon: "consensus_anonymity equal_top\<^sub>\<C>"
  using equal_top_cons'_anonymous
        ex_anon_cons_imp_cons_anonymous[of equal_top\<^sub>\<C> equal_top\<^sub>\<C>']
  by fastforce

lemma eq_vote_cons'_anonymous:
  fixes r :: "'a Preference_Relation"
  shows "consensus_anonymity (equal_vote\<^sub>\<C>' r)"
proof (unfold consensus_anonymity_def Let_def, clarify)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij_\<pi>: "bij \<pi>" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and
    eq_vote: "equal_vote\<^sub>\<C>' r (A, V, p)"
  have "\<forall> v' \<in> V'. q v' = p ((the_inv \<pi>) v')"
    using renamed
    by auto
  moreover have "\<forall> v' \<in> V'. (the_inv \<pi>) v' \<in> V"
    using bij_\<pi> renamed rename.simps bij_is_inj
          f_the_inv_into_f_bij_betw inj_image_mem_iff
    by fastforce
  moreover have winner: "\<forall> v \<in> V. p v = r"
    using eq_vote
    by simp
  ultimately have "\<forall> v' \<in> V'. q v' = r"
    by simp
  thus "equal_vote\<^sub>\<C>' r (A', V', q)"
    unfolding equal_vote\<^sub>\<C>'.simps
    by metis
qed

lemma eq_vote_cons_anonymous: "consensus_anonymity equal_vote\<^sub>\<C>"
  unfolding equal_vote\<^sub>\<C>.simps
  using eq_vote_cons'_anonymous ex_anon_cons_imp_cons_anonymous
  by blast

subsubsection \<open>Neutrality\<close>

lemma nonempty_set\<^sub>\<C>_neutral: "consensus_neutrality well_formed_elections nonempty_set\<^sub>\<C>"
  unfolding well_formed_elections_def
  by auto

lemma nonempty_profile\<^sub>\<C>_neutral: "consensus_neutrality well_formed_elections nonempty_profile\<^sub>\<C>"
  unfolding well_formed_elections_def
  by auto

lemma equal_vote\<^sub>\<C>_neutral: "consensus_neutrality well_formed_elections equal_vote\<^sub>\<C>"
proof (unfold well_formed_elections_def consensus_neutrality.simps is_symmetry.simps,
       intro allI impI,
       unfold split_paired_all neutrality\<^sub>\<R>.simps action_induced_rel.simps
       voters_\<E>.simps alternatives_\<E>.simps profile_\<E>.simps \<phi>_neutral.simps
       extensional_continuation.simps equal_vote\<^sub>\<C>.simps equal_vote\<^sub>\<C>'.simps
       alternatives_rename.simps case_prod_unfold mem_Collect_eq fst_conv
       snd_conv mem_Sigma_iff conj_assoc If_def simp_thms, safe)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    r :: "'a rel"
  assume
    "profile V A p" and
    "(THE z.
        (profile V A p \<longrightarrow> z = (\<pi> ` A, V, rel_rename \<pi> \<circ> p))
        \<and> (\<not> profile V A p \<longrightarrow> z = undefined)) = (A', V', p')"
  hence
    equal_voters: "V' = V" and
    perm_profile: "p' = (\<lambda> x. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p x})"
    unfolding comp_def
    by (simp, simp)
  have
    "(\<forall> v \<in> V. p v = r)
      \<longrightarrow> (\<exists> r'. \<forall> v \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v} = r')"
    by simp
  {
    moreover assume "\<forall> v' \<in> V. p v' = r"
    ultimately show "\<exists> r. \<forall> v \<in> V'. p' v = r"
      using equal_voters perm_profile
      by metis
  }
  assume "\<pi> \<in> carrier neutrality\<^sub>\<G>"
  hence "bij \<pi>"
    using rewrite_carrier
    unfolding neutrality\<^sub>\<G>_def
    by blast
  hence "\<forall> a. the_inv \<pi> (\<pi> a) = a"
    using bij_is_inj the_inv_f_f
    by metis
  moreover have
    "(\<forall> v \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v} = r) \<longrightarrow>
      (\<forall> v \<in> V. {(the_inv \<pi> (\<pi> a), the_inv \<pi> (\<pi> b)) | a b. (a, b) \<in> p v} =
               {(the_inv \<pi> a, the_inv \<pi> b) | a b. (a, b) \<in> r})"
    by fastforce
  ultimately have
    "(\<forall> v \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v} = r) \<longrightarrow>
      (\<forall> v \<in> V. {(a, b) | a b. (a, b) \<in> p v} =
              {(the_inv \<pi> a, the_inv \<pi> b) | a b. (a, b) \<in> r})"
    by auto
  hence
    "(\<forall> v' \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v'} = r)
      \<longrightarrow> (\<exists> r'. \<forall> v' \<in> V. p v' = r')"
    by simp
  moreover assume "\<forall> v' \<in> V'. p' v' = r"
  ultimately show "\<exists> r'. \<forall> v' \<in> V. p v' = r'"
    using equal_voters perm_profile
    by metis
qed

lemma strong_unanimity\<^sub>\<C>_neutral: "consensus_neutrality
        well_formed_elections strong_unanimity\<^sub>\<C>"
  using nonempty_set\<^sub>\<C>_neutral equal_vote\<^sub>\<C>_neutral nonempty_profile\<^sub>\<C>_neutral
        cons_conjunction_invariant[of
          "{nonempty_set\<^sub>\<C>, nonempty_profile\<^sub>\<C>, equal_vote\<^sub>\<C>}"
          "neutrality\<^sub>\<R> well_formed_elections"]
  unfolding strong_unanimity\<^sub>\<C>.simps
  by fastforce

end
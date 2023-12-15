(*  File:       Consensus.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Consensus\<close>

theory Consensus
  imports "HOL-Combinatorics.List_Permutation"
          "Social_Choice_Types/Profile"
          "Social_Choice_Types/Property_Interpretations"
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
  Nonempty profile, i.e. nonempty voter set.
  Note that this is also true if p v = {} for all voters v in V.
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
    (\<forall> A V p \<pi>::('v \<Rightarrow> 'v). 
        bij \<pi> \<longrightarrow>
          (let (A', V', q) = (rename \<pi> (A, V, p)) in
            profile V A p \<longrightarrow> profile V' A' q 
            \<longrightarrow> c (A, V, p) \<longrightarrow> c (A', V', q)))"

fun consensus_neutrality :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Consensus \<Rightarrow> bool" where
  "consensus_neutrality X c = satisfies c (Invariance (neutrality\<^sub>\<R> X))"

subsection \<open>Auxiliary Lemmas\<close>

lemma cons_anon_conj:
  fixes
    c1 :: "('a, 'v) Consensus" and
    c2 :: "('a, 'v) Consensus"
  assumes 
    anon1: "consensus_anonymity c1" and
    anon2: "consensus_anonymity c2"
  shows "consensus_anonymity (\<lambda>e. c1 e \<and> c2 e)"
proof (unfold consensus_anonymity_def Let_def, clarify)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij: "bij \<pi>" and
    prof: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and
    c1: "c1 (A, V, p)" and
    c2: "c2 (A, V, p)"
  hence "profile V' A' q"
    using rename_sound renamed bij fst_conv rename.simps
    by metis
  thus "c1 (A', V', q) \<and> c2 (A', V', q)"
    using bij renamed c1 c2 assms prof
    unfolding consensus_anonymity_def
    by auto
qed

theorem cons_conjunction_invariant:
  fixes
    \<CC> :: "('a, 'v) Consensus set" and
    rel :: "('a, 'v) Election rel"
  defines 
    "C \<equiv> (\<lambda>E. (\<forall>C' \<in> \<CC>. C' E))"
  assumes
    "\<And>C'. C' \<in> \<CC> \<Longrightarrow> satisfies C' (Invariance rel)"
  shows "satisfies C (Invariance rel)"
proof (unfold satisfies.simps, standard, standard, standard)
  fix
    E :: "('a,'v) Election" and
    E' :: "('a,'v) Election"
  assume
    "(E,E') \<in> rel"
  hence "\<forall>C' \<in> \<CC>. C' E = C' E'"
    using assms
    unfolding satisfies.simps
    by blast
  thus "C E = C E'"
    unfolding C_def
    by blast
qed

lemma cons_anon_invariant:
  fixes
    c :: "('a, 'v) Consensus" and
    A :: "'a set" and 
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes 
    anon: "consensus_anonymity c" and
    bij: "bij \<pi>" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and
    cond_c: "c (A, V, p)"
  shows "c (A', V', q)"
proof -
  have "profile V' A' q"
    using rename_sound bij renamed prof_p 
    by fastforce
  thus ?thesis
    using anon cond_c renamed rename_finite bij prof_p
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
    A :: "'a set" and 
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij: "bij \<pi>" and
    cond_b: "b (A, V, p)" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)"
  have "\<exists> x. b' x (A, V, p)"
    using cond_b general_cond_b
    by simp
  then obtain x :: 'b where
    "b' x (A, V, p)"
    by blast
  moreover have "consensus_anonymity (b' x)" 
    using all_cond_anon
    by simp
  moreover have "profile V' A' q" 
    using prof_p renamed bij rename_sound
    by fastforce
  ultimately have "b' x (A', V', q)"
    using all_cond_anon bij prof_p renamed
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
    A :: "'a set" and 
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij: "bij \<pi>" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and
    not_empty_p: "nonempty_profile\<^sub>\<C> (A, V, p)"
  have "card V = card V'"
    using renamed bij rename.simps Pair_inject 
          bij_betw_same_card bij_betw_subset top_greatest
    by (metis (mono_tags, lifting))
  thus "nonempty_profile\<^sub>\<C> (A', V', q)"
    using not_empty_p length_0_conv renamed
    unfolding nonempty_profile\<^sub>\<C>.simps
    by auto
qed

lemma equal_top_cons'_anonymous:
  fixes a :: "'a"
  shows "consensus_anonymity (equal_top\<^sub>\<C>' a)"
proof (unfold consensus_anonymity_def Let_def, clarify)
  fix
    A :: "'a set" and 
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij: "bij \<pi>" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and 
    top_cons_a: "equal_top\<^sub>\<C>' a (A, V, p)"
  have "\<forall>v'\<in>V'. q v' = p ((the_inv \<pi>) v')"
    using renamed
    by auto
  moreover have "\<forall> v' \<in> V'. (the_inv \<pi>) v' \<in> V"
    using bij renamed rename.simps bij_is_inj 
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
    A :: "'a set" and 
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bij: "bij \<pi>" and
    prof_p: "profile V A p" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and 
    eq_vote: "equal_vote\<^sub>\<C>' r (A, V, p)"
  have "\<forall>v'\<in>V'. q v' = p ((the_inv \<pi>) v')"
    using renamed
    by auto
  moreover have "\<forall> v' \<in> V'. (the_inv \<pi>) v' \<in> V"
    using bij renamed rename.simps bij_is_inj 
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

lemma nonempty_set\<^sub>\<C>_neutral:               
  "consensus_neutrality valid_elections nonempty_set\<^sub>\<C>"
proof (simp, unfold valid_elections_def, safe) qed

lemma nonempty_profile\<^sub>\<C>_neutral:
  "consensus_neutrality valid_elections nonempty_profile\<^sub>\<C>"
proof (simp, unfold valid_elections_def, safe) qed
    
lemma equal_vote\<^sub>\<C>_neutral:
  "consensus_neutrality valid_elections equal_vote\<^sub>\<C>"
proof (simp, unfold valid_elections_def, clarsimp, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    r :: "'a rel"
  show
    "\<forall>v \<in> V. p v = r \<Longrightarrow> \<exists>r. \<forall>v \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v} = r"
    by simp
  assume
    bij: "\<pi> \<in> carrier neutrality\<^sub>\<G>"
  hence
    "bij \<pi>"
    unfolding neutrality\<^sub>\<G>_def
    using rewrite_carrier
    by blast
  hence "\<forall>a. the_inv \<pi> (\<pi> a) = a"
    by (simp add: bij_is_inj the_inv_f_f)
  moreover have
    "\<forall>v \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v} = r \<Longrightarrow> 
      \<forall>v \<in> V. {(the_inv \<pi> (\<pi> a), the_inv \<pi> (\<pi> b)) | a b. (a, b) \<in> p v} = 
              {(the_inv \<pi> a, the_inv \<pi> b) | a b. (a, b) \<in> r}"
    by fastforce
  ultimately have
    "\<forall>v \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v} = r \<Longrightarrow> 
      \<forall>v \<in> V. {(a, b) | a b. (a, b) \<in> p v} = 
              {(the_inv \<pi> a, the_inv \<pi> b) | a b. (a, b) \<in> r}"
    by auto
  hence 
    "\<forall>v \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v} = r \<Longrightarrow> 
          \<forall>v \<in> V. p v = {(the_inv \<pi> a, the_inv \<pi> b) | a b. (a, b) \<in> r}"
    by simp
  thus
    "\<forall>v \<in> V. {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p v} = r \<Longrightarrow> \<exists>r. \<forall>v \<in> V. p v = r"
    by simp
qed

lemma strong_unanimity\<^sub>\<C>_neutral: 
  "consensus_neutrality valid_elections strong_unanimity\<^sub>\<C>"
  using nonempty_set\<^sub>\<C>_neutral equal_vote\<^sub>\<C>_neutral nonempty_profile\<^sub>\<C>_neutral
        cons_conjunction_invariant[of 
          "{nonempty_set\<^sub>\<C>, nonempty_profile\<^sub>\<C>, equal_vote\<^sub>\<C>}" "neutrality\<^sub>\<R> valid_elections"]
  unfolding strong_unanimity\<^sub>\<C>.simps
  by fastforce

end

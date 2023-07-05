(*  File:       Consensus_Rule.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Consensus Rule\<close>

theory Consensus_Rule
  imports "Consensus_Condition"
          "../Defer_Module"
          "../Elect_First_Module"
begin

text \<open>
  TODO.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Consensus_Rule = "'a Consensus_Condition \<times> 'a Electoral_Module"

definition consensus_rule :: "'a Consensus_Rule \<Rightarrow> bool" where
  "consensus_rule K \<equiv> (
    \<forall> A p. finite_profile A p \<longrightarrow> (
      if fst K (A, p)
      then (\<exists> a. a \<in> A \<and> snd K A p = ({a}, (A - {a}), {}))
      else snd K A p = ({}, {}, A)))"

subsection \<open>TODO\<close>

definition determined_if :: "'a Consensus_Condition \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "determined_if c m \<equiv>
    \<forall> A p p'. finite A \<and> profile A p \<and> profile A p' \<and> c (A, p) \<and> c (A, p') \<longrightarrow> m A p = m A p'"

fun consensus_condition_\<K> :: "'a Consensus_Condition \<Rightarrow> 'a Electoral_Module \<Rightarrow>
                                'a Consensus_Rule" where
  "consensus_condition_\<K> c m =
    (let
      w = (\<lambda> A p. if c (A, p) then m A p else defer_module A p)
      in (c, w)
     )"

subsection \<open>Auxiliary Lemmas\<close>

lemma elect_fst_mod_determined_if_unanimity_cond:
  fixes a :: "'a"
  shows
    "determined_if
      (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_top_condition' a c)
        elect_first_module"
proof (unfold determined_if_def, safe)
  fix
    a :: 'a and
    A :: "'a set" and
    p :: "'a Profile" and
    p' :: "'a Profile"
  let ?cond =
    "\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_top_condition' a c"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    prof_p': "profile A p'" and
    eq_top_p: "equal_top_condition' a (A, p)" and
    eq_top_p': "equal_top_condition' a (A, p')" and
    not_empty_A: "nonempty_set_condition (A, p)" and
    not_empty_A': "nonempty_set_condition (A, p')" and
    not_empty_p: "nonempty_profile_condition (A, p)" and
    not_empty_p': "nonempty_profile_condition (A, p')"
  hence
    cond_Ap: "?cond (A, p)" and
    cond_Ap': "?cond (A, p')"
    by simp_all
  have "\<forall> a' \<in> A. (above (p!0) a' = {a'}) = (above (p'!0) a' = {a'})"
  proof
    fix a' :: "'a"
    assume "a' \<in> A"
    show "(above (p!0) a' = {a'}) = (above (p'!0) a' = {a'})"
    proof (cases)
      assume "a' = a"
      thus ?thesis
        using cond_Ap cond_Ap'
        by simp
    next
      assume a'_neq_a: "a' \<noteq> a"
      have lens_p_and_p'_ok: "0 < length p \<and> 0 < length p'"
        using not_empty_p not_empty_p'
        by simp
      hence "A \<noteq> {} \<and> linear_order_on A (p!0) \<and> linear_order_on A (p'!0)"
        using not_empty_A not_empty_A' prof_p prof_p'
        unfolding profile_def
        by simp
      hence "(above (p!0) a = {a} \<and> above (p!0) a' = {a'} \<longrightarrow> a = a') \<and>
             (above (p'!0) a = {a} \<and> above (p'!0) a' = {a'} \<longrightarrow> a = a')"
        using a'_neq_a fin_A above_one_2
        by metis
      thus ?thesis
        using a'_neq_a eq_top_p' eq_top_p lens_p_and_p'_ok
        by simp
    qed
  qed
  thus "elect_first_module A p = elect_first_module A p'"
    by auto
qed

lemma elect_fst_mod_determined_if_strong_unanimity_cond:
  fixes r :: "'a Preference_Relation"
  shows
    "determined_if
      (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_vote_condition' r c)
        elect_first_module"
  unfolding determined_if_def
  by simp

subsection \<open>Consensus Rules\<close>

definition non_empty_set :: "'a Consensus_Rule \<Rightarrow> bool" where
  "non_empty_set K \<equiv> \<exists> E. fst K E"

text \<open>
  Unanimity condition.
\<close>

definition unanimity :: "'a Consensus_Rule" where
  "unanimity = consensus_condition_\<K> unanimity_condition elect_first_module"

text \<open>
  Strong unanimity condition.
\<close>

definition strong_unanimity :: "'a Consensus_Rule" where
  "strong_unanimity = consensus_condition_\<K> strong_unanimity_condition elect_first_module"

subsection \<open>Properties\<close>

definition consensus_rule_anonymity :: "'a Consensus_Rule \<Rightarrow> bool" where
  "consensus_rule_anonymity K \<equiv>
    \<forall> A p q. finite_profile A p \<and> finite_profile A q \<and> p <~~> q \<and> fst K (A, p) \<longrightarrow>
      fst K (A, q) \<and> (snd K A p = snd K A q)"

subsection \<open>Inference Rules\<close>

lemma consensus_rule_anonymous:
  fixes
    \<beta>' :: "'b \<Rightarrow> 'a Consensus_Condition" and
    \<beta> :: "'a Consensus_Condition" and
    \<alpha> :: "'a Consensus_Condition" and
    m :: "'a Electoral_Module"
  assumes
    beta_sat: "\<beta> = (\<lambda> E. \<exists> a. \<beta>' a E)" and
    beta'_anon: "\<forall> x. consensus_anonymity (\<beta>' x)" and
    anon_cons_cond: "consensus_anonymity \<alpha>" and
    conditions_univ: "\<forall> x. determined_if (\<lambda> E. \<alpha> E \<and> \<beta>' x E) m"
  shows "consensus_rule_anonymity (consensus_condition_\<K> (\<lambda> E. \<alpha> E \<and> \<beta> E) m)"
proof (unfold consensus_rule_anonymity_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    prof_q: "profile A q" and
    perm: "p <~~> q" and
    consensus_cond: "fst (consensus_condition_\<K> (\<lambda> E. \<alpha> E \<and> \<beta> E) m) (A, p)"
  hence "(\<lambda> E. \<alpha> E \<and> \<beta> E) (A, p)"
    by simp
  hence
    alpha_Ap: "\<alpha> (A, p)" and
    beta_Ap: "\<beta> (A, p)"
    by simp_all
  have alpha_A_perm_p: "\<alpha> (A, q)"
    using anon_cons_cond alpha_Ap perm fin_A prof_p prof_q
    unfolding consensus_anonymity_def
    by metis
  moreover have "\<beta> (A, q)"
    using beta'_anon
    unfolding consensus_anonymity_def
    using beta_Ap beta_sat cons_anon_if_ex_cons_anon perm fin_A prof_p prof_q
    by blast
  ultimately show em_cond_perm: "fst (consensus_condition_\<K> (\<lambda> E. \<alpha> E \<and> \<beta> E) m) (A, q)"
    by simp
  have "\<exists> x. \<beta>' x (A, p)"
    using beta_Ap beta_sat
    by simp
  then obtain x where
    beta'_x_Ap: "\<beta>' x (A, p)"
    by metis
  hence beta'_x_A_perm_p: "\<beta>' x (A, q)"
    using beta'_anon perm fin_A prof_p prof_q
    unfolding consensus_anonymity_def
    by metis
  have "m A p = m A q"
    using alpha_Ap alpha_A_perm_p beta'_x_Ap beta'_x_A_perm_p conditions_univ fin_A prof_p prof_q
    unfolding determined_if_def
    by metis
  thus "snd (consensus_condition_\<K> (\<lambda> E. \<alpha> E \<and> \<beta> E) m) A p =
             snd (consensus_condition_\<K> (\<lambda> E. \<alpha> E \<and> \<beta> E) m) A q"
    using consensus_cond em_cond_perm
    by simp
qed

subsection \<open>Theorems\<close>

lemma unanimity_anonymous: "consensus_rule_anonymity unanimity"
proof (unfold unanimity_def)
  let ?ne_cond = "(\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c)"
  have "consensus_anonymity ?ne_cond"
    using nonempty_set_cond_anonymous nonempty_profile_cond_anonymous
    unfolding consensus_anonymity_def
    by metis
  moreover have "equal_top_condition = (\<lambda> c. \<exists> a. equal_top_condition' a c)"
    by fastforce
  ultimately have "consensus_rule_anonymity
     (consensus_condition_\<K>
        (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_top_condition c)
          elect_first_module)"
    using consensus_rule_anonymous[of equal_top_condition equal_top_condition' ?ne_cond]
          equal_top_cond'_anonymous elect_fst_mod_determined_if_unanimity_cond
    by fastforce
  moreover have
    "unanimity_condition =
      (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_top_condition c)"
    by force
  hence "consensus_condition_\<K>
    (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_top_condition c)
      elect_first_module =
        consensus_condition_\<K> unanimity_condition elect_first_module"
    by metis
  ultimately show
    "consensus_rule_anonymity (consensus_condition_\<K> unanimity_condition elect_first_module)"
    by metis
qed

lemma strong_unanimity_anonymous: "consensus_rule_anonymity strong_unanimity"
proof (unfold strong_unanimity_def)
  have "consensus_anonymity (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c)"
    using nonempty_set_cond_anonymous nonempty_profile_cond_anonymous
    unfolding consensus_anonymity_def
    by metis
  moreover have "equal_vote_condition = (\<lambda> c. \<exists> v. equal_vote_condition' v c)"
    by fastforce
  ultimately have
    "consensus_rule_anonymity
      (consensus_condition_\<K>
        (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_vote_condition c)
        elect_first_module)"
    using consensus_rule_anonymous[of equal_vote_condition equal_vote_condition'
            "\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c"]
          nonempty_set_cond_anonymous nonempty_profile_cond_anonymous eq_vote_cond'_anon
          elect_fst_mod_determined_if_strong_unanimity_cond
    by fastforce
  moreover have
    "strong_unanimity_condition =
      (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_vote_condition c)"
    by force
  hence
    "consensus_condition_\<K>
      (\<lambda> c. nonempty_set_condition c \<and> nonempty_profile_condition c \<and> equal_vote_condition c)
        elect_first_module =
          consensus_condition_\<K> strong_unanimity_condition elect_first_module"
    by metis
  ultimately show
    "consensus_rule_anonymity
      (consensus_condition_\<K> strong_unanimity_condition elect_first_module)"
    by metis
qed

end

(*  File:       Consensus_Class.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Consensus Class\<close>

theory Consensus_Class
  imports "Consensus"
          "../Defer_Module"
          "../Elect_First_Module"
begin

text \<open>
  A consensus class is a pair of a set of elections and a mapping that assigns a unique alternative
  to each election in that set (of elections). This alternative is then called the consensus
  alternative (winner). Here, we model the mapping by an electoral module that defers alternatives
  which are not in the consensus.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Consensus_Class = "'a Consensus \<times> 'a Electoral_Module"

fun consensus_\<K> :: "'a Consensus_Class \<Rightarrow> 'a Consensus" where
  "consensus_\<K> K = fst K"

fun rule_\<K> :: "'a Consensus_Class \<Rightarrow> 'a Electoral_Module" where
  "rule_\<K> K = snd K"

subsection \<open>Consensus Choice\<close>

text \<open>
  A consensus class is deemed well-formed if the result of its mapping is completely
  determined by its consensus, the elected set of the electoral module's result.
\<close>

definition well_formed :: "'a Consensus \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "well_formed c m \<equiv>
    \<forall> A p p'. finite A \<and> profile A p \<and> profile A p' \<and> c (A, p) \<and> c (A, p') \<longrightarrow>
      m A p = m A p'"

fun consensus_choice :: "'a Consensus \<Rightarrow> 'a Electoral_Module \<Rightarrow> 'a Consensus_Class" where
  "consensus_choice c m =
    (let
      w = (\<lambda> A p. if c (A, p) then m A p else defer_module A p)
      in (c, w)
     )"

subsection \<open>Auxiliary Lemmas\<close>

lemma unanimity'_consensus_imp_elect_fst_mod_well_formed:
  fixes a :: "'a"
  shows
    "well_formed (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C>' a c)
      elect_first_module"
proof (unfold well_formed_def, safe)
  fix
    a :: 'a and
    A :: "'a set" and
    p :: "'a Profile" and
    p' :: "'a Profile"
  let ?cond =
    "\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C>' a c"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    prof_p': "profile A p'" and
    eq_top_p: "equal_top\<^sub>\<C>' a (A, p)" and
    eq_top_p': "equal_top\<^sub>\<C>' a (A, p')" and
    not_empty_A: "nonempty_set\<^sub>\<C> (A, p)" and
    not_empty_A': "nonempty_set\<^sub>\<C> (A, p')" and
    not_empty_p: "nonempty_profile\<^sub>\<C> (A, p)" and
    not_empty_p': "nonempty_profile\<^sub>\<C> (A, p')"
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

lemma strong_unanimity'consensus_imp_elect_fst_mod_well_formed:
  fixes r :: "'a Preference_Relation"
  shows
    "well_formed (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C>' r c)
      elect_first_module"
  unfolding well_formed_def
  by simp

subsection \<open>Consensus Rules\<close>

definition non_empty_set :: "'a Consensus_Class \<Rightarrow> bool" where
  "non_empty_set c \<equiv> \<exists> K. consensus_\<K> c K"

text \<open>
  Unanimity condition.
\<close>

definition unanimity :: "'a Consensus_Class" where
  "unanimity = consensus_choice unanimity\<^sub>\<C> elect_first_module"

text \<open>
  Strong unanimity condition.
\<close>

definition strong_unanimity :: "'a Consensus_Class" where
  "strong_unanimity = consensus_choice strong_unanimity\<^sub>\<C> elect_first_module"

subsection \<open>Properties\<close>

definition consensus_rule_anonymity :: "'a Consensus_Class \<Rightarrow> bool" where
  "consensus_rule_anonymity c \<equiv>
    \<forall> A p q.
      finite_profile A p \<and> finite_profile A q \<and> p <~~> q \<and> consensus_\<K> c (A, p) \<longrightarrow>
      consensus_\<K> c (A, q) \<and> (rule_\<K> c A p = rule_\<K> c A q)"

subsection \<open>Inference Rules\<close>

lemma consensus_choice_anonymous:
  fixes
    \<alpha> :: "'a Consensus" and
    \<beta> :: "'a Consensus" and
    m :: "'a Electoral_Module" and
    \<beta>' :: "'b \<Rightarrow> 'a Consensus"
  assumes
    beta_sat: "\<beta> = (\<lambda> E. \<exists> a. \<beta>' a E)" and
    beta'_anon: "\<forall> x. consensus_anonymity (\<beta>' x)" and
    anon_cons_cond: "consensus_anonymity \<alpha>" and
    conditions_univ: "\<forall> x. well_formed (\<lambda> E. \<alpha> E \<and> \<beta>' x E) m"
  shows "consensus_rule_anonymity (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m)"
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
    consensus_cond: "consensus_\<K> (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m) (A, p)"
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
    using beta_Ap beta_sat ex_anon_cons_imp_cons_anonymous perm fin_A
          prof_p prof_q
    by blast
  ultimately show em_cond_perm:
    "consensus_\<K> (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m) (A, q)"
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
    using alpha_Ap alpha_A_perm_p beta'_x_Ap beta'_x_A_perm_p conditions_univ
          fin_A prof_p prof_q
    unfolding well_formed_def
    by metis
  thus "rule_\<K> (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m) A p =
             rule_\<K> (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m) A q"
    using consensus_cond em_cond_perm
    by simp
qed

subsection \<open>Theorems\<close>

lemma unanimity_anonymous: "consensus_rule_anonymity unanimity"
proof (unfold unanimity_def)
  let ?ne_cond = "(\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c)"
  have "consensus_anonymity ?ne_cond"
    using nonempty_set_cons_anonymous nonempty_profile_cons_anonymous
    unfolding consensus_anonymity_def
    by metis
  moreover have "equal_top\<^sub>\<C> = (\<lambda> c. \<exists> a. equal_top\<^sub>\<C>' a c)"
    by fastforce
  ultimately have "consensus_rule_anonymity
     (consensus_choice
        (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C> c) elect_first_module)"
    using consensus_choice_anonymous[of equal_top\<^sub>\<C> equal_top\<^sub>\<C>' ?ne_cond]
          equal_top_cons'_anonymous unanimity'_consensus_imp_elect_fst_mod_well_formed
    by fastforce
  moreover have
    "unanimity\<^sub>\<C> = (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C> c)"
    by force
  hence "consensus_choice
    (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C> c)
      elect_first_module =
        consensus_choice unanimity\<^sub>\<C> elect_first_module"
    by metis
  ultimately show "consensus_rule_anonymity (consensus_choice unanimity\<^sub>\<C> elect_first_module)"
    by metis
qed

lemma strong_unanimity_anonymous: "consensus_rule_anonymity strong_unanimity"
proof (unfold strong_unanimity_def)
  have "consensus_anonymity (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c)"
    using nonempty_set_cons_anonymous nonempty_profile_cons_anonymous
    unfolding consensus_anonymity_def
    by metis
  moreover have "equal_vote\<^sub>\<C> = (\<lambda> c. \<exists> v. equal_vote\<^sub>\<C>' v c)"
    by fastforce
  ultimately have
    "consensus_rule_anonymity
      (consensus_choice
        (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C> c) elect_first_module)"
    using consensus_choice_anonymous[of equal_vote\<^sub>\<C> equal_vote\<^sub>\<C>'
            "\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c"]
          nonempty_set_cons_anonymous nonempty_profile_cons_anonymous eq_vote_cons'_anonymous
          strong_unanimity'consensus_imp_elect_fst_mod_well_formed
    by fastforce
  moreover have "strong_unanimity\<^sub>\<C> =
    (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C> c)"
    by force
  hence
    "consensus_choice (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C> c)
        elect_first_module =
          consensus_choice strong_unanimity\<^sub>\<C> elect_first_module"
    by metis
  ultimately show
    "consensus_rule_anonymity (consensus_choice strong_unanimity\<^sub>\<C> elect_first_module)"
    by metis
qed

end

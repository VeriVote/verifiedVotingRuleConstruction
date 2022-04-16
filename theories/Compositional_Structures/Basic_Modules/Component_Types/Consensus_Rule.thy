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
  "determined_if K m \<equiv>
    \<forall> A p p'. finite A \<and> profile A p \<and> profile A p' \<and> K (A, p) \<and> K (A, p')
    \<longrightarrow> m A p = m A p'"

definition non_empty_set :: "'a Consensus_Rule \<Rightarrow> bool" where
  "non_empty_set K \<equiv> \<exists> E. fst K E"

definition consensus_rule_anonymity :: "'a Consensus_Rule \<Rightarrow> bool" where
  "consensus_rule_anonymity K \<equiv>
    (\<forall> pi A p. finite_profile A p \<longrightarrow> is_perm pi \<longrightarrow> fst K (A, p) \<longrightarrow>
      (fst K (A, build_perm pi p) \<and> (snd K A p = snd K A (build_perm pi p))))"

fun em_with_condition :: "'a Consensus_Condition \<Rightarrow> 'a Electoral_Module \<Rightarrow>
                          'a Consensus_Rule" where
  "em_with_condition cond m =
    (let
      w = (\<lambda> A p.
        if cond (A, p)
        then m A p
        else defer_module A p)
      in (cond, w)
     )"

lemma cons_rule_anon:
  fixes
    \<beta>' :: "'b \<Rightarrow> 'a Consensus_Condition" and
    \<beta> :: "'a Consensus_Condition" and
    \<alpha> :: "'a Consensus_Condition" and
    m :: "'a Electoral_Module"
  assumes
    beta_sat: "\<beta> = (\<lambda> E. \<exists> a. \<beta>' a E)" and
    beta'_anon: "\<forall> x. consensus_condition_anonymity (\<beta>' x)" and
    anon_cons_cond: "consensus_condition_anonymity \<alpha>" and
    conditions_univ: "\<forall> x. determined_if (\<lambda> E. \<alpha> E \<and> \<beta>' x E) m"
  shows "consensus_rule_anonymity (em_with_condition (\<lambda> E. \<alpha> E \<and> \<beta> E) m)"
proof(unfold consensus_rule_anonymity_def, safe)
  fix
    pi :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
    A :: "'a set" and
    p :: "'a Profile"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    perm_pi: "is_perm pi" and
    em_cond: "fst (em_with_condition (\<lambda> E. \<alpha> E \<and> \<beta> E) m) (A, p)"
  hence "(\<lambda> E. \<alpha> E \<and> \<beta> E) (A, p)"
    by simp
  hence
    alpha_Ap: "\<alpha> (A, p)" and
    beta_Ap: "\<beta> (A, p)"
    by simp_all
  from alpha_Ap anon_cons_cond
  have alpha_A_perm_p: "\<alpha> (A, build_perm pi p)"
    using perm_pi fin_A prof_p
    unfolding consensus_condition_anonymity_def
    by simp
  moreover from beta_Ap beta_sat beta'_anon
  have "\<beta> (A, build_perm pi p)"
    using cond_anon_if_ex_cond_anon[of \<beta> \<beta>'] perm_pi
          fin_A prof_p
    unfolding consensus_condition_anonymity_def
    by simp
  ultimately show em_cond_perm:
    "fst (em_with_condition (\<lambda> E. \<alpha> E \<and> \<beta> E) m) (A, build_perm pi p)"
    by simp
  from beta_Ap beta_sat
  have "\<exists> x. \<beta>' x (A, p)"
    by simp
  then obtain x where
    beta'_x_Ap: "\<beta>' x (A, p)"
    by blast
  with beta'_anon
  have beta'_x_A_perm_p: "\<beta>' x (A, build_perm pi p)"
    using perm_pi fin_A prof_p
    unfolding consensus_condition_anonymity_def
    by simp
  from fin_A prof_p perm_pi
  have "profile A (build_perm pi p)"
    unfolding profile_def is_perm_def
    by (metis prof_p build_perm.elims length_permute_list nth_mem profile_set set_permute_list)
  with alpha_Ap alpha_A_perm_p beta'_x_Ap beta'_x_A_perm_p
  have "m A p = m A (build_perm pi p)"
    using conditions_univ fin_A prof_p
    unfolding determined_if_def
    by metis
  thus "snd (em_with_condition (\<lambda> E. \<alpha> E \<and> \<beta> E) m) A p =
             snd (em_with_condition (\<lambda> E. \<alpha> E \<and> \<beta> E) m) A (build_perm pi p)"
    using em_cond em_cond_perm
    by auto
qed

subsection \<open>Consensus Rules\<close>

text \<open>
  Unanimity condition.
\<close>

definition unanimity :: "'a Consensus_Rule" where
  "unanimity = em_with_condition unanimity_condition elect_first_module"

lemma elct_fst_mod_determined_if_unanimity_cond:
  "\<forall> a. determined_if (\<lambda> E. ne_set_cond E \<and> ne_profile_cond E \<and> eq_top_cond' a E)
                     elect_first_module"
proof (unfold determined_if_def, safe)
  fix
    a :: 'a and
    A :: "'a set" and
    p :: "'a Profile" and
    p' :: "'a Profile"
  let ?cond = "\<lambda> E. ne_set_cond E \<and> ne_profile_cond E \<and> eq_top_cond' a E"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    prof_p': "profile A p'" and
    eq_top_p: "eq_top_cond' a (A, p)" and
    eq_top_p': "eq_top_cond' a (A, p')" and
    not_empty_A: "ne_set_cond (A, p)" and
    not_empty_A': "ne_set_cond (A, p')" and
    not_empty_p: "ne_profile_cond (A, p)" and
    not_empty_p': "ne_profile_cond (A, p')"
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
      from not_empty_p not_empty_p'
      have lens_p_and_p'_ok: "0 < length p \<and> 0 < length p'"
        by simp
      hence "A \<noteq> {} \<and> linear_order_on A (p!0) \<and> linear_order_on A (p'!0)"
        using not_empty_A not_empty_A' prof_p prof_p'
        unfolding profile_def
        by simp
      hence "(above (p!0) a = {a} \<and> above (p ! 0) a' = {a'} \<longrightarrow> a = a') \<and>
             (above (p'!0) a = {a} \<and> above (p' ! 0) a' = {a'} \<longrightarrow> a = a')"
        using a'_neq_a fin_A above_one2[of "p!0"] above_one2[of A]
        by metis
      thus ?thesis
        using a'_neq_a eq_top_p' eq_top_p lens_p_and_p'_ok
        by simp
    qed
  qed
  thus "elect_first_module A p = elect_first_module A p'"
    by auto
qed

lemma unanimity_is_anon: "consensus_rule_anonymity unanimity"
proof (unfold unanimity_def)
  let ?ne_cond = "(\<lambda> E. ne_set_cond E \<and> ne_profile_cond E)"
  have "consensus_condition_anonymity ?ne_cond"
    using ne_set_cond_anon ne_profile_cond_anon
    unfolding consensus_condition_anonymity_def
    by metis
  moreover have "eq_top_cond = (\<lambda> e. \<exists> a. eq_top_cond' a e)"
    by fastforce
  ultimately have "consensus_rule_anonymity
     (em_with_condition (\<lambda> e. ne_set_cond e \<and> ne_profile_cond e \<and> eq_top_cond e)
                        elect_first_module)"
    using cons_rule_anon[of eq_top_cond eq_top_cond' ?ne_cond]
          ne_set_cond_anon ne_profile_cond_anon eq_top_cond'_anon
          elct_fst_mod_determined_if_unanimity_cond
    by simp
  moreover have "unanimity_condition = (\<lambda> E. ne_set_cond E \<and> ne_profile_cond E \<and>
                                            eq_top_cond E)"
    by force
  hence "em_with_condition (\<lambda> e. ne_set_cond e \<and> ne_profile_cond e \<and> eq_top_cond e)
                           elect_first_module =
         em_with_condition unanimity_condition elect_first_module"
    by metis
  ultimately show "consensus_rule_anonymity
     (em_with_condition unanimity_condition elect_first_module)"
    by metis
qed

text \<open>
  Strong unanimity condition.
\<close>

definition strong_unanimity :: "'a Consensus_Rule" where
  "strong_unanimity = em_with_condition strong_unanimity_condition elect_first_module"

lemma elct_fst_mod_determined_if_strong_unanimity_cond:
  "\<forall> v. determined_if (\<lambda> E. ne_set_cond E \<and> ne_profile_cond E \<and> eq_vote_cond' v E)
                     elect_first_module"
proof (unfold determined_if_def, safe)
  fix
    v :: "'a Preference_Relation" and
    A :: "'a set" and
    p :: "'a Profile" and
    p' :: "'a Profile"
  assume
    eq_votes_v_in_p: "eq_vote_cond' v (A, p)" and
    eq_votes_v_in_p': "eq_vote_cond' v (A, p')" and
    not_empty_p: "ne_profile_cond (A, p)" and
    not_empty_p': "ne_profile_cond (A, p')"
  from not_empty_p not_empty_p'
  have "p \<noteq> [] \<and> p' \<noteq> []"
    by simp
  with eq_votes_v_in_p eq_votes_v_in_p'
  have "p!0 = p'!0"
    by simp
  thus "elect_first_module A p = elect_first_module A p'"
    by auto
qed

lemma strong_unanimity_is_anon: "consensus_rule_anonymity strong_unanimity"
proof (unfold strong_unanimity_def)
  have "consensus_condition_anonymity (\<lambda> E. ne_set_cond E \<and> ne_profile_cond E)"
    using ne_set_cond_anon ne_profile_cond_anon
    unfolding consensus_condition_anonymity_def
    by metis
  moreover have "eq_vote_cond = (\<lambda> e. \<exists> v. eq_vote_cond' v e)"
    by fastforce
  ultimately have
    "consensus_rule_anonymity
      (em_with_condition
        (\<lambda> e. ne_set_cond e \<and> ne_profile_cond e \<and> eq_vote_cond e)
        elect_first_module)"
    using cons_rule_anon[of eq_vote_cond eq_vote_cond'
                            "\<lambda> E. ne_set_cond E \<and> ne_profile_cond E"
                            elect_first_module]
          ne_set_cond_anon ne_profile_cond_anon eq_vote_cond'_anon
          elct_fst_mod_determined_if_strong_unanimity_cond
    by simp
  moreover have
    "strong_unanimity_condition = (\<lambda> E. ne_set_cond E \<and> ne_profile_cond E \<and>
                                       eq_vote_cond E)"
    by force
  hence
    "em_with_condition (\<lambda> e. ne_set_cond e \<and> ne_profile_cond e \<and> eq_vote_cond e)
                       elect_first_module =
     em_with_condition strong_unanimity_condition elect_first_module"
    by metis
  ultimately show
    "consensus_rule_anonymity
      (em_with_condition strong_unanimity_condition elect_first_module)"
    by metis
qed

end

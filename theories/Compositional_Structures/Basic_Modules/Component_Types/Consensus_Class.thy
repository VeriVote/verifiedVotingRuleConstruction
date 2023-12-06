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

type_synonym ('a, 'v, 'r) Consensus_Class 
  = "('a, 'v) Consensus \<times> ('a, 'v, 'r) Electoral_Module"

fun consensus_\<K> :: "('a, 'v, 'r) Consensus_Class \<Rightarrow> ('a, 'v) Consensus" 
  where "consensus_\<K> K = fst K"

fun rule_\<K> :: "('a, 'v, 'r) Consensus_Class \<Rightarrow> ('a, 'v, 'r) Electoral_Module" 
  where "rule_\<K> K = snd K"

subsection \<open>Consensus Choice\<close>

text \<open>
  A consensus class is deemed well-formed if the result of its mapping is completely
  determined by its consensus, the elected set of the electoral module's result.
\<close>

definition well_formed :: "('a, 'v) Consensus \<Rightarrow> ('a, 'v, 'r) Electoral_Module \<Rightarrow> bool" where
  "well_formed c m \<equiv>
    \<forall> A V V' p p'. profile V A p \<and> profile V' A p' \<and> c (A, V, p) \<and> c (A, V', p') \<longrightarrow> 
                    m V A p = m V' A p'"

text \<open>
  A sensible social choice rule for a given arbitrary consensus 
  and social choice rule r is the one that chooses the result of r
  for all consensus elections and defers all candidates otherwise.
\<close>

fun consensus_choice :: 
"('a, 'v) Consensus \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module 
  \<Rightarrow> ('a, 'v, 'a Result) Consensus_Class" where
  "consensus_choice c m =
    (let
      w = (\<lambda> V A p. if c (A, V, p) then m V A p else defer_module V A p)
      in (c, w))"

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
    V :: "'v::wellorder set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  let ?cond =
    "\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C>' a c"
  assume
    prof_p: "profile V A p" and
    prof_p': "profile V' A p'" and
    eq_top_p: "equal_top\<^sub>\<C>' a (A, V, p)" and
    eq_top_p': "equal_top\<^sub>\<C>' a (A, V', p')" and
    not_empty_A: "nonempty_set\<^sub>\<C> (A, V, p)" and
    not_empty_A': "nonempty_set\<^sub>\<C> (A, V', p')" and
    not_empty_p: "nonempty_profile\<^sub>\<C> (A, V, p)" and
    not_empty_p': "nonempty_profile\<^sub>\<C> (A, V', p')"
  hence
    cond_Ap: "?cond (A, V, p)" and
    cond_Ap': "?cond (A, V', p')"
    by simp_all
  have "\<forall> a' \<in> A. ((above (p (least V)) a' = {a'}) = (above (p' (least V')) a' = {a'}))"
  proof
    fix a' :: 'a
    assume "a' \<in> A"
    show "(above (p (least V)) a' = {a'}) = (above (p' (least V')) a' = {a'})"
    proof (cases)
      assume "a' = a"
      thus ?thesis
        using cond_Ap cond_Ap' Collect_mem_eq LeastI 
              empty_Collect_eq equal_top\<^sub>\<C>'.simps 
              nonempty_profile\<^sub>\<C>.simps 
              least.simps
        by (metis (no_types, lifting))
    next
      assume a'_neq_a: "a' \<noteq> a"
      have non_empty: "V \<noteq> {} \<and> V' \<noteq> {}"
        using not_empty_p not_empty_p'
        by simp
      hence "A \<noteq> {} \<and> linear_order_on A (p (least V)) 
                \<and> linear_order_on A (p' (least V'))"
        using not_empty_A not_empty_A' prof_p prof_p' 
              \<open>a' \<in> A\<close> card.remove enumerate.simps(1) 
              enumerate_in_set finite_enumerate_in_set 
              least.elims all_not_in_conv
              zero_less_Suc
        unfolding profile_def
        by metis
      hence "(above (p (least V)) a = {a} \<and> above (p (least V)) a' = {a'} \<longrightarrow> a = a') \<and>
             (above (p' (least V')) a = {a} \<and> above (p' (least V')) a' = {a'} \<longrightarrow> a = a')"
        using a'_neq_a
        sorry
      thus ?thesis
        using bot_nat_0.not_eq_extremum card_0_eq cond_Ap cond_Ap' 
              enumerate.simps(1) enumerate_in_set equal_top\<^sub>\<C>'.simps 
              finite_enumerate_in_set non_empty least.simps
        by metis
    qed
  qed
  thus "elect_first_module V A p = elect_first_module V' A p'"
    by auto
qed

lemma strong_unanimity'consensus_imp_elect_fst_mod_completely_determined:
  fixes r :: "'a Preference_Relation"
  shows
    "well_formed
      (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C>' r c) elect_first_module"
proof (unfold well_formed_def, clarify)
 fix
    a :: 'a and
    A :: "'a set" and
    V :: "'v::wellorder set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  let ?cond =
    "\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C>' r c"
  assume
    prof_p: "profile V A p" and
    prof_p': "profile V' A p'" and
    eq_vote_p: "equal_vote\<^sub>\<C>' r (A, V,  p)" and
    eq_vote_p': "equal_vote\<^sub>\<C>' r (A, V', p')" and
    not_empty_A: "nonempty_set\<^sub>\<C> (A, V, p)" and
    not_empty_A': "nonempty_set\<^sub>\<C> (A, V', p')" and
    not_empty_p: "nonempty_profile\<^sub>\<C> (A, V, p)" and
    not_empty_p': "nonempty_profile\<^sub>\<C> (A, V', p')"
  hence
    cond_Ap: "?cond (A, V, p)" and
    cond_Ap': "?cond (A, V', p')"
    by simp_all
  have "p (least V) = r \<and> p' (least V') = r"
    using eq_vote_p eq_vote_p' not_empty_p not_empty_p'
          bot_nat_0.not_eq_extremum card_0_eq enumerate.simps(1) 
          enumerate_in_set equal_vote\<^sub>\<C>'.simps finite_enumerate_in_set 
          nonempty_profile\<^sub>\<C>.simps least.elims
    by (metis (no_types, lifting))
  thus "elect_first_module V A p = elect_first_module V' A p'"
    by auto
qed

lemma strong_unanimity'consensus_imp_elect_fst_mod_well_formed:
  fixes r :: "'a Preference_Relation"
  shows
    "well_formed (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C>' r c)
      elect_first_module"
  using strong_unanimity'consensus_imp_elect_fst_mod_completely_determined
  by blast

subsection \<open>Consensus Rules\<close>

definition non_empty_set :: "('a, 'v, 'r) Consensus_Class \<Rightarrow> bool" where
  "non_empty_set c \<equiv> \<exists> K. consensus_\<K> c K"

text \<open>
  Unanimity condition.
\<close>

definition unanimity :: 
"('a, 'v::wellorder, 'a Result) Consensus_Class" where
  "unanimity = consensus_choice unanimity\<^sub>\<C> elect_first_module"

text \<open>
  Strong unanimity condition.
\<close>

definition strong_unanimity :: 
"('a, 'v::wellorder, 'a Result) Consensus_Class" where
  "strong_unanimity = consensus_choice strong_unanimity\<^sub>\<C> elect_first_module"

subsection \<open>Properties\<close>

definition consensus_rule_anonymity :: "('a, 'v, 'r) Consensus_Class \<Rightarrow> bool" where
  "consensus_rule_anonymity c \<equiv>
    (\<forall> A V p \<pi>::('v \<Rightarrow> 'v). 
        bij \<pi> \<longrightarrow>
          (let (A', V', q) = (rename \<pi> (A, V, p)) in
            profile V A p \<longrightarrow> profile V' A' q 
            \<longrightarrow> consensus_\<K> c (A, V, p) 
            \<longrightarrow> (consensus_\<K> c (A', V', q) \<and> (rule_\<K> c V A p = rule_\<K> c V' A' q))))"

subsection \<open>Inference Rules\<close>

lemma consensus_choice_anonymous:
  fixes
    \<alpha> :: "('a, 'v) Consensus" and
    \<beta> :: "('a, 'v) Consensus" and
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    \<beta>' :: "'b \<Rightarrow> ('a, 'v) Consensus"
  assumes
    beta_sat: "\<beta> = (\<lambda> E. \<exists> a. \<beta>' a E)" and
    beta'_anon: "\<forall> x. consensus_anonymity (\<beta>' x)" and
    anon_cons_cond: "consensus_anonymity \<alpha>" and
    conditions_univ: "\<forall> x. well_formed (\<lambda> E. \<alpha> E \<and> \<beta>' x E) m"
  shows "consensus_rule_anonymity (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m)"
proof (unfold consensus_rule_anonymity_def Let_def, safe)
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
    prof_q: "profile V' A' q" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)" and
    consensus_cond: "consensus_\<K> (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m) (A, V, p)"
  hence "(\<lambda> E. \<alpha> E \<and> \<beta> E) (A, V, p)"
    by simp
  hence
    alpha_Ap: "\<alpha> (A, V, p)" and
    beta_Ap: "\<beta> (A, V, p)"
    by simp_all
  have alpha_A_perm_p: "\<alpha> (A', V', q)"
    using anon_cons_cond alpha_Ap bij prof_p prof_q renamed
    unfolding consensus_anonymity_def
    by fastforce
  moreover have "\<beta> (A', V', q)"
    using beta'_anon beta_Ap beta_sat ex_anon_cons_imp_cons_anonymous bij 
          prof_p renamed beta'_anon cons_anon_invariant
    unfolding consensus_anonymity_def
    sorry
  ultimately show em_cond_perm: 
    "consensus_\<K> (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m) (A', V', q)"
    using beta_Ap beta_sat ex_anon_cons_imp_cons_anonymous bij
          prof_p prof_q
    by simp
  have "\<exists> x. \<beta>' x (A, V, p)"
    using beta_Ap beta_sat
    by simp
  then obtain x where
    beta'_x_Ap: "\<beta>' x (A, V, p)"
    by metis
  hence beta'_x_A_perm_p: "\<beta>' x (A', V', q)"
    using beta'_anon bij prof_p renamed
          cons_anon_invariant prof_q
    unfolding consensus_anonymity_def
    by auto
  have "m V A p = m V' A' q"
    using alpha_Ap alpha_A_perm_p beta'_x_Ap beta'_x_A_perm_p
          conditions_univ prof_p prof_q rename.simps prod.inject renamed
    unfolding well_formed_def
    by metis
  thus "rule_\<K> (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m) V A p =
             rule_\<K> (consensus_choice (\<lambda> E. \<alpha> E \<and> \<beta> E) m) V' A' q"
    using consensus_cond em_cond_perm
    by simp
qed

subsection \<open>Theorems\<close>

subsubsection \<open>Anonymity\<close>

lemma unanimity_anonymous: "consensus_rule_anonymity unanimity"
proof (unfold unanimity_def)
  let ?ne_cond = "(\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c)"
  have "consensus_anonymity ?ne_cond"
    using nonempty_set_cons_anonymous nonempty_profile_cons_anonymous cons_anon_conj
    by auto
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
    by (rule HOL.back_subst)
qed

lemma strong_unanimity_anonymous: 
"consensus_rule_anonymity strong_unanimity"
proof (unfold strong_unanimity_def)
  have "consensus_anonymity (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c)"
    using nonempty_set_cons_anonymous nonempty_profile_cons_anonymous cons_anon_conj
    unfolding consensus_anonymity_def
    by simp
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
    by (rule HOL.back_subst)
qed

end

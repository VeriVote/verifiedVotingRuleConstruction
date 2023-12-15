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
  Returns those consensus elections on a given alternative and voter set
  from a given consensus that are mapped to the given unique winner by a 
  given consensus rule.
\<close>

fun \<K>\<^sub>\<E> :: 
"('a, 'v, 'r Result) Consensus_Class \<Rightarrow> 'r \<Rightarrow> ('a, 'v) Election set" where
  "\<K>\<^sub>\<E> K w =
    {(A, V, p) | A V p. (consensus_\<K> K) (A, V, p) \<and> finite_profile V A p 
                  \<and> elect (rule_\<K> K) V A p = {w}}" (* use profile instead of finite_profile? *)

abbreviation \<K>_els :: "('a, 'v, 'r Result) Consensus_Class \<Rightarrow> ('a, 'v) Election set" where
  "\<K>_els K \<equiv> \<Union> ((\<K>\<^sub>\<E> K) ` UNIV)"

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
      hence "(a \<in> above (p (least V)) a' \<or> a' \<in> above (p (least V)) a) \<and>
        (a \<in> above (p' (least V')) a' \<or> a' \<in> above (p' (least V')) a)"
        using \<open>a' \<in> A\<close> a'_neq_a eq_top_p
        unfolding above_def linear_order_on_def total_on_def
        by auto
      hence "(above (p (least V)) a = {a} \<and> above (p (least V)) a' = {a'} \<longrightarrow> a = a') \<and>
             (above (p' (least V')) a = {a} \<and> above (p' (least V')) a' = {a'} \<longrightarrow> a = a')"
        by auto
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

fun consensus_rule_anonymity' :: "('a, 'v, 'r Result) Consensus_Class \<Rightarrow> bool" where
  "consensus_rule_anonymity' C = 
    satisfies (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (Invariance (anonymity\<^sub>\<R> (\<K>_els C)))"

fun (in result_properties) consensus_rule_neutrality :: 
  "('a, 'v) Election set \<Rightarrow> ('a, 'v, 'b Result) Consensus_Class \<Rightarrow> bool" where
  "consensus_rule_neutrality X C = satisfies (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
    (equivar_ind_by_act (carrier neutrality\<^sub>\<G>) X \<phi>_neutr (set_action \<psi>_neutr))"

subsection \<open>Inference Rules\<close>

lemma consensus_choice_equivar:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    c :: "('a, 'v) Consensus" and
    G :: "'x set" and
    X :: "('a, 'v) Election set" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    \<psi> :: "('x, 'a) binary_fun" and
    f :: "'a Result \<Rightarrow> 'a set"
  defines
    "equivar \<equiv> equivar_ind_by_act G X \<phi> (set_action \<psi>)"
  assumes
    equivar_m: "satisfies (f \<circ> fun\<^sub>\<E> m) equivar" and
    equivar_defer: "satisfies (f \<circ> fun\<^sub>\<E> defer_module) equivar" and
    \<comment> \<open>Could be generalized to arbitrary modules instead of defer_module\<close>
    invar_cons: "satisfies c (Invariance (rel_induced_by_action G X \<phi>))"
  shows
    "satisfies (f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) 
              (equivar_ind_by_act G X \<phi> (set_action \<psi>))"
proof (simp only: rewrite_equivar_ind_by_act, standard, standard, standard)
  fix
    E :: "('a, 'v) Election" and
    g :: 'x
  assume
    "g \<in> G" and "E \<in> X" and "\<phi> g E \<in> X"
  show "(f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) (\<phi> g E) =
           set_action \<psi> g ((f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) E)"
  proof (cases "c E")
    case True
    hence "c (\<phi> g E)"
      using invar_cons rewrite_invar_ind_by_act \<open>g \<in> G\<close> \<open>\<phi> g E \<in> X\<close> \<open>E \<in> X\<close>
      by metis
    hence "(f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) (\<phi> g E) =
      (f \<circ> fun\<^sub>\<E> m) (\<phi> g E)"
      by simp
    also have "(f \<circ> fun\<^sub>\<E> m) (\<phi> g E) = 
      set_action \<psi> g ((f \<circ> fun\<^sub>\<E> m) E)"
      using equivar_m \<open>E \<in> X\<close> \<open>\<phi> g E \<in> X\<close> \<open>g \<in> G\<close> rewrite_equivar_ind_by_act
      unfolding equivar_def
      by (metis (mono_tags, lifting))
    also have "(f \<circ> fun\<^sub>\<E> m) E = 
      (f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) E"
      using \<open>E \<in> X\<close> \<open>g \<in> G\<close> invar_cons
      by (simp add: True)
    finally show ?thesis 
      by simp
  next
    case False  
    hence "\<not> c (\<phi> g E)"
      using invar_cons rewrite_invar_ind_by_act \<open>g \<in> G\<close> \<open>\<phi> g E \<in> X\<close> \<open>E \<in> X\<close>
      by metis
    hence "(f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) (\<phi> g E) =
      (f \<circ> fun\<^sub>\<E> defer_module) (\<phi> g E)"
      by simp
    also have "(f \<circ> fun\<^sub>\<E> defer_module) (\<phi> g E) = 
      set_action \<psi> g ((f \<circ> fun\<^sub>\<E> defer_module) E)"
      using equivar_defer \<open>E \<in> X\<close> \<open>\<phi> g E \<in> X\<close> \<open>g \<in> G\<close> rewrite_equivar_ind_by_act
      unfolding equivar_def
      by (metis (mono_tags, lifting))
    also have "(f \<circ> fun\<^sub>\<E> defer_module) E = 
      (f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) E"
      using \<open>E \<in> X\<close> \<open>g \<in> G\<close> invar_cons
      by (simp add: False)
    finally show ?thesis 
      by simp
  qed
qed

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
    using beta'_anon beta_Ap beta_sat ex_anon_cons_imp_cons_anonymous[of \<beta> \<beta>'] bij 
          prof_p renamed beta'_anon cons_anon_invariant[of \<beta> \<pi> V A p A' V' q]
    unfolding consensus_anonymity_def
    by blast
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

subsubsection \<open>Neutrality\<close>

lemma defer_winners_equivar:
  fixes
    G :: "'x set" and
    X :: "('a, 'v) Election set" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    \<psi> :: "('x, 'a) binary_fun"
  shows
    "satisfies (elect_r \<circ> fun\<^sub>\<E> defer_module) 
              (equivar_ind_by_act G X \<phi> (set_action \<psi>))"
  using rewrite_equivar_ind_by_act
  by fastforce

lemma elect_first_winners_neutral:
  shows
    "satisfies (elect_r \<circ> fun\<^sub>\<E> elect_first_module)
              (equivar_ind_by_act (carrier neutrality\<^sub>\<G>) 
                valid_elections
                \<phi>_neutr (set_action \<psi>_neutr\<^sub>\<c>))"
proof (simp only: rewrite_equivar_ind_by_act, clarify)
  fix
    A :: "'a set" and
    V :: "'v::wellorder set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assume
    bij: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    valid: "(A, V, p) \<in> valid_elections"
  hence "bij \<pi>"
    unfolding neutrality\<^sub>\<G>_def
    using rewrite_carrier
    by blast
  hence inv: "\<forall>a. a = \<pi> (the_inv \<pi> a)"
    by (simp add: f_the_inv_into_f_bij_betw)
  from bij valid have 
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr \<pi> (A, V, p)) = 
      {a \<in> \<pi> ` A. above (rel_rename \<pi> (p (least V))) a = {a}}"
    by simp
  moreover have 
    "{a \<in> \<pi> ` A. above (rel_rename \<pi> (p (least V))) a = {a}} = 
      {a \<in> \<pi> ` A. {b. (a, b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p (least V)}} = {a}}"
    by (simp add: above_def)
  ultimately have elect_simp:
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr \<pi> (A, V, p)) = 
      {a \<in> \<pi> ` A. {b. (a, b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p (least V)}} = {a}}"
    by simp
  have "\<forall>a \<in> \<pi> ` A. {b. (a, b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}} =
    {\<pi> b | b. (a, \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}}"
    by blast
  moreover have "\<forall>a \<in> \<pi> ` A. 
    {\<pi> b | b. (a, \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}} =
    {\<pi> b | b. (\<pi> (the_inv \<pi> a), \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}}"
    using \<open>bij \<pi>\<close>
    by (simp add: f_the_inv_into_f_bij_betw)
  moreover have "\<forall>a \<in> \<pi> ` A. \<forall>b. 
    ((\<pi> (the_inv \<pi> a), \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}) = 
    ((the_inv \<pi> a, b) \<in> {(x, y) | x y. (x, y) \<in> p (least V)})"
    using \<open>bij \<pi>\<close> rel_rename_helper[of \<pi>]
    by auto
  moreover have "{(x, y) | x y. (x, y) \<in> p (least V)} = p (least V)"
    by simp
  ultimately have 
    "\<forall>a \<in> \<pi> ` A. ({b. (a, b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p (least V)}} = {a}) =
       ({\<pi> b | b. (the_inv \<pi> a, b) \<in> p (least V)} = {a})"
    by force
  hence 
    "{a \<in> \<pi> ` A. {b. (a, b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p (least V)}} = {a}} = 
      {a \<in> \<pi> ` A. {\<pi> b | b. (the_inv \<pi> a, b) \<in> p (least V)} = {a}}"
    by auto
  hence "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr \<pi> (A, V, p)) = 
    {a \<in> \<pi> ` A. {\<pi> b | b. (the_inv \<pi> a, b) \<in> p (least V)} = {a}}"
    using elect_simp
    by simp
  also have "{a \<in> \<pi> ` A. {\<pi> b | b. (the_inv \<pi> a, b) \<in> p (least V)} = {a}} =
    {\<pi> a | a. a \<in> A \<and> {\<pi> b | b. (a, b) \<in> p (least V)} = {\<pi> a}}"
    using \<open>bij \<pi>\<close> inv bij_is_inj the_inv_f_f 
    by fastforce
  also have "{\<pi> a | a. a \<in> A \<and> {\<pi> b | b. (a, b) \<in> p (least V)} = {\<pi> a}} =
    \<pi> ` {a \<in> A. {\<pi> b | b. (a, b) \<in> p (least V)} = {\<pi> a}}"
    by blast
  also have "\<pi> ` {a \<in> A. {\<pi> b | b. (a, b) \<in> p (least V)} = {\<pi> a}} =
    \<pi> ` {a \<in> A. \<pi> ` {b | b. (a, b) \<in> p (least V)} = \<pi> ` {a}}"
    by blast
  finally have
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr \<pi> (A, V, p)) =
      \<pi> ` {a \<in> A. \<pi> ` (above (p (least V)) a) = \<pi> ` {a}}"
    unfolding above_def
    by simp
  moreover have 
    "\<forall>a. (\<pi> ` (above (p (least V)) a) = \<pi> ` {a}) = 
      (the_inv \<pi> ` \<pi> ` above (p (least V)) a = the_inv \<pi> ` \<pi> ` {a})"
    by (metis \<open>bij \<pi>\<close> bij_betw_the_inv_into bij_def inj_image_eq_iff)
  moreover have 
    "\<forall>a. (the_inv \<pi> ` \<pi> ` above (p (least V)) a = the_inv \<pi> ` \<pi> ` {a}) =
      (above (p (least V)) a = {a})"
    by (metis \<open>bij \<pi>\<close> bij_betw_imp_inj_on bij_betw_the_inv_into inj_image_eq_iff)
  ultimately have 
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr \<pi> (A, V, p)) =
      \<pi> ` {a \<in> A. above (p (least V)) a = {a}}"
    by presburger
  moreover have "elect elect_first_module V A p = {a \<in> A. above (p (least V)) a = {a}}"
    by simp
  moreover have
    "set_action \<psi>_neutr\<^sub>\<c> \<pi> 
                ((elect_r \<circ> fun\<^sub>\<E> elect_first_module) (A, V, p)) =
      \<pi> ` (elect elect_first_module V A p)"
    by auto
  ultimately show
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr \<pi> (A, V, p)) =
      set_action \<psi>_neutr\<^sub>\<c> \<pi> 
                 ((elect_r \<circ> fun\<^sub>\<E> elect_first_module) (A, V, p))"
    by blast
qed  

lemma strong_unanimity_neutral:
  defines
    "domain \<equiv> valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>"
  shows "social_choice_properties.consensus_rule_neutrality domain strong_unanimity"
proof -
  have "consensus_neutrality domain strong_unanimity\<^sub>\<C>"
    using strong_unanimity\<^sub>\<C>_neutral invar_under_subset_rel
    unfolding domain_def
    by simp
  moreover have 
    "satisfies (elect_r \<circ> fun\<^sub>\<E> elect_first_module)
              (equivar_ind_by_act (carrier neutrality\<^sub>\<G>) 
                domain \<phi>_neutr (set_action \<psi>_neutr\<^sub>\<c>))"
    using elect_first_winners_neutral 
    unfolding domain_def equivar_ind_by_act_def
    using equivar_under_subset
    by blast            
  ultimately show ?thesis
    using elect_first_winners_neutral
          defer_winners_equivar[of "carrier neutrality\<^sub>\<G>" domain \<phi>_neutr \<psi>_neutr\<^sub>\<c>]    
          consensus_choice_equivar[of 
            elect_r elect_first_module "carrier neutrality\<^sub>\<G>" domain
            \<phi>_neutr \<psi>_neutr\<^sub>\<c> strong_unanimity\<^sub>\<C>]
  unfolding consensus_neutrality.simps strong_unanimity_def neutrality\<^sub>\<R>.simps
            social_choice_properties.consensus_rule_neutrality.simps domain_def
  by blast
qed
  
lemma strong_unanimity_closed_under_neutrality:
  "neutrality\<^sub>\<R> valid_elections \<inter> (\<K>_els strong_unanimity) \<times> valid_elections \<subseteq> 
    (neutrality\<^sub>\<R> (\<K>_els strong_unanimity))"
proof (unfold valid_elections_def neutrality\<^sub>\<R>.simps rel_induced_by_action.simps, clarify)
  fix
    A :: "'a set" and
    V :: "'b set" and
    p :: "('a, 'b) Profile" and
    A' :: "'a set" and
    V' :: "'b set" and
    p' :: "('a, 'b) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    a :: 'a
  assume
    prof: "fun\<^sub>\<E> profile (A, V, p)" and
    cons: "(A, V, p) \<in> \<K>\<^sub>\<E> strong_unanimity a" and
    bij: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    img: "\<phi>_neutr \<pi> (A, V, p) = (A', V', p')"
  hence fin: "(A, V, p) \<in> finite_elections"
    unfolding \<K>\<^sub>\<E>.simps finite_elections_def
    by simp
  hence valid': "(A', V', p') \<in> valid_elections"
    using bij img CollectI \<phi>_neutr_act.group_action_axioms group_action.element_image prof
    unfolding finite_elections_def valid_elections_def
    by (metis (mono_tags, lifting))
  moreover have "V' = V \<and> A' = \<pi> ` A"
    using img fin valid_elections_def CollectI alts_rename.elims 
          extensional_continuation.simps fstI prof sndI
    unfolding \<phi>_neutr.simps
    by (metis (no_types, lifting))
  ultimately have prof': "finite_profile V' A' p'"
    using fin bij CollectD finite_elections_def finite_imageI fst_eqD snd_eqD
    unfolding valid_elections_def neutrality\<^sub>\<G>_def
    by (metis (no_types, lifting))   
  have "((A, V, p), (A', V', p')) \<in> neutrality\<^sub>\<R> valid_elections"
    using bij img fin valid'
    unfolding neutrality\<^sub>\<R>.simps rel_induced_by_action.simps neutrality\<^sub>\<G>_def 
              finite_elections_def valid_elections_def 
    by blast
  moreover have unanimous: "(A, V, p) \<in> valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>"
    using cons fin
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_def valid_elections_def
    by simp
  ultimately have unanimous': "(A', V', p') \<in> valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>"
    using strong_unanimity\<^sub>\<C>_neutral
    by force
  have rewrite:
    "\<forall>\<pi> \<in> carrier neutrality\<^sub>\<G>. 
      \<phi>_neutr \<pi> (A, V, p) \<in> valid_elections \<inter> Collect strong_unanimity\<^sub>\<C> \<longrightarrow>
        (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (\<phi>_neutr \<pi> (A, V, p)) =
          set_action \<psi>_neutr\<^sub>\<c> \<pi> 
            ((elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (A, V, p))"
    using strong_unanimity_neutral unanimous
          rewrite_equivar_ind_by_act[of
            "elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)"
            "carrier neutrality\<^sub>\<G>" "valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>" \<phi>_neutr
            "set_action \<psi>_neutr\<^sub>\<c>"]
    unfolding social_choice_properties.consensus_rule_neutrality.simps
    by blast
  have "elect (rule_\<K> strong_unanimity) V' A' p' = 
          (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (\<phi>_neutr \<pi> (A, V, p))"
    using img
    by simp
  also have 
    "(elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (\<phi>_neutr \<pi> (A, V, p)) =
      set_action \<psi>_neutr\<^sub>\<c> \<pi> 
        ((elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (A, V, p))"
    using bij img unanimous' rewrite
    by fastforce   
  also have "(elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (A, V, p) = {a}"
    using cons
    unfolding \<K>\<^sub>\<E>.simps
    by simp
  finally have "elect (rule_\<K> strong_unanimity) V' A' p' = {\<psi>_neutr\<^sub>\<c> \<pi> a}"
    by simp
  hence "(A', V', p') \<in> \<K>\<^sub>\<E> strong_unanimity (\<psi>_neutr\<^sub>\<c> \<pi> a)"
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_def consensus_choice.simps
    using unanimous' prof'
    by simp
  hence "(A', V', p') \<in> \<K>_els strong_unanimity"
    by simp
  hence "((A, V, p), (A', V', p'))
          \<in> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity)) \<times> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity))"
    using cons 
    by blast
  moreover have "\<exists>\<pi> \<in> carrier neutrality\<^sub>\<G>. \<phi>_neutr \<pi> (A, V, p) = (A', V', p')"
    using img bij 
    unfolding neutrality\<^sub>\<G>_def
    by blast
  ultimately show
    "((A, V, p), (A', V', p'))
          \<in> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity)) \<times> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity)) \<and>
     (\<exists>\<pi> \<in> carrier neutrality\<^sub>\<G>. \<phi>_neutr \<pi> (A, V, p) = (A', V', p'))"
    by blast
qed

end

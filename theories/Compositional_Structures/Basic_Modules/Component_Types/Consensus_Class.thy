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

type_synonym ('a, 'v, 'r) Consensus_Class = "('a, 'v) Consensus \<times> ('a, 'v, 'r) Electoral_Module"

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

fun \<K>\<^sub>\<E> :: "('a, 'v, 'r Result) Consensus_Class \<Rightarrow> 'r \<Rightarrow> ('a, 'v) Election set" where
  "\<K>\<^sub>\<E> K w =
    {(A, V, p) | A V p. (consensus_\<K> K) (A, V, p) \<and> finite_profile V A p
                  \<and> elect (rule_\<K> K) V A p = {w}}" (* use profile instead of finite_profile? *)

fun elections_\<K> :: "('a, 'v, 'r Result) Consensus_Class \<Rightarrow> ('a, 'v) Election set" where
  "elections_\<K> K = \<Union> ((\<K>\<^sub>\<E> K) ` UNIV)"

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

fun consensus_choice :: "('a, 'v) Consensus \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module
          \<Rightarrow> ('a, 'v, 'a Result) Consensus_Class" where
  "consensus_choice c m =
    (let
      w = (\<lambda> V A p. if c (A, V, p) then m V A p else defer_module V A p)
      in (c, w))"

subsection \<open>Auxiliary Lemmas\<close>

lemma unanimity'_consensus_imp_elect_fst_mod_well_formed:
  fixes a :: "'a"
  shows "well_formed (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C>' a c)
            elect_first_module"
proof (unfold well_formed_def, safe)
  fix
    a :: "'a" and
    A :: "'a set" and
    V :: "'v::wellorder set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  let ?cond = "\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C>' a c"
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
    fix a' :: "'a"
    assume a'_in_A: "a' \<in> A"
    show "(above (p (least V)) a' = {a'}) = (above (p' (least V')) a' = {a'})"
    proof (cases)
      assume "a' = a"
      thus ?thesis
        using cond_Ap cond_Ap' Collect_mem_eq LeastI empty_Collect_eq equal_top\<^sub>\<C>'.simps
              nonempty_profile\<^sub>\<C>.simps least.simps
        by (metis (no_types, lifting))
    next
      assume a'_neq_a: "a' \<noteq> a"
      have non_empty: "V \<noteq> {} \<and> V' \<noteq> {}"
        using not_empty_p not_empty_p'
        by simp
      hence "A \<noteq> {} \<and> linear_order_on A (p (least V))
                \<and> linear_order_on A (p' (least V'))"
        using not_empty_A not_empty_A' prof_p prof_p'
              a'_in_A card.remove enumerate.simps(1)
              enumerate_in_set finite_enumerate_in_set
              least.elims all_not_in_conv
              zero_less_Suc
        unfolding profile_def
        by metis
      hence "(a \<in> above (p (least V)) a' \<or> a' \<in> above (p (least V)) a) \<and>
        (a \<in> above (p' (least V')) a' \<or> a' \<in> above (p' (least V')) a)"
        using a'_in_A a'_neq_a eq_top_p
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
  shows "well_formed
          (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C>' r c) elect_first_module"
proof (unfold well_formed_def, clarify)
 fix
    a :: "'a" and
    A :: "'a set" and
    V :: "'v::wellorder set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  let ?cond = "\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C>' r c"
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
  shows "well_formed (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C>' r c)
            elect_first_module"
  using strong_unanimity'consensus_imp_elect_fst_mod_completely_determined
  by blast

lemma cons_domain_valid:
  fixes C :: "('a, 'v, 'r Result) Consensus_Class"
  shows "elections_\<K> C \<subseteq> valid_elections"
proof
  fix E :: "('a,'v) Election"
  assume "E \<in> elections_\<K> C"
  hence "fun\<^sub>\<E> profile E"
    unfolding \<K>\<^sub>\<E>.simps
    by force
  thus "E \<in> valid_elections"
    unfolding valid_elections_def
    by simp
qed

lemma cons_domain_finite:
  fixes C :: "('a, 'v, 'r Result) Consensus_Class"
  shows
    finite: "elections_\<K> C \<subseteq> finite_elections" and
    finite_voters: "elections_\<K> C \<subseteq> finite_elections_\<V>"
proof -
  have "\<forall> E \<in> elections_\<K> C. fun\<^sub>\<E> profile E \<and> finite (alternatives_\<E> E) \<and> finite (voters_\<E> E)"
    unfolding \<K>\<^sub>\<E>.simps
    by force
  thus "elections_\<K> C \<subseteq> finite_elections"
    unfolding finite_elections_def fun\<^sub>\<E>.simps
    by blast
  thus "elections_\<K> C \<subseteq> finite_elections_\<V>"
    unfolding finite_elections_def finite_elections_\<V>_def
    by blast
qed

subsection \<open>Consensus Rules\<close>

definition non_empty_set :: "('a, 'v, 'r) Consensus_Class \<Rightarrow> bool" where
  "non_empty_set c \<equiv> \<exists> K. consensus_\<K> c K"

text \<open>
  Unanimity condition.
\<close>

definition unanimity :: "('a, 'v::wellorder, 'a Result) Consensus_Class" where
  "unanimity = consensus_choice unanimity\<^sub>\<C> elect_first_module"

text \<open>
  Strong unanimity condition.
\<close>

definition strong_unanimity :: "('a, 'v::wellorder, 'a Result) Consensus_Class" where
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

fun consensus_rule_anonymity' :: "('a, 'v) Election set \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class
          \<Rightarrow> bool" where
  "consensus_rule_anonymity' X C =
    is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (Invariance (anonymity\<^sub>\<R> X))"

fun (in result_properties) consensus_rule_neutrality :: "('a, 'v) Election set
          \<Rightarrow> ('a, 'v, 'b Result) Consensus_Class \<Rightarrow> bool" where
  "consensus_rule_neutrality X C = is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
    (action_induced_equivariance (carrier neutrality\<^sub>\<G>) X (\<phi>_neutr X) (set_action \<psi>_neutr))"

fun consensus_rule_reversal_symmetry :: "('a, 'v) Election set
        \<Rightarrow> ('a, 'v, 'a rel Result) Consensus_Class \<Rightarrow> bool" where
  "consensus_rule_reversal_symmetry X C = is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
    (action_induced_equivariance (carrier reversal\<^sub>\<G>) X (\<phi>_rev X) (set_action \<psi>_rev))"

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
  defines "equivar \<equiv> action_induced_equivariance G X \<phi> (set_action \<psi>)"
  assumes
    equivar_m: "is_symmetry (f \<circ> fun\<^sub>\<E> m) equivar" and
    equivar_defer: "is_symmetry (f \<circ> fun\<^sub>\<E> defer_module) equivar" and
    \<comment> \<open>This could be generalized to arbitrary modules instead of \<open>defer_module\<close>.\<close>
    invar_cons: "is_symmetry c (Invariance (action_induced_rel G X \<phi>))"
  shows "is_symmetry (f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m)))
              (action_induced_equivariance G X \<phi> (set_action \<psi>))"
proof (simp only: rewrite_equivariance, standard, standard, standard)
  fix
    E :: "('a, 'v) Election" and
    g :: "'x"
  assume
    g_in_G: "g \<in> G" and
    E_in_X: "E \<in> X" and
    \<phi>_g_E_in_X: "\<phi> g E \<in> X"
  show "(f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) (\<phi> g E) =
           set_action \<psi> g ((f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) E)"
  proof (cases "c E")
    case True
    hence "c (\<phi> g E)"
      using invar_cons rewrite_invar_ind_by_act g_in_G \<phi>_g_E_in_X E_in_X
      by metis
    hence "(f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) (\<phi> g E) = (f \<circ> fun\<^sub>\<E> m) (\<phi> g E)"
      by simp
    also have "(f \<circ> fun\<^sub>\<E> m) (\<phi> g E) =
      set_action \<psi> g ((f \<circ> fun\<^sub>\<E> m) E)"
      using equivar_m E_in_X \<phi>_g_E_in_X g_in_G rewrite_equivariance
      unfolding equivar_def
      by (metis (mono_tags, lifting))
    also have "(f \<circ> fun\<^sub>\<E> m) E =
      (f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) E"
      using True E_in_X g_in_G invar_cons
      by simp
    finally show ?thesis
      by simp
  next
    case False
    hence "\<not> c (\<phi> g E)"
      using invar_cons rewrite_invar_ind_by_act g_in_G \<phi>_g_E_in_X E_in_X
      by metis
    hence "(f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) (\<phi> g E) =
      (f \<circ> fun\<^sub>\<E> defer_module) (\<phi> g E)"
      by simp
    also have "(f \<circ> fun\<^sub>\<E> defer_module) (\<phi> g E) =
      set_action \<psi> g ((f \<circ> fun\<^sub>\<E> defer_module) E)"
      using equivar_defer E_in_X g_in_G \<phi>_g_E_in_X rewrite_equivariance
      unfolding equivar_def
      by (metis (mono_tags, lifting))
    also have "(f \<circ> fun\<^sub>\<E> defer_module) E =
      (f \<circ> fun\<^sub>\<E> (rule_\<K> (consensus_choice c m))) E"
      using False E_in_X g_in_G invar_cons
      by simp
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
          prof_p renamed beta'_anon cons_anon_invariant[of \<beta>]
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
    using consensus_choice_anonymous[of equal_top\<^sub>\<C>]
          equal_top_cons'_anonymous unanimity'_consensus_imp_elect_fst_mod_well_formed
    by fastforce
  moreover have "consensus_choice
    (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_top\<^sub>\<C> c)
      elect_first_module =
        consensus_choice unanimity\<^sub>\<C> elect_first_module"
    using unanimity\<^sub>\<C>.simps
    by metis
  ultimately show "consensus_rule_anonymity (consensus_choice unanimity\<^sub>\<C> elect_first_module)"
    by (metis (no_types))
qed

lemma strong_unanimity_anonymous: "consensus_rule_anonymity strong_unanimity"
proof (unfold strong_unanimity_def)
  have "consensus_anonymity (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c)"
    using nonempty_set_cons_anonymous nonempty_profile_cons_anonymous cons_anon_conj
    unfolding consensus_anonymity_def
    by simp
  moreover have "equal_vote\<^sub>\<C> = (\<lambda> c. \<exists> v. equal_vote\<^sub>\<C>' v c)"
    by fastforce
  ultimately have "consensus_rule_anonymity
      (consensus_choice
        (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C> c) elect_first_module)"
    using consensus_choice_anonymous[of equal_vote\<^sub>\<C>]
          nonempty_set_cons_anonymous nonempty_profile_cons_anonymous eq_vote_cons'_anonymous
          strong_unanimity'consensus_imp_elect_fst_mod_well_formed
    by fastforce
  moreover have "consensus_choice (\<lambda> c. nonempty_set\<^sub>\<C> c \<and> nonempty_profile\<^sub>\<C> c \<and> equal_vote\<^sub>\<C> c)
            elect_first_module =
              consensus_choice strong_unanimity\<^sub>\<C> elect_first_module"
    using strong_unanimity\<^sub>\<C>.elims(2, 3)
    by metis
  ultimately show
    "consensus_rule_anonymity (consensus_choice strong_unanimity\<^sub>\<C> elect_first_module)"
      by (metis (no_types))
qed

subsubsection \<open>Neutrality\<close>

lemma defer_winners_equivariant:
  fixes
    G :: "'x set" and
    X :: "('a, 'v) Election set" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    \<psi> :: "('x, 'a) binary_fun"
  shows "is_symmetry (elect_r \<circ> fun\<^sub>\<E> defer_module)
                (action_induced_equivariance G X \<phi> (set_action \<psi>))"
  using rewrite_equivariance
  by fastforce

lemma elect_first_winners_neutral: "is_symmetry (elect_r \<circ> fun\<^sub>\<E> elect_first_module)
                (action_induced_equivariance (carrier neutrality\<^sub>\<G>)
                  valid_elections (\<phi>_neutr valid_elections) (set_action \<psi>_neutr\<^sub>\<c>))"
proof (simp only: rewrite_equivariance, clarify)
  fix
    A :: "'a set" and
    V :: "'v::wellorder set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assume
    bij: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    valid: "(A, V, p) \<in> valid_elections"
  hence bijective_\<pi>: "bij \<pi>"
    unfolding neutrality\<^sub>\<G>_def
    using rewrite_carrier
    by blast
  hence inv: "\<forall> a. a = \<pi> (the_inv \<pi> a)"
    by (simp add: f_the_inv_into_f_bij_betw)
  from bij valid have
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr valid_elections \<pi> (A, V, p)) =
      {a \<in> \<pi> ` A. above (rel_rename \<pi> (p (least V))) a = {a}}"
    by simp
  moreover have
    "{a \<in> \<pi> ` A. above (rel_rename \<pi> (p (least V))) a = {a}} =
      {a \<in> \<pi> ` A. {b. (a, b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p (least V)}} = {a}}"
    unfolding above_def
    by simp
  ultimately have elect_simp:
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr valid_elections \<pi> (A, V, p)) =
      {a \<in> \<pi> ` A. {b. (a, b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p (least V)}} = {a}}"
    by simp
  have "\<forall> a \<in> \<pi> ` A. {b. (a, b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}} =
    {\<pi> b | b. (a, \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}}"
    by blast
  moreover have "\<forall> a \<in> \<pi> ` A.
    {\<pi> b | b. (a, \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}} =
    {\<pi> b | b. (\<pi> (the_inv \<pi> a), \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}}"
    using bijective_\<pi>
    by (simp add: f_the_inv_into_f_bij_betw)
  moreover have "\<forall> a \<in> \<pi> ` A. \<forall> b.
    ((\<pi> (the_inv \<pi> a), \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> p (least V)}) =
      ((the_inv \<pi> a, b) \<in> {(x, y) | x y. (x, y) \<in> p (least V)})"
    using bijective_\<pi> rel_rename_helper[of \<pi>]
    by auto
  moreover have "{(x, y) | x y. (x, y) \<in> p (least V)} = p (least V)"
    by simp
  ultimately have
    "\<forall> a \<in> \<pi> ` A. ({b. (a, b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p (least V)}} = {a}) =
       ({\<pi> b | b. (the_inv \<pi> a, b) \<in> p (least V)} = {a})"
    by force
  hence "{a \<in> \<pi> ` A. {b. (a, b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> p (least V)}} = {a}} =
      {a \<in> \<pi> ` A. {\<pi> b | b. (the_inv \<pi> a, b) \<in> p (least V)} = {a}}"
    by auto
  hence "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr valid_elections \<pi> (A, V, p)) =
    {a \<in> \<pi> ` A. {\<pi> b | b. (the_inv \<pi> a, b) \<in> p (least V)} = {a}}"
    using elect_simp
    by simp
  also have "{a \<in> \<pi> ` A. {\<pi> b | b. (the_inv \<pi> a, b) \<in> p (least V)} = {a}} =
    {\<pi> a | a. a \<in> A \<and> {\<pi> b | b. (a, b) \<in> p (least V)} = {\<pi> a}}"
    using bijective_\<pi> inv bij_is_inj the_inv_f_f
    by fastforce
  also have "{\<pi> a | a. a \<in> A \<and> {\<pi> b | b. (a, b) \<in> p (least V)} = {\<pi> a}} =
    \<pi> ` {a \<in> A. {\<pi> b | b. (a, b) \<in> p (least V)} = {\<pi> a}}"
    by blast
  also have "\<pi> ` {a \<in> A. {\<pi> b | b. (a, b) \<in> p (least V)} = {\<pi> a}} =
    \<pi> ` {a \<in> A. \<pi> ` {b | b. (a, b) \<in> p (least V)} = \<pi> ` {a}}"
    by blast
  finally have
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr valid_elections \<pi> (A, V, p)) =
      \<pi> ` {a \<in> A. \<pi> ` (above (p (least V)) a) = \<pi> ` {a}}"
    unfolding above_def
    by simp
  moreover have
    "\<forall> a. (\<pi> ` (above (p (least V)) a) = \<pi> ` {a}) =
      (the_inv \<pi> ` \<pi> ` above (p (least V)) a = the_inv \<pi> ` \<pi> ` {a})"
    using \<open>bij \<pi>\<close> bij_betw_the_inv_into bij_def inj_image_eq_iff
    by metis
  moreover have "\<forall> a. (the_inv \<pi> ` \<pi> ` above (p (least V)) a = the_inv \<pi> ` \<pi> ` {a}) =
      (above (p (least V)) a = {a})"
    using bijective_\<pi> bij_betw_imp_inj_on bij_betw_the_inv_into inj_image_eq_iff
    by metis
  ultimately have "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr valid_elections \<pi> (A, V, p)) =
      \<pi> ` {a \<in> A. above (p (least V)) a = {a}}"
    by presburger
  moreover have "elect elect_first_module V A p = {a \<in> A. above (p (least V)) a = {a}}"
    by simp
  moreover have "set_action \<psi>_neutr\<^sub>\<c> \<pi>
                ((elect_r \<circ> fun\<^sub>\<E> elect_first_module) (A, V, p)) =
      \<pi> ` (elect elect_first_module V A p)"
    by auto
  ultimately show
    "(elect_r \<circ> fun\<^sub>\<E> elect_first_module) (\<phi>_neutr valid_elections \<pi> (A, V, p)) =
      set_action \<psi>_neutr\<^sub>\<c> \<pi>
                 ((elect_r \<circ> fun\<^sub>\<E> elect_first_module) (A, V, p))"
    by blast
qed

lemma strong_unanimity_neutral:
  defines "domain \<equiv> valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>"
  \<comment> \<open>We want to show neutrality on a set as general as possible,
      as this implies subset neutrality.\<close>
  shows "\<S>\<C>\<F>_properties.consensus_rule_neutrality domain strong_unanimity"
proof -
  have coincides: "\<forall> \<pi>. \<forall> E \<in> domain. \<phi>_neutr domain \<pi> E = \<phi>_neutr valid_elections \<pi> E"
    unfolding domain_def \<phi>_neutr.simps
    by auto
  have "consensus_neutrality domain strong_unanimity\<^sub>\<C>"
    using strong_unanimity\<^sub>\<C>_neutral invar_under_subset_rel
    unfolding domain_def
    by simp
  hence "is_symmetry strong_unanimity\<^sub>\<C>
     (Invariance (action_induced_rel (carrier neutrality\<^sub>\<G>) domain (\<phi>_neutr valid_elections)))"
    unfolding consensus_neutrality.simps neutrality\<^sub>\<R>.simps
    using coincides coinciding_actions_ind_equal_rel
    by metis
  moreover have "is_symmetry (elect_r \<circ> fun\<^sub>\<E> elect_first_module)
                (action_induced_equivariance (carrier neutrality\<^sub>\<G>)
                  domain (\<phi>_neutr valid_elections) (set_action \<psi>_neutr\<^sub>\<c>))"
    using elect_first_winners_neutral
    unfolding domain_def action_induced_equivariance_def
    using equivar_under_subset
    by blast
  ultimately have "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity))
      (action_induced_equivariance (carrier neutrality\<^sub>\<G>) domain
                          (\<phi>_neutr valid_elections) (set_action \<psi>_neutr\<^sub>\<c>))"
    using defer_winners_equivariant[of
            "carrier neutrality\<^sub>\<G>" domain "\<phi>_neutr valid_elections" "\<psi>_neutr\<^sub>\<c>"]
          consensus_choice_equivar[of
            "elect_r" "elect_first_module" "carrier neutrality\<^sub>\<G>" domain
            "\<phi>_neutr valid_elections" "\<psi>_neutr\<^sub>\<c>" "strong_unanimity\<^sub>\<C>"]
    unfolding strong_unanimity_def
    by metis
  thus ?thesis
    unfolding \<S>\<C>\<F>_properties.consensus_rule_neutrality.simps
    using coincides equivar_ind_by_act_coincide
    by (metis (no_types, lifting))
qed

lemma strong_unanimity_neutral': "\<S>\<C>\<F>_properties.consensus_rule_neutrality
    (elections_\<K> strong_unanimity) strong_unanimity"
proof -
  have "elections_\<K> strong_unanimity \<subseteq> valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>"
    unfolding valid_elections_def \<K>\<^sub>\<E>.simps strong_unanimity_def
    by force
  moreover from this have coincide:
    "\<forall> \<pi>. \<forall> E \<in> elections_\<K> strong_unanimity.
        \<phi>_neutr (valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>) \<pi> E =
          \<phi>_neutr (elections_\<K> strong_unanimity) \<pi> E"
    unfolding \<phi>_neutr.simps
    using extensional_continuation_subset
    by (metis (no_types, lifting))
  ultimately have
    "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity))
     (action_induced_equivariance (carrier neutrality\<^sub>\<G>) (elections_\<K> strong_unanimity)
       (\<phi>_neutr (valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>)) (set_action \<psi>_neutr\<^sub>\<c>))"
    using strong_unanimity_neutral
          equivar_under_subset[of
            "elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)"
            "valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>"
            "{(\<phi>_neutr (valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>) g, set_action \<psi>_neutr\<^sub>\<c> g) | g.
                g \<in> carrier neutrality\<^sub>\<G>}" "elections_\<K> strong_unanimity"]
    unfolding action_induced_equivariance_def \<S>\<C>\<F>_properties.consensus_rule_neutrality.simps
    by blast
  thus ?thesis
    unfolding \<S>\<C>\<F>_properties.consensus_rule_neutrality.simps
    using coincide
          equivar_ind_by_act_coincide[of
            "carrier neutrality\<^sub>\<G>" "elections_\<K> strong_unanimity"
            "\<phi>_neutr (elections_\<K> strong_unanimity)"
            "\<phi>_neutr (valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>)"
            "elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)" "set_action \<psi>_neutr\<^sub>\<c>"]
    by (metis (no_types))
qed

lemma strong_unanimity_closed_under_neutrality: "closed_restricted_rel
          (neutrality\<^sub>\<R> valid_elections) valid_elections (elections_\<K> strong_unanimity)"
proof (unfold closed_restricted_rel.simps restricted_rel.simps neutrality\<^sub>\<R>.simps
              action_induced_rel.simps elections_\<K>.simps, safe)
  fix
    A :: "'a set" and
    V :: "'b set" and
    p :: "('a, 'b) Profile" and
    A' :: "'a set" and
    V' :: "'b set" and
    p' :: "('a, 'b) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    a :: "'a"
  assume
    prof: "(A, V, p) \<in> valid_elections" and
    cons: "(A, V, p) \<in> \<K>\<^sub>\<E> strong_unanimity a" and
    bij: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    img: "\<phi>_neutr valid_elections \<pi> (A, V, p) = (A', V', p')"
  hence fin: "(A, V, p) \<in> finite_elections"
    unfolding \<K>\<^sub>\<E>.simps finite_elections_def
    by simp
  hence valid': "(A', V', p') \<in> valid_elections"
    using bij img \<phi>_neutr_act.group_action_axioms group_action.element_image prof
    unfolding finite_elections_def
    by (metis (mono_tags, lifting))
  moreover have "V' = V \<and> A' = \<pi> ` A"
    using img fin alternatives_rename.elims fstI prof sndI
    unfolding extensional_continuation.simps \<phi>_neutr.simps alternatives_\<E>.simps voters_\<E>.simps
    by (metis (no_types, lifting))
  ultimately have prof': "finite_profile V' A' p'"
    using fin bij CollectD finite_imageI fst_eqD snd_eqD
    unfolding finite_elections_def valid_elections_def alternatives_\<E>.simps
              voters_\<E>.simps profile_\<E>.simps
    by (metis (no_types, lifting))
  let ?domain = "valid_elections \<inter> Collect strong_unanimity\<^sub>\<C>"
  have "((A, V, p), (A', V', p')) \<in> neutrality\<^sub>\<R> valid_elections"
    using bij img fin valid'
    unfolding neutrality\<^sub>\<R>.simps action_induced_rel.simps
              finite_elections_def valid_elections_def
    by blast
  moreover have unanimous: "(A, V, p) \<in> ?domain"
    using cons fin
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_def valid_elections_def
    by simp
  ultimately have unanimous': "(A', V', p') \<in> ?domain"
    using strong_unanimity\<^sub>\<C>_neutral
    by force
  have rewrite: "\<forall> \<pi> \<in> carrier neutrality\<^sub>\<G>.
      \<phi>_neutr ?domain \<pi> (A, V, p) \<in> ?domain \<longrightarrow>
        (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (\<phi>_neutr ?domain \<pi> (A, V, p)) =
          set_action \<psi>_neutr\<^sub>\<c> \<pi> ((elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (A, V, p))"
    using strong_unanimity_neutral unanimous
          rewrite_equivariance[of
            "elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)"
            "carrier neutrality\<^sub>\<G>" ?domain
            "\<phi>_neutr ?domain" "set_action \<psi>_neutr\<^sub>\<c>"]
    unfolding \<S>\<C>\<F>_properties.consensus_rule_neutrality.simps
    by blast
  have img': "\<phi>_neutr ?domain \<pi> (A, V, p) = (A', V', p')"
    using img unanimous
    by simp
  hence "elect (rule_\<K> strong_unanimity) V' A' p' =
          (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (\<phi>_neutr ?domain \<pi> (A, V, p))"
    by simp
  also have "(elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (\<phi>_neutr ?domain \<pi> (A, V, p)) =
      set_action \<psi>_neutr\<^sub>\<c> \<pi>
        ((elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) (A, V, p))"
    using bij img' unanimous' rewrite
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
  hence "(A', V', p') \<in> elections_\<K> strong_unanimity"
    by simp
  hence "((A, V, p), (A', V', p'))
          \<in> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity)) \<times> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity))"
    unfolding elections_\<K>.simps
    using cons
    by blast
  moreover have "\<exists> \<pi> \<in> carrier neutrality\<^sub>\<G>. \<phi>_neutr valid_elections \<pi> (A, V, p) = (A', V', p')"
    using img bij
    unfolding neutrality\<^sub>\<G>_def
    by blast
  ultimately show "(A', V', p') \<in> \<Union> (range (\<K>\<^sub>\<E> strong_unanimity))"
    by blast
qed

end
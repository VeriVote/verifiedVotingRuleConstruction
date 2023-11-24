(*  File:       Electoral_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Component Types\<close>

section \<open>Electoral Module\<close>

theory Electoral_Module
  imports "Social_Choice_Types/Profile"
          "Social_Choice_Types/Result"
          "HOL-Combinatorics.List_Permutation"
begin

text \<open>
  Electoral modules are the principal component type of the composable
  modules voting framework, as they are a generalization of voting rules in
  the sense of social choice functions.
  These are only the types used for electoral modules. Further restrictions
  are encompassed by the electoral-module predicate.

  An electoral module does not need to make final decisions for all
  alternatives, but can instead defer the decision for some or all of them
  to other modules. Hence, electoral modules partition the received
  (possibly empty) set of alternatives into elected, rejected and deferred
  alternatives.
  In particular, any of those sets, e.g., the set of winning (elected)
  alternatives, may also be left empty, as long as they collectively still
  hold all the received alternatives. Just like a voting rule, an electoral
  module also receives a profile which holds the voters’ preferences, which,
  unlike a voting rule, consider only the (sub-)set of alternatives that
  the module receives.
\<close>

subsection \<open>Definition\<close>

text \<open>
  An electoral module maps a set of alternatives and a profile to a result.
\<close>

type_synonym 'a Electoral_Module = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result"

subsection \<open>Auxiliary Definitions\<close>

text \<open>
  Electoral modules partition a given set of alternatives A into a set of
  elected alternatives e, a set of rejected alternatives r, and a set of
  deferred alternatives d, using a profile.
  e, r, and d partition A.
  Electoral modules can be used as voting rules. They can also be composed
  in multiple structures to create more complex electoral modules.
\<close>

definition electoral_module :: " 'a Electoral_Module \<Rightarrow> bool" where
  "electoral_module m \<equiv> \<forall> A p. profile A p \<longrightarrow> well_formed A (m A p)"

text \<open>
  The next three functions take an electoral module and turn it into a
  function only outputting the elect, reject, or defer set respectively.
\<close>

abbreviation elect :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "elect m A p \<equiv> elect_r (m A p)"

abbreviation reject :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "reject m A p \<equiv> reject_r (m A p)"

abbreviation "defer" :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "defer m A p \<equiv> defer_r (m A p)"

text \<open>
  "defers n" is true for all electoral modules that defer exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition defers :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "defers n m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. card A \<ge> n \<and> finite_profile A p \<longrightarrow> card (defer m A p) = n)"

text \<open>
  "rejects n" is true for all electoral modules that reject exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition rejects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. card A \<ge> n \<and> finite_profile A p \<longrightarrow> card (reject m A p) = n)"

text \<open>
  As opposed to "rejects", "eliminates" allows to stop rejecting if no
  alternatives were to remain.
\<close>

definition eliminates :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. card A > n \<and> profile A p \<longrightarrow> card (reject m A p) = n)"

text \<open>
  "elects n" is true for all electoral modules that
  elect exactly n alternatives, whenever there are n or more alternatives.
\<close>

definition elects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "elects n m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. card A \<ge> n \<and> profile A p \<longrightarrow> card (elect m A p) = n)"

text \<open>
  An electoral module is independent of an alternative a iff
  a's ranking does not influence the outcome.
\<close>

definition indep_of_alt :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "indep_of_alt m A a \<equiv>
    electoral_module m \<and> (\<forall> p q. equiv_prof_except_a A p q a \<longrightarrow> m A p = m A q)"

definition unique_winner_if_profile_non_empty :: "'a Electoral_Module \<Rightarrow> bool" where
  "unique_winner_if_profile_non_empty m \<equiv>
    electoral_module m \<and>
    (\<forall> A p. A \<noteq> {} \<and> p \<noteq> [] \<and> profile A p \<longrightarrow> (\<exists> a \<in> A. m A p = ({a}, A - {a}, {})))"

subsection \<open>Equivalence Definitions\<close>

definition prof_contains_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                       'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_contains_result m A p q a \<equiv>
    electoral_module m \<and> profile A p \<and> profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer m A q)"

definition prof_leq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_leq_result m A p q a \<equiv>
    electoral_module m \<and> profile A p \<and> profile A q \<and> a \<in> A \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> elect m A q)"

definition prof_geq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_geq_result m A p q a \<equiv>
    electoral_module m \<and> profile A p \<and> profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> reject m A q)"

definition mod_contains_result :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
                                      'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "mod_contains_result m n A p a \<equiv>
    electoral_module m \<and> electoral_module n \<and> profile A p \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect n A p) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject n A p) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer n A p)"

definition mod_contains_result_sym :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
                                      'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "mod_contains_result_sym m n A p a \<equiv>
    electoral_module m \<and> electoral_module n \<and> profile A p \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longleftrightarrow> a \<in> elect n A p) \<and>
    (a \<in> reject m A p \<longleftrightarrow> a \<in> reject n A p) \<and>
    (a \<in> defer m A p \<longleftrightarrow> a \<in> defer n A p)"

subsection \<open>Auxiliary Lemmas\<close>

lemma combine_ele_rej_def:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assumes
    "elect m A p = e" and
    "reject m A p = r" and
    "defer m A p = d"
  shows "m A p = (e, r, d)"
  using assms
  by auto

lemma par_comp_result_sound:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "well_formed A (m A p)"
  using assms
  unfolding electoral_module_def
  by simp

lemma result_presv_alts:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> elect m A p"
  moreover have
    "\<forall> p'. set_equals_partition A p' \<longrightarrow>
        (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)"
    by simp
  moreover have "set_equals_partition A (m A p)"
    using assms
    unfolding electoral_module_def
    by simp
  ultimately show "a \<in> A"
    using UnI1 fstI
    by (metis (no_types))
next
  fix a :: "'a"
  assume "a \<in> reject m A p"
  moreover have
    "\<forall> p'. set_equals_partition A p' \<longrightarrow>
        (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)"
    by simp
  moreover have "set_equals_partition A (m A p)"
    using assms
    unfolding electoral_module_def
    by simp
  ultimately show "a \<in> A"
    using UnI1 fstI sndI subsetD sup_ge2
    by metis
next
  fix a :: "'a"
  assume "a \<in> defer m A p"
  moreover have
    "\<forall> p'. set_equals_partition A p' \<longrightarrow>
        (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)"
    by simp
  moreover have "set_equals_partition A (m A p)"
    using assms
    unfolding electoral_module_def
    by simp
  ultimately show "a \<in> A"
    using sndI subsetD sup_ge2
    by metis
next
  fix a :: "'a"
  assume
    "a \<in> A" and
    "a \<notin> defer m A p" and
    "a \<notin> reject m A p"
  moreover have
    "\<forall> p'. set_equals_partition A p' \<longrightarrow>
        (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)"
    by simp
  moreover have "set_equals_partition A (m A p)"
    using assms
    unfolding electoral_module_def
    by simp
  ultimately show "a \<in> elect m A p"
    using prod.sel Un_iff
    by metis
qed

lemma result_disj:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows
    "(elect m A p) \<inter> (reject m A p) = {} \<and>
        (elect m A p) \<inter> (defer m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
proof (safe, simp_all)
  fix a :: "'a"
  assume
    "a \<in> elect m A p" and
    "a \<in> reject m A p"
  moreover have "well_formed A (m A p)"
    using assms
    unfolding electoral_module_def
    by metis
  ultimately show False
    using prod.exhaust_sel DiffE UnCI result_imp_rej
    by (metis (no_types))
next
  fix a :: "'a"
  assume
    elect_a: "a \<in> elect m A p" and
    defer_a: "a \<in> defer m A p"
  have disj:
    "\<forall> p'. disjoint3 p' \<longrightarrow>
      (\<exists> B C D. p' = (B, C, D) \<and> B \<inter> C = {} \<and> B \<inter> D = {} \<and> C \<inter> D = {})"
    by simp
  have "well_formed A (m A p)"
    using assms
    unfolding electoral_module_def
    by metis
  hence "disjoint3 (m A p)"
    by simp
  then obtain
    e :: "'a Result \<Rightarrow> 'a set" and
    r :: "'a Result \<Rightarrow> 'a set" and
    d :: "'a Result \<Rightarrow> 'a set"
    where
    "m A p =
      (e (m A p), r (m A p), d (m A p)) \<and>
        e (m A p) \<inter> r (m A p) = {} \<and>
        e (m A p) \<inter> d (m A p) = {} \<and>
        r (m A p) \<inter> d (m A p) = {}"
    using elect_a defer_a disj
    by metis
  hence "((elect m A p) \<inter> (reject m A p) = {}) \<and>
          ((elect m A p) \<inter> (defer m A p) = {}) \<and>
          ((reject m A p) \<inter> (defer m A p) = {})"
    using eq_snd_iff fstI
    by metis
  thus False
    using elect_a defer_a disjoint_iff_not_equal
    by (metis (no_types))
next
  fix a :: "'a"
  assume
    "a \<in> reject m A p" and
    "a \<in> defer m A p"
  moreover have "well_formed A (m A p)"
    using assms
    unfolding electoral_module_def
    by simp
  ultimately show False
    using prod.exhaust_sel DiffE UnCI result_imp_rej
    by (metis (no_types))
qed

lemma elect_in_alts:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "elect m A p \<subseteq> A"
  using le_supI1 assms result_presv_alts sup_ge1
  by metis

lemma reject_in_alts:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "reject m A p \<subseteq> A"
  using le_supI1 assms result_presv_alts sup_ge2
  by fastforce

lemma defer_in_alts:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "defer m A p \<subseteq> A"
  using assms result_presv_alts
  by auto

lemma def_presv_prof:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "profile (defer m A p) (limit_profile (defer m A p) p)"
  using defer_in_alts limit_profile_sound assms
  by metis

text \<open>
  An electoral module can never reject, defer or elect more than
  |A| alternatives.
\<close>

lemma upper_card_bounds_for_result:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "finite_profile A p"
  shows
    upper_card_bound_for_elect: "card (elect m A p) \<le> card A" and
    upper_card_bound_for_reject: "card (reject m A p) \<le> card A" and
    upper_card_bound_for_defer: "card (defer m A p) \<le> card A"
proof -
  show "card (elect m A p) \<le> card A"
    by (simp add: assms card_mono elect_in_alts)
next
  show "card (reject m A p) \<le> card A"
    by (simp add: assms card_mono reject_in_alts)
next
  show "card (defer m A p) \<le> card A"
    by (simp add: assms card_mono defer_in_alts)
qed

lemma reject_not_elec_or_def:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "reject m A p = A - (elect m A p) - (defer m A p)"
proof -
  have "well_formed A (m A p)"
    using assms
    unfolding electoral_module_def
    by simp
  hence "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using assms result_presv_alts
    by simp
  moreover have
    "(elect m A p) \<inter> (reject m A p) = {} \<and> (reject m A p) \<inter> (defer m A p) = {}"
    using assms result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma elec_and_def_not_rej:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "elect m A p \<union> defer m A p = A - (reject m A p)"
proof -
  have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using assms result_presv_alts
    by blast
  moreover have
    "(elect m A p) \<inter> (reject m A p) = {} \<and> (reject m A p) \<inter> (defer m A p) = {}"
    using assms result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma defer_not_elec_or_rej:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "electoral_module m" and
    "profile A p"
  shows "defer m A p = A - (elect m A p) - (reject m A p)"
proof -
  have "well_formed A (m A p)"
    using assms
    unfolding electoral_module_def
    by simp
  hence "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using assms result_presv_alts
    by simp
  moreover have
    "(elect m A p) \<inter> (defer m A p) = {} \<and> (reject m A p) \<inter> (defer m A p) = {}"
    using assms result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma electoral_mod_defer_elem:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    "electoral_module m" and
    "profile A p" and
    "a \<in> A" and
    "a \<notin> elect m A p" and
    "a \<notin> reject m A p"
  shows "a \<in> defer m A p"
  using DiffI assms reject_not_elec_or_def
  by metis

lemma mod_contains_result_comm:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes "mod_contains_result m n A p a"
  shows "mod_contains_result n m A p a"
proof (unfold mod_contains_result_def, safe)
  from assms
  show "electoral_module n"
    unfolding mod_contains_result_def
    by safe
next
  from assms
  show "electoral_module m"
    unfolding mod_contains_result_def
    by safe
next
  from assms
  show "profile A p"
    unfolding mod_contains_result_def
    by safe
next
  from assms
  show "a \<in> A"
    unfolding mod_contains_result_def
    by safe
next
  assume "a \<in> elect n A p"
  thus "a \<in> elect m A p"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
next
  assume "a \<in> reject n A p"
  thus "a \<in> reject m A p"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
next
  assume "a \<in> defer n A p"
  thus "a \<in> defer m A p"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
qed

lemma not_rej_imp_elec_or_def:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    "electoral_module m" and
    "profile A p" and
    "a \<in> A" and
    "a \<notin> reject m A p"
  shows "a \<in> elect m A p \<or> a \<in> defer m A p"
  using assms electoral_mod_defer_elem
  by metis

lemma single_elim_imp_red_def_set:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "eliminates 1 m" and
    "card A > 1" and
    "profile A p"
  shows "defer m A p \<subset> A"
  using Diff_eq_empty_iff Diff_subset card_eq_0_iff defer_in_alts eliminates_def
        eq_iff not_one_le_zero psubsetI reject_not_elec_or_def assms
  by metis

lemma eq_alts_in_profs_imp_eq_results:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assumes
    eq: "\<forall> a \<in> A. prof_contains_result m A p q a" and
    mod_m: "electoral_module m" and
    prof_p: "profile A p" and
    prof_q: "profile A q"
  shows "m A p = m A q"
proof -
  have elected_in_A: "elect m A q \<subseteq> A"
    using elect_in_alts mod_m prof_q
    by metis
  have rejected_in_A: "reject m A q \<subseteq> A"
    using reject_in_alts mod_m prof_q
    by metis
  have deferred_in_A: "defer m A q \<subseteq> A"
    using defer_in_alts mod_m prof_q
    by metis
  have "\<forall> a \<in> elect m A p. a \<in> elect m A q"
    using elect_in_alts eq prof_contains_result_def mod_m prof_p in_mono
    by metis
  moreover have "\<forall> a \<in> elect m A q. a \<in> elect m A p"
  proof
    fix a :: "'a"
    assume q_elect_a: "a \<in> elect m A q"
    hence "a \<in> A"
      using elected_in_A
      by blast
    moreover have "a \<notin> defer m A q"
      using q_elect_a prof_q mod_m result_disj
      by blast
    moreover have "a \<notin> reject m A q"
      using q_elect_a disjoint_iff_not_equal prof_q mod_m result_disj
      by metis
    ultimately show "a \<in> elect m A p"
      using electoral_mod_defer_elem eq prof_contains_result_def
      by metis
  qed
  moreover have "\<forall> a \<in> reject m A p. a \<in> reject m A q"
    using reject_in_alts eq prof_contains_result_def mod_m prof_p
    by fastforce
  moreover have "\<forall> a \<in> reject m A q. a \<in> reject m A p"
  proof
    fix a :: 'a
    assume q_rejects_a: "a \<in> reject m A q"
    hence "a \<in> A"
      using rejected_in_A
      by blast
    moreover have a_not_deferred_q: "a \<notin> defer m A q"
      using q_rejects_a prof_q mod_m result_disj
      by blast
    moreover have a_not_elected_q: "a \<notin> elect m A q"
      using q_rejects_a disjoint_iff_not_equal prof_q mod_m result_disj
      by metis
    ultimately show "a \<in> reject m A p"
      using electoral_mod_defer_elem eq prof_contains_result_def
      by metis
  qed
  moreover have "\<forall> a \<in> defer m A p. a \<in> defer m A q"
    using defer_in_alts eq prof_contains_result_def mod_m prof_p
    by fastforce
  moreover have "\<forall> a \<in> defer m A q. a \<in> defer m A p"
  proof
    fix a :: "'a"
    assume q_defers_a: "a \<in> defer m A q"
    moreover have "a \<in> A"
      using q_defers_a deferred_in_A
      by blast
    moreover have "a \<notin> elect m A q"
      using q_defers_a prof_q mod_m result_disj
      by blast
    moreover have "a \<notin> reject m A q"
      using q_defers_a prof_q disjoint_iff_not_equal mod_m result_disj
      by metis
    ultimately show "a \<in> defer m A p"
      using electoral_mod_defer_elem eq prof_contains_result_def
      by metis
  qed
  ultimately show ?thesis
    using prod.collapse subsetI subset_antisym
    by (metis (no_types))
qed

lemma eq_def_and_elect_imp_eq:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n" and
    prof_p: "profile A p" and
    prof_q: "profile A q" and
    elec_eq: "elect m A p = elect n A q" and
    def_eq: "defer m A p = defer n A q"
  shows "m A p = n A q"
proof -
  have "reject m A p = A - ((elect m A p) \<union> (defer m A p))"
    using mod_m prof_p combine_ele_rej_def result_imp_rej
    unfolding electoral_module_def
    by metis
  moreover have "reject n A q = A - ((elect n A q) \<union> (defer n A q))"
    using mod_n prof_q combine_ele_rej_def result_imp_rej
    unfolding electoral_module_def
    by metis
  ultimately show ?thesis
    using elec_eq def_eq prod_eqI
    by metis
qed

subsection \<open>Non-Blocking\<close>

text \<open>
  An electoral module is non-blocking iff
  this module never rejects all alternatives.
\<close>

definition non_blocking :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_blocking m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow> reject m A p \<noteq> A)"

subsection \<open>Electing\<close>

text \<open>
  An electoral module is electing iff
  it always elects at least one alternative.
\<close>

definition electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "electing m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow> elect m A p \<noteq> {})"

lemma electing_for_only_alt:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    one_alt: "card A = 1" and
    electing: "electing m" and
    prof_p: "profile A p"
  shows "elect m A p = A"
proof (safe)
  fix a :: "'a"
  assume elect_a: "a \<in> elect m A p"
  have "electoral_module m \<longrightarrow> elect m A p \<subseteq> A"
    using prof_p
    by (simp add: elect_in_alts)
  hence "elect m A p \<subseteq> A"
    using electing
    unfolding electing_def
    by metis
  thus "a \<in> A"
    using elect_a
    by blast
next
  fix a :: "'a"
  assume "a \<in> A"
  thus "a \<in> elect m A p"
    using electing prof_p one_alt One_nat_def Suc_leI card_seteq card_gt_0_iff
          elect_in_alts infinite_super lessI
    unfolding electing_def
    by metis
qed

theorem electing_imp_non_blocking:
  fixes m :: "'a Electoral_Module"
  assumes "electing m"
  shows "non_blocking m"
proof (unfold non_blocking_def, safe)
  from assms
  show "electoral_module m"
    unfolding electing_def
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    "finite A" and
    "profile A p" and
    "reject m A p = A" and
    "a \<in> A"
  moreover have
    "electoral_module m \<and>
      (\<forall> A q. A \<noteq> {} \<and> finite_profile A q \<longrightarrow> elect m A q \<noteq> {})"
    using assms
    unfolding electing_def
    by metis
  ultimately show "a \<in> {}"
    using Diff_cancel Un_empty elec_and_def_not_rej
    by (metis (no_types))
qed

subsection \<open>Properties\<close>

text \<open>
  An electoral module is non-electing iff
  it never elects an alternative.
\<close>

definition non_electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_electing m \<equiv>
    electoral_module m \<and> (\<forall> A p. profile A p \<longrightarrow> elect m A p = {})"

lemma single_rej_decr_def_card:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    rejecting: "rejects 1 m" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p"
  shows "card (defer m A p) = card A - 1"
proof -
  have no_elect:
    "electoral_module m \<and> (\<forall> A q. profile A q \<longrightarrow> elect m A q = {})"
    using non_electing
    unfolding non_electing_def
    by (metis (no_types))
  hence "reject m A p \<subseteq> A"
    using f_prof reject_in_alts
    by metis
  moreover have "A = A - elect m A p"
    using no_elect f_prof
    by blast
  ultimately show ?thesis
    using f_prof no_elect rejecting card_Diff_subset card_gt_0_iff
          defer_not_elec_or_rej less_one order_less_imp_le Suc_leI
          bot.extremum_unique card.empty diff_is_0_eq' One_nat_def
    unfolding rejects_def
    by metis
qed

lemma single_elim_decr_def_card:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    eliminating: "eliminates 1 m" and
    non_electing: "non_electing m" and
    not_empty: "card A > 1" and
    prof_p: "profile A p"
  shows "card (defer m A p) = card A - 1"
proof -
  have no_elect:
    "electoral_module m \<and> (\<forall> A q. profile A q \<longrightarrow> elect m A q = {})"
    using non_electing
    unfolding non_electing_def
    by (metis (no_types))
  hence "reject m A p \<subseteq> A"
    using prof_p reject_in_alts
    by metis
  moreover have "A = A - elect m A p"
    using no_elect prof_p
    by blast
  ultimately show ?thesis
    using prof_p not_empty no_elect eliminating card_ge_0_finite
          card_Diff_subset defer_not_elec_or_rej zero_less_one
    unfolding eliminates_def
    by (metis (no_types, lifting))
qed

text \<open>
  An electoral module is defer-deciding iff
  this module chooses exactly 1 alternative to defer and
  rejects any other alternative.
  Note that `rejects n-1 m` can be omitted due to the
  well-formedness property.
\<close>

definition defer_deciding :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_deciding m \<equiv>
    electoral_module m \<and> non_electing m \<and> defers 1 m"

text \<open>
  An electoral module decrements iff
  this module rejects at least one alternative whenever possible (|A| > 1).
\<close>

definition decrementing :: "'a Electoral_Module \<Rightarrow> bool" where
  "decrementing m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. profile A p \<and> card A > 1 \<longrightarrow> card (reject m A p) \<ge> 1)"

definition defer_condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p a. condorcet_winner A p a \<longrightarrow>
      (m A p = ({}, A - (defer m A p), {d \<in> A. condorcet_winner A p d})))"

definition condorcet_compatibility :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_compatibility m \<equiv>
    electoral_module m \<and>
    (\<forall> A p a. condorcet_winner A p a \<longrightarrow>
      (a \<notin> reject m A p \<and>
        (\<forall> b. \<not> condorcet_winner A p b \<longrightarrow> b \<notin> elect m A p) \<and>
          (a \<in> elect m A p \<longrightarrow>
            (\<forall> b \<in> A. \<not> condorcet_winner A p b \<longrightarrow> b \<in> reject m A p))))"

text \<open>
  An electoral module is defer-monotone iff,
  when a deferred alternative is lifted, this alternative remains deferred.
\<close>

definition defer_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall> A p q a. a \<in> defer m A p \<and> lifted A p q a \<longrightarrow> a \<in> defer m A q)"

text \<open>
  An electoral module is defer-lift-invariant iff
  lifting a deferred alternative does not affect the outcome.
\<close>

definition defer_lift_invariance :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_lift_invariance m \<equiv>
    electoral_module m \<and>
      (\<forall> A p q a. a \<in> (defer m A p) \<and> lifted A p q a \<longrightarrow> m A p = m A q)"

text \<open>
  Two electoral modules are disjoint-compatible if they only make decisions
  over disjoint sets of alternatives. Electoral modules reject alternatives
  for which they make no decision.
\<close>

definition disjoint_compatibility :: "'a Electoral_Module \<Rightarrow>
                                         'a Electoral_Module \<Rightarrow> bool" where
  "disjoint_compatibility m n \<equiv>
    electoral_module m \<and> electoral_module n \<and>
        (\<forall> A.
          (\<exists> B \<subseteq> A.
            (\<forall> a \<in> B. indep_of_alt m A a \<and>
              (\<forall> p. profile A p \<longrightarrow> a \<in> reject m A p)) \<and>
            (\<forall> a \<in> A - B. indep_of_alt n A a \<and>
              (\<forall> p. profile A p \<longrightarrow> a \<in> reject n A p))))"

text \<open>
  Lifting an elected alternative a from an invariant-monotone
  electoral module either does not change the elect set, or
  makes a the only elected alternative.
\<close>

definition invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "invariant_monotonicity m \<equiv>
    electoral_module m \<and>
        (\<forall> A p q a. (a \<in> elect m A p \<and> lifted A p q a) \<longrightarrow>
          (elect m A q = elect m A p \<or> elect m A q = {a}))"

text \<open>
  Lifting a deferred alternative a from a defer-invariant-monotone
  electoral module either does not change the defer set, or
  makes a the only deferred alternative.
\<close>

definition defer_invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_invariant_monotonicity m \<equiv>
    electoral_module m \<and> non_electing m \<and>
        (\<forall> A p q a. (a \<in> defer m A p \<and> lifted A p q a) \<longrightarrow>
          (defer m A q = defer m A p \<or> defer m A q = {a}))"

subsection \<open>Inference Rules\<close>

lemma ccomp_and_dd_imp_def_only_winner:
  fixes
    m :: "'a Electoral_Module" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    ccomp: "condorcet_compatibility m" and
    dd: "defer_deciding m" and
    winner: "condorcet_winner A p a"
  shows "defer m A p = {a}"
proof (rule ccontr)
  assume not_w: "defer m A p \<noteq> {a}"
  have def_one: "defers 1 m"
    using dd
    unfolding defer_deciding_def
    by metis
  hence c_win: "finite_profile A p \<and> a \<in> A \<and> (\<forall> b \<in> A - {a}. wins a p b)"
    using winner
    by simp
  hence "card (defer m A p) = 1"
    using Suc_leI card_gt_0_iff def_one equals0D
    unfolding One_nat_def defers_def
    by metis
  hence "\<exists> b \<in> A. defer m A p = {b}"
    using card_1_singletonE dd defer_in_alts insert_subset c_win
    unfolding defer_deciding_def
    by metis
  hence "\<exists> b \<in> A. b \<noteq> a \<and> defer m A p = {b}"
    using not_w
    by metis
  hence not_in_defer: "a \<notin> defer m A p"
    by auto
  have "non_electing m"
    using dd
    unfolding defer_deciding_def
    by simp
  hence "a \<notin> elect m A p"
    using c_win equals0D
    unfolding non_electing_def
    by simp
  hence "a \<in> reject m A p"
    using not_in_defer ccomp c_win electoral_mod_defer_elem
    unfolding condorcet_compatibility_def
    by metis
  moreover have "a \<notin> reject m A p"
    using ccomp c_win winner
    unfolding condorcet_compatibility_def
    by simp
  ultimately show False
    by simp
qed

theorem ccomp_and_dd_imp_dcc[simp]:
  fixes m :: "'a Electoral_Module"
  assumes
    ccomp: "condorcet_compatibility m" and
    dd: "defer_deciding m"
  shows "defer_condorcet_consistency m"
proof (unfold defer_condorcet_consistency_def, auto)
  show "electoral_module m"
    using dd
    unfolding defer_deciding_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    a_in_A: "a \<in> A" and
    c_winner: "\<forall> b \<in> A - {a}.
                 card {i. i < length p \<and> (a, b) \<in> (p!i)} <
                   card {i. i < length p \<and> (b, a) \<in> (p!i)}"
  hence winner: "condorcet_winner A p a"
    by simp
  hence elect_empty: "elect m A p = {}"
    using dd
    unfolding defer_deciding_def non_electing_def
    by simp
  have cond_winner_a: "{a} = {c \<in> A. condorcet_winner A p c}"
    using cond_winner_unique winner
    by metis
  have defer_a: "defer m A p = {a}"
    using winner dd ccomp ccomp_and_dd_imp_def_only_winner winner
    by simp
  hence "reject m A p = A - defer m A p"
    using Diff_empty dd reject_not_elec_or_def winner elect_empty
    unfolding defer_deciding_def
    by fastforce
  hence "m A p = ({}, A - defer m A p, {a})"
    using elect_empty defer_a combine_ele_rej_def
    by metis
  hence "m A p = ({}, A - defer m A p, {c \<in> A. condorcet_winner A p c})"
    using cond_winner_a
    by simp
  thus "m A p =
          ({},
            A - defer m A p,
            {c \<in> A. \<forall> b \<in> A - {c}.
              card {i. i < length p \<and> (c, b) \<in> (p!i)} <
                card {i. i < length p \<and> (b, c) \<in> (p!i)}})"
    using prof_A winner Collect_cong
    by simp
qed

text \<open>
  If m and n are disjoint compatible, so are n and m.
\<close>

theorem disj_compat_comm[simp]:
  fixes
    m :: "'a Electoral_Module" and
    n :: "'a Electoral_Module"
  assumes "disjoint_compatibility m n"
  shows "disjoint_compatibility n m"
proof (unfold disjoint_compatibility_def, safe)
  show "electoral_module m"
    using assms
    unfolding disjoint_compatibility_def
    by simp
next
  show "electoral_module n"
    using assms
    unfolding disjoint_compatibility_def
    by simp
next
  fix A :: "'a set"
  obtain B where
    "B \<subseteq> A \<and>
      (\<forall> a \<in> B.
        indep_of_alt m A a \<and> (\<forall> p. profile A p \<longrightarrow> a \<in> reject m A p)) \<and>
      (\<forall> a \<in> A - B.
        indep_of_alt n A a \<and> (\<forall> p. profile A p \<longrightarrow> a \<in> reject n A p))"
    using assms
    unfolding disjoint_compatibility_def
    by metis
  hence
    "\<exists> B \<subseteq> A.
      (\<forall> a \<in> A - B.
        indep_of_alt n A a \<and> (\<forall> p. profile A p \<longrightarrow> a \<in> reject n A p)) \<and>
      (\<forall> a \<in> B.
        indep_of_alt m A a \<and> (\<forall> p. profile A p \<longrightarrow> a \<in> reject m A p))"
    by auto
  hence "\<exists> B \<subseteq> A.
          (\<forall> a \<in> A - B.
            indep_of_alt n A a \<and> (\<forall> p. profile A p \<longrightarrow> a \<in> reject n A p)) \<and>
          (\<forall> a \<in> A - (A - B).
            indep_of_alt m A a \<and> (\<forall> p. profile A p \<longrightarrow> a \<in> reject m A p))"
    using double_diff order_refl
    by metis
  thus "\<exists> B \<subseteq> A.
          (\<forall> a \<in> B.
            indep_of_alt n A a \<and> (\<forall> p. profile A p \<longrightarrow> a \<in> reject n A p)) \<and>
          (\<forall> a \<in> A - B.
            indep_of_alt m A a \<and> (\<forall> p. profile A p \<longrightarrow> a \<in> reject m A p))"
    by fastforce
qed

text \<open>
  Every electoral module which is defer-lift-invariant is
  also defer-monotone.
\<close>

theorem dl_inv_imp_def_mono[simp]:
  fixes m :: "'a Electoral_Module"
  assumes "defer_lift_invariance m"
  shows "defer_monotonicity m"
  using assms
  unfolding defer_monotonicity_def defer_lift_invariance_def
  by metis

subsection \<open>Social Choice Properties\<close>

subsubsection \<open>Condorcet Consistency\<close>

definition condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p a. condorcet_winner A p a \<longrightarrow>
      (m A p = ({e \<in> A. condorcet_winner A p e}, A - (elect m A p), {})))"

lemma condorcet_consistency':
  fixes m :: "'a Electoral_Module"
  shows "condorcet_consistency m =
           (electoral_module m \<and>
              (\<forall> A p a. condorcet_winner A p a \<longrightarrow>
                (m A p = ({a}, A - (elect m A p), {}))))"
proof (safe)
  assume "condorcet_consistency m"
  thus "electoral_module m"
    unfolding condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    "condorcet_consistency m" and
    "condorcet_winner A p a"
  thus "m A p = ({a}, A - elect m A p, {})"
    using cond_winner_unique
    unfolding condorcet_consistency_def
    by (metis (mono_tags, lifting))
next
  assume
    "electoral_module m" and
    "\<forall> A p a. condorcet_winner A p a \<longrightarrow> m A p = ({a}, A - elect m A p, {})"
  moreover have
    "\<forall> m'. condorcet_consistency m' =
      (electoral_module m' \<and>
        (\<forall> A p a. condorcet_winner A p a \<longrightarrow>
          m' A p = ({a \<in> A. condorcet_winner A p a}, A - elect m' A p, {})))"
    unfolding condorcet_consistency_def
    by blast
  moreover have
    "\<forall> A p a. condorcet_winner A p (a::'a) \<longrightarrow>
        {b \<in> A. condorcet_winner A p b} = {a}"
    using cond_winner_unique
    by (metis (full_types))
  ultimately show "condorcet_consistency m"
    unfolding condorcet_consistency_def
    using cond_winner_unique
    by presburger
qed

lemma condorcet_consistency'':
  fixes m :: "'a Electoral_Module"
  shows "condorcet_consistency m =
           (electoral_module m \<and>
              (\<forall> A p a.
                condorcet_winner A p a \<longrightarrow> (m A p = ({a}, A - {a}, {}))))"
proof (simp only: condorcet_consistency', safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    e_mod: "electoral_module m" and
    cc: "\<forall> A p a'. condorcet_winner A p a' \<longrightarrow>
      m A p = ({a'}, A - elect m A p, {})" and
    c_win: "condorcet_winner A p a"
  show "m A p = ({a}, A - {a}, {})"
    using cc c_win fst_conv
    by (metis (mono_tags, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    e_mod: "electoral_module m" and
    cc: "\<forall> A p a'. condorcet_winner A p a' \<longrightarrow> m A p = ({a'}, A -  {a'}, {})" and
    c_win: "condorcet_winner A p a"
  show "m A p = ({a}, A -  elect m A p, {})"
    using cc c_win fst_conv
    by (metis (mono_tags, lifting))
qed

subsubsection \<open>(Weak) Monotonicity\<close>

text \<open>
  An electoral module is monotone iff
  when an elected alternative is lifted, this alternative remains elected.
\<close>

definition monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall> A p q a. a \<in> elect m A p \<and> lifted A p q a \<longrightarrow> a \<in> elect m A q)"

subsubsection \<open>Homogeneity\<close>

fun times :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "times n l = concat (replicate n l)"

definition homogeneity :: "'a Electoral_Module \<Rightarrow> bool" where
  "homogeneity m \<equiv>
    electoral_module m \<and>
      (\<forall> A p n. profile A p \<and> n > 0 \<longrightarrow> m A p = m A (times n p))"

subsubsection \<open>Anonymity\<close>

definition anonymity :: "'a Electoral_Module \<Rightarrow> bool" where
  "anonymity m \<equiv>
    electoral_module m \<and>
      (\<forall> A p q. profile A p \<and> profile A q \<and> p <~~> q \<longrightarrow> m A p = m A q)"

end

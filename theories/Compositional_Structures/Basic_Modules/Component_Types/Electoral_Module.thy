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
          "Social_Choice_Types/Result_Interpretations"
          "HOL-Combinatorics.List_Permutation"
begin

text \<open>
  Electoral modules are the principal component type of the composable modules
  voting framework, as they are a generalization of voting rules in the sense
  of social choice functions.
  These are only the types used for electoral modules. Further restrictions are
  encompassed by the electoral-module predicate.

  An electoral module does not need to make final decisions for all
  alternatives, but can instead defer the decision for some or all of them to
  other modules. Hence, electoral modules partition the received (possibly
  empty) set of alternatives into elected, rejected and deferred alternatives.
  In particular, any of those sets, e.g., the set of winning (elected)
  alternatives, may also be left empty, as long as they collectively still hold
  all the received alternatives. Just like a voting rule, an electoral module
  also receives a profile which holds the voters’ preferences, which, unlike a
  voting rule, consider only the (sub-)set of alternatives that the module
  receives.
\<close>

subsection \<open>Definition\<close>

text \<open>
  An electoral module maps an election to a result.
  To enable currying, the Election type is not used here because that would require tuples.
\<close>

type_synonym ('a, 'v, 'r) Electoral_Module = "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r"

abbreviation on_els :: "('a, 'v, 'r) Electoral_Module \<Rightarrow> (('a,'v) Election \<Rightarrow> 'r)" where
  "on_els m \<equiv> (\<lambda>E. m (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E))"

text \<open>
  The next three functions take an electoral module and turn it into a
  function only outputting the elect, reject, or defer set respectively.
\<close>

fun elect :: 
"('a, 'v, 'r Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r set" where
  "elect m V A p = elect_r (m V A p)"

fun reject :: 
"('a, 'v, 'r Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r set" where
  "reject m V A p = reject_r (m V A p)"

fun "defer" :: 
"('a, 'v, 'r Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r set" where
  "defer m V A p = defer_r (m V A p)"

subsection \<open>Auxiliary Definitions\<close>

text \<open>
  Electoral modules partition a given set of alternatives A into a set of
  elected alternatives e, a set of rejected alternatives r, and a set of
  deferred alternatives d, using a profile.
  e, r, and d partition A.
  Electoral modules can be used as voting rules. They can also be composed
  in multiple structures to create more complex electoral modules.
\<close>

definition (in result) electoral_module :: "('a, 'v, ('r Result)) Electoral_Module \<Rightarrow> bool" 
  where
    "electoral_module m \<equiv> \<forall> A V p. finite_profile V A p \<longrightarrow> well_formed A (m V A p)"

definition only_voters_vote :: "('a, 'v, ('r Result)) Electoral_Module \<Rightarrow> bool" where
  "only_voters_vote m \<equiv> \<forall> A V p p'. (\<forall> v \<in> V. p v = p' v) \<longrightarrow> m V A p = m V A p'"

lemma (in result) electoral_modI:
  fixes m :: "('a, 'v, ('r Result)) Electoral_Module"
  assumes "\<And> A V p. finite_profile V A p \<Longrightarrow> well_formed A (m V A p)"
  shows "electoral_module m"
  unfolding electoral_module_def
  using assms
  by simp

subsection \<open>Properties\<close>

subsubsection \<open>Homogeneity\<close>

definition (in result) homogeneity :: "('a, 'v, ('r Result)) Electoral_Module \<Rightarrow> bool" where
  "homogeneity m \<equiv>
    let count = \<lambda>r V p. card {v \<in> V. p v = r} in
    electoral_module m \<and>
      (\<forall> A V V' p p' n. (n > 0 \<longrightarrow> finite_profile V A p
                        \<longrightarrow> (\<forall>r::('a Preference_Relation). count r V' p' = n * (count r V p))
                        \<longrightarrow> finite_profile V' A p'
                        \<longrightarrow> m V A p = m V' A p'))"

subsubsection \<open>Anonymity\<close>

text \<open>
  An electoral module is anonymous iff the result is invariant under renamings of voters,
  i.e. any permutation of the voter set that does not change the preferences leads to an
  identical result.
\<close>

definition (in result) anonymity :: "('a, 'v, ('r Result)) Electoral_Module \<Rightarrow> bool" where
  "anonymity m \<equiv> 
    electoral_module m \<and>
      (\<forall> A V p \<pi>::('v \<Rightarrow> 'v). 
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> m V A p = m V' A' q))"
      
lemma (in result) hom_imp_anon: 
  "homogeneity m \<Longrightarrow> anonymity m"
proof (unfold anonymity_def  Let_def, safe)
  fix
    m :: "('a, 'v, ('r Result)) Electoral_Module"
  assume
    "homogeneity m"
  thus "electoral_module m"
    using homogeneity_def 
    by fastforce
next
  fix 
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'c set" and
    V' :: "'c set" and
    p :: "('a, 'c) Profile" and
    p' :: "('a, 'c) Profile" and
    \<pi> :: "'c \<Rightarrow> 'c" and
    m :: "('a, 'c, ('r Result)) Electoral_Module"
  assume
    hom:  "homogeneity m" and
    bij: "bij \<pi>" and
    rn: "rename \<pi> (A, V, p) = (A', V', p')" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    prof: "profile V A p"
  hence "finite_profile V A p" by simp
  moreover have "finite_profile V' A' p'" 
    using rn rename.simps fin_A fin_V prof bij
          prod.inject rename_finite
    by metis
  moreover have "A' = A" 
    using rn
    by simp
  ultimately have 
    "\<forall>n. n > 0 \<longrightarrow> ((\<forall>r. card {v \<in> V'. p' v = r} = n * card {v \<in> V. p v = r}) \<longrightarrow> 
          m V A p = m V' A p')"
    using hom
    unfolding homogeneity_def Let_def
    by auto
  hence "(\<forall>r. card {v \<in> V'. p' v = r} = card {v \<in> V. p v = r}) \<longrightarrow> 
          m V A p = m V' A p'"
    by auto
  moreover have "\<forall>r. card {v \<in> V'. p' v = r} = card {v \<in> V. p v = r}"
  proof (clarify)
    fix
      r :: "'a Preference_Relation"
    have "\<forall>v \<in> {v \<in> V'. p' v = r}. p ((the_inv \<pi>) v) = r"
      using bij rn rename.simps
      by auto
    hence "\<forall>v \<in> {v \<in> V'. p' v = r}. \<exists>x \<in>  {v \<in> V. p v = r}. \<pi> x = v"
      using the_inv_f_f
      sorry
    hence "\<pi> ` {v \<in> V. p v = r} = {v \<in> V'. p' v = r}" sorry
    moreover have "inj_on \<pi> {v \<in> V. p v = r}"
      using bij bij_is_inj injD inj_onI
      by (metis (mono_tags, lifting))
    ultimately have "bij_betw \<pi> {v \<in> V. p v = r} {v \<in> V'. p' v = r}"
      by (simp add: bij_betw_def)
    thus "card {v \<in> V'. p' v = r} = card {v \<in> V. p v = r}"
      by (simp add: bij_betw_same_card)
  qed
  ultimately show "m V A p = m V' A' p'"
    using \<open>A' = A\<close> 
    by fastforce
qed

text \<open>
  The following results require electoral modules to return social choice results, 
  i.e. sets of elected, rejected and deferred alternatives.
  In order to export code, we use the hack provided by Locale_Code.
\<close>

text \<open>
  "defers n" is true for all electoral modules that defer exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition defers :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defers n m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> finite_profile V A p) \<longrightarrow> card (defer m V A p) = n)"

text \<open>
  "rejects n" is true for all electoral modules that reject exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition rejects :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> finite_profile V A p) \<longrightarrow> card (reject m V A p) = n)"

text \<open>
  As opposed to "rejects", "eliminates" allows to stop rejecting if no
  alternatives were to remain.
\<close>

definition eliminates :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p. (card A > n \<and> finite_profile V A p) \<longrightarrow> card (reject m V A p) = n)"

text \<open>
  "elects n" is true for all electoral modules that
  elect exactly n alternatives, whenever there are n or more alternatives.
\<close>

definition elects :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "elects n m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> finite_profile V A p) \<longrightarrow> card (elect m V A p) = n)"

text \<open>
  An electoral module is independent of an alternative a iff
  a's ranking does not influence the outcome.
\<close>

definition indep_of_alt :: "'v set \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" 
  where
  "indep_of_alt V m A a \<equiv>
    social_choice_result.electoral_module m 
      \<and> (\<forall> p q. equiv_prof_except_a V A p q a \<longrightarrow> m V A p = m V A q)"

definition unique_winner_if_profile_non_empty :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" 
  where
  "unique_winner_if_profile_non_empty m \<equiv>
    social_choice_result.electoral_module m \<and>
    (\<forall> A V p. (A \<noteq> {} \<and> V \<noteq> {} \<and> finite_profile V A p) \<longrightarrow>
              (\<exists> a \<in> A. m V A p = ({a}, A - {a}, {})))"

subsection \<open>Equivalence Definitions\<close>

definition prof_contains_result :: "'v set \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a set
                                    \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_contains_result V m A p q a \<equiv>
    social_choice_result.electoral_module m \<and> 
    finite_profile V A p \<and> finite_profile V A q \<and> a \<in> A \<and>
    (a \<in> elect m V A p \<longrightarrow> a \<in> elect m V A q) \<and>
    (a \<in> reject m V A p \<longrightarrow> a \<in> reject m V A q) \<and>
    (a \<in> defer m V A p \<longrightarrow> a \<in> defer m V A q)"

definition prof_leq_result :: "'v set \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a set 
                                \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_leq_result V m A p q a \<equiv>
    social_choice_result.electoral_module m \<and> 
    finite_profile V A p \<and> finite_profile V A q \<and> a \<in> A \<and>
    (a \<in> reject m V A p \<longrightarrow> a \<in> reject m V A q) \<and>
    (a \<in> defer m V A p \<longrightarrow> a \<notin> elect m V A q)"

definition prof_geq_result :: "'v set \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a set 
                                \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_geq_result V m A p q a \<equiv>
    social_choice_result.electoral_module m \<and> 
    finite_profile V A p \<and> finite_profile V A q \<and> a \<in> A \<and>
    (a \<in> elect m V A p \<longrightarrow> a \<in> elect m V A q) \<and>
    (a \<in> defer m V A p \<longrightarrow> a \<notin> reject m V A q)"

definition mod_contains_result :: "'v set \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module 
                                    \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a set 
                                    \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "mod_contains_result V m n A p a \<equiv>
    social_choice_result.electoral_module m \<and> 
    social_choice_result.electoral_module n \<and> 
    finite_profile V A p \<and> a \<in> A \<and>
    (a \<in> elect m V A p \<longrightarrow> a \<in> elect n V A p) \<and>
    (a \<in> reject m V A p \<longrightarrow> a \<in> reject n V A p) \<and>
    (a \<in> defer m V A p \<longrightarrow> a \<in> defer n V A p)"

subsection \<open>Auxiliary Lemmas\<close>

lemma combine_ele_rej_def:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assumes
    "elect m V A p = e" and
    "reject m V A p = r" and
    "defer m V A p = d"
  shows "m V A p = (e, r, d)"
  using assms
  by auto

lemma par_comp_result_sound:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "well_formed_soc_choice A (m V A p)"
  using assms
  unfolding social_choice_result.electoral_module_def
  by simp

lemma result_presv_alts:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "(elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p) = A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> elect m V A p"
  moreover have
    "\<forall> p'. set_equals_partition A p' \<longrightarrow>
        (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)"
    by simp
  moreover have "set_equals_partition A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by simp
  ultimately show "a \<in> A"
    using UnI1 fstI
    unfolding elect.simps elect_r.simps
    by (metis (no_types))
next
  fix a :: "'a"
  assume "a \<in> reject m V A p"
  moreover have
    "\<forall> p'. set_equals_partition A p' \<longrightarrow>
        (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)"
    by simp
  moreover have "set_equals_partition A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by simp
  ultimately show "a \<in> A"
    using UnI1 fstI sndI subsetD sup_ge2
    unfolding reject.simps reject_r.simps
    by metis
next
  fix a :: "'a"
  assume "a \<in> defer m V A p"
  moreover have
    "\<forall> p'. set_equals_partition A p' \<longrightarrow>
        (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)"
    by simp
  moreover have "set_equals_partition A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by simp
  ultimately show "a \<in> A"
    using sndI subsetD sup_ge2
    unfolding defer.simps defer_r.simps
    by metis
next
  fix a :: "'a"
  assume
    "a \<in> A" and
    "a \<notin> defer m V A p" and
    "a \<notin> reject m V A p"
  moreover have
    "\<forall> p'. set_equals_partition A p' \<longrightarrow>
        (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)"
    by simp
  moreover have "set_equals_partition A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by simp
  ultimately show "a \<in> elect m V A p"
    using fst_conv snd_conv Un_iff
    unfolding reject.simps defer.simps elect.simps
              reject_r.simps defer_r.simps elect_r.simps
    by metis
qed

lemma result_disj:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    V :: "'v set"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows
    "(elect m V A p) \<inter> (reject m V A p) = {} \<and>
        (elect m V A p) \<inter> (defer m V A p) = {} \<and>
        (reject m V A p) \<inter> (defer m V A p) = {}"
proof (safe)
  fix a :: "'a"
  assume
    "a \<in> elect m V A p" and
    "a \<in> reject m V A p"
  moreover have "well_formed_soc_choice A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by metis
  ultimately show "a \<in> {}"
    using prod.exhaust_sel DiffE UnCI result_imp_rej
    unfolding reject.simps elect.simps elect_r.simps reject_r.simps
    by (metis (no_types))
next
  fix a :: "'a"
  assume
    elect_a: "a \<in> elect m V A p" and
    defer_a: "a \<in> defer m V A p"
  have disj:
    "\<forall> p'. disjoint3 p' \<longrightarrow>
      (\<exists> B C D. p' = (B, C, D) \<and> B \<inter> C = {} \<and> B \<inter> D = {} \<and> C \<inter> D = {})"
    by simp
  have "well_formed_soc_choice A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by metis
  hence "disjoint3 (m V A p)"
    by simp
  then obtain
    e :: "'a Result \<Rightarrow> 'a set" and
    r :: "'a Result \<Rightarrow> 'a set" and
    d :: "'a Result \<Rightarrow> 'a set"
    where
    "m V A p =
      (e (m V A p), r (m V A p), d (m V A p)) \<and>
        e (m V A p) \<inter> r (m V A p) = {} \<and>
        e (m V A p) \<inter> d (m V A p) = {} \<and>
        r (m V A p) \<inter> d (m V A p) = {}"
    using elect_a defer_a disj
    by metis
  hence "((elect m V A p) \<inter> (reject m V A p) = {}) \<and>
          ((elect m V A p) \<inter> (defer m V A p) = {}) \<and>
          ((reject m V A p) \<inter> (defer m V A p) = {})"
    using eq_snd_iff fstI
    unfolding elect.simps defer.simps reject.simps
              elect_r.simps defer_r.simps reject_r.simps
    by metis
  thus "a \<in> {}"
    using elect_a defer_a disjoint_iff_not_equal
    by (metis (no_types))
next
  fix a :: "'a"
  assume
    "a \<in> reject m V A p" and
    "a \<in> defer m V A p"
  moreover have "well_formed_soc_choice A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by simp
  ultimately show "a \<in> {}"
    using prod.exhaust_sel DiffE UnCI result_imp_rej
    unfolding reject.simps defer.simps reject_r.simps defer_r.simps
    by (metis (no_types))
qed

lemma elect_in_alts:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "elect m V A p \<subseteq> A"
  using le_supI1 assms result_presv_alts sup_ge1
  by metis

lemma reject_in_alts:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "reject m V A p \<subseteq> A"
  using le_supI1 assms result_presv_alts sup_ge2
  by fastforce

lemma defer_in_alts:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "defer m V A p \<subseteq> A"
  using assms result_presv_alts
  by fastforce

lemma def_presv_fin_prof:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "let new_A = defer m V A p in finite_profile V new_A (limit_profile new_A p)"
  using defer_in_alts infinite_super limit_profile_sound assms
  by metis

text \<open>
  An electoral module can never reject, defer or elect more than
  |A| alternatives.
\<close>

lemma upper_card_bounds_for_result:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows
    "card (elect m V A p) \<le> card A \<and>
      card (reject m V A p) \<le> card A \<and>
      card (defer m V A p) \<le> card A "
  using assms card_mono defer_in_alts elect_in_alts reject_in_alts
  by metis

lemma reject_not_elec_or_def:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "reject m V A p = A - (elect m V A p) - (defer m V A p)"
proof -
  have "well_formed_soc_choice A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by simp
  hence "(elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p) = A"
    using assms result_presv_alts
    by simp
  moreover have
    "(elect m V A p) \<inter> (reject m V A p) = {} \<and> (reject m V A p) \<inter> (defer m V A p) = {}"
    using assms result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma elec_and_def_not_rej:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "elect m V A p \<union> defer m V A p = A - (reject m V A p)"
proof -
  have "(elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p) = A"
    using assms result_presv_alts
    by blast
  moreover have
    "(elect m V A p) \<inter> (reject m V A p) = {} \<and> (reject m V A p) \<inter> (defer m V A p) = {}"
    using assms result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma defer_not_elec_or_rej:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p"
  shows "defer m V A p = A - (elect m V A p) - (reject m V A p)"
proof -
  have "well_formed_soc_choice A (m V A p)"
    using assms
    unfolding social_choice_result.electoral_module_def
    by simp
  hence "(elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p) = A"
    using assms result_presv_alts
    by simp
  moreover have
    "(elect m V A p) \<inter> (defer m V A p) = {} \<and> (reject m V A p) \<inter> (defer m V A p) = {}"
    using assms result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma electoral_mod_defer_elem:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p" and
    "a \<in> A" and
    "a \<notin> elect m V A p" and
    "a \<notin> reject m V A p"
  shows "a \<in> defer m V A p"
  using DiffI assms reject_not_elec_or_def
  by metis

lemma mod_contains_result_comm:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result)  Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "mod_contains_result V m n A p a"
  shows "mod_contains_result V n m A p a"
proof (unfold mod_contains_result_def, safe)
  from assms
  show "social_choice_result.electoral_module n"
    unfolding mod_contains_result_def
    by safe
next
  from assms
  show "social_choice_result.electoral_module m"
    unfolding mod_contains_result_def
    by safe
next
  from assms
  show "finite A"
    unfolding mod_contains_result_def
    by safe
next
  from assms
  show "finite V"
    unfolding mod_contains_result_def
    by safe
next
  from assms
  show "profile V A p"
    unfolding mod_contains_result_def
    by safe
next
  from assms
  show "a \<in> A"
    unfolding mod_contains_result_def
    by safe
next
  assume "a \<in> elect n V A p"
  thus "a \<in> elect m V A p"
    using IntI assms electoral_mod_defer_elem empty_iff result_disj
    unfolding mod_contains_result_def
    by (metis (mono_tags, lifting))
next
  assume "a \<in> reject n V A p"
  thus "a \<in> reject m V A p"
    using IntI assms electoral_mod_defer_elem empty_iff result_disj
    unfolding mod_contains_result_def
    by (metis (mono_tags, lifting))
next
  assume "a \<in> defer n V A p"
  thus "a \<in> defer m V A p"
    using IntI assms electoral_mod_defer_elem empty_iff result_disj
    unfolding mod_contains_result_def
    by (metis (mono_tags, lifting))
qed

lemma not_rej_imp_elec_or_def:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "social_choice_result.electoral_module m" and
    "finite_profile V A p" and
    "a \<in> A" and
    "a \<notin> reject m V A p"
  shows "a \<in> elect m V A p \<or> a \<in> defer m V A p"
  using assms electoral_mod_defer_elem
  by metis

lemma single_elim_imp_red_def_set:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "eliminates 1 m" and
    "card A > 1" and
    "finite_profile V A p"
  shows "defer m V A p \<subset> A"
  using Diff_eq_empty_iff Diff_subset card_eq_0_iff defer_in_alts eliminates_def
        eq_iff not_one_le_zero psubsetI reject_not_elec_or_def assms
  by (metis (no_types, lifting))

lemma eq_alts_in_profs_imp_eq_results:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile"
  assumes
    eq: "\<forall> a \<in> A. prof_contains_result V m A p q a" and
    mod_m: "social_choice_result.electoral_module m" and
    fin_prof_p: "finite_profile V A p" and
    fin_prof_q: "finite_profile V A q"
  shows "m V A p = m V A q"
proof -
  have elected_in_A: "elect m V A q \<subseteq> A"
    using elect_in_alts mod_m fin_prof_q
    by metis
  have rejected_in_A: "reject m V A q \<subseteq> A"
    using reject_in_alts mod_m fin_prof_q
    by metis
  have deferred_in_A: "defer m V A q \<subseteq> A"
    using defer_in_alts mod_m fin_prof_q
    by metis
  have "\<forall> a \<in> elect m V A p. a \<in> elect m V A q"
    using elect_in_alts eq prof_contains_result_def mod_m fin_prof_p in_mono
    by fastforce
  moreover have "\<forall> a \<in> elect m V A q. a \<in> elect m V A p"
  proof
    fix a :: "'a"
    assume q_elect_a: "a \<in> elect m V A q"
    hence "a \<in> A"
      using elected_in_A
      by blast
    moreover have "a \<notin> defer m V A q"
      using q_elect_a fin_prof_q mod_m result_disj
      by blast
    moreover have "a \<notin> reject m V A q"
      using q_elect_a disjoint_iff_not_equal fin_prof_q mod_m result_disj
      by metis
    ultimately show "a \<in> elect m V A p"
      using electoral_mod_defer_elem eq prof_contains_result_def
      by fastforce
  qed
  moreover have "\<forall> a \<in> reject m V A p. a \<in> reject m V A q"
    using reject_in_alts eq prof_contains_result_def mod_m fin_prof_p
    by fastforce
  moreover have "\<forall> a \<in> reject m V A q. a \<in> reject m V A p"
  proof
    fix a :: 'a
    assume q_rejects_a: "a \<in> reject m V A q"
    hence "a \<in> A"
      using rejected_in_A
      by blast
    moreover have a_not_deferred_q: "a \<notin> defer m V A q"
      using q_rejects_a fin_prof_q mod_m result_disj
      by blast
    moreover have a_not_elected_q: "a \<notin> elect m V A q"
      using q_rejects_a disjoint_iff_not_equal fin_prof_q mod_m result_disj
      by metis
    ultimately show "a \<in> reject m V A p"
      using electoral_mod_defer_elem eq prof_contains_result_def
      by fastforce
  qed
  moreover have "\<forall> a \<in> defer m V A p. a \<in> defer m V A q"
    using defer_in_alts eq prof_contains_result_def mod_m fin_prof_p
    by fastforce
  moreover have "\<forall> a \<in> defer m V A q. a \<in> defer m V A p"
  proof
    fix a :: "'a"
    assume q_defers_a: "a \<in> defer m V A q"
    moreover have "a \<in> A"
      using q_defers_a deferred_in_A
      by blast
    moreover have "a \<notin> elect m V A q"
      using q_defers_a fin_prof_q mod_m result_disj
      by blast
    moreover have "a \<notin> reject m V A q"
      using q_defers_a fin_prof_q disjoint_iff_not_equal mod_m result_disj
      by metis
    ultimately show "a \<in> defer m V A p"
      using electoral_mod_defer_elem eq prof_contains_result_def
      by fastforce
  qed
  ultimately show ?thesis
    using prod.collapse subsetI subset_antisym
    unfolding elect.simps defer.simps reject.simps
              elect_r.simps defer_r.simps reject_r.simps
    by (metis (no_types))
qed

lemma eq_def_and_elect_imp_eq:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile"
  assumes
    mod_m: "social_choice_result.electoral_module m" and
    mod_n: "social_choice_result.electoral_module n" and
    fin_p: "finite_profile V A p" and
    fin_q: "finite_profile V A q" and
    elec_eq: "elect m V A p = elect n V A q" and
    def_eq: "defer m V A p = defer n V A q"
  shows "m V A p = n V A q"
proof -
  have "reject m V A p = A - ((elect m V A p) \<union> (defer m V A p))"
    using mod_m fin_p combine_ele_rej_def result_imp_rej
    unfolding social_choice_result.electoral_module_def
    by metis
  moreover have "reject n V A q = A - ((elect n V A q) \<union> (defer n V A q))"
    using mod_n fin_q combine_ele_rej_def result_imp_rej
    unfolding social_choice_result.electoral_module_def
    by metis
  ultimately show ?thesis
    using elec_eq def_eq prod_eqI
    unfolding elect.simps defer.simps reject.simps
              elect_r.simps defer_r.simps reject_r.simps
    by metis
qed

subsection \<open>Non-Blocking\<close>

text \<open>
  An electoral module is non-blocking iff
  this module never rejects all alternatives.
\<close>

definition non_blocking :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "non_blocking m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p. ((A \<noteq> {} \<and> finite_profile V A p) \<longrightarrow> reject m V A p \<noteq> A))"

subsection \<open>Electing\<close>

text \<open>
  An electoral module is electing iff
  it always elects at least one alternative.
\<close>

definition electing :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "electing m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p. (A \<noteq> {} \<and> finite_profile V A p) \<longrightarrow> elect m V A p \<noteq> {})"

lemma electing_for_only_alt:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    one_alt: "card A = 1" and
    electing: "electing m" and
    f_prof: "finite_profile V A p"
  shows "elect m V A p = A"
proof (safe)
  fix a :: "'a"
  assume elect_a: "a \<in> elect m V A p"
  have "social_choice_result.electoral_module m \<longrightarrow> elect m V A p \<subseteq> A"
    using f_prof elect_in_alts
    by blast
  hence "elect m V A p \<subseteq> A"
    using electing
    unfolding electing_def
    by metis
  thus "a \<in> A"
    using elect_a
    by blast
next
  fix a :: "'a"
  assume "a \<in> A"
  thus "a \<in> elect m V A p"
    using electing f_prof one_alt One_nat_def Suc_leI card_seteq card_gt_0_iff
          elect_in_alts infinite_super
    unfolding electing_def
    by metis
qed

theorem electing_imp_non_blocking:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "electing m"
  shows "non_blocking m"
proof (unfold non_blocking_def, safe)
  from assms
  show "social_choice_result.electoral_module m"
    unfolding electing_def
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    "finite A" and
    "finite V" and
    "profile V A p" and
    "reject m V A p = A" and
    "a \<in> A"
  moreover have
    "social_choice_result.electoral_module m \<and>
      (\<forall> A V q. A \<noteq> {} \<and> finite A \<and> finite V \<and> profile V A q \<longrightarrow> elect m V A q \<noteq> {})"
    using assms
    unfolding electing_def
    by metis
  ultimately show "a \<in> {}"
    using Diff_cancel Un_empty elec_and_def_not_rej
    by metis
qed

subsection \<open>Properties\<close>

text \<open>
  An electoral module is non-electing iff
  it never elects an alternative.
\<close>

definition non_electing :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "non_electing m \<equiv>
    social_choice_result.electoral_module m \<and> 
      (\<forall> A V p. finite_profile V A p \<longrightarrow> elect m V A p = {})"

lemma single_elim_decr_def_card:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    rejecting: "rejects 1 m" and
    not_empty: "A \<noteq> {}" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile V A p"
  shows "card (defer m V A p) = card A - 1"
proof -
  have no_elect:
    "social_choice_result.electoral_module m \<and> 
      (\<forall> A V q. finite A \<and> finite V \<and> profile V A q \<longrightarrow> elect m V A q = {})"
    using non_electing
    unfolding non_electing_def
    by (metis (no_types))
  hence "reject m V A p \<subseteq> A"
    using f_prof reject_in_alts
    by metis
  moreover have "A = A - elect m V A p"
    using no_elect f_prof
    by blast
  ultimately show ?thesis
    using f_prof rejecting not_empty
    by (metis One_nat_def Suc_leI card_Diff_subset card_gt_0_iff 
              defer_not_elec_or_rej infinite_super rejects_def)
qed

lemma single_elim_decr_def_card_2:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    eliminating: "eliminates 1 m" and
    not_empty: "card A > 1" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile V A p"
  shows "card (defer m V A p) = card A - 1"
proof -
  have no_elect:
    "social_choice_result.electoral_module m \<and> 
      (\<forall> A V q. finite A \<and> finite V \<and> profile V A q \<longrightarrow> elect m V A q = {})"
    using non_electing
    unfolding non_electing_def
    by (metis (no_types))
  hence "reject m V A p \<subseteq> A"
    using f_prof reject_in_alts
    by metis
  moreover have "A = A - elect m V A p"
    using no_elect f_prof
    by blast
  ultimately show ?thesis
    using f_prof eliminating not_empty card_Diff_subset defer_not_elec_or_rej 
          eliminates_def finite_subset
    by metis
qed

text \<open>
  An electoral module is defer-deciding iff
  this module chooses exactly 1 alternative to defer and
  rejects any other alternative.
  Note that `rejects n-1 m` can be omitted due to the
  well-formedness property.
\<close>

definition defer_deciding :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defer_deciding m \<equiv>
    social_choice_result.electoral_module m \<and> non_electing m \<and> defers 1 m"

text \<open>
  An electoral module decrements iff
  this module rejects at least one alternative whenever possible (|A| > 1).
\<close>

definition decrementing :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "decrementing m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p. finite_profile V A p \<and> card A > 1 \<longrightarrow> card (reject m V A p) \<ge> 1)"

definition defer_condorcet_consistency :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defer_condorcet_consistency m \<equiv>
    social_choice_result.electoral_module m \<and>
    (\<forall> A V p a. condorcet_winner V A p a \<and> finite A \<and> finite V \<longrightarrow>
      (m V A p = ({}, A - (defer m V A p), {d \<in> A. condorcet_winner V A p d})))"

definition condorcet_compatibility :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "condorcet_compatibility m \<equiv>
    social_choice_result.electoral_module m \<and>
    (\<forall> A V p a. condorcet_winner V A p a \<and> finite A \<and> finite V \<longrightarrow>
      (a \<notin> reject m V A p \<and>
        (\<forall> b. \<not> condorcet_winner V A p b \<longrightarrow> b \<notin> elect m V A p) \<and>
          (a \<in> elect m V A p \<longrightarrow>
            (\<forall> b \<in> A. \<not> condorcet_winner V A p b \<longrightarrow> b \<in> reject m V A p))))"

text \<open>
  An electoral module is defer-monotone iff,
  when a deferred alternative is lifted, this alternative remains deferred.
\<close>

definition defer_monotonicity :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defer_monotonicity m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p q a.
        (finite A \<and> finite V \<and> a \<in> defer m V A p \<and> lifted V A p q a) \<longrightarrow> a \<in> defer m V A q)"

text \<open>
  An electoral module is defer-lift-invariant iff
  lifting a deferred alternative does not affect the outcome.
\<close>

definition defer_lift_invariance :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defer_lift_invariance m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p q a. (a \<in> (defer m V A p) \<and> lifted V A p q a) \<longrightarrow> m V A p = m V A q)"

text \<open>
  Two electoral modules are disjoint-compatible if they only make decisions
  over disjoint sets of alternatives. Electoral modules reject alternatives
  for which they make no decision.
\<close>

definition disjoint_compatibility :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
                                         ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "disjoint_compatibility m n \<equiv>
    social_choice_result.electoral_module m \<and> social_choice_result.electoral_module n \<and>
        (\<forall> V. finite V \<longrightarrow>
          (\<forall> A. finite A \<longrightarrow>
            (\<exists> B \<subseteq> A.
              (\<forall> a \<in> B. indep_of_alt V m A a \<and>
                (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject m V A p)) \<and>
              (\<forall> a \<in> A - B. indep_of_alt V n A a \<and>
                (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject n V A p)))))"

text \<open>
  Lifting an elected alternative a from an invariant-monotone
  electoral module either does not change the elect set, or
  makes a the only elected alternative.
\<close>

definition invariant_monotonicity :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "invariant_monotonicity m \<equiv>
    social_choice_result.electoral_module m \<and>
        (\<forall> A V p q a. (a \<in> elect m V A p \<and> lifted V A p q a) \<longrightarrow>
          (elect m V A q = elect m V A p \<or> elect m V A q = {a}))"

text \<open>
  Lifting a deferred alternative a from a defer-invariant-monotone
  electoral module either does not change the defer set, or
  makes a the only deferred alternative.
\<close>

definition defer_invariant_monotonicity :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defer_invariant_monotonicity m \<equiv>
    social_choice_result.electoral_module m \<and> non_electing m \<and>
        (\<forall> A V p q a. (a \<in> defer m V A p \<and> lifted V A p q a) \<longrightarrow>
          (defer m V A q = defer m V A p \<or> defer m V A q = {a}))"

subsection \<open>Inference Rules\<close>

lemma ccomp_and_dd_imp_def_only_winner:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    ccomp: "condorcet_compatibility m" and
    dd: "defer_deciding m" and
    winner: "condorcet_winner V A p a"
  shows "defer m V A p = {a}"
proof (rule ccontr)
  assume not_w: "defer m V A p \<noteq> {a}"
  have def_one: "defers 1 m"
    using dd
    unfolding defer_deciding_def
    by metis
  hence c_win: "finite_profile V A p \<and>  a \<in> A \<and> (\<forall> b \<in> A - {a}. wins V a p b)"
    using winner
    by auto
  hence "card (defer m V A p) = 1"
    using Suc_leI card_gt_0_iff def_one equals0D
    unfolding One_nat_def defers_def
    by metis
  hence "\<exists> b \<in> A. defer m V A p = {b}"
    using card_1_singletonE dd defer_in_alts insert_subset c_win
    unfolding defer_deciding_def
    by metis
  hence "\<exists> b \<in> A. b \<noteq> a \<and> defer m V A p = {b}"
    using not_w
    by metis
  hence not_in_defer: "a \<notin> defer m V A p"
    by auto
  have "non_electing m"
    using dd
    unfolding defer_deciding_def
    by simp
  hence "a \<notin> elect m V A p"
    using c_win equals0D
    unfolding non_electing_def
    by simp
  hence "a \<in> reject m V A p"
    using not_in_defer ccomp c_win electoral_mod_defer_elem
    unfolding condorcet_compatibility_def
    by metis
  moreover have "a \<notin> reject m V A p"
    using ccomp c_win winner
    unfolding condorcet_compatibility_def
    by simp
  ultimately show False
    by simp
qed

theorem ccomp_and_dd_imp_dcc[simp]:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    ccomp: "condorcet_compatibility m" and
    dd: "defer_deciding m"
  shows "defer_condorcet_consistency m"
proof (unfold defer_condorcet_consistency_def, simp del: defer.simps, safe)
  show "social_choice_result.electoral_module m"
    using dd
    unfolding defer_deciding_def
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    prof_A: "profile V A p" and
    a_in_A: "a \<in> A" and
    finA: "finite A" and
    finV: "finite V" and
    c_winner: 
      "\<forall>x\<in>A - {a}.
        (finite V \<longrightarrow> card {v \<in> V. (a, x) \<in> p v} < card {v \<in> V. (x, a) \<in> p v}) \<and> finite V"
  hence winner: "condorcet_winner V A p a"
    by simp
  hence elect_empty: "elect m V A p = {}"
    using dd
    unfolding defer_deciding_def non_electing_def
    by simp
  have cond_winner_a: "{a} = {c \<in> A. condorcet_winner V A p c}"
    using cond_winner_unique_3 winner
    by metis
  have defer_a: "defer m V A p = {a}"
    using winner dd ccomp ccomp_and_dd_imp_def_only_winner winner
    by simp
  hence "reject m V A p = A - defer m V A p"
    using Diff_empty dd reject_not_elec_or_def winner elect_empty
    unfolding defer_deciding_def
    by fastforce
  hence "m V A p = ({}, A - defer m V A p, {a})"
    using elect_empty defer_a combine_ele_rej_def
    by metis
  hence "m V A p = ({}, A - defer m V A p, {c \<in> A. condorcet_winner V A p c})"
    using cond_winner_a
    by simp
  thus "m V A p =
          ({}, A - defer m V A p,
            {d \<in> A. \<forall>x\<in>A - {d}. card {v \<in> V. (d, x) \<in> p v} < card {v \<in> V. (x, d) \<in> p v}})"
    using finA finV prof_A winner Collect_cong
    by simp
qed

text \<open>
  If m and n are disjoint compatible, so are n and m.
\<close>

theorem disj_compat_comm[simp]:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    n :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "disjoint_compatibility m n"
  shows "disjoint_compatibility n m"
proof (unfold disjoint_compatibility_def, safe)
  show "social_choice_result.electoral_module m"
    using assms
    unfolding disjoint_compatibility_def
    by simp
next
  show "social_choice_result.electoral_module n"
    using assms
    unfolding disjoint_compatibility_def
    by simp
next
  fix 
    A :: "'a set" and
    V :: "'v set"  
  assume 
    "finite A" and 
    "finite V"
  then obtain B where
    "B \<subseteq> A \<and>
      (\<forall> a \<in> B.
        indep_of_alt V m A a \<and> (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject m V A p)) \<and>
      (\<forall> a \<in> A - B.
        indep_of_alt V n A a \<and> (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject n V A p))"
    using assms
    unfolding disjoint_compatibility_def
    by metis
  hence
    "\<exists> B \<subseteq> A.
      (\<forall> a \<in> A - B.
        indep_of_alt V n A a \<and> (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject n V A p)) \<and>
      (\<forall> a \<in> B.
        indep_of_alt V m A a \<and> (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject m V A p))"
    by auto
  hence "\<exists> B \<subseteq> A.
          (\<forall> a \<in> A - B.
            indep_of_alt V n A a \<and> (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject n V A p)) \<and>
          (\<forall> a \<in> A - (A - B).
            indep_of_alt V m A a \<and> (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject m V A p))"
    using double_diff order_refl
    by metis
  thus "\<exists> B \<subseteq> A.
          (\<forall> a \<in> B.
            indep_of_alt V n A a \<and> (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject n V A p)) \<and>
          (\<forall> a \<in> A - B.
            indep_of_alt V m A a \<and> (\<forall> p. finite_profile V A p \<longrightarrow> a \<in> reject m V A p))"
    by fastforce
qed

text \<open>
  Every electoral module which is defer-lift-invariant is
  also defer-monotone.
\<close>

theorem dl_inv_imp_def_mono[simp]:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "defer_lift_invariance m"
  shows "defer_monotonicity m"
  using assms
  unfolding defer_monotonicity_def defer_lift_invariance_def
  by (metis defer.elims)

subsection \<open>Social Choice Properties\<close>

subsubsection \<open>Condorcet Consistency\<close>

definition condorcet_consistency :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "condorcet_consistency m \<equiv>
    social_choice_result.electoral_module m \<and>
    (\<forall> A V p a. condorcet_winner V A p a \<longrightarrow>
      (m V A p = ({e \<in> A. condorcet_winner V A p e}, A - (elect m V A p), {})))"

lemma condorcet_consistency_2:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  shows "condorcet_consistency m =
           (social_choice_result.electoral_module m \<and>
              (\<forall> A V p a. condorcet_winner V A p a \<longrightarrow>
                (m V A p = ({a}, A - (elect m V A p), {}))))"
proof (safe)
  assume "condorcet_consistency m"
  thus "social_choice_result.electoral_module m"
    unfolding condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    "condorcet_consistency m" and
    "condorcet_winner V A p a"
  thus "m V A p = ({a}, A - elect m V A p, {})"
    using cond_winner_unique_3
    unfolding condorcet_consistency_def
    by (metis (mono_tags, lifting))
next
  assume
    "social_choice_result.electoral_module m" and
    "\<forall> A V p a. condorcet_winner V A p a \<longrightarrow> m V A p = ({a}, A - elect m V A p, {})"
  moreover have
    "\<forall> A V p a. condorcet_winner V A p (a::'a) \<longrightarrow>
        {b \<in> A. condorcet_winner V A p b} = {a}"
    using cond_winner_unique_3
    by (metis (full_types))
  ultimately show "condorcet_consistency m"
    unfolding condorcet_consistency_def
    by (metis (mono_tags, lifting))
qed

lemma condorcet_consistency_3:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  shows "condorcet_consistency m =
           (social_choice_result.electoral_module m \<and>
              (\<forall> A V p a.
                condorcet_winner V A p a \<longrightarrow> (m V A p = ({a}, A - {a}, {}))))"
proof (simp only: condorcet_consistency_2, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    e_mod: "social_choice_result.electoral_module m" and
    cc: "\<forall> A V p a'. condorcet_winner V A p a' \<longrightarrow>
      m V A p = ({a'}, A - elect m V A p, {})" and
    c_win: "condorcet_winner V A p a"
  show "m V A p = ({a}, A - {a}, {})"
    using cc c_win fst_conv
    by (metis elect.elims elect_r.elims)
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    e_mod: "social_choice_result.electoral_module m" and
    cc: "\<forall> A V p a'. condorcet_winner V A p a' \<longrightarrow> m V A p = ({a'}, A -  {a'}, {})" and
    c_win: "condorcet_winner V A p a"
  show "m V A p = ({a}, A -  elect m V A p, {})"
    using cc c_win fst_conv
    by (metis elect.elims elect_r.elims)
qed

subsubsection \<open>(Weak) Monotonicity\<close>

text \<open>
  An electoral module is monotone iff
  when an elected alternative is lifted, this alternative remains elected.
\<close>

definition monotonicity :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "monotonicity m \<equiv>
    social_choice_result.electoral_module m \<and>
      (\<forall> A V p q a. (finite A \<and> finite V \<and> a \<in> elect m V A p \<and> lifted V A p q a) 
                        \<longrightarrow> a \<in> elect m V A q)"

end

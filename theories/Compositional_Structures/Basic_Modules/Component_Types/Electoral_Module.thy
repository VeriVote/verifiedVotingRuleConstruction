(*  File:       Electoral_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Module\<close>

theory Electoral_Module
  imports "Social_Choice_Types/Property_Interpretations"
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
  An electoral module maps an election to a result.
  To enable currying, the Election type is not used here because that would require tuples.
\<close>

type_synonym ('a, 'v, 'r) Electoral_Module = "'v set \<Rightarrow> 'a set
                                              \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r"

fun fun\<^sub>\<E> :: "('v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r)
                  \<Rightarrow> (('a, 'v) Election \<Rightarrow> 'r)" where
  "fun\<^sub>\<E> m = (\<lambda> E. m (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E))"

text \<open>
  The next three functions take an electoral module and turn it into a
  function only outputting the elect, reject, or defer set respectively.
\<close>

abbreviation elect :: "('a, 'v, 'r Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
        \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r set" where
  "elect m V A p \<equiv> elect_r (m V A p)"

abbreviation reject :: "('a, 'v, 'r Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
        \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r set" where
  "reject m V A p \<equiv> reject_r (m V A p)"

abbreviation "defer" :: "('a, 'v, 'r Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
        \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r set" where
  "defer m V A p \<equiv> defer_r (m V A p)"

subsection \<open>Auxiliary Definitions\<close>

text \<open>
  Electoral modules partition a given set of alternatives A into a set of
  elected alternatives e, a set of rejected alternatives r, and a set of
  deferred alternatives d, using a profile.
  e, r, and d partition A.
  Electoral modules can be used as voting rules. They can also be composed
  in multiple structures to create more complex electoral modules.
\<close>

fun (in result) electoral_module :: "('a, 'v, ('r Result)) Electoral_Module
                                      \<Rightarrow> bool" where
    "electoral_module m = (\<forall> A V p. profile V A p \<longrightarrow> well_formed A (m V A p))"

fun voters_determine_election :: "('a, 'v, ('r Result)) Electoral_Module \<Rightarrow> bool" where
  "voters_determine_election m =
    (\<forall> A V p p'. (\<forall> v \<in> V. p v = p' v) \<longrightarrow> m V A p = m V A p')"

lemma (in result) electoral_modI:
  fixes m :: "('a, 'v, ('r Result)) Electoral_Module"
  assumes "\<And> A V p. profile V A p \<Longrightarrow> well_formed A (m V A p)"
  shows "electoral_module m"
  unfolding electoral_module.simps
  using assms
  by simp

subsection \<open>Properties\<close>

text \<open>
  We only require voting rules to behave a specific way on admissible elections,
  i.e., elections that are valid profiles (= votes are linear orders on the alternatives).
  Note that we do not assume finiteness of voter or alternative sets by default.
\<close>

subsubsection \<open>Anonymity\<close>

text \<open>
  An electoral module is anonymous iff the result is invariant under renamings of voters,
  i.e., any permutation of the voter set that does not change the preferences leads to an
  identical result.
\<close>

definition (in result) anonymity :: "('a, 'v, ('r Result)) Electoral_Module
                                          \<Rightarrow> bool" where
  "anonymity m \<equiv>
    electoral_module m \<and>
      (\<forall> A V p \<pi>::('v \<Rightarrow> 'v).
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> m V A p = m V' A' q))"

text \<open>
  Anonymity can alternatively be described as invariance
  under the voter permutation group acting on elections
  via the rename function.
\<close>

fun anonymity' :: "('a, 'v) Election set \<Rightarrow> ('a, 'v, 'r) Electoral_Module \<Rightarrow> bool" where
  "anonymity' X m = is_symmetry (fun\<^sub>\<E> m) (Invariance (anonymity\<^sub>\<R> X))"

subsubsection \<open>Homogeneity\<close>

text \<open>
  A voting rule is homogeneous if copying an election does not change the result.
  For ordered voter types and finite elections, we use the notion of copying ballot
  lists to define copying an election.
  The more general definition of homogeneity for unordered voter types already
  implies anonymity.
\<close>

fun (in result) homogeneity :: "('a, 'v) Election set
                                \<Rightarrow> ('a, 'v, ('r Result)) Electoral_Module \<Rightarrow> bool" where
  "homogeneity X m = is_symmetry (fun\<^sub>\<E> m) (Invariance (homogeneity\<^sub>\<R> X))"
\<comment> \<open>This does not require any specific behaviour on infinite voter sets \<open>\<dots>\<close>
    It might make sense to extend the definition to that case somehow.\<close>

fun homogeneity' :: "('a, 'v::linorder) Election set \<Rightarrow> ('a, 'v, 'b Result) Electoral_Module
                          \<Rightarrow> bool" where
  "homogeneity' X m = is_symmetry (fun\<^sub>\<E> m) (Invariance (homogeneity\<^sub>\<R>' X))"

lemma (in result) hom_imp_anon:
  fixes X :: "('a, 'v) Election set"
  assumes
    "homogeneity X m" and
    "\<forall> E \<in> X. finite (voters_\<E> E)"
  shows "anonymity' X m"
proof (unfold anonymity'.simps is_symmetry.simps, intro allI impI)
  fix
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election"
  assume rel: "(E, E') \<in> anonymity\<^sub>\<R> X"
  then obtain \<pi> :: "'v \<Rightarrow> 'v" where
    "\<pi> \<in> carrier anonymity\<^sub>\<G>" and img: "E' = \<phi>_anon X \<pi> E"
    unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps
    by blast
  hence bij: "bij \<pi>"
    unfolding anonymity\<^sub>\<G>_def
    by (simp add: rewrite_carrier)
  from rel have "E \<in> X"
    unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps
    by blast
  moreover from this have fin_E: "finite (voters_\<E> E)"
    using assms
    unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps
    by blast
  moreover have "finite (voters_\<E> E')"
    using bij img \<open>E \<in> X\<close> fin_E rename.simps rename_finite'
    unfolding \<phi>_anon.simps extensional_continuation.simps
    by (metis split_pairs voters_\<E>.simps)
  moreover from this and fin_E have
    "\<forall> r. vote_count r E = 1 * (vote_count r E')" and
    "alternatives_\<E> E = alternatives_\<E> E'"
    using anon_rel_vote_count rel
    by (metis mult_1, metis)
  ultimately show "fun\<^sub>\<E> m E = fun\<^sub>\<E> m E'"
    using assms
    unfolding homogeneity.simps is_symmetry.simps homogeneity\<^sub>\<R>.simps
    by blast
qed

subsubsection \<open>Neutrality\<close>

text \<open>
  Neutrality is equivariance under consistent renaming of
  candidates in the candidate set and election results.
\<close>

fun (in result_properties) neutrality :: "('a, 'v) Election set
        \<Rightarrow> ('a, 'v, 'b Result) Electoral_Module \<Rightarrow> bool" where
  "neutrality X m =
    is_symmetry (fun\<^sub>\<E> m) (action_induced_equivariance (carrier neutrality\<^sub>\<G>) X
          (\<phi>_neutr X) (result_action \<psi>_neutr))"

subsection \<open>Reversal Symmetry of Social Welfare Rules\<close>

text \<open>
  A social welfare rule is reversal symmetric if reversing all voters' preferences
  reverses the result rankings as well.
\<close>

definition reversal_symmetry :: "('a, 'v) Election set
                        \<Rightarrow> ('a, 'v, 'a rel Result) Electoral_Module \<Rightarrow> bool" where
  "reversal_symmetry X m =
    is_symmetry (fun\<^sub>\<E> m) (action_induced_equivariance (carrier reversal\<^sub>\<G>) X
          (\<phi>_rev X) (result_action \<psi>_rev))"

subsection \<open>Social Choice Modules\<close>

text \<open>
  The following results require electoral modules to return social choice results,
  i.e., sets of elected, rejected and deferred alternatives.
  In order to export code, we use the hack provided by Locale-Code.
\<close>

text \<open>
  "defers n" is true for all electoral modules that defer exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition defers :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defers n m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> finite A \<and> profile V A p)
          \<longrightarrow> card (defer m V A p) = n)"

text \<open>
  "rejects n" is true for all electoral modules that reject exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition rejects :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> finite A \<and> profile V A p)
          \<longrightarrow> card (reject m V A p) = n)"

text \<open>
  As opposed to "rejects", "eliminates" allows to stop rejecting if no
  alternatives were to remain.
\<close>

definition eliminates :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (card A > n \<and> profile V A p) \<longrightarrow> card (reject m V A p) = n)"

text \<open>
  "elects n" is true for all electoral modules that
  elect exactly n alternatives, whenever there are n or more alternatives.
\<close>

definition elects :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "elects n m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> profile V A p) \<longrightarrow> card (elect m V A p) = n)"

text \<open>
  An electoral module is independent of an alternative a iff
  a's ranking does not influence the outcome.
\<close>

definition indep_of_alt :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'v set
                                \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "indep_of_alt m V A a \<equiv>
    \<S>\<C>\<F>_result.electoral_module m
      \<and> (\<forall> p q. equiv_prof_except_a V A p q a \<longrightarrow> m V A p = m V A q)"

definition unique_winner_if_profile_non_empty :: "('a, 'v, 'a Result) Electoral_Module
                                                      \<Rightarrow> bool" where
  "unique_winner_if_profile_non_empty m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    (\<forall> A V p. (A \<noteq> {} \<and> V \<noteq> {} \<and> profile V A p) \<longrightarrow>
              (\<exists> a \<in> A. m V A p = ({a}, A - {a}, {})))"

subsection \<open>Equivalence Definitions\<close>

definition prof_contains_result :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'v set
                                      \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile
                                          \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_contains_result m V A p q a \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    profile V A p \<and> profile V A q \<and> a \<in> A \<and>
    (a \<in> elect m V A p \<longrightarrow> a \<in> elect m V A q) \<and>
    (a \<in> reject m V A p \<longrightarrow> a \<in> reject m V A q) \<and>
    (a \<in> defer m V A p \<longrightarrow> a \<in> defer m V A q)"

definition prof_leq_result :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
                                \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_leq_result m V A p q a \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    profile V A p \<and> profile V A q \<and> a \<in> A \<and>
    (a \<in> reject m V A p \<longrightarrow> a \<in> reject m V A q) \<and>
    (a \<in> defer m V A p \<longrightarrow> a \<notin> elect m V A q)"

definition prof_geq_result :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
                                \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_geq_result m V A p q a \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    profile V A p \<and> profile V A q \<and> a \<in> A \<and>
    (a \<in> elect m V A p \<longrightarrow> a \<in> elect m V A q) \<and>
    (a \<in> defer m V A p \<longrightarrow> a \<notin> reject m V A q)"

definition mod_contains_result :: "('a, 'v, 'a Result) Electoral_Module
                                    \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
                                    \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "mod_contains_result m n V A p a \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    \<S>\<C>\<F>_result.electoral_module n \<and>
    profile V A p \<and> a \<in> A \<and>
    (a \<in> elect m V A p \<longrightarrow> a \<in> elect n V A p) \<and>
    (a \<in> reject m V A p \<longrightarrow> a \<in> reject n V A p) \<and>
    (a \<in> defer m V A p \<longrightarrow> a \<in> defer n V A p)"

definition mod_contains_result_sym :: "('a, 'v, 'a Result) Electoral_Module
                                    \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
                                    \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "mod_contains_result_sym m n V A p a \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    \<S>\<C>\<F>_result.electoral_module n \<and>
    profile V A p \<and> a \<in> A \<and>
    (a \<in> elect m V A p \<longleftrightarrow> a \<in> elect n V A p) \<and>
    (a \<in> reject m V A p \<longleftrightarrow> a \<in> reject n V A p) \<and>
    (a \<in> defer m V A p \<longleftrightarrow> a \<in> defer n V A p)"

subsection \<open>Auxiliary Lemmas\<close>

lemma elect_rej_def_combination:
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
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows "well_formed_\<S>\<C>\<F> A (m V A p)"
  using assms
  by simp

lemma result_presv_alts:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows "(elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p) = A"
proof (safe)
  fix a :: "'a"
  have
    partition_1:
    "\<forall> p'. set_equals_partition A p'
      \<longrightarrow> (\<exists> E R D. p' = (E, R, D) \<and> E \<union> R \<union> D = A)" and
    partition_2:
    "set_equals_partition A (m V A p)"
    using assms
    by (simp, simp)
  {
    assume "a \<in> elect m V A p"
    with partition_1 partition_2
    show "a \<in> A"
      using UnI1 fstI
      by (metis (no_types))
  }
  {
    assume "a \<in> reject m V A p"
    with partition_1 partition_2
    show "a \<in> A"
      using UnI1 fstI sndI subsetD sup_ge2
      by metis
  }
  {
    assume "a \<in> defer m V A p"
    with partition_1 partition_2
    show "a \<in> A"
      using sndI subsetD sup_ge2
      by metis
  }
  {
    assume
      "a \<in> A" and
      "a \<notin> defer m V A p" and
      "a \<notin> reject m V A p"
    with partition_1 partition_2
    show "a \<in> elect m V A p"
      using fst_conv snd_conv Un_iff
      by metis
  }
qed

lemma result_disj:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    V :: "'v set"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows
    "(elect m V A p) \<inter> (reject m V A p) = {} \<and>
        (elect m V A p) \<inter> (defer m V A p) = {} \<and>
        (reject m V A p) \<inter> (defer m V A p) = {}"
proof (safe)
  fix a :: "'a"
  have wf: "well_formed_\<S>\<C>\<F> A (m V A p)"
    using assms
    unfolding \<S>\<C>\<F>_result.electoral_module.simps
    by metis
  have disj: "disjoint3 (m V A p)"
    using assms
    by simp
  {
    assume
      "a \<in> elect m V A p" and
      "a \<in> reject m V A p"
    with wf disj
    show "a \<in> {}"
      using prod.exhaust_sel DiffE UnCI result_imp_rej
      by (metis (no_types))
  }
  {
    assume
      elect_a: "a \<in> elect m V A p" and
      defer_a: "a \<in> defer m V A p"
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
      using IntI emptyE prod.collapse disj disjoint3.simps
      by metis
    hence "((elect m V A p) \<inter> (reject m V A p) = {}) \<and>
          ((elect m V A p) \<inter> (defer m V A p) = {}) \<and>
          ((reject m V A p) \<inter> (defer m V A p) = {})"
      using eq_snd_iff fstI
      by metis
    thus "a \<in> {}"
      using elect_a defer_a disjoint_iff_not_equal
      by (metis (no_types))
  }
  {
    assume
      "a \<in> reject m V A p" and
      "a \<in> defer m V A p"
    with wf disj
    show "a \<in> {}"
      using prod.exhaust_sel DiffE UnCI result_imp_rej
      by (metis (no_types))
  }
qed

lemma elect_in_alts:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
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
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows "reject m V A p \<subseteq> A"
  using le_supI1 assms result_presv_alts sup_ge2
  by metis

lemma defer_in_alts:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows "defer m V A p \<subseteq> A"
  using assms result_presv_alts
  by fastforce

lemma def_presv_prof:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows "let new_A = defer m V A p in profile V new_A (limit_profile new_A p)"
  using defer_in_alts limit_profile_sound assms
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
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p" and
    "finite A"
  shows
    upper_card_bound_for_elect: "card (elect m V A p) \<le> card A" and
    upper_card_bound_for_reject: "card (reject m V A p) \<le> card A" and
    upper_card_bound_for_defer: "card (defer m V A p) \<le> card A"
  using assms card_mono
  by (metis elect_in_alts,
      metis reject_in_alts,
      metis defer_in_alts)

lemma reject_not_elec_or_def:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows "reject m V A p = A - (elect m V A p) - (defer m V A p)"
proof -
  from assms have "(elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p) = A"
    using result_presv_alts
    by blast
  with assms show ?thesis
    using result_disj
    by blast
qed

lemma elec_and_def_not_rej:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows "elect m V A p \<union> defer m V A p = A - (reject m V A p)"
proof -
  from assms have "(elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p) = A"
    using result_presv_alts
    by blast
  with assms show ?thesis
    using result_disj
    by blast
qed

lemma defer_not_elec_or_rej:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p"
  shows "defer m V A p = A - (elect m V A p) - (reject m V A p)"
proof -
  from assms have "(elect m V A p) \<union> (reject m V A p) \<union> (defer m V A p) = A"
    using result_presv_alts
    by simp
  with assms show ?thesis
    using result_disj
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
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p" and
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
  assumes "mod_contains_result m n V A p a"
  shows "mod_contains_result n m V A p a"
proof (unfold mod_contains_result_def, safe)
  show
    "\<S>\<C>\<F>_result.electoral_module n" and
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p" and
    "a \<in> A"
    using assms
    unfolding mod_contains_result_def
    by safe
next
  show
    "a \<in> elect n V A p \<Longrightarrow> a \<in> elect m V A p" and
    "a \<in> reject n V A p \<Longrightarrow> a \<in> reject m V A p" and
    "a \<in> defer n V A p \<Longrightarrow> a \<in> defer m V A p"
    using assms IntI electoral_mod_defer_elem empty_iff result_disj
    unfolding mod_contains_result_def
    by (metis (mono_tags, lifting),
        metis (mono_tags, lifting),
        metis (mono_tags, lifting))
qed

lemma not_rej_imp_elec_or_defer:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "\<S>\<C>\<F>_result.electoral_module m" and
    "profile V A p" and
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
    "profile V A p"
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
    eq: "\<forall> a \<in> A. prof_contains_result m V A p q a" and
    mod_m: "\<S>\<C>\<F>_result.electoral_module m" and
    prof_p: "profile V A p" and
    prof_q: "profile V A q"
  shows "m V A p = m V A q"
proof -
  have
    elected_in_A: "elect m V A q \<subseteq> A" and
    rejected_in_A: "reject m V A q \<subseteq> A" and
    deferred_in_A: "defer m V A q \<subseteq> A"
    using mod_m prof_q
    by (metis elect_in_alts, metis reject_in_alts, metis defer_in_alts)
  have
    "\<forall> a \<in> elect m V A p. a \<in> elect m V A q" and
    "\<forall> a \<in> reject m V A p. a \<in> reject m V A q" and
    "\<forall> a \<in> defer m V A p. a \<in> defer m V A q"
    using eq mod_m prof_p in_mono
    unfolding prof_contains_result_def
    by (metis (no_types, lifting) elect_in_alts,
        metis (no_types, lifting) reject_in_alts,
        metis (no_types, lifting) defer_in_alts)
  moreover have
    "\<forall> a \<in> elect m V A q. a \<in> elect m V A p" and
    "\<forall> a \<in> reject m V A q. a \<in> reject m V A p" and
    "\<forall> a \<in> defer m V A q. a \<in> defer m V A p"
  proof (safe)
    fix a :: "'a"
    assume q_elect_a: "a \<in> elect m V A q"
    hence "a \<in> A"
      using elected_in_A
      by blast
    moreover have
      "a \<notin> defer m V A q" and
      "a \<notin> reject m V A q"
      using q_elect_a prof_q mod_m result_disj disjoint_iff_not_equal
      by (metis, metis)
    ultimately show "a \<in> elect m V A p"
      using eq electoral_mod_defer_elem
      unfolding prof_contains_result_def
      by metis
  next
    fix a :: "'a"
    assume q_rejects_a: "a \<in> reject m V A q"
    hence "a \<in> A"
      using rejected_in_A
      by blast
    moreover have
      "a \<notin> defer m V A q" and
      "a \<notin> elect m V A q"
      using q_rejects_a prof_q mod_m result_disj disjoint_iff_not_equal
      by (metis, metis)
    ultimately show "a \<in> reject m V A p"
      using eq electoral_mod_defer_elem
      unfolding prof_contains_result_def
      by metis
  next
    fix a :: "'a"
    assume q_defers_a: "a \<in> defer m V A q"
    moreover have "a \<in> A"
      using q_defers_a deferred_in_A
      by blast
    moreover have
      "a \<notin> elect m V A q" and
      "a \<notin> reject m V A q"
      using q_defers_a prof_q mod_m result_disj disjoint_iff_not_equal
      by (metis, metis)
    ultimately show "a \<in> defer m V A p"
      using eq electoral_mod_defer_elem
      unfolding prof_contains_result_def
      by metis
  qed
  ultimately show ?thesis
    using prod.collapse subsetI subset_antisym
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
    mod_m: "\<S>\<C>\<F>_result.electoral_module m" and
    mod_n: "\<S>\<C>\<F>_result.electoral_module n" and
    fin_p: "profile V A p" and
    fin_q: "profile V A q" and
    elec_eq: "elect m V A p = elect n V A q" and
    def_eq: "defer m V A p = defer n V A q"
  shows "m V A p = n V A q"
proof -
  have
    "reject m V A p = A - ((elect m V A p) \<union> (defer m V A p))" and
    "reject n V A q = A - ((elect n V A q) \<union> (defer n V A q))"
    using elect_rej_def_combination result_imp_rej mod_m mod_n fin_p fin_q
    unfolding \<S>\<C>\<F>_result.electoral_module.simps
    by (metis, metis)
  thus ?thesis
    using prod_eqI elec_eq def_eq
    by metis
qed

subsection \<open>Non-Blocking\<close>

text \<open>
  An electoral module is non-blocking iff
  this module never rejects all alternatives.
\<close>

definition non_blocking :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "non_blocking m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. ((A \<noteq> {} \<and> finite A \<and> profile V A p) \<longrightarrow> reject m V A p \<noteq> A))"

subsection \<open>Electing\<close>

text \<open>
  An electoral module is electing iff
  it always elects at least one alternative.
\<close>

definition electing :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "electing m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (A \<noteq> {} \<and> finite A \<and> profile V A p) \<longrightarrow> elect m V A p \<noteq> {})"

lemma electing_for_only_alt:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    one_alt: "card A = 1" and
    electing: "electing m" and
    prof: "profile V A p"
  shows "elect m V A p = A"
proof (intro equalityI)
  show elect_in_A: "elect m V A p \<subseteq> A"
    using electing prof elect_in_alts
    unfolding electing_def
    by metis
  show "A \<subseteq> elect m V A p"
  proof (intro subsetI)
    fix a :: "'a"
    assume "a \<in> A"
    thus "a \<in> elect m V A p"
      using one_alt electing prof elect_in_A IntD2 Int_absorb2 card_1_singletonE
            card_gt_0_iff equals0I zero_less_one singletonD
      unfolding electing_def
      by (metis (no_types))
  qed
qed

theorem electing_imp_non_blocking:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "electing m"
  shows "non_blocking m"
proof (unfold non_blocking_def, safe)
  from assms
  show "\<S>\<C>\<F>_result.electoral_module m"
    unfolding electing_def
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    "profile V A p" and
    "finite A" and
    "reject m V A p = A" and
    "a \<in> A"
  moreover have
    "\<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V q. A \<noteq> {} \<and> finite A \<and> profile V A q \<longrightarrow> elect m V A q \<noteq> {})"
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
    \<S>\<C>\<F>_result.electoral_module m
      \<and> (\<forall> A V p. profile V A p \<longrightarrow> elect m V A p = {})"

lemma single_rej_decr_def_card:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    rejecting: "rejects 1 m" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile V A p"
  shows "card (defer m V A p) = card A - 1"
proof -
  have no_elect:
    "\<S>\<C>\<F>_result.electoral_module m
        \<and> (\<forall> V A q. profile V A q \<longrightarrow> elect m V A q = {})"
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
    using f_prof no_elect rejecting card_Diff_subset card_gt_0_iff
          defer_not_elec_or_rej less_one order_less_imp_le Suc_leI
          bot.extremum_unique card.empty diff_is_0_eq' One_nat_def
    unfolding rejects_def
    by metis
qed

lemma single_elim_decr_def_card_2:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    eliminating: "eliminates 1 m" and
    non_electing: "non_electing m" and
    not_empty: "card A > 1" and
    prof_p: "profile V A p"
  shows "card (defer m V A p) = card A - 1"
proof -
  have no_elect:
    "\<S>\<C>\<F>_result.electoral_module m
        \<and> (\<forall> A V q. profile V A q \<longrightarrow> elect m V A q = {})"
    using non_electing
    unfolding non_electing_def
    by (metis (no_types))
  hence "reject m V A p \<subseteq> A"
    using prof_p reject_in_alts
    by metis
  moreover have "A = A - elect m V A p"
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

definition defer_deciding :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defer_deciding m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and> non_electing m \<and> defers 1 m"

text \<open>
  An electoral module decrements iff
  this module rejects at least one alternative whenever possible (|A| > 1).
\<close>

definition decrementing :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "decrementing m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. profile V A p \<and> card A > 1 \<longrightarrow> card (reject m V A p) \<ge> 1)"

definition defer_condorcet_consistency :: "('a, 'v, 'a Result) Electoral_Module
                                              \<Rightarrow> bool" where
  "defer_condorcet_consistency m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    (\<forall> A V p a. condorcet_winner V A p a \<longrightarrow>
      (m V A p = ({}, A - (defer m V A p), {d \<in> A. condorcet_winner V A p d})))"

definition condorcet_compatibility :: "('a, 'v, 'a Result) Electoral_Module
                                          \<Rightarrow> bool" where
  "condorcet_compatibility m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    (\<forall> A V p a. condorcet_winner V A p a \<longrightarrow>
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
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p q a.
        (a \<in> defer m V A p \<and> lifted V A p q a) \<longrightarrow> a \<in> defer m V A q)"

text \<open>
  An electoral module is defer-lift-invariant iff
  lifting a deferred alternative does not affect the outcome.
\<close>

definition defer_lift_invariance :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defer_lift_invariance m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p q a. (a \<in> (defer m V A p) \<and> lifted V A p q a)
                      \<longrightarrow> m V A p = m V A q)"

fun dli_rel :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> ('a, 'v) Election rel" where
  "dli_rel m = {((A, V, p), (A, V, q)) |A V p q. (\<exists> a \<in> defer m V A p. lifted V A p q a)}"

lemma rewrite_dli_as_invariance:
  fixes
    m :: "('a, 'v, 'a Result) Electoral_Module"
  shows
    "defer_lift_invariance m =
      (\<S>\<C>\<F>_result.electoral_module m
            \<and> (is_symmetry (fun\<^sub>\<E> m) (Invariance (dli_rel m))))"
proof (unfold is_symmetry.simps, safe)
  assume "defer_lift_invariance m"
  thus "\<S>\<C>\<F>_result.electoral_module m"
    unfolding defer_lift_invariance_def
    by blast
next
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile"
  assume
    invar: "defer_lift_invariance m" and
    rel: "((A, V, p), (A', V', q)) \<in> dli_rel m"
  then obtain a :: 'a where
    "a \<in> defer m V A p \<and> lifted V A p q a"
    unfolding dli_rel.simps
    by blast
  moreover with rel have "A = A' \<and> V = V'"
    by simp
  ultimately show "fun\<^sub>\<E> m (A, V, p) = fun\<^sub>\<E> m (A', V', q)"
    using invar fst_eqD snd_eqD profile_\<E>.simps
    unfolding defer_lift_invariance_def fun\<^sub>\<E>.simps alternatives_\<E>.simps voters_\<E>.simps
    by metis
next
  assume
    "\<S>\<C>\<F>_result.electoral_module m" and
    "\<forall>E E'. (E, E') \<in> dli_rel m \<longrightarrow> fun\<^sub>\<E> m E = fun\<^sub>\<E> m E'"
  hence "\<S>\<C>\<F>_result.electoral_module m \<and> (\<forall> A V p q.
    ((A, V, p), (A, V, q)) \<in> dli_rel m \<longrightarrow> m V A p = m V A q)"
    unfolding fun\<^sub>\<E>.simps alternatives_\<E>.simps profile_\<E>.simps voters_\<E>.simps
    using fst_conv snd_conv
    by metis
  moreover have
    "\<forall> A V p q a. (a \<in> (defer m V A p) \<and> lifted V A p q a) \<longrightarrow>
      ((A, V, p), (A, V, q)) \<in> dli_rel m"
    unfolding dli_rel.simps
    by blast
  ultimately show "defer_lift_invariance m"
    unfolding defer_lift_invariance_def
    by blast
qed

text \<open>
  Two electoral modules are disjoint-compatible if they only make decisions
  over disjoint sets of alternatives. Electoral modules reject alternatives
  for which they make no decision.
\<close>

definition disjoint_compatibility :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow>
                                         ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "disjoint_compatibility m n \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and> \<S>\<C>\<F>_result.electoral_module n \<and>
        (\<forall> V.
          (\<forall> A.
            (\<exists> B \<subseteq> A.
              (\<forall> a \<in> B. indep_of_alt m V A a \<and>
                (\<forall> p. profile V A p \<longrightarrow> a \<in> reject m V A p)) \<and>
              (\<forall> a \<in> A - B. indep_of_alt n V A a \<and>
                (\<forall> p. profile V A p \<longrightarrow> a \<in> reject n V A p)))))"

text \<open>
  Lifting an elected alternative a from an invariant-monotone
  electoral module either does not change the elect set, or
  makes a the only elected alternative.
\<close>

definition invariant_monotonicity :: "('a, 'v, 'a Result) Electoral_Module
                                          \<Rightarrow> bool" where
  "invariant_monotonicity m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
        (\<forall> A V p q a. (a \<in> elect m V A p \<and> lifted V A p q a) \<longrightarrow>
          (elect m V A q = elect m V A p \<or> elect m V A q = {a}))"

text \<open>
  Lifting a deferred alternative a from a defer-invariant-monotone
  electoral module either does not change the defer set, or
  makes a the only deferred alternative.
\<close>

definition defer_invariant_monotonicity :: "('a, 'v, 'a Result) Electoral_Module
                                                \<Rightarrow> bool" where
  "defer_invariant_monotonicity m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and> non_electing m \<and>
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
  assume "defer m V A p \<noteq> {a}"
  moreover have def_one: "defers 1 m"
    using dd
    unfolding defer_deciding_def
    by metis
  hence c_win: "finite_profile V A p \<and>  a \<in> A \<and> (\<forall> b \<in> A - {a}. wins V a p b)"
    using winner
    by auto
  ultimately have "\<exists> b \<in> A. b \<noteq> a \<and> defer m V A p = {b}"
    using Suc_leI card_gt_0_iff def_one equals0D card_1_singletonE
          defer_in_alts insert_subset
    unfolding defer_deciding_def One_nat_def defers_def
    by metis
  hence "a \<notin> defer m V A p"
    by force
  hence "a \<in> reject m V A p"
    using ccomp c_win electoral_mod_defer_elem dd equals0D
    unfolding defer_deciding_def non_electing_def condorcet_compatibility_def
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
proof (unfold defer_condorcet_consistency_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module m"
    using dd
    unfolding defer_deciding_def
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume c_winner: "condorcet_winner V A p a"
  hence "elect m V A p = {}"
    using dd
    unfolding defer_deciding_def non_electing_def
    by simp
  moreover have "defer m V A p = {a}"
    using c_winner dd ccomp ccomp_and_dd_imp_def_only_winner
    by simp
  ultimately have "m V A p = ({}, A - defer m V A p, {a})"
    using c_winner reject_not_elec_or_def elect_rej_def_combination Diff_empty dd
    unfolding defer_deciding_def condorcet_winner.simps
    by metis
  moreover have "{a} = {c \<in> A. condorcet_winner V A p c}"
    using c_winner cond_winner_unique
    by metis
  ultimately show
    "m V A p = ({}, A - defer m V A p, {c \<in> A. condorcet_winner V A p c})"
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
  show
    "\<S>\<C>\<F>_result.electoral_module m" and
    "\<S>\<C>\<F>_result.electoral_module n"
    using assms
    unfolding disjoint_compatibility_def
    by safe
next
  fix
    A :: "'a set" and
    V :: "'v set"
  obtain B :: "'a set" where
    "B \<subseteq> A \<and>
      (\<forall> a \<in> B.
        indep_of_alt m V A a \<and> (\<forall> p. profile V A p \<longrightarrow> a \<in> reject m V A p)) \<and>
      (\<forall> a \<in> A - B.
        indep_of_alt n V A a \<and> (\<forall> p. profile V A p \<longrightarrow> a \<in> reject n V A p))"
    using assms
    unfolding disjoint_compatibility_def
    by metis
  hence
    "\<exists> B \<subseteq> A.
      (\<forall> a \<in> A - B.
        indep_of_alt n V A a \<and> (\<forall> p. profile V A p \<longrightarrow> a \<in> reject n V A p)) \<and>
      (\<forall> a \<in> B.
        indep_of_alt m V A a \<and> (\<forall> p. profile V A p \<longrightarrow> a \<in> reject m V A p))"
    by blast
  thus "\<exists> B \<subseteq> A.
          (\<forall> a \<in> B.
            indep_of_alt n V A a \<and> (\<forall> p. profile V A p \<longrightarrow> a \<in> reject n V A p)) \<and>
          (\<forall> a \<in> A - B.
            indep_of_alt m V A a \<and> (\<forall> p. profile V A p \<longrightarrow> a \<in> reject m V A p))"
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
  by metis

subsection \<open>Social Choice Properties\<close>

subsubsection \<open>Condorcet Consistency\<close>

definition condorcet_consistency :: "('a, 'v, 'a Result) Electoral_Module
                                        \<Rightarrow> bool" where
  "condorcet_consistency m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
    (\<forall> A V p a. condorcet_winner V A p a \<longrightarrow>
      (m V A p = ({e \<in> A. condorcet_winner V A p e}, A - (elect m V A p), {})))"

lemma condorcet_consistency':
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  shows "condorcet_consistency m =
           (\<S>\<C>\<F>_result.electoral_module m \<and>
              (\<forall> A V p a. condorcet_winner V A p a \<longrightarrow>
                (m V A p = ({a}, A - (elect m V A p), {}))))"
proof (safe)
  assume "condorcet_consistency m"
  thus "\<S>\<C>\<F>_result.electoral_module m"
    unfolding condorcet_consistency_def
    by (metis (mono_tags, lifting))
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
    using cond_winner_unique
    unfolding condorcet_consistency_def
    by (metis (mono_tags, lifting))
next
  assume
    "\<S>\<C>\<F>_result.electoral_module m" and
    "\<forall> A V p a. condorcet_winner V A p a
          \<longrightarrow> m V A p = ({a}, A - elect m V A p, {})"
  thus "condorcet_consistency m"
    using cond_winner_unique
    unfolding condorcet_consistency_def
    by (metis (mono_tags, lifting))
qed

lemma condorcet_consistency'':
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  shows "condorcet_consistency m =
           (\<S>\<C>\<F>_result.electoral_module m \<and>
              (\<forall> A V p a.
                condorcet_winner V A p a \<longrightarrow> m V A p = ({a}, A - {a}, {})))"
proof (unfold condorcet_consistency', safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume "condorcet_winner V A p a"
  {
    moreover assume
      "\<forall> A V p a'. condorcet_winner V A p a'
          \<longrightarrow> m V A p = ({a'}, A - elect m V A p, {})"
    ultimately show "m V A p = ({a}, A - {a}, {})"
      using fst_conv
      by metis
  }
  {
    moreover assume
      "\<forall> A V p a'. condorcet_winner V A p a'
          \<longrightarrow> m V A p = ({a'}, A -  {a'}, {})"
    ultimately show "m V A p = ({a}, A -  elect m V A p, {})"
      using fst_conv
      by metis
  }
qed

subsubsection \<open>(Weak) Monotonicity\<close>

text \<open>
  An electoral module is monotone iff
  when an elected alternative is lifted, this alternative remains elected.
\<close>

definition monotonicity :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "monotonicity m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p q a. a \<in> elect m V A p \<and> lifted V A p q a \<longrightarrow> a \<in> elect m V A q)"

end
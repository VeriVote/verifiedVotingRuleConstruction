(*  File:       Election_Quotients.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Quotients of Election Set Equivalences\<close>

theory Election_Quotients
  imports Relation_Quotients
          "../Social_Choice_Types/Voting_Symmetry"
          "../Social_Choice_Types/Ordered_Relation"
          "HOL-Analysis.Convex"
          "HOL-Analysis.Cartesian_Space"
begin

subsection \<open>Auxiliary Lemmas\<close>

lemma obtain_partition:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    f :: "'v \<Rightarrow> nat"
  assumes
    "finite A" and
    "finite V" and
    "(\<Sum> v :: 'v \<in> V. f v) = card A"
  shows "\<exists> \<B> :: 'v \<Rightarrow> 'a set.
    A = \<Union> {\<B> v | v :: 'v. v \<in> V} \<and> (\<forall> v :: 'v \<in> V. card (\<B> v) = f v)
    \<and> (\<forall> v v' :: 'v. v \<noteq> v' \<longrightarrow> v \<in> V \<and> v' \<in> V \<longrightarrow> \<B> v \<inter> \<B> v' = {})"
  using assms
proof (induction "card V" arbitrary: A V)
  case 0
  fix
    A :: "'a set" and
    V :: "'v set"
  let ?\<B> = "\<lambda> v :: 'v. {}"
  assume
    "finite V" and
    "0 = card V"
  hence V_empty: "V = {}"
    using 0
    by simp
  hence "(\<Sum> v :: 'v \<in> V. f v) = 0"
    by simp
  moreover assume
    "finite A" and
    "(\<Sum> v :: 'v \<in> V. f v) = card A"
  ultimately have "A = {}"
    by simp
  hence "A = \<Union> {?\<B> v | v :: 'v. v \<in> V}"
    by blast
  moreover have "\<forall> v v' :: 'v. v \<noteq> v' \<longrightarrow> v \<in> V \<and> v' \<in> V \<longrightarrow> ?\<B> v \<inter> ?\<B> v' = {}"
    by blast
  ultimately show
    "\<exists> \<B> :: 'v \<Rightarrow> 'a set.
      A = \<Union> {\<B> v | v :: 'v. v \<in> V} \<and> (\<forall> v :: 'v \<in> V. card (\<B> v) = f v)
      \<and> (\<forall> v v' :: 'v. v \<noteq> v' \<longrightarrow> v \<in> V \<and> v' \<in> V \<longrightarrow> \<B> v \<inter> \<B> v' = {})"
    using V_empty
    by simp
next
  case (Suc n)
  fix
    n :: "nat" and
    A :: "'a set" and
    V :: "'v set"
  assume
    card_V: "Suc n = card V" and
    fin_V: "finite V" and
    fin_A: "finite A" and
    card_A: "(\<Sum> v :: 'v \<in> V. f v) = card A" and
    hyp:
      "\<And> V' (A' :: 'a set).
         n = card V' \<Longrightarrow>
         finite A' \<Longrightarrow>
         finite V' \<Longrightarrow>
         (\<Sum> v :: 'v \<in> V'. f v) = card A' \<Longrightarrow>
         \<exists> \<B> :: 'v \<Rightarrow> 'a set.
          A' = \<Union> {\<B> v | v :: 'v. v \<in> V'} \<and>
                  (\<forall> v :: 'v \<in> V'. card (\<B> v) = f v) \<and>
                  (\<forall> v v' :: 'v. v \<noteq> v' \<longrightarrow> v \<in> V' \<and> v' \<in> V' \<longrightarrow> \<B> v \<inter> \<B> v' = {})"
  then obtain
    V' :: "'v set" and
    v :: "'v" where
    ins_V: "V = insert v V'" and
    card_V': "card V' = n" and
    fin_V': "finite V'" and
    v_not_in_V': "v \<notin> V'"
    using card_Suc_eq_finite
    by (metis (no_types, lifting))
  hence "f v \<le> card A"
    using card_A le_add1 n_not_Suc_n sum.insert
    by metis
  then obtain A' :: "'a set" where
    A'_in_A: "A' \<subseteq> A" and
    card_A': "card A' = f v"
    using fin_A ex_card
    by metis
  hence "finite (A - A') \<and> card (A - A') = (\<Sum> v' :: 'v \<in> V'. f v')"
    using card_V card_A fin_A ins_V card_V' fin_V' Suc_n_not_n
          add_diff_cancel_left' card_Diff_subset card_insert_if
          finite_Diff finite_subset sum.insert
    by metis
  then obtain \<B> :: "'v \<Rightarrow> 'a set" where
    part: "A - A' = \<Union> {\<B> v' | v' :: 'v. v' \<in> V'}" and
    disj: "\<forall> v' v'' :: 'v. v' \<noteq> v'' \<longrightarrow> v' \<in> V' \<and> v'' \<in> V' \<longrightarrow> \<B> v' \<inter> \<B> v'' = {}" and
    card: "\<forall> v' :: 'v \<in> V'. card (\<B> v') = f v'"
    using hyp[of V' "A - A'"] fin_V' card_V'
    by auto
  then obtain \<B>' :: "'v \<Rightarrow> 'a set" where
    map': "\<B>' = (\<lambda> z :: 'v. if z = v then A' else \<B> z)"
    by simp
  hence eq_\<B>: "\<forall> v' :: 'v \<in> V'. \<B>' v' = \<B> v'"
    using v_not_in_V'
    by simp
  have "V = {v} \<union> V'"
    using ins_V
    by simp
  hence "\<Union> {\<B>' v' | v' :: 'v. v' \<in> V} = \<B>' v \<union> \<Union> {\<B>' v' | v' :: 'v. v' \<in> V'}"
    by blast
  also have "\<dots> = A' \<union> \<Union> {\<B> v' | v' :: 'v. v' \<in> V'}"
    using map' eq_\<B>
    by fastforce
  finally have part': "A = \<Union> {\<B>' v' | v' :: 'v. v' \<in> V}"
    using part Diff_partition A'_in_A
    by metis
  have "\<forall> v' :: 'v \<in> V'. \<B>' v' \<subseteq> A - A'"
    using part eq_\<B> Setcompr_eq_image UN_upper
    by metis
  hence "\<forall> v' :: 'v \<in> V'. \<B>' v' \<inter> A' = {}"
    by blast
  hence "\<forall> v' :: 'v \<in> V'. \<B>' v' \<inter> \<B>' v = {}"
    using map'
    by simp
  hence "\<forall> v' v'' :: 'v. v' \<noteq> v'' \<longrightarrow> v' \<in> V \<and> v'' \<in> V \<longrightarrow> \<B>' v' \<inter> \<B>' v'' = {}"
    using map' disj ins_V inf.commute insertE
    by (metis (no_types, lifting))
  moreover have "\<forall> v' :: 'v \<in> V. card (\<B>' v') = f v'"
    using map' card card_A' ins_V
    by simp
  ultimately show
    "\<exists> \<B> :: 'v \<Rightarrow> 'a set.
      A = \<Union> {\<B> v' | v' :: 'v. v' \<in> V} \<and> (\<forall> v' :: 'v \<in> V. card (\<B> v') = f v')
      \<and> (\<forall> v' v'' :: 'v. v' \<noteq> v'' \<longrightarrow> v' \<in> V \<and> v'' \<in> V \<longrightarrow> \<B> v' \<inter> \<B> v'' = {})"
    using part'
    by blast
qed

subsection \<open>Anonymity Quotient: Grid\<close>

\<comment> \<open>The election equivalence classes of the anonymity equivalence relation.\<close>
fun anonymity\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anonymity\<^sub>\<Q> A = quotient (elections_\<A> A) (anonymity\<^sub>\<R> (elections_\<A> A))"

\<comment> \<open>Here, we count the occurrences of a ballot per election in a set of elections for which
    the occurrences of the ballot per election coincide for all elections in the set.\<close>
fun vote_count\<^sub>\<Q> :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election set \<Rightarrow> nat" where
  "vote_count\<^sub>\<Q> r = \<pi>\<^sub>\<Q> (vote_count r)"

fun anonymity_class :: "('a :: finite, 'v) Election set \<Rightarrow>
        (nat, 'a Ordered_Preference) vec" where
  "anonymity_class \<C> = (\<chi> p. vote_count\<^sub>\<Q> (ord2pref p) \<C>)"

lemma anon_rel_equiv: "equiv (elections_\<A> UNIV) (anonymity\<^sub>\<R> (elections_\<A> UNIV))"
proof -
  have subset: "elections_\<A> UNIV \<subseteq> well_formed_elections"
    by simp
  have equiv: "equiv well_formed_elections (anonymity\<^sub>\<R> well_formed_elections)"
    using anonymous_group_action.group_action_axioms rel_ind_by_group_act_equiv[of
            "bijection\<^sub>\<V>\<^sub>\<G>" "well_formed_elections" "\<phi>_anon well_formed_elections"]
          rel_ind_by_coinciding_action_on_subset_eq_restr
    by fastforce 
  have closed: 
    "closed_restricted_rel
      (anonymity\<^sub>\<R> well_formed_elections) well_formed_elections (elections_\<A> UNIV)"
  proof (unfold closed_restricted_rel.simps restricted_rel.simps, safe)
    fix
      A A' :: "'c set" and
      V V' :: "'d set" and
      p p' :: "('c, 'd) Profile"
    assume elt: "(A, V, p) \<in> elections_\<A> UNIV"
    hence wf_elections: "(A, V, p) \<in> well_formed_elections"
      unfolding elections_\<A>.simps
      by blast
    assume "((A, V, p), A', V', p') \<in> anonymity\<^sub>\<R> well_formed_elections"
    then obtain \<pi> :: "'d \<Rightarrow> 'd" where
      bij_\<pi>: "bij \<pi>" and
      img: "(A', V', p') = rename \<pi> (A, V, p)"
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps 
                bijection\<^sub>\<V>\<^sub>\<G>_def \<phi>_anon.simps rewrite_carrier
                extensional_continuation.simps 
      by auto
    hence "(A', V', p') \<in> well_formed_elections"
      using wf_elections rename_sound 
      unfolding well_formed_elections_def
      by fastforce
    moreover have "A' = A \<and> finite V"
      using bij_\<pi> elt img rename.simps wf_elections well_formed_elections_def
      by auto
    moreover have "\<forall> v. v \<notin> V' \<longrightarrow> (the_inv \<pi> v) \<notin> V"
      using elt Pair_inject UNIV_I bij_\<pi> rename.simps
            f_the_inv_into_f_bij_betw image_eqI img 
      unfolding elections_\<A>.simps
      by (metis (mono_tags, opaque_lifting))
    moreover have "\<forall> v. v \<notin> V' \<longrightarrow> p' v = p (the_inv \<pi> v)"
      using img
      by simp
    ultimately show "(A', V', p') \<in> elections_\<A> UNIV"
      using elt img
      unfolding elections_\<A>.simps rename.simps
      by auto
  qed
  have
    "anonymity\<^sub>\<R> (elections_\<A> UNIV) =
      restricted_rel (anonymity\<^sub>\<R> well_formed_elections) (elections_\<A> UNIV)
          well_formed_elections"
  proof (unfold restricted_rel.simps, safe)
    fix
      A A' :: "'c set" and
      V V' :: "'d set" and
      p p' :: "('c, 'd) Profile"
    assume rel: "((A, V, p), A', V', p') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV)"
    hence "(A, V, p) \<in> well_formed_elections"
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps elections_\<A>.simps
      by blast
    moreover obtain \<pi> :: "'d \<Rightarrow> 'd" where
      "bij \<pi>" and
      "(A', V', p') = rename \<pi> (A, V, p)"
      using rel
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps 
                bijection\<^sub>\<V>\<^sub>\<G>_def \<phi>_anon.simps rewrite_carrier
                extensional_continuation.simps 
      by auto
    ultimately show "((A, V, p), A', V', p') \<in> anonymity\<^sub>\<R> well_formed_elections"
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps
                bijection\<^sub>\<V>\<^sub>\<G>_def \<phi>_anon.simps rewrite_carrier
      by auto
  next
    fix
      A A' :: "'c set" and
      V V' :: "'d set" and
      p p' :: "('c, 'd) Profile"
    assume "((A, V, p), A', V', p') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV)"
    thus "(A, V, p) \<in> elections_\<A> UNIV"
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps
      by blast
  next
    fix
      A A' :: "'c set" and
      V V' :: "'d set" and
      p p' :: "('c, 'd) Profile"
    assume
      rel: "((A, V, p), A', V', p') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV)"
    hence "((A, V, p), A', V', p') \<in> anonymity\<^sub>\<R> well_formed_elections"
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps
      by fastforce
    moreover have elt: "(A, V, p) \<in> elections_\<A> UNIV"
      using rel
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps
      by blast
    ultimately have
      "((A, V, p), A', V', p') \<in> restricted_rel 
        (anonymity\<^sub>\<R> well_formed_elections) (elections_\<A> UNIV) well_formed_elections"
      using equiv
      unfolding restricted_rel.simps equiv_def refl_on_def
      by blast
    hence "(A', V', p') \<in> elections_\<A> UNIV"
      using closed elt
      unfolding closed_restricted_rel.simps
      by blast
    thus "(A', V', p') \<in> well_formed_elections"
      using subset
      by blast
  next
    fix
      A A' :: "'c set" and
      V V' :: "'d set" and
      p p' :: "('c, 'd) Profile"
    assume
      "(A, V, p) \<in> elections_\<A> UNIV" and
      "((A, V, p), A', V', p') \<in> anonymity\<^sub>\<R> well_formed_elections"
    moreover from this
    obtain \<pi> :: "'d \<Rightarrow> 'd" where
      "bij \<pi>" and
      "(A', V', p') = rename \<pi> (A, V, p)"
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps 
                bijection\<^sub>\<V>\<^sub>\<G>_def \<phi>_anon.simps rewrite_carrier
                extensional_continuation.simps 
      by auto
    ultimately show "((A, V, p), A', V', p') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV)"
      unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps 
                bijection\<^sub>\<V>\<^sub>\<G>_def \<phi>_anon.simps rewrite_carrier
                extensional_continuation.simps 
      by auto
  qed
  also have "\<dots> = Restr (anonymity\<^sub>\<R> well_formed_elections) (elections_\<A> UNIV)"
    using restr_equals_restricted_rel closed subset
    by blast
  finally have
    "anonymity\<^sub>\<R> (elections_\<A> UNIV) =
      Restr (anonymity\<^sub>\<R> well_formed_elections) (elections_\<A> UNIV)"
    by simp
  thus ?thesis
    using equiv_rel_restr subset equiv
    by metis
qed

text \<open>
  We assume that all elections consist of a fixed finite alternative set of size \<open>n\<close> and
  finite subsets of an infinite voter universe. Profiles are linear orders on the alternatives.
  Then, we can operate on the natural-number-vectors of dimension \<open>n!\<close> instead of the equivalence
  classes of the anonymity relation:
  Each dimension corresponds to one possible linear order on the alternative set,
  i.e., the possible preferences.
  Each equivalence class of elections corresponds to a vector whose entries denote the amount
  of voters per election in that class who vote the respective corresponding preference.
\<close>
theorem anonymity\<^sub>\<Q>_isomorphism:
  assumes "infinite (UNIV :: 'v set)"
  shows "bij_betw (anonymity_class :: ('a :: finite, 'v) Election set
            \<Rightarrow> nat^('a Ordered_Preference)) (anonymity\<^sub>\<Q> (UNIV :: 'a set))
              (UNIV :: (nat^('a Ordered_Preference)) set)"
proof (unfold bij_betw_def inj_on_def, intro conjI ballI impI)
  fix X Y :: "('a, 'v) Election set"
  assume
    class_X: "X \<in> anonymity\<^sub>\<Q> UNIV" and
    class_Y: "Y \<in> anonymity\<^sub>\<Q> UNIV" and
    eq_vec: "anonymity_class X = anonymity_class Y"
  have "\<forall> E \<in> elections_\<A> UNIV. finite (voters_\<E> E)"
    by simp
  hence "\<forall> (E, E') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV). finite (voters_\<E> E)"
    by simp
  moreover have subset: "elections_\<A> UNIV \<subseteq> well_formed_elections"
    by simp
  ultimately have
    "\<forall> (E, E') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV).
          \<forall> p. vote_count p E = vote_count p E'"
    using anon_rel_vote_count
    by blast
  hence vote_count_invar:
    "\<forall> p. (vote_count p) respects (anonymity\<^sub>\<R> (elections_\<A> UNIV))"
    unfolding congruent_def
    by blast
  have quotient_count:
    "\<forall> X \<in> anonymity\<^sub>\<Q> UNIV. \<forall> p. \<forall> E \<in> X. vote_count\<^sub>\<Q> p X = vote_count p E"
    using pass_to_quotient[of "anonymity\<^sub>\<R> (elections_\<A> UNIV)"]
          vote_count_invar anon_rel_equiv
    unfolding anonymity\<^sub>\<Q>.simps anonymity\<^sub>\<R>.simps vote_count\<^sub>\<Q>.simps
    by metis
  moreover from anon_rel_equiv
  obtain
    E E' :: "('a, 'v) Election" where
    E_in_X: "E \<in> X" and
    E'_in_Y: "E' \<in> Y"
    using class_X class_Y equiv_Eps_in
    unfolding anonymity\<^sub>\<Q>.simps
    by metis
  ultimately have
    "\<forall> p. vote_count\<^sub>\<Q> p X = vote_count p E \<and> vote_count\<^sub>\<Q> p Y = vote_count p E'"
    using class_X class_Y
    by blast
  moreover with eq_vec have
    "\<forall> p. vote_count\<^sub>\<Q> (ord2pref p) X = vote_count\<^sub>\<Q> (ord2pref p) Y"
    unfolding anonymity_class.simps
    using UNIV_I vec_lambda_inverse
    by metis
  ultimately have "\<forall> p. vote_count (ord2pref p) E = vote_count (ord2pref p) E'"
    by simp
  hence eq: "\<forall> p \<in> {r. linear_order_on (UNIV :: 'a set) r}.
                vote_count p E = vote_count p E'"
    using pref2ord_inverse
    by metis
  from anon_rel_equiv class_X class_Y have subset_fixed_alts:
    "X \<subseteq> elections_\<A> UNIV \<and> Y \<subseteq> elections_\<A> UNIV"
    unfolding anonymity\<^sub>\<Q>.simps
    using in_quotient_imp_subset
    by blast
  hence eq_alts: "alternatives_\<E> E = UNIV \<and> alternatives_\<E> E' = UNIV"
    using E_in_X E'_in_Y
    unfolding elections_\<A>.simps
    by blast
  with subset_fixed_alts have eq_complement:
    "\<forall> p \<in> UNIV - {r. linear_order_on (UNIV :: 'a set) r}.
      {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}
      \<and> {v \<in> voters_\<E> E'. profile_\<E> E' v = p} = {}"
    using E_in_X E'_in_Y
    unfolding elections_\<A>.simps well_formed_elections_def profile_def
    by auto
  hence "\<forall> p \<in> UNIV - {r. linear_order_on (UNIV :: 'a set) r}.
          vote_count p E = 0 \<and> vote_count p E' = 0"
    unfolding card_eq_0_iff vote_count.simps
    by simp
  with eq have eq_vote_count: "\<forall> p. vote_count p E = vote_count p E'"
    using DiffI UNIV_I
    by metis
  moreover from subset_fixed_alts E_in_X E'_in_Y
    have "finite (voters_\<E> E) \<and> finite (voters_\<E> E')"
    unfolding elections_\<A>.simps
    by blast
  moreover from subset_fixed_alts E_in_X E'_in_Y
    have "(E, E') \<in> (elections_\<A> UNIV) \<times> (elections_\<A> UNIV)"
    by blast
  moreover from this
  have "(\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {})
      \<and> (\<forall> v. v \<notin> voters_\<E> E' \<longrightarrow> profile_\<E> E' v = {})"
    by simp
  ultimately have "(E, E') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV)"
    using eq_alts vote_count_anon_rel
    by metis
  hence "anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {E} =
            anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {E'}"
    using anon_rel_equiv equiv_class_eq
    by metis
  also have "anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {E} = X"
    using E_in_X class_X anon_rel_equiv Image_singleton_iff equiv_class_eq quotientE
    unfolding anonymity\<^sub>\<Q>.simps
    by (metis (no_types, lifting))
  also have "anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {E'} = Y"
    using E'_in_Y class_Y anon_rel_equiv Image_singleton_iff equiv_class_eq quotientE
    unfolding anonymity\<^sub>\<Q>.simps
    by (metis (no_types, lifting))
  finally show "X = Y"
    by simp
next
  have "(UNIV :: (nat, 'a Ordered_Preference) vec set) \<subseteq>
      (anonymity_class :: ('a, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec) `
      anonymity\<^sub>\<Q> UNIV"
  proof (unfold anonymity_class.simps, safe)
    fix x :: "(nat, 'a Ordered_Preference) vec"
    have "finite (UNIV :: 'a Ordered_Preference set)"
      by simp
    hence "finite {x$i | i. i \<in> UNIV}"
      using finite_Atleast_Atmost_nat
      by blast
    hence "(\<Sum> i \<in> UNIV. x$i) < \<infinity>"
      using enat_ord_code
      by simp
    moreover have "0 \<le> (\<Sum> i \<in> UNIV. x$i)"
      by blast
    ultimately obtain V :: "'v set" where
      fin_V: "finite V" and
      "card V = (\<Sum> i \<in> UNIV. x$i)"
      using assms infinite_arbitrarily_large
      by metis
    then obtain X' :: "'a Ordered_Preference \<Rightarrow> 'v set" where
      card': "\<forall> i. card (X' i) = x$i" and
      partition': "V = \<Union> {X' i | i. i \<in> UNIV}" and
      disjoint': "\<forall> i j. i \<noteq> j \<longrightarrow> X' i \<inter> X' j = {}"
      using obtain_partition[of V UNIV "($) x"]
      by auto
    obtain X :: "'a Preference_Relation \<Rightarrow> 'v set" where
      def_X: "X = (\<lambda> i. if i \<in> {r. linear_order r}
                        then X' (pref2ord i) else {})"
      by simp
    hence "{X i | i. i \<notin> {r. linear_order r}} \<subseteq> {{}}"
      by auto
    moreover have
      "{X i | i. i \<in> {r. linear_order r}} =
          {X' (pref2ord i) | i. i \<in> {r. linear_order r}}"
      using def_X
      by metis
    moreover have
      "{X i | i. i \<in> UNIV} =
          {X i | i. i \<in> {r. linear_order r}}
          \<union> {X i | i. i \<in> UNIV - {r. linear_order r}}"
      by blast
    ultimately have
      "{X i | i. i \<in> UNIV} = {X' (pref2ord i) | i. i \<in> {r. linear_order r}}
        \<or> {X i | i. i \<in> UNIV} =
            {X' (pref2ord i) | i. i \<in> {r. linear_order r}} \<union> {{}}"
      by auto
    also have
      "{X' (pref2ord i) | i. i \<in> {r. linear_order r}} = {X' i | i. i \<in> UNIV}"
      using iso_tuple_UNIV_I pref2ord_cases
      by metis
    finally have
      "{X i | i. i \<in> UNIV} = {X' i | i. i \<in> UNIV} \<or>
        {X i | i. i \<in> UNIV} = {X' i | i. i \<in> UNIV} \<union> {{}}"
      by simp
    hence "\<Union> {X i | i. i \<in> UNIV} = \<Union> {X' i | i. i \<in> UNIV}"
      using Sup_union_distrib ccpo_Sup_singleton sup_bot.right_neutral
      by (metis (no_types, lifting))
    hence partition: "V = \<Union> {X i | i. i \<in> UNIV}"
      using partition'
      by simp
    moreover have "\<forall> i j. i \<noteq> j \<longrightarrow> X i \<inter> X j = {}"
      using disjoint' def_X pref2ord_inject
      by auto
    ultimately have "\<forall> v \<in> V. \<exists>! i. v \<in> X i"
      by auto
    then obtain p' :: "'v \<Rightarrow> 'a Preference_Relation" where
      p_X: "\<forall> v \<in> V. v \<in> X (p' v)" and
      p_disj: "\<forall> v \<in> V. \<forall> i. i \<noteq> p' v \<longrightarrow> v \<notin> X i"
      by metis
    then obtain p :: "'v \<Rightarrow> 'a Preference_Relation" where
      p_in_V_then_p': "p = (\<lambda> v. if v \<in> V then p' v else {})"
      by simp
    hence lin_ord: "\<forall> v \<in> V. linear_order (p v)"
      using def_X p_X p_disj
      by fastforce
    hence wf_elections: "(UNIV, V, p) \<in> elections_\<A> UNIV"
      using fin_V
      unfolding p_in_V_then_p' elections_\<A>.simps
                well_formed_elections_def profile_def
      by auto
    hence "\<forall> i. \<forall> E \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}.
              vote_count i E = vote_count i (UNIV, V, p)"
      using fin_V anon_rel_vote_count[of "(UNIV, V, p)" _ "elections_\<A> UNIV"]
      by simp
    moreover have
      "(UNIV, V, p) \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}"
      using anon_rel_equiv wf_elections
      unfolding Image_def equiv_def refl_on_def
      by blast
    ultimately have eq_vote_count:
      "\<forall> i. vote_count i `
          (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) =
            {vote_count i (UNIV, V, p)}"
      by blast
    have "\<forall> i. \<forall> v \<in> V. p v = i \<longleftrightarrow> v \<in> X i"
      using p_X p_disj
      unfolding p_in_V_then_p'
      by metis
    hence "\<forall> i. {v \<in> V. p v = i} = {v \<in> V. v \<in> X i}"
      by blast
    moreover have "\<forall> i. X i \<subseteq> V"
      using partition
      by blast
    ultimately have rewr_preimg: "\<forall> i. {v \<in> V. p v = i} = X i"
      by auto
    hence "\<forall> i \<in> {r. linear_order r}.
              vote_count i (UNIV, V, p) = x$(pref2ord i)"
      using def_X card'
      by simp
    hence "\<forall> i \<in> {r. linear_order r}.
       vote_count i ` (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) =
          {x$(pref2ord i)}"
      using eq_vote_count
      by metis
    hence
      "\<forall> i \<in> {r. linear_order r}.
        vote_count\<^sub>\<Q> i (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) =
            x$(pref2ord i)"
      unfolding vote_count\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
      using is_singleton_altdef singleton_set_def_if_card_one
      by fastforce
    hence "\<forall> i. vote_count\<^sub>\<Q> (ord2pref i)
        (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) = x$i"
      using ord2pref ord2pref_inverse
      by metis
    hence "anonymity_class
        (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) = x"
      using anonymity_class.simps vec_lambda_unique
      by (metis (no_types, lifting))
    moreover have
      "anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)} \<in> anonymity\<^sub>\<Q> UNIV"
      using wf_elections
      unfolding anonymity\<^sub>\<Q>.simps quotient_def
      by blast
    ultimately show
      "x \<in> (\<lambda> X :: ('a, 'v) Election set. \<chi> p. vote_count\<^sub>\<Q> (ord2pref p) X)
              ` anonymity\<^sub>\<Q> UNIV"
      using anonymity_class.elims
      by blast
  qed
  thus "(anonymity_class :: ('a, 'v) Election set
          \<Rightarrow> (nat, 'a Ordered_Preference) vec) `
          anonymity\<^sub>\<Q> UNIV =
            (UNIV :: (nat, 'a Ordered_Preference) vec set)"
    by blast
qed

subsection \<open>Homogeneity Quotient: Simplex\<close>

fun vote_fraction :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election \<Rightarrow> rat" where
  "vote_fraction r E =
    (if finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {}
      then Fract (vote_count r E) (card (voters_\<E> E)) else 0)"

fun anonymity_homogeneity\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "anonymity_homogeneity\<^sub>\<R> \<E> =
    {(E, E') | E E'. E \<in> \<E> \<and> E' \<in> \<E>
                  \<and> finite (voters_\<E> E) = finite (voters_\<E> E')
                  \<and> (\<forall> r. vote_fraction r E = vote_fraction r E')}"

fun anonymity_homogeneity\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anonymity_homogeneity\<^sub>\<Q> A =
    quotient (elections_\<A> A) (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))"

fun vote_fraction\<^sub>\<Q> :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election set \<Rightarrow> rat" where
  "vote_fraction\<^sub>\<Q> p = \<pi>\<^sub>\<Q> (vote_fraction p)"

fun anonymity_homogeneity_class :: "('a :: finite, 'v) Election set \<Rightarrow>
        (rat, 'a Ordered_Preference) vec" where
  "anonymity_homogeneity_class \<E> = (\<chi> p. vote_fraction\<^sub>\<Q> (ord2pref p) \<E>)"

text \<open>
  Maps each rational real vector entry to the corresponding rational.
  If the entry is not rational, the corresponding entry will be undefined.
\<close>
fun rat_vector :: "real^'b \<Rightarrow> rat^'b" where
  "rat_vector v = (\<chi> p. the_inv of_rat (v$p))"

fun rat_vector_set :: "(real^'b) set \<Rightarrow> (rat^'b) set" where
  "rat_vector_set V = rat_vector ` {v \<in> V. \<forall> i. v$i \<in> \<rat>}"

definition standard_basis :: "(real^'b) set" where
  "standard_basis \<equiv> {v. \<exists> b. v$b = 1 \<and> (\<forall> c \<noteq> b. v$c = 0)}"

text \<open>
  The rational points in the simplex.
\<close>
definition vote_simplex :: "(rat^'b) set" where
  "vote_simplex \<equiv>
    insert 0 (rat_vector_set (convex hull standard_basis :: (real^'b) set))"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma convex_combination_in_convex_hull:
  fixes
    X :: "(real^'b) set" and
    x :: "real^'b"
  assumes "\<exists> f :: real^'b \<Rightarrow> real.
            (\<Sum> y \<in> X. f y) = 1 \<and> (\<forall> x \<in> X. f x \<ge> 0)
              \<and> x = (\<Sum> x \<in> X. f x *\<^sub>R x)"
  shows "x \<in> convex hull X"
  using assms
proof (induction "card X" arbitrary: X x)
  case 0
  fix
    X :: "(real^'b) set" and
    x :: "real^'b"
  assume
    "0 = card X" and
    "\<exists> f. (\<Sum> y \<in> X. f y) = 1 \<and> (\<forall> x \<in> X. 0 \<le> f x) \<and> x = (\<Sum> x \<in> X. f x *\<^sub>R x)"
  hence "(\<forall> f. (\<Sum> y \<in> X. f y) = 0) \<and> (\<exists> f. (\<Sum> y \<in> X. f y) = 1)"
    using card_0_eq empty_iff sum.infinite sum.neutral zero_neq_one
    by metis
  hence "\<exists> f. (\<Sum> y \<in> X. f y) = 1 \<and> (\<Sum> y \<in> X. f y) = 0"
    by metis
  hence False
    using zero_neq_one
    by metis
  thus ?case
    by simp
next
  case (Suc n)
  fix
    X :: "(real^'b) set" and
    x :: "real^'b" and
    n :: "nat"
  assume
    card: "Suc n = card X" and
    "\<exists> f. (\<Sum> y \<in> X. f y) = 1 \<and> (\<forall> x \<in> X. 0 \<le> f x) \<and> x = (\<Sum> x \<in> X. f x *\<^sub>R x)" and
    hyp: "\<And> (X :: (real^'b) set) x. n = card X
            \<Longrightarrow> \<exists> f. (\<Sum> y \<in> X. f y) = 1 \<and> (\<forall> x \<in> X. 0 \<le> f x) \<and> x =
                      (\<Sum> x \<in> X. f x *\<^sub>R x)
            \<Longrightarrow> x \<in> convex hull X"
  then obtain f :: "real^'b \<Rightarrow> real" where
    sum: "(\<Sum> y \<in> X. f y) = 1" and
    nonneg: "\<forall> x \<in> X. 0 \<le> f x" and
    x_sum: "x = (\<Sum> x \<in> X. f x *\<^sub>R x)"
    by blast
  have "card X > 0"
    using card
    by linarith
  hence fin: "finite X"
    using card_gt_0_iff
    by blast
  have "n = 0 \<longrightarrow> card X = 1"
    using card
    by presburger
  hence "n = 0 \<longrightarrow> (\<exists> y. X = {y} \<and> f y = 1)"
    using sum nonneg One_nat_def add.right_neutral card_1_singleton_iff
          empty_iff finite.emptyI sum.insert sum.neutral
    by (metis (no_types, opaque_lifting))
  hence "n = 0 \<longrightarrow> (\<exists> y. X = {y} \<and> x = y)"
    using x_sum
    by fastforce
  hence "n = 0 \<longrightarrow> x \<in> X"
    by blast
  moreover have "n > 0 \<longrightarrow> x \<in> convex hull X"
  proof (safe)
    assume "0 < n"
    hence card_X_gt_one: "card X > 1"
      using card
      by simp
    have "(\<forall> y \<in> X. f y \<ge> 1) \<longrightarrow> (\<Sum> y \<in> X. f y) \<ge> (\<Sum> x \<in> X. 1)"
      using fin sum_mono
      by metis
    moreover have "(\<Sum> x \<in> X. 1) = card X"
      by force
    ultimately have "(\<forall> y \<in> X. f y \<ge> 1) \<longrightarrow> card X \<le> (\<Sum> y \<in> X. f y)"
      by force
    hence "(\<forall> y \<in> X. f y \<ge> 1) \<longrightarrow> 1 < (\<Sum> y \<in> X. f y)"
      using card_X_gt_one
      by linarith
    then obtain y :: "real^'b" where
      y_in_X: "y \<in> X" and
      f_y_lt_one: "f y < 1"
      using sum
      by auto
    hence "1 - f y \<noteq> 0 \<and> x = f y *\<^sub>R y + (\<Sum> x \<in> X - {y}. f x *\<^sub>R x)"
      using fin sum.remove x_sum
      by simp
    moreover have
      "\<forall> \<alpha> \<noteq> 0. (\<Sum> x \<in> X - {y}. f x *\<^sub>R x) =
            \<alpha> *\<^sub>R (\<Sum> x \<in> X - {y}. (f x / \<alpha>) *\<^sub>R x)"
      unfolding scaleR_sum_right
      by simp
    ultimately have convex_comb:
      "x = f y *\<^sub>R y + (1 - f y) *\<^sub>R (\<Sum> x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x)"
      by simp
    obtain f' :: "real^'b \<Rightarrow> real" where
      def': "f' = (\<lambda> x. f x / (1 - f y))"
      by simp
    hence "\<forall> x \<in> X - {y}. f' x \<ge> 0"
      using nonneg f_y_lt_one
      by fastforce
    moreover have
      "(\<Sum> y \<in> X - {y}. f' y) = (\<Sum> x \<in> X - {y}. f x) / (1 - f y)"
      unfolding def' sum_divide_distrib
      by simp
    moreover have
      "(\<Sum> x \<in> X - {y}. f x) / (1 - f y) = (1 - f y) / (1 - f y)"
      using sum y_in_X
      by (simp add: fin sum.remove)
    moreover have "(1 - f y) / (1 - f y) = 1"
      using f_y_lt_one
      by simp
    ultimately have
      "(\<Sum> y \<in> X - {y}. f' y) = 1 \<and> (\<forall> x \<in> X - {y}. 0 \<le> f' x)
            \<and> (\<Sum> x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) =
          (\<Sum> x \<in> X - {y}. f' x *\<^sub>R x)"
      using def'
      by metis
    hence "\<exists> f'. (\<Sum> y \<in> X - {y}. f' y) = 1 \<and> (\<forall> x \<in> X - {y}. 0 \<le> f' x)
              \<and> (\<Sum> x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) =
          (\<Sum> x \<in> X - {y}. f' x *\<^sub>R x)"
      by metis
    moreover have "card (X - {y}) = n"
      using card y_in_X
      by simp
    ultimately have
      "(\<Sum> x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) \<in> convex hull (X - {y})"
      using hyp
      by blast
    hence "(\<Sum> x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) \<in> convex hull X"
      using Diff_subset hull_mono in_mono
      by (metis (no_types, lifting))
    moreover have "f y \<ge> 0 \<and> 1 - f y \<ge> 0"
      using f_y_lt_one nonneg y_in_X
      by simp
    moreover have "f y + (1 - f y) \<ge> 0"
      by simp
    moreover have "y \<in> convex hull X"
      using y_in_X
      by (simp add: hull_inc)
    moreover have
      "\<forall> x y. x \<in> convex hull X \<and> y \<in> convex hull X \<longrightarrow>
        (\<forall> a \<ge> 0. \<forall> b \<ge> 0. a + b = 1 \<longrightarrow> a *\<^sub>R x + b *\<^sub>R y \<in> convex hull X)"
      using convex_def convex_convex_hull
      by (metis (no_types, opaque_lifting))
    ultimately show "x \<in> convex hull X"
      using convex_comb
      by simp
  qed
  ultimately show "x \<in> convex hull X"
    using hull_inc
    by fastforce
qed

lemma standard_simplex_rewrite: "convex hull standard_basis =
    {v :: real^'b. (\<forall> i. v$i \<ge> 0) \<and> (\<Sum> y \<in> UNIV. v$y) = 1}"
proof (unfold convex_def hull_def, intro equalityI)
  let ?simplex = "{v :: real^'b. (\<forall> i. v$i \<ge> 0) \<and> (\<Sum> y \<in> UNIV. v$y) = 1}"
  have "\<forall> v :: real^'b \<in> standard_basis. \<exists> b.
        v$b = 1 \<and> (\<forall> c. c \<noteq> b \<longrightarrow> v$c = 0)"
    unfolding standard_basis_def
    by simp
  then obtain one :: "real^'b \<Rightarrow> 'b" where
    def_map: "\<forall> v \<in> standard_basis. v$(one v) = 1 \<and> (\<forall> i \<noteq> one v. v$i = 0)"
    by metis
  hence "\<forall> v :: real^'b \<in> standard_basis. \<forall> b. v$b \<ge> 0"
    using dual_order.refl zero_less_one_class.zero_le_one
    by metis
  moreover have "\<forall> v :: real^'b \<in> standard_basis.
      (\<Sum> z \<in> UNIV. v$z) = (\<Sum> z \<in> UNIV - {one v}. v$z) + v$(one v)"
    unfolding def_map
    using add.commute finite insert_UNIV sum.insert_remove
    by metis
  moreover have "\<forall> v \<in> standard_basis.
        (\<Sum> z \<in> UNIV - {one v}. v$z) + v$(one v) = 1"
    using def_map
    by simp
  ultimately have "standard_basis \<subseteq> ?simplex"
    by force
  moreover have "\<forall> x :: real^'b. \<forall> y. (\<Sum> z \<in> UNIV. (x + y)$z) =
            (\<Sum> z \<in> UNIV. x$z) + (\<Sum> z \<in> UNIV. y$z)"
    by (simp add: sum.distrib)
  hence "\<forall> x :: real^'b. \<forall> y. \<forall> u v.
    (\<Sum> z \<in> UNIV. (u *\<^sub>R x + v *\<^sub>R y)$z) =
          u *\<^sub>R (\<Sum> z \<in> UNIV. x$z) + v *\<^sub>R (\<Sum> z \<in> UNIV. y$z)"
    using scaleR_right.sum sum.cong vector_scaleR_component
    by (metis (no_types))
  hence "\<forall> x \<in> ?simplex. \<forall> y \<in> ?simplex. \<forall> u v.
          (\<Sum> z \<in> UNIV. (u *\<^sub>R x + v *\<^sub>R y)$z) = u *\<^sub>R 1 + v *\<^sub>R 1"
    by simp
  hence "\<forall> x \<in> ?simplex. \<forall> y \<in> ?simplex. \<forall> u \<ge> 0. \<forall> v \<ge> 0.
      u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> ?simplex"
    by simp
  ultimately show
    "\<Inter> {t. (\<forall> x \<in> t. \<forall> y \<in> t. \<forall> u \<ge> 0. \<forall> v \<ge> 0.
                    u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t)
            \<and> standard_basis \<subseteq> t} \<subseteq> ?simplex"
    by blast
next
  show "{v. (\<forall> i. 0 \<le> v$i) \<and> (\<Sum> y \<in> UNIV. v$y) = 1} \<subseteq>
      \<Inter> {t. (\<forall> x \<in> t. \<forall> y \<in> t. \<forall> u \<ge> 0. \<forall> v \<ge> 0.
                  u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t)
              \<and> (standard_basis :: (real^'b) set) \<subseteq> t}"
  proof (intro subsetI)
    fix
      x :: "real^'b" and
      X :: "real^'b set"
    assume convex_comb:
      "x \<in> {v. (\<forall> i. 0 \<le> v$i) \<and> (\<Sum> y \<in> UNIV. v$y) = 1}"
    have "\<forall> v \<in> standard_basis. \<exists> b. v$b = 1 \<and> (\<forall> b' \<noteq> b. v$b' = 0)"
      unfolding standard_basis_def
      by simp
    then obtain ind :: "real^'b \<Rightarrow> 'b" where
      ind_eq_one: "\<forall> v \<in> standard_basis. v$(ind v) = 1" and
      ind_eq_zero: "\<forall> v \<in> standard_basis. \<forall> b \<noteq> (ind v). v$b = 0"
      by metis
    hence "\<forall> v \<in> standard_basis. \<forall> v' \<in> standard_basis.
              ind v = ind v' \<longrightarrow> (\<forall> b. v$b = v'$b)"
      by metis
    hence inj_ind:
      "\<forall> v \<in> standard_basis. \<forall> v' \<in> standard_basis.
          ind v = ind v' \<longrightarrow> v = v'"
      unfolding vec_eq_iff
      by blast
    hence "inj_on ind standard_basis"
      unfolding inj_on_def
      by blast
    hence bij_ind_std: "bij_betw ind standard_basis (ind ` standard_basis)"
      unfolding bij_betw_def
      by simp
    obtain ind_inv :: "'b \<Rightarrow> real^'b" where
      char_vec: "ind_inv = (\<lambda> b. \<chi> i. if i = b then 1 else 0)"
      by blast
    hence in_basis: "\<forall> b. ind_inv b \<in> standard_basis"
      unfolding standard_basis_def
      by simp
    moreover from this
    have ind_inv_map: "\<forall> b. ind (ind_inv b) = b"
      using char_vec ind_eq_zero ind_eq_one axis_def axis_nth zero_neq_one
      by metis
    ultimately have "\<forall> b. \<exists> v. v \<in> standard_basis \<and> b = ind v"
      by metis
    hence univ: "ind ` standard_basis = UNIV"
      by blast
    have bij_inv: "bij_betw ind_inv UNIV standard_basis"
      using ind_inv_map bij_ind_std bij_betw_byWitness[of _ ind] in_basis inj_ind
      unfolding image_subset_iff
      by simp
    obtain f :: "real^'b \<Rightarrow> real" where
      func: "f = (\<lambda> v. if v \<in> standard_basis then x$(ind v) else 0)"
      by blast
    hence "(\<Sum> y \<in> standard_basis. f y) = (\<Sum> v \<in> standard_basis. x$(ind v))"
      by simp
    also have "\<dots> = (\<Sum> y \<in> ind ` standard_basis. x$y)"
      using bij_ind_std sum_comp[of "ind" _ _ "($) x"]
      by simp
    finally have sum_eq_one: "(\<Sum> y \<in> standard_basis. f y) = 1"
      using univ convex_comb
      by simp
    have nonneg: "\<forall> v \<in> standard_basis. f v \<ge> 0"
      using func convex_comb
      by simp
    have "\<forall> v \<in> standard_basis. (\<chi> i. x$(ind v) * v$i)
          = (\<chi> i. if i = ind v then x$(ind v) else 0)"
      using ind_eq_one ind_eq_zero
      by fastforce
    hence
      "\<forall> v \<in> standard_basis.
          x$(ind v) *\<^sub>R v = (\<chi> i. if i = ind v then x$(ind v) else 0)"
      unfolding scaleR_vec_def
      by simp
    moreover have "(\<Sum> x \<in> standard_basis. f x *\<^sub>R x) =
        (\<Sum> v \<in> standard_basis. x$(ind v) *\<^sub>R v)"
      unfolding func
      by simp
    ultimately have "(\<Sum> x \<in> standard_basis. f x *\<^sub>R x)
          = (\<Sum> v \<in> standard_basis. \<chi> i. if i = ind v then x$(ind v) else 0)"
      by force
    also have "\<dots> = (\<Sum> b \<in> UNIV. \<chi> i. if i = ind (ind_inv b)
                              then x$(ind (ind_inv b)) else 0)"
      using bij_inv sum_comp
      unfolding comp_def
      by blast
    also have "\<dots> = (\<Sum> b \<in> UNIV. \<chi> i. if i = b then x$b else 0)"
      using ind_inv_map
      by presburger
    finally have "(\<Sum> x \<in> standard_basis. f x *\<^sub>R x) =
        (\<Sum> b \<in> UNIV. \<chi> i. if i = b then x$b else 0)"
      by simp
    hence "(\<Sum> x \<in> standard_basis. f x *\<^sub>R x) = x"
      unfolding vec_eq_iff
      by simp
    hence "\<exists> f :: real^'b \<Rightarrow> real.
              (\<Sum> y \<in> standard_basis. f y) = 1 \<and> (\<forall> x \<in> standard_basis. f x \<ge> 0)
            \<and> x = (\<Sum> x \<in> standard_basis. f x *\<^sub>R x)"
      using sum_eq_one nonneg
      by blast
    thus "x \<in> \<Inter> {t. (\<forall> x \<in> t. \<forall> y \<in> t. \<forall> u \<ge> 0. \<forall> v \<ge> 0.
                          u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t)
                  \<and> (standard_basis :: (real^'b) set) \<subseteq> t}"
      using convex_combination_in_convex_hull
      unfolding convex_def hull_def
      by blast
  qed
qed

lemma fract_distr_helper:
  fixes a b c :: "int"
  assumes "c \<noteq> 0"
  shows "Fract a c + Fract b c = Fract (a + b) c"
  using add_rat assms mult.commute mult_rat_cancel distrib_right
  by metis

lemma anonymity_homogeneity_is_equivalence:
  fixes X :: "('a, 'v) Election set"
  assumes "\<forall> E \<in> X. finite (voters_\<E> E)"
  shows "equiv X (anonymity_homogeneity\<^sub>\<R> X)"
proof (unfold equiv_def, safe)
  show "refl_on X (anonymity_homogeneity\<^sub>\<R> X)"
    unfolding refl_on_def anonymity_homogeneity\<^sub>\<R>.simps
    by blast
next
  show "sym (anonymity_homogeneity\<^sub>\<R> X)"
    unfolding sym_def anonymity_homogeneity\<^sub>\<R>.simps
    using sup_commute
    by simp
next
  show "Relation.trans (anonymity_homogeneity\<^sub>\<R> X)"
  proof
    fix E E' F :: "('a, 'v) Election"
    assume
      rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> X" and
      rel': "(E', F) \<in> anonymity_homogeneity\<^sub>\<R> X"
    hence "finite (voters_\<E> E')"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      using assms
      by fastforce
    from rel rel' have eq_frac:
      "(\<forall> r. vote_fraction r E = vote_fraction r E') \<and>
        (\<forall> r. vote_fraction r E' = vote_fraction r F)"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by blast
    hence "\<forall> r. vote_fraction r E = vote_fraction r F"
      by metis
    thus "(E, F) \<in> anonymity_homogeneity\<^sub>\<R> X"
      using rel rel' snd_conv
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by blast
  qed
qed

lemma fract_distr:
  fixes
    A :: "'x set" and
    f :: "'x \<Rightarrow> int" and
    b :: "int"
  assumes
    "finite A" and
    "b \<noteq> 0"
  shows "(\<Sum> a \<in> A. Fract (f a) b) = Fract (\<Sum> x \<in> A. f x) b"
  using assms
proof (induction "card A" arbitrary: A f b)
  case 0
  fix
    A :: "'x set" and
    f :: "'x \<Rightarrow> int" and
    b :: "int"
  assume
    "0 = card A" and
    "finite A" and
    "b \<noteq> 0"
  hence "(\<Sum> a \<in> A. Fract (f a) b) = 0 \<and> (\<Sum> y \<in> A. f y) = 0"
    by simp
  thus ?case
    using 0 rat_number_collapse
    by simp
next
  case (Suc n)
  fix
    A :: "'x set" and
    f :: "'x \<Rightarrow> int" and
    b :: "int" and
    n :: "nat"
  assume
    card_A: "Suc n = card A" and
    fin_A: "finite A" and
    b_non_zero: "b \<noteq> 0" and
    hyp: "\<And> A f b.
           n = card (A :: 'x set) \<Longrightarrow>
           finite A \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (\<Sum> a \<in> A. Fract (f a) b) = Fract (\<Sum> x \<in> A. f x) b"
  hence "A \<noteq> {}"
    by auto
  then obtain c :: "'x" where
    c_in_A: "c \<in> A"
    by blast
  hence "(\<Sum> a \<in> A. Fract (f a) b) =
            (\<Sum> a \<in> A - {c}. Fract (f a) b) + Fract (f c) b"
    using fin_A
    by (simp add: sum_diff1)
  also have "\<dots>  = Fract (\<Sum> x \<in> A - {c}. f x) b + Fract (f c) b"
    using hyp card_A fin_A b_non_zero c_in_A Diff_empty card_Diff_singleton
          diff_Suc_1 finite_Diff_insert
    by metis
  also have "\<dots> = Fract (\<Sum> x \<in> A. f x) b"
    using c_in_A fin_A b_non_zero fract_distr_helper
    by (simp add: sum_diff1)
  finally show "(\<Sum> a \<in> A. Fract (f a) b) = Fract (\<Sum> x \<in> A. f x) b"
    by blast
qed

subsubsection \<open>Simplex Bijection\<close>

text \<open>
  We assume all our elections to consist of a fixed finite set of \<open>n\<close> alternatives and finite
  subsets of an infinite universe of voters. Profiles are linear orders on the alternatives.
  Then we can work on the standard simplex of dimension \<open>n!\<close> instead of the equivalence
  classes of the equivalence relation for anonymous and homogeneous voting rules:
  Each dimension corresponds to one possible linear order on the alternative set, i.e.,
  the possible preferences.
  Each equivalence class of elections corresponds to a vector whose entries denote the fraction
  of voters per election in that class who vote the respective corresponding preference.
\<close>
theorem anonymity_homogeneity\<^sub>\<Q>_isomorphism:
  assumes "infinite (UNIV :: 'v set)"
  shows
    "bij_betw (anonymity_homogeneity_class :: ('a :: finite, 'v) Election set \<Rightarrow>
        rat^'a Ordered_Preference) (anonymity_homogeneity\<^sub>\<Q> (UNIV :: 'a set))
          (vote_simplex :: (rat^'a Ordered_Preference) set)"
proof (unfold bij_betw_def inj_on_def, intro conjI ballI impI)
  fix X Y :: "('a, 'v) Election set"
  assume
    class_X: "X \<in> anonymity_homogeneity\<^sub>\<Q> UNIV" and
    class_Y: "Y \<in> anonymity_homogeneity\<^sub>\<Q> UNIV"
  moreover have equiv:
    "equiv (elections_\<A> UNIV) (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV))"
    using anonymity_homogeneity_is_equivalence CollectD IntD1 inf_commute
    unfolding elections_\<A>.simps
    by (metis (no_types, lifting))
  ultimately have subset:
    "X \<noteq> {} \<and> X \<subseteq> elections_\<A> UNIV \<and> Y \<noteq> {} \<and> Y \<subseteq> elections_\<A> UNIV"
    using in_quotient_imp_non_empty in_quotient_imp_subset
    unfolding anonymity_homogeneity\<^sub>\<Q>.simps
    by blast
  then obtain E E' :: "('a, 'v) Election" where
    E_in_X: "E \<in> X" and
    E'_in_Y: "E' \<in> Y"
    by blast
  hence class_X_E: "anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {E} = X"
    using class_X equiv Image_singleton_iff equiv_class_eq quotientE
    unfolding anonymity_homogeneity\<^sub>\<Q>.simps
    by (metis (no_types, opaque_lifting))
  hence "\<forall> F :: ('a, 'v) Election \<in> X. \<forall> p :: 'a Preference_Relation.
            vote_fraction p F = vote_fraction p E"
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by fastforce
  hence "\<forall> p :: 'a Preference_Relation.
            vote_fraction p ` X = {vote_fraction p E}"
    using E_in_X
    by blast
  hence "\<forall> p :: 'a Preference_Relation.
            vote_fraction\<^sub>\<Q> p X = vote_fraction p E"
    using is_singletonI singleton_set_def_if_card_one the_elem_eq
    unfolding is_singleton_altdef vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
    by metis
  hence "\<forall> p :: 'a Ordered_Preference.
            (anonymity_homogeneity_class X)$p = vote_fraction (ord2pref p) E"
    unfolding anonymity_homogeneity_class.simps
    using vec_lambda_beta
    by metis
  moreover assume
    "anonymity_homogeneity_class X = anonymity_homogeneity_class Y"
  moreover have class_Y_E': "anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {E'} = Y"
    using class_Y equiv E'_in_Y Image_singleton_iff equiv_class_eq quotientE
    unfolding anonymity_homogeneity\<^sub>\<Q>.simps
    by (metis (no_types, opaque_lifting))
  hence "\<forall> F :: ('a, 'v) Election \<in> Y. \<forall> p :: 'a Preference_Relation.
            vote_fraction p E' = vote_fraction p F"
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast
  hence "\<forall> p :: 'a Preference_Relation.
            vote_fraction p ` Y = {vote_fraction p E'}"
    using E'_in_Y
    by fastforce
  hence "\<forall> p :: 'a Preference_Relation. vote_fraction\<^sub>\<Q> p Y = vote_fraction p E'"
    using is_singletonI singleton_set_def_if_card_one the_elem_eq
    unfolding is_singleton_altdef vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
    by metis
  hence eq_Y_E':
    "\<forall> p :: 'a Ordered_Preference.
        (anonymity_homogeneity_class Y)$p = vote_fraction (ord2pref p) E'"
    unfolding anonymity_homogeneity_class.simps
    using vec_lambda_beta
    by metis
  ultimately have "\<forall> p :: 'a Preference_Relation.
        linear_order p \<longrightarrow> vote_fraction p E = vote_fraction p E'"
    using mem_Collect_eq pref2ord_inverse
    by metis
  moreover have
    "(\<forall> v :: 'v. v \<in> voters_\<E> E \<longrightarrow> linear_order (profile_\<E> E v)) \<and>
      (\<forall> v :: 'v. v \<in> voters_\<E> E' \<longrightarrow> linear_order (profile_\<E> E' v))"
    using subset E_in_X E'_in_Y
    unfolding elections_\<A>.simps well_formed_elections_def profile_def
    by fastforce
  hence "\<forall> p :: 'a Preference_Relation.
            \<not> linear_order p \<longrightarrow> vote_count p E = 0 \<and> vote_count p E' = 0"
    unfolding vote_count.simps
    using card.infinite card_0_eq Collect_empty_eq
    by (metis (mono_tags, lifting))
  hence "\<forall> p :: 'a Preference_Relation.
            \<not> linear_order p \<longrightarrow> vote_fraction p E = 0 \<and> vote_fraction p E' = 0"
    using int_ops rat_number_collapse
    by simp
  ultimately have "\<forall> p :: 'a Preference_Relation.
            vote_fraction p E = vote_fraction p E'"
    by metis
  hence "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)"
    using subset E_in_X E'_in_Y elections_\<A>.simps
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast
  thus "X = Y"
    using class_X_E class_Y_E' equiv equiv_class_eq
    by (metis (no_types, lifting))
next
  show "(anonymity_homogeneity_class :: ('a, 'v) Election set
            \<Rightarrow> rat^'a Ordered_Preference)
        ` anonymity_homogeneity\<^sub>\<Q> UNIV = vote_simplex"
  proof (unfold vote_simplex_def, safe)
    fix X :: "('a, 'v) Election set"
    assume "X \<in> anonymity_homogeneity\<^sub>\<Q> UNIV"
    moreover have "equiv (elections_\<A> UNIV) (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV))"
      using anonymity_homogeneity_is_equivalence elections_\<A>.simps
      by blast
    ultimately obtain E :: "('a, 'v) Election" where
      E_in_X: "E \<in> X" and
      rel: "\<forall> E' \<in> X. (E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)"
      using anonymity_homogeneity\<^sub>\<Q>.simps equiv_Eps_in proj_Eps
      unfolding proj_def
      by blast
    hence "\<forall> p :: 'a Ordered_Preference. \<forall> E' \<in> X.
        vote_fraction (ord2pref p) E' = vote_fraction (ord2pref p) E"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by fastforce
    hence "\<forall> p :: 'a Ordered_Preference.
        vote_fraction (ord2pref p) ` X = {vote_fraction (ord2pref p) E}"
      using E_in_X
      by blast
    hence repr: "\<forall> p :: 'a Ordered_Preference.
        vote_fraction\<^sub>\<Q> (ord2pref p) X = vote_fraction (ord2pref p) E"
      using is_singletonI singleton_set_def_if_card_one the_elem_eq
      unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps is_singleton_altdef
      by metis
    hence "\<forall> p :: 'a Ordered_Preference. vote_fraction\<^sub>\<Q> (ord2pref p) X \<ge> 0"
      using zero_le_Fract_iff Orderings.order_eq_iff card_eq_0_iff
            of_nat_le_0_iff of_nat_less_0_iff linorder_not_less
      unfolding vote_fraction.simps card_gt_0_iff
      by metis
    hence geq_zero: "\<forall> p :: 'a Ordered_Preference.
        real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X) \<ge> 0"
      using zero_le_of_rat_iff
      by blast
    have zero_case:
      "voters_\<E> E = {} \<or> infinite (voters_\<E> E) \<longrightarrow>
        (\<chi> p :: 'a Ordered_Preference.
          real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = 0"
      using repr
      unfolding zero_vec_def
      by simp
    let ?vote_sum = "(\<Sum> r :: 'a Preference_Relation \<in> UNIV. vote_count r E)"
    have "finite (UNIV :: 'a Preference_Relation)"
      by simp
    hence eq_card: "finite (voters_\<E> E) \<longrightarrow> card (voters_\<E> E) = ?vote_sum"
      using vote_count_sum
      by metis
    hence "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow>
        (\<Sum> r :: 'a Preference_Relation \<in> UNIV. vote_fraction r E) =
          (\<Sum> r :: 'a Preference_Relation \<in> UNIV. Fract (vote_count r E) ?vote_sum)"
      unfolding vote_fraction.simps
      by presburger
    moreover have fin_imp_sum_gt_zero:
      "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow> ?vote_sum > 0"
      by fastforce
    hence "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow>
      (\<Sum> r :: 'a Preference_Relation \<in> UNIV.
        Fract (vote_count r E) ?vote_sum) = Fract ?vote_sum ?vote_sum"
      using fract_distr[of UNIV ?vote_sum] card_0_eq eq_card of_nat_eq_0_iff
            finite_class.finite_UNIV of_nat_sum sum.cong
      by (metis (no_types, lifting))
    moreover have
      "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow> Fract ?vote_sum ?vote_sum = 1"
      using fin_imp_sum_gt_zero Fract_le_one_iff Fract_less_one_iff
            of_nat_0_less_iff order_le_less order_less_irrefl
      by metis
    ultimately have fin_imp_sum_eq_one:
      "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow>
        (\<Sum> r :: 'a Preference_Relation \<in> UNIV. vote_fraction r E) = 1"
      by presburger
    have "\<forall> r :: 'a Preference_Relation. \<not> linear_order r \<longrightarrow> vote_count r E = 0"
      using E_in_X rel
      unfolding elections_\<A>.simps well_formed_elections_def profile_def
      by fastforce
    hence "\<forall> r :: 'a Preference_Relation. \<not> linear_order r \<longrightarrow> vote_fraction r E = 0"
      using rat_number_collapse
      by simp
    moreover have "(\<Sum> r :: 'a Preference_Relation \<in> UNIV. vote_fraction r E) =
      (\<Sum> r :: 'a Preference_Relation \<in> {s :: 'a Preference_Relation. linear_order s}.
        vote_fraction r E) +
      (\<Sum> r :: 'a Preference_Relation
          \<in> UNIV - {s :: 'a Preference_Relation. linear_order s}.
        vote_fraction r E)"
      using finite CollectD Collect_mono UNIV_I add.commute
            sum.subset_diff top_set_def
      by metis
    ultimately have "(\<Sum> r :: 'a Preference_Relation \<in> UNIV. vote_fraction r E) =
      (\<Sum> r :: 'a rel \<in> {s :: 'a Preference_Relation. linear_order s}. vote_fraction r E)"
      by simp
    moreover have "bij_betw ord2pref UNIV {r :: 'a Preference_Relation. linear_order r}"
      using inj_def ord2pref_inject range_ord2pref
      unfolding bij_betw_def
      by blast
    ultimately have
      "(\<Sum> r :: 'a Preference_Relation \<in> UNIV. vote_fraction r E) =
          (\<Sum> r :: 'a Ordered_Preference \<in> UNIV. vote_fraction (ord2pref r) E)"
      using sum_comp
      by simp
    hence "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow>
      (\<Sum> p :: 'a Ordered_Preference \<in> UNIV.
        real_of_rat (vote_fraction (ord2pref p) E)) = 1"
      using fin_imp_sum_eq_one of_rat_1 of_rat_sum
      by metis
    hence "(\<chi> p :: 'a Ordered_Preference. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = 0
      \<or> ((\<forall> p :: 'a Ordered_Preference. (\<chi> q :: 'a Ordered_Preference.
            real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref q) X))$p \<ge> 0)
        \<and> (\<Sum> p :: 'a Ordered_Preference \<in> UNIV.
            (\<chi> q. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref q) X))$p) = 1)"
      using zero_case repr geq_zero
      by force
    moreover have
      "\<forall> p :: 'a Ordered_Preference.
          (\<chi> q :: 'a Ordered_Preference.
        real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref q) X))$p \<in> \<rat>"
      by simp
    ultimately have simplex_el:
      "(\<chi> p :: 'a Ordered_Preference. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))
          \<in> {x \<in> insert 0 (convex hull standard_basis).
              \<forall> p :: 'a Ordered_Preference. x$p \<in> \<rat>}"
      using standard_simplex_rewrite
      by blast
    moreover have
      "\<forall> p :: 'a Ordered_Preference.
        (rat_vector (\<chi> q :: 'a Ordered_Preference.
        of_rat (vote_fraction\<^sub>\<Q> (ord2pref q) X)))$p =
          the_inv real_of_rat ((\<chi> q :: 'a Ordered_Preference.
            real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref q) X))$p)"
      unfolding rat_vector.simps
      using vec_lambda_beta
      by blast
    moreover have
      "\<forall> p :: 'a Ordered_Preference. the_inv real_of_rat
          ((\<chi> q :: 'a Ordered_Preference.
            real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref q) X))$p) =
        the_inv real_of_rat (real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))"
      by simp
    moreover have inv_of_rat:
      "\<forall> x :: rat \<in> \<rat>. the_inv of_rat (of_rat x) = x"
      using the_inv_f_f injI of_rat_eq_iff
      by metis
    hence "\<forall> p :: 'a Ordered_Preference.
      the_inv real_of_rat (real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) =
        vote_fraction\<^sub>\<Q> (ord2pref p) X"
      using Rats_eq_range_nat_to_rat_surj surj_nat_to_rat_surj
      by blast
    moreover have
      "\<forall> p :: 'a Ordered_Preference.
      vote_fraction\<^sub>\<Q> (ord2pref p) X = (anonymity_homogeneity_class X)$p"
      by simp
    ultimately have
      "\<forall> p :: 'a Ordered_Preference.
        (rat_vector (\<chi> q :: 'a Ordered_Preference.
          of_rat (vote_fraction\<^sub>\<Q> (ord2pref q) X)))$p =
      (anonymity_homogeneity_class X)$p"
      by metis
    hence "rat_vector
      (\<chi> p :: 'a Ordered_Preference. of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) =
      anonymity_homogeneity_class X"
      by simp
    hence "\<exists> x :: (real, 'a Ordered_Preference) vec
      \<in> {y :: (real, 'a Ordered_Preference) vec
          \<in> insert 0 (convex hull standard_basis). \<forall> p :: 'a Ordered_Preference.
        y$p \<in> \<rat>}.
        rat_vector x = anonymity_homogeneity_class X"
      using simplex_el
      by blast
    moreover assume
      "anonymity_homogeneity_class X \<notin> rat_vector_set (convex hull standard_basis)"
    ultimately have "rat_vector 0 = anonymity_homogeneity_class X"
      using image_iff insertE mem_Collect_eq
      unfolding rat_vector_set.simps
      by (metis (mono_tags, lifting))
    thus "anonymity_homogeneity_class X = 0"
      unfolding rat_vector.simps
      using Rats_0 inv_of_rat of_rat_0 vec_lambda_unique zero_index
      by (metis (no_types, lifting))
  next
    have all_zero:
      "\<forall> r :: 'a Preference_Relation.
        \<forall> (E :: ('a, 'c) Election)
          \<in> (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)) `` {(UNIV, {}, (\<lambda> v :: 'c. {}))}.
      vote_fraction r E = 0"
      unfolding Image_def anonymity_homogeneity\<^sub>\<R>.simps
      by fastforce
    moreover have "(UNIV, {}, \<lambda> v :: 'c. {})
          \<in> (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v :: 'c. {})})"
      unfolding elections_\<A>.simps well_formed_elections_def profile_def
      by simp
    ultimately have
      "\<forall> r :: 'a Preference_Relation. 0 \<in> vote_fraction r
            ` (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV))
                `` {(UNIV, {}, (\<lambda> v :: 'c. {}))}"
      using image_eqI
      by (metis (mono_tags, lifting))
    hence
      "\<forall> r :: 'a Preference_Relation. vote_fraction r
        ` (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)
            `` {(UNIV, {}, \<lambda> v :: 'c. {})}) = {0}"
      using all_zero
      by blast
    hence "\<forall> r :: 'a Ordered_Preference. vote_fraction\<^sub>\<Q> (ord2pref r)
          (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)
            `` {(UNIV, {}, \<lambda> v :: 'c. {})}) = 0"
      using is_singletonI singleton_insert_inj_eq' singleton_set_def_if_card_one
      unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps is_singleton_altdef
      by metis
    hence "\<forall> r :: 'a Ordered_Preference.
        (anonymity_homogeneity_class (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)
            `` {(UNIV, {}, \<lambda> v :: 'c. {})}))$r = 0"
      unfolding anonymity_homogeneity_class.simps
      using vec_lambda_beta
      by (metis (no_types))
    moreover have "\<forall> r :: 'a Ordered_Preference. 0$r = 0"
      by simp
    ultimately have "anonymity_homogeneity_class
      (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)
          `` {(UNIV, {}, \<lambda> v :: 'c. {})}) = (0 :: rat^'a Ordered_Preference)"
      using vec_eq_iff
      by (metis (no_types))
    moreover have
      "(UNIV, {}, \<lambda> v :: 'c. {}) \<in> elections_\<A> UNIV"
      unfolding elections_\<A>.simps well_formed_elections_def profile_def
      by simp
    hence "(anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v :: 'c. {})})
              \<in> anonymity_homogeneity\<^sub>\<Q> UNIV"
      unfolding anonymity_homogeneity\<^sub>\<Q>.simps quotient_def
      by blast
    ultimately show "0 \<in> anonymity_homogeneity_class ` anonymity_homogeneity\<^sub>\<Q> UNIV"
      using image_eqI
      by (metis (no_types))
  next
    fix x :: "rat^'a Ordered_Preference"
    assume "x \<in> rat_vector_set (convex hull standard_basis)"
    \<comment> \<open>The following converts a rational vector \<open>x\<close> to real vector \<open>x'\<close>.\<close>
    then obtain x' :: "real^'a Ordered_Preference" where
      conv: "(\<forall> p :: 'a Ordered_Preference. 0 \<le> x'$p)
              \<and> (\<Sum> p :: 'a Ordered_Preference \<in> UNIV. x'$p) = 1" and
      rat_inv: "\<forall> p :: 'a Ordered_Preference.
                  x$p = the_inv real_of_rat (x'$p) \<and>  x'$p \<in> \<rat>"
      unfolding rat_vector_set.simps rat_vector.simps
      using standard_simplex_rewrite
      by fastforce
    have "\<forall> p :: 'a Ordered_Preference. real_of_rat (x$p) = x'$p"
      using rat_inv f_the_inv_into_f inj_onCI of_rat_eq_iff
      unfolding Rats_def
      by (metis (no_types))
    moreover have
      "\<forall> p :: 'a Ordered_Preference. \<exists> fract :: int \<times> int.
        Fract (fst fract) (snd fract) = x$p \<and> 0 < snd fract"
      using quotient_of_unique
      by metis
    then obtain fraction' :: "'a Ordered_Preference \<Rightarrow> (int \<times> int)" where
      "\<forall> p :: 'a Ordered_Preference.
        x$p = Fract (fst (fraction' p)) (snd (fraction' p))" and
      pos': "\<forall> p :: 'a Ordered_Preference. 0 < snd (fraction' p)"
      by metis
    ultimately have fract':
      "\<forall> p :: 'a Ordered_Preference. x'$p = (fst (fraction' p)) / (snd (fraction' p))"
      using div_by_0 divide_less_cancel of_int_0 of_int_pos of_rat_rat
      by metis
    hence "\<forall> p :: 'a Ordered_Preference. (fst (fraction' p)) / (snd (fraction' p)) \<ge> 0"
      using conv
      by fastforce
    hence "\<forall> p :: 'a Ordered_Preference. fst (fraction' p) \<in> \<nat> \<and> snd (fraction' p) \<in> \<nat>"
      using pos' nonneg_int_cases of_nat_in_Nats not_less of_int_0_le_iff
            of_int_pos zero_le_divide_iff
      by metis
    hence "\<forall> p :: 'a Ordered_Preference. \<exists> (n :: nat) (m :: nat).
      fst (fraction' p) = n \<and> snd (fraction' p) = m"
      using Nats_cases
      by metis
    hence "\<forall> p :: 'a Ordered_Preference. \<exists> m :: nat \<times> nat.
      fst (fraction' p) = int (fst m) \<and> snd (fraction' p) = int (snd m)"
      by simp
    then obtain fraction :: "'a Ordered_Preference \<Rightarrow> (nat \<times> nat)" where
      eq: "\<forall> p :: 'a Ordered_Preference.
      fst (fraction' p) = int (fst (fraction p))
      \<and> snd (fraction' p) = int (snd (fraction p))"
      by metis
    hence fract:
      "\<forall> p :: 'a Ordered_Preference. x'$p = (fst (fraction p)) / (snd (fraction p))"
      using fract'
      by simp
    hence pos: "\<forall> p :: 'a Ordered_Preference. 0 < snd (fraction p)"
      using eq pos'
      by simp
    let ?prod = "\<Prod> p :: 'a Ordered_Preference \<in> UNIV. snd (fraction p)"
    have pos_prod: "?prod > 0"
      using pos
      by simp
    have "\<forall> p :: 'a Ordered_Preference. ?prod mod (snd (fraction p)) = 0"
      using finite UNIV_I mod_mod_trivial mod_prod_eq mod_self prod_zero
      by (metis (no_types, lifting))
    hence div: "\<forall> p :: 'a Ordered_Preference.
      (?prod div (snd (fraction p))) * (snd (fraction p)) = ?prod"
      using add.commute add_0 div_mult_mod_eq
      by metis
    obtain voter_amount :: "'a Ordered_Preference \<Rightarrow> nat" where
      def_amount:
        "voter_amount =
      (\<lambda> p :: 'a Ordered_Preference \<in> UNIV. (fst (fraction p)) * (?prod div (snd (fraction p))))"
      by blast
    let ?voter_sum =
      "(\<Sum> p :: 'a Ordered_Preference \<in> UNIV. (fst (fraction p)) * (?prod div (snd (fraction p))))"
    have rewrite_div:
      "\<forall> p :: 'a Ordered_Preference. ?prod div (snd (fraction p)) = ?prod / (snd (fraction p))"
      using div less_imp_of_nat_less nonzero_mult_div_cancel_right
            of_nat_less_0_iff of_nat_mult pos
      by metis
    hence "?voter_sum =
      (\<Sum> p :: 'a Ordered_Preference \<in> UNIV. fst (fraction p) * (?prod / (snd (fraction p))))"
      using def_amount
      by simp
    hence "?voter_sum =
      ?prod * (\<Sum> p :: 'a Ordered_Preference \<in> UNIV. fst (fraction p) / (snd (fraction p)))"
      using mult_of_nat_commute sum.cong times_divide_eq_right
            vector_space_over_itself.scale_sum_right
      by (metis (mono_tags, lifting))
    hence rewrite_sum: "?voter_sum = ?prod"
      using fract conv mult_cancel_left1 of_nat_eq_iff sum.cong
      by (metis (mono_tags, lifting))
    obtain V :: "'v set" where
      fin_V: "finite V" and
      card_V_eq_sum: "card V = ?voter_sum"
      using assms infinite_arbitrarily_large
      by blast
    then obtain part :: "'a Ordered_Preference \<Rightarrow> 'v set" where
      partition: "V = \<Union> {part p | p :: 'a Ordered_Preference. p \<in> UNIV}" and
      disjoint: "\<forall> p p' :: 'a Ordered_Preference.
                      p \<noteq> p' \<longrightarrow> part p \<inter> part p' = {}" and
      card: "\<forall> p :: 'a Ordered_Preference. card (part p) = voter_amount p"
      using def_amount obtain_partition[of V UNIV voter_amount]
      by auto
    hence exactly_one_prof: "\<forall> v :: 'v \<in> V. \<exists>!p. v \<in> part p"
      by blast
    then obtain prof' :: "'v \<Rightarrow> 'a Ordered_Preference" where
      "\<forall> v :: 'v \<in> V. v \<in> part (prof' v)"
      by metis
    hence "\<forall> p :: 'a Ordered_Preference. {v :: 'v \<in> V. prof' v = p} = part p"
      using partition exactly_one_prof
      by blast
    hence "\<forall> p :: 'a Ordered_Preference.
              card {v :: 'v \<in> V. prof' v = p} = voter_amount p"
      using card
      by presburger
    moreover obtain prof :: "'v \<Rightarrow> 'a Preference_Relation" where
      prof: "prof = (\<lambda> v :: 'v. if v \<in> V then ord2pref (prof' v) else {})"
      by blast
    hence
      "\<forall> p :: 'a Ordered_Preference. \<forall> v :: 'v.
        (v \<in> {v \<in> V. prof' v = p}) = (v \<in> {v \<in> V. prof v = ord2pref p})"
      by (simp add: ord2pref_inject)
    ultimately have
      "\<forall> p :: 'a Ordered_Preference.
        vote_fraction (ord2pref p) (UNIV, V, prof) = Fract (voter_amount p) (card V)"
      using rat_number_collapse fin_V
      by simp
    moreover have
      "\<forall> p. Fract (voter_amount p) (card V) = (voter_amount p) / (card V)"
      unfolding Fract_of_int_quotient of_rat_divide
      by simp
    moreover have
      "\<forall> p. (voter_amount p) / (card V) = fst (fraction p) / snd (fraction p)"
      using rewrite_div pos_prod def_amount card_V_eq_sum rewrite_sum
      by auto
    \<comment> \<open>The following are the percentages of voters voting for each linearly ordered
        profile in (UNIV, V, prof) that equals the entries of the given vector.\<close>
    ultimately have
      "\<forall> p :: 'a Ordered_Preference. vote_fraction (ord2pref p) (UNIV, V, prof) = x'$p"
      using fract
      by presburger
    moreover have
      "\<forall> E \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}.
        \<forall> p. vote_fraction (ord2pref p) E =
            vote_fraction (ord2pref p) (UNIV, V, prof)"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by fastforce
    ultimately have all_eq_vec:
      "\<forall> p. \<forall> E \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)
          `` {(UNIV, V, prof)}. vote_fraction (ord2pref p) E = x$p"
      using Re_complex_of_real Re_divide_of_real of_rat.rep_eq of_real_of_int_eq
            injI of_rat_eq_iff the_inv_f_f rat_inv
      by (metis (mono_tags, opaque_lifting))
    moreover have election: "(UNIV, V, prof) \<in> elections_\<A> UNIV"
      unfolding elections_\<A>.simps well_formed_elections_def profile_def
      using fin_V ord2pref prof
      by auto
    hence
      "(UNIV, V, prof) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by blast
    ultimately have "\<forall> p. vote_fraction (ord2pref p) `
        anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)} \<supseteq> {x$p}"
      using image_insert insert_iff mk_disjoint_insert singletonD subsetI
      by (metis (no_types, lifting))
    hence "\<forall> p. vote_fraction (ord2pref p) `
      anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)} = {x$p}"
      using all_eq_vec
      by blast
    hence "x = anonymity_homogeneity_class
                  (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)})"
      using is_singletonI singleton_inject singleton_set_def_if_card_one vec_lambda_unique
      unfolding anonymity_homogeneity_class.simps is_singleton_altdef
                vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps
      by (metis (no_types, lifting))
    thus "x \<in> (anonymity_homogeneity_class
              :: ('a, 'v) Election set \<Rightarrow> rat^'a Ordered_Preference)
            ` anonymity_homogeneity\<^sub>\<Q> UNIV"
      unfolding anonymity_homogeneity\<^sub>\<Q>.simps quotient_def
      using election
      by blast
  qed
qed

end
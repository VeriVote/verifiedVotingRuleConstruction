(*  File:       Election_Quotients.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Quotients of Equivalence Relations on Election Sets\<close>

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
    X :: "'x set" and
    N :: "'y \<Rightarrow> nat" and
    Y :: "'y set"
  assumes
    "finite X" and
    "finite Y" and
    "sum N Y = card X"
  shows "\<exists> \<X>. X = \<Union> {\<X> i | i. i \<in> Y} \<and> (\<forall> i \<in> Y. card (\<X> i) = N i) \<and>
                (\<forall> i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
  using assms
proof (induction "card Y" arbitrary: X Y)
  case 0
  fix
    X :: "'x set" and
    Y :: "'y set"
  assume
    fin_X: "finite X" and
    card_X: "sum N Y = card X" and
    fin_Y: "finite Y" and
    card_Y: "0 = card Y"
  let ?\<X> = "\<lambda> y. {}"
  have Y_empty: "Y = {}"
    using 0 fin_Y card_Y
    by simp
  hence "sum N Y = 0"
    by simp
  hence "X = {}"
    using fin_X card_X
    by simp
  hence "X = \<Union> {?\<X> i | i. i \<in> Y}"
    by blast
  moreover have "\<forall> i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> ?\<X> i \<inter> ?\<X> j = {}"
    by blast
  ultimately show
    "\<exists> \<X>. X = \<Union> {\<X> i | i. i \<in> Y} \<and>
                (\<forall> i \<in> Y. card (\<X> i) = N i) \<and>
                (\<forall> i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
    using Y_empty
    by simp
next
  case (Suc x)
  fix
    x :: "nat" and
    X :: "'x set" and
    Y :: "'y set"
  assume
    card_Y: "Suc x = card Y" and
    fin_Y: "finite Y" and
    fin_X: "finite X" and
    card_X: "sum N Y = card X" and
    hyp:
      "\<And> Y (X::'x set).
         x = card Y \<Longrightarrow>
         finite X \<Longrightarrow>
         finite Y \<Longrightarrow>
         sum N Y = card X \<Longrightarrow>
         \<exists> \<X>.
          X = \<Union> {\<X> i | i. i \<in> Y} \<and>
                  (\<forall> i \<in> Y. card (\<X> i) = N i) \<and>
                  (\<forall> i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
  then obtain
    Y' :: "'y set" and
    y :: "'y" where
      ins_Y: "Y = insert y Y'" and
      card_Y': "card Y' = x" and
      fin_Y': "finite Y'" and
      y_not_in_Y': "y \<notin> Y'"
    using card_Suc_eq_finite
    by (metis (no_types, lifting))
  hence "N y \<le> card X"
    using card_X card_Y fin_Y le_add1 n_not_Suc_n sum.insert
    by metis
  then obtain X' :: "'x set" where
    X'_in_X: "X' \<subseteq> X" and
    card_X': "card X' = N y"
    using fin_X ex_card
    by metis
  hence "finite (X - X') \<and> card (X - X') = sum N Y'"
    using card_Y card_X fin_X fin_Y ins_Y card_Y' fin_Y'
          Suc_n_not_n add_diff_cancel_left' card_Diff_subset card_insert_if
          finite_Diff finite_subset sum.insert
    by metis
  then obtain \<X> :: "'y \<Rightarrow> 'x set" where
    part: "X - X' = \<Union> {\<X> i | i. i \<in> Y'}" and
    disj: "\<forall> i j. i \<noteq> j \<longrightarrow> i \<in> Y' \<and> j \<in> Y' \<longrightarrow> \<X> i \<inter> \<X> j = {}" and
    card: "\<forall> i \<in> Y'. card (\<X> i) = N i"
    using hyp[of Y' "X - X'"] fin_Y' card_Y'
    by auto
  then obtain \<X>' :: "'y \<Rightarrow> 'x set" where
    map': "\<X>' = (\<lambda> z. if (z = y) then X' else \<X> z)"
    by simp
  hence eq_\<X>: "\<forall> i \<in> Y'. \<X>' i = \<X> i"
    using y_not_in_Y'
    by simp
  have "Y = {y} \<union> Y'"
    using ins_Y
    by simp
  hence "\<forall> f. {f i | i. i \<in> Y} = {f y} \<union> {f i | i. i \<in> Y'}"
    by blast
  hence "{\<X>' i | i. i \<in> Y} = {\<X>' y} \<union> {\<X>' i | i. i \<in> Y'}"
    by metis
  hence "\<Union> {\<X>' i | i. i \<in> Y} = \<X>' y \<union> \<Union> {\<X>' i | i. i \<in> Y'}"
    by simp
  also have "\<X>' y = X'"
    using map'
    by presburger
  also have "\<Union> {\<X>' i | i. i \<in> Y'} = \<Union> {\<X> i | i. i \<in> Y'}"
    using eq_\<X>
    by blast
  finally have part': "X = \<Union> {\<X>' i | i. i \<in> Y}"
    using part Diff_partition X'_in_X
    by metis
  have "\<forall> i \<in> Y'. \<X>' i \<subseteq> X - X'"
    using part eq_\<X> Setcompr_eq_image UN_upper
    by metis
  hence "\<forall> i \<in> Y'. \<X>' i \<inter> X' = {}"
    by blast
  hence "\<forall> i \<in> Y'. \<X>' i \<inter> \<X>' y = {}"
    using map'
    by simp
  hence "\<forall> i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X>' i \<inter> \<X>' j = {}"
    using map' disj ins_Y inf.commute insertE
    by (metis (no_types, lifting))
  moreover have "\<forall> i \<in> Y. card (\<X>' i) = N i"
    using map' card card_X' ins_Y
    by simp
  ultimately show
    "\<exists> \<X>. X = \<Union> {\<X> i | i. i \<in> Y} \<and>
                (\<forall> i \<in> Y. card (\<X> i) = N i) \<and>
                    (\<forall> i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
    using part'
    by blast
qed

subsection \<open>Anonymity Quotient: Grid\<close>

\<comment> \<open>The election equivalence classes of the anonymity equivalence relation.\<close>
fun anonymity\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anonymity\<^sub>\<Q> A = quotient (elections_\<A> A) (anonymity\<^sub>\<R> (elections_\<A> A))"

\<comment> \<open>Counts the occurrences of a ballot per election in a set of elections
    if the occurrences of the ballot per election coincide for all elections in the set.\<close>
fun vote_count\<^sub>\<Q> :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election set \<Rightarrow> nat" where
  "vote_count\<^sub>\<Q> p = \<pi>\<^sub>\<Q> (vote_count p)"

fun anonymity_class :: "('a::finite, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec" where
  "anonymity_class X = (\<chi> p. vote_count\<^sub>\<Q> (ord2pref p) X)"

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
  assumes "infinite (UNIV::('v set))"
  shows "bij_betw (anonymity_class::('a::finite, 'v) Election set \<Rightarrow> nat^('a Ordered_Preference))
              (anonymity\<^sub>\<Q> (UNIV::'a set)) (UNIV::(nat^('a Ordered_Preference)) set)"
proof (unfold bij_betw_def inj_on_def, standard, standard, standard, standard)
  fix
    X :: "('a, 'v) Election set" and
    Y :: "('a, 'v) Election set"
  assume
    class_X: "X \<in> anonymity\<^sub>\<Q> UNIV" and
    class_Y: "Y \<in> anonymity\<^sub>\<Q> UNIV" and
    eq_vec: "anonymity_class X = anonymity_class Y"
  have "\<forall> E \<in> elections_\<A> UNIV. finite (voters_\<E> E)"
    by simp
  hence "\<forall> (E, E') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV). finite (voters_\<E> E)"
    by simp
  moreover have subset: "elections_\<A> UNIV \<subseteq> valid_elections"
    by simp
  ultimately have
    "\<forall> (E, E') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV). \<forall> p. vote_count p E = vote_count p E'"
    using anon_rel_vote_count
    by blast
  hence vote_count_invar: "\<forall> p. (vote_count p) respects (anonymity\<^sub>\<R> (elections_\<A> UNIV))"
    unfolding congruent_def
    by blast
  have "equiv valid_elections (anonymity\<^sub>\<R> valid_elections)"
    using rel_ind_by_group_act_equiv[of "anonymity\<^sub>\<G>" "valid_elections" "\<phi>_anon valid_elections"]
          rel_ind_by_coinciding_action_on_subset_eq_restr
    by (simp add: anonymous_group_action.group_action_axioms)
  moreover have
    "\<forall> \<pi> \<in> carrier anonymity\<^sub>\<G>.
      \<forall> E \<in> elections_\<A> UNIV.
        \<phi>_anon (elections_\<A> UNIV) \<pi> E = \<phi>_anon valid_elections \<pi> E"
    by simp
  ultimately have equiv_rel:
    "equiv (elections_\<A> UNIV) (anonymity\<^sub>\<R> (elections_\<A> UNIV))"
    using subset rel_ind_by_coinciding_action_on_subset_eq_restr[of "elections_\<A> UNIV"
            "valid_elections" "carrier anonymity\<^sub>\<G>" "\<phi>_anon (elections_\<A> UNIV)"]
          equiv_rel_restr
    unfolding anonymity\<^sub>\<R>.simps
    by (metis (no_types))
  with vote_count_invar
  have quotient_count: "\<forall> X \<in> anonymity\<^sub>\<Q> UNIV. \<forall> p. \<forall> E \<in> X. vote_count\<^sub>\<Q> p X = vote_count p E"
    using pass_to_quotient[of "anonymity\<^sub>\<R> (elections_\<A> UNIV)"]
    unfolding anonymity\<^sub>\<Q>.simps anonymity\<^sub>\<R>.simps vote_count\<^sub>\<Q>.simps
    by metis
  moreover from equiv_rel
  obtain
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election" where
      E_in_X: "E \<in> X" and
      E'_in_Y: "E' \<in> Y"
    using class_X class_Y equiv_Eps_in
    unfolding anonymity\<^sub>\<Q>.simps
    by metis
  ultimately have "\<forall> p. vote_count\<^sub>\<Q> p X = vote_count p E \<and> vote_count\<^sub>\<Q> p Y = vote_count p E'"
    using class_X class_Y
    by blast
  moreover with eq_vec have "\<forall> p. vote_count\<^sub>\<Q> (ord2pref p) X = vote_count\<^sub>\<Q> (ord2pref p) Y"
    unfolding anonymity_class.simps
    using UNIV_I vec_lambda_inverse
    by metis
  ultimately have "\<forall> p. vote_count (ord2pref p) E = vote_count (ord2pref p) E'"
    by simp
  hence eq: "\<forall> p \<in> {p. linear_order_on (UNIV::'a set) p}. vote_count p E = vote_count p E'"
    using pref2ord_inverse
    by metis
  from equiv_rel class_X class_Y have subset_fixed_alts:
    "X \<subseteq> elections_\<A> UNIV \<and> Y \<subseteq> elections_\<A> UNIV"
    unfolding anonymity\<^sub>\<Q>.simps
    using in_quotient_imp_subset
    by blast
  hence eq_alts: "alternatives_\<E> E = UNIV \<and> alternatives_\<E> E' = UNIV"
    using E_in_X E'_in_Y
    unfolding elections_\<A>.simps
    by blast
  with subset_fixed_alts have eq_complement:
    "\<forall> p \<in> UNIV - {p. linear_order_on (UNIV::'a set) p}.
      {v \<in> voters_\<E> E. profile_\<E> E v = p} = {} \<and> {v \<in> voters_\<E> E'. profile_\<E> E' v = p} = {}"
    using E_in_X E'_in_Y
    unfolding elections_\<A>.simps valid_elections_def profile_def
    by auto
  hence "\<forall> p \<in> UNIV - {p. linear_order_on (UNIV::'a set) p}.
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
  have
    "(\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {}) \<and> (\<forall> v. v \<notin> voters_\<E> E' \<longrightarrow> profile_\<E> E' v = {})"
    by simp
  ultimately have "(E, E') \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV)"
    using eq_alts vote_count_anon_rel
    by metis
  hence "anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {E} =
            anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {E'}"
    using equiv_rel equiv_class_eq
    by metis
  also have "anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {E} = X"
    using E_in_X class_X equiv_rel Image_singleton_iff equiv_class_eq quotientE
    unfolding anonymity\<^sub>\<Q>.simps
    by (metis (no_types, lifting))
  also have "anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {E'} = Y"
    using E'_in_Y class_Y equiv_rel Image_singleton_iff equiv_class_eq quotientE
    unfolding anonymity\<^sub>\<Q>.simps
    by (metis (no_types, lifting))
  finally show "X = Y"
    by simp
next
  have subset: "elections_\<A> UNIV \<subseteq> valid_elections"
      by simp
  have "equiv valid_elections (anonymity\<^sub>\<R> valid_elections)"
    using rel_ind_by_group_act_equiv[of "anonymity\<^sub>\<G>" "valid_elections" "\<phi>_anon valid_elections"]
          rel_ind_by_coinciding_action_on_subset_eq_restr
    by (simp add: anonymous_group_action.group_action_axioms)
  (* TODO: Remove this duplicate, already shown in the previous subgoal... *)
  moreover have
    "\<forall> \<pi> \<in> carrier anonymity\<^sub>\<G>.
      \<forall> E \<in> elections_\<A> UNIV.
        \<phi>_anon (elections_\<A> UNIV) \<pi> E = \<phi>_anon valid_elections \<pi> E"
    using subset
    unfolding \<phi>_anon.simps
    by simp
  ultimately have equiv_rel:
    "equiv (elections_\<A> UNIV) (anonymity\<^sub>\<R> (elections_\<A> UNIV))"
    using subset equiv_rel_restr rel_ind_by_coinciding_action_on_subset_eq_restr[of
            "elections_\<A> UNIV" "valid_elections" "carrier anonymity\<^sub>\<G>"
            "\<phi>_anon (elections_\<A> UNIV)"]
    unfolding anonymity\<^sub>\<R>.simps
    by (metis (no_types))
  have "(UNIV::((nat, 'a Ordered_Preference) vec set)) \<subseteq>
      (anonymity_class::('a, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec) `
      anonymity\<^sub>\<Q> UNIV"
  proof (unfold anonymity_class.simps, safe)
    fix x :: "(nat, 'a Ordered_Preference) vec"
    have "finite (UNIV::('a Ordered_Preference set))"
      by simp
    hence "finite {x$i | i. i \<in> UNIV}"
      using finite_Atleast_Atmost_nat
      by blast
    hence "sum (\<lambda> i. x$i) UNIV < \<infinity>"
      using enat_ord_code
      by simp
    moreover have "0 \<le> sum (\<lambda> i. x$i) UNIV"
      by blast
    ultimately obtain V :: "'v set" where
      fin_V: "finite V" and
      "card V = sum (\<lambda> i. x$i) UNIV"
      using assms infinite_arbitrarily_large
      by metis
    then obtain X' :: "'a Ordered_Preference \<Rightarrow> 'v set" where
      card': "\<forall> i. card (X' i) = x$i" and
      partition': "V = \<Union> {X' i | i. i \<in> UNIV}" and
      disjoint': "\<forall> i j. i \<noteq> j \<longrightarrow> X' i \<inter> X' j = {}"
      using obtain_partition[of V UNIV "($) x"]
      by auto
    obtain X :: "'a Preference_Relation \<Rightarrow> 'v set" where
      def_X: "X = (\<lambda> i. if (i \<in> {i. linear_order i}) then X' (pref2ord i) else {})"
      by simp
    hence "{X i | i. i \<notin> {i. linear_order i}} \<subseteq> {{}}"
      by auto
    moreover have
      "{X i | i. i \<in> {i. linear_order i}} = {X' (pref2ord i) | i. i \<in> {i. linear_order i}}"
      using def_X
      by metis
    moreover have
      "{X i | i. i \<in> UNIV} =
          {X i | i. i \<in> {i. linear_order i}} \<union> {X i | i. i \<in> UNIV - {i. linear_order i}}"
      by blast
    ultimately have
      "{X i | i. i \<in> UNIV} = {X' (pref2ord i) | i. i \<in> {i. linear_order i}} \<or>
        {X i | i. i \<in> UNIV} = {X' (pref2ord i) | i. i \<in> {i. linear_order i}} \<union> {{}}"
      by auto
    also have "{X' (pref2ord i) | i. i \<in> {i. linear_order i}} = {X' i | i. i \<in> UNIV}"
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
      p_def: "p = (\<lambda> v. if v \<in> V then p' v else {})"
      by simp
    hence lin_ord: "\<forall> v \<in> V. linear_order (p v)"
      using def_X p_X p_disj
      by fastforce
    hence valid: "(UNIV, V, p) \<in> elections_\<A> UNIV"
      using fin_V
      unfolding p_def elections_\<A>.simps valid_elections_def profile_def
      by auto
    hence "\<forall> i. \<forall> E \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}.
              vote_count i E = vote_count i (UNIV, V, p)"
      using anon_rel_vote_count[of "(UNIV, V, p)" _ "elections_\<A> UNIV"]
            fin_V subset
      by simp
    moreover have "(UNIV, V, p) \<in> anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}"
      using equiv_rel valid
      unfolding Image_def equiv_def refl_on_def
      by blast
    ultimately have eq_vote_count:
      "\<forall> i. vote_count i ` (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) =
            {vote_count i (UNIV, V, p)}"
      by blast
    have "\<forall> i. \<forall> v \<in> V. p v = i \<longleftrightarrow> v \<in> X i"
      using p_X p_disj
      unfolding p_def
      by metis
    hence "\<forall> i. {v \<in> V. p v = i} = {v \<in> V. v \<in> X i}"
      by blast
    moreover have "\<forall> i. X i \<subseteq> V"
      using partition
      by blast
    ultimately have rewr_preimg: "\<forall> i. {v \<in> V. p v = i} = X i"
      by auto
    hence "\<forall> i \<in> {i. linear_order i}. vote_count i (UNIV, V, p) = x$(pref2ord i)"
      using def_X card'
      by simp
    hence "\<forall> i \<in> {i. linear_order i}.
       vote_count i ` (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) = {x$(pref2ord i)}"
      using eq_vote_count
      by metis
    hence
      "\<forall> i \<in> {i. linear_order i}.
        vote_count\<^sub>\<Q> i (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) = x$(pref2ord i)"
      unfolding vote_count\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
      using is_singleton_altdef singleton_set_def_if_card_one
      by fastforce
    hence "\<forall> i. vote_count\<^sub>\<Q> (ord2pref i) (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)})
        = x$i"
      using ord2pref ord2pref_inverse
      by metis
    hence "anonymity_class (anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)}) = x"
      using anonymity_class.simps vec_lambda_unique
      by (metis (no_types, lifting))
    moreover have
      "anonymity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, p)} \<in> anonymity\<^sub>\<Q> UNIV"
      using valid
      unfolding anonymity\<^sub>\<Q>.simps quotient_def
      by blast
    ultimately show
      "x \<in> (\<lambda> X::(('a, 'v) Election set). \<chi> p. vote_count\<^sub>\<Q> (ord2pref p) X) ` anonymity\<^sub>\<Q> UNIV"
      using anonymity_class.elims
      by blast
  qed
  thus "(anonymity_class::('a, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec) `
          anonymity\<^sub>\<Q> UNIV = (UNIV::((nat, 'a Ordered_Preference) vec set))"
    by blast
qed

subsection \<open>Homogeneity Quotient: Simplex\<close>

fun vote_fraction :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election \<Rightarrow> rat" where
  "vote_fraction r E =
    (if (finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {})
      then (Fract (vote_count r E) (card (voters_\<E> E))) else 0)"

fun anonymity_homogeneity\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "anonymity_homogeneity\<^sub>\<R> \<E> =
    {(E, E') | E E'. E \<in> \<E> \<and> E' \<in> \<E> \<and> (finite (voters_\<E> E) = finite (voters_\<E> E'))
                    \<and> (\<forall> r. vote_fraction r E = vote_fraction r E')}"

fun anonymity_homogeneity\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anonymity_homogeneity\<^sub>\<Q> A = quotient (elections_\<A> A) (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))"

fun vote_fraction\<^sub>\<Q> :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election set \<Rightarrow> rat" where
  "vote_fraction\<^sub>\<Q> p = \<pi>\<^sub>\<Q> (vote_fraction p)"

fun anonymity_homogeneity_class :: "('a::finite, 'v) Election set
        \<Rightarrow> (rat, 'a Ordered_Preference) vec" where
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
  "vote_simplex \<equiv> insert 0 (rat_vector_set (convex hull (standard_basis :: (real^'b) set)))"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma convex_combination_in_convex_hull:
  fixes
    X :: "(real^'b) set" and
    x :: "real^'b"
  assumes "\<exists> f::(real^'b) \<Rightarrow> real.
            sum f X = 1 \<and> (\<forall> x \<in> X. f x \<ge> 0) \<and> x = sum (\<lambda> x. (f x) *\<^sub>R x) X"
  shows "x \<in> convex hull X"
  using assms
proof (induction "card X" arbitrary: X x)
  case 0
  fix
    X :: "(real^'b) set" and
    x :: "real^'b"
  assume
    "0 = card X" and
    "\<exists> f. sum f X = 1 \<and> (\<forall> x \<in> X. 0 \<le> f x) \<and> x = (\<Sum> x \<in> X. f x *\<^sub>R x)"
  hence "(\<forall> f. sum f X = 0) \<and> (\<exists> f. sum f X = 1)"
    using card_0_eq empty_iff sum.infinite sum.neutral zero_neq_one
    by metis
  hence "\<exists> f. sum f X = 1 \<and> sum f X = 0"
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
    "\<exists> f. sum f X = 1 \<and> (\<forall> x \<in> X. 0 \<le> f x) \<and> x = (\<Sum> x \<in> X. f x *\<^sub>R x)" and
    hyp: "\<And> (X::(real^'b) set) x. n = card X
            \<Longrightarrow> \<exists> f. sum f X = 1 \<and> (\<forall> x \<in> X. 0 \<le> f x) \<and> x = (\<Sum> x \<in> X. f x *\<^sub>R x)
            \<Longrightarrow> x \<in> convex hull X"
  then obtain f :: "(real^'b) \<Rightarrow> real" where
    sum: "sum f X = 1" and
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
    hence card_X_gt_1: "card X > 1"
      using card
      by simp
    have "(\<forall> y \<in> X. f y \<ge> 1) \<longrightarrow> sum f X \<ge> sum (\<lambda> x. 1) X"
      using fin sum_mono
      by metis
    moreover have "sum (\<lambda> x. 1) X = card X"
      by force
    ultimately have "(\<forall> y \<in> X. f y \<ge> 1) \<longrightarrow> card X \<le> sum f X"
      by force
    hence "(\<forall> y \<in> X. f y \<ge> 1) \<longrightarrow> 1 < sum f X"
      using card_X_gt_1
      by linarith
    then obtain y :: "real^'b" where
      y_in_X: "y \<in> X" and
      f_y_lt_one: "f y < 1"
      using sum
      by auto
    hence "1 - f y \<noteq> 0 \<and> x = f y *\<^sub>R y + (\<Sum> x \<in> X - {y}. f x *\<^sub>R x)"
      using fin sum.remove x_sum
      by simp
    moreover have "\<forall> \<alpha> \<noteq> 0. (\<Sum> x \<in> X - {y}. f x *\<^sub>R x) = \<alpha> *\<^sub>R (\<Sum> x \<in> X - {y}. (f x / \<alpha>) *\<^sub>R x)"
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
    moreover have "sum f' (X - {y}) = (sum (\<lambda> x. f x) (X - {y})) / (1 - f y)"
      unfolding def' sum_divide_distrib
      by simp
    moreover have "(sum (\<lambda> x. f x) (X - {y})) / (1 - f y) = (1 - f y) / (1 - f y)"
      using sum y_in_X
      by (simp add: fin sum.remove)
    moreover have "(1 - f y) / (1 - f y) = 1"
      using f_y_lt_one
      by simp
    ultimately have
      "sum f' (X - {y}) = 1 \<and> (\<forall> x \<in> X - {y}. 0 \<le> f' x)
            \<and> (\<Sum> x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) = (\<Sum> x \<in> X - {y}. f' x *\<^sub>R x)"
      using def'
      by metis
    hence "\<exists> f'. sum f' (X - {y}) = 1 \<and> (\<forall> x \<in> X - {y}. 0 \<le> f' x)
              \<and> (\<Sum> x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) = (\<Sum> x \<in> X - {y}. f' x *\<^sub>R x)"
      by metis
    moreover have "card (X - {y}) = n"
      using card y_in_X
      by simp
    ultimately have "(\<Sum> x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) \<in> convex hull (X - {y})"
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

lemma standard_simplex_rewrite: "convex hull standard_basis
        = {v::(real^'b). (\<forall> i. v$i \<ge> 0) \<and> sum (($) v) UNIV = 1}"
proof (unfold convex_def hull_def, standard)
  let ?simplex = "{v:: (real^'b). (\<forall> i. v$i \<ge> 0) \<and> sum (($) v) UNIV = 1}"
  have fin_dim: "finite (UNIV::'b set)"
    by simp
  have "\<forall> x::(real^'b). \<forall> y. sum (($) (x + y)) UNIV = sum (($) x) UNIV + sum (($) y) UNIV"
    by (simp add: sum.distrib)
  hence "\<forall> x::(real^'b). \<forall> y. \<forall> u v.
    sum (($) (u *\<^sub>R x + v *\<^sub>R y)) UNIV = sum (($) (u *\<^sub>R x)) UNIV + sum (($) (v *\<^sub>R y)) UNIV"
    by blast
  moreover have "\<forall> x u. sum (($) (u *\<^sub>R x)) UNIV = u *\<^sub>R (sum (($) x) UNIV)"
    using scaleR_right.sum sum.cong vector_scaleR_component
    by (metis (mono_tags, lifting))
  ultimately have "\<forall> x::(real^'b). \<forall> y. \<forall> u v.
    sum (($) (u *\<^sub>R x + v *\<^sub>R y)) UNIV = u *\<^sub>R (sum (($) x) UNIV) + v *\<^sub>R (sum (($) y) UNIV)"
    by (metis (no_types))
  moreover have "\<forall> x \<in> ?simplex. sum (($) x) UNIV = 1"
    by simp
  ultimately have
    "\<forall> x \<in> ?simplex. \<forall> y \<in> ?simplex. \<forall> u v. sum (($) (u *\<^sub>R x + v *\<^sub>R y)) UNIV = u *\<^sub>R 1 + v *\<^sub>R 1"
    by (metis (no_types, lifting))
  hence "\<forall> x \<in> ?simplex. \<forall> y \<in> ?simplex. \<forall> u v. sum (($) (u *\<^sub>R x + v *\<^sub>R y)) UNIV = u + v"
    by simp
  moreover have
    "\<forall> x \<in> ?simplex. \<forall> y \<in> ?simplex. \<forall> u \<ge> 0. \<forall> v \<ge> 0.
      u + v = 1 \<longrightarrow> (\<forall> i. (u *\<^sub>R x + v *\<^sub>R y)$i \<ge> 0)"
    by simp
  ultimately have simplex_convex:
    "\<forall> x \<in> ?simplex. \<forall> y \<in> ?simplex. \<forall> u \<ge> 0. \<forall> v \<ge> 0.
      u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> ?simplex"
    by simp
  have entries: "\<forall> v::(real^'b) \<in> standard_basis. \<exists> b. v$b = 1 \<and> (\<forall> c. c \<noteq> b \<longrightarrow> v$c = 0)"
    unfolding standard_basis_def
    by simp
  then obtain one :: "real^'b \<Rightarrow> 'b" where
    def: "\<forall> v \<in> standard_basis. v$(one v) = 1 \<and> (\<forall> i \<noteq> one v. v$i = 0)"
    by metis
  hence "\<forall> v::(real^'b) \<in> standard_basis. \<forall> b. v$b = 0 \<or> v$b = 1"
    by metis
  hence geq_0: "\<forall> v::(real^'b) \<in> standard_basis. \<forall> b. v$b \<ge> 0"
    using dual_order.refl zero_less_one_class.zero_le_one
    by metis
  moreover have "\<forall> v::(real^'b) \<in> standard_basis.
      sum (($) v) UNIV = sum (($) v) (UNIV - {one v}) + v$(one v)"
    unfolding def
    using add.commute finite insert_UNIV sum.insert_remove
    by metis
  moreover have "\<forall> v \<in> standard_basis. sum (($) v) (UNIV - {one v}) + v$(one v) = 1"
    using def
    by simp
  ultimately have "standard_basis \<subseteq> ?simplex"
    by force
  with simplex_convex
  have "?simplex \<in>
      {t. (\<forall> x \<in> t. \<forall> y \<in> t. \<forall> u \<ge> 0. \<forall> v \<ge> 0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t)
            \<and> standard_basis \<subseteq> t}"
    by blast
  thus "\<Inter> {t. (\<forall> x \<in> t. \<forall> y \<in> t. \<forall> u \<ge> 0. \<forall> v \<ge> 0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t)
            \<and> standard_basis \<subseteq> t} \<subseteq> ?simplex"
    by blast
next
  show "{v. (\<forall> i. 0 \<le> v $ i) \<and> sum (($) v) UNIV = 1} \<subseteq>
      \<Inter> {t. (\<forall> x \<in> t. \<forall> y \<in> t. \<forall> u \<ge> 0. \<forall> v \<ge> 0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t)
              \<and> (standard_basis::((real^'b) set)) \<subseteq> t}"
  proof
    fix
      x :: "real^'b" and
      X :: "(real^'b) set"
    assume convex_comb: "x \<in> {v. (\<forall> i. 0 \<le> v $ i) \<and> sum (($) v) UNIV = 1}"
    have "\<forall> v \<in> standard_basis. \<exists> b. v$b = 1 \<and> (\<forall> b' \<noteq> b. v$b' = 0)"
      unfolding standard_basis_def
      by simp
    then obtain ind :: "(real^'b) \<Rightarrow> 'b" where
      ind_1: "\<forall> v \<in> standard_basis. v$(ind v) = 1" and
      ind_0: "\<forall> v \<in> standard_basis. \<forall> b \<noteq> (ind v). v$b = 0"
      by metis
    hence "\<forall> v v'. v \<in> standard_basis \<and> v' \<in> standard_basis \<longrightarrow> ind v = ind v'
              \<longrightarrow> (\<forall> b. v$b = v'$b)"
      by metis
    hence inj_ind:
      "\<forall> v v'. v \<in> standard_basis \<and> v' \<in> standard_basis \<longrightarrow> ind v = ind v' \<longrightarrow> v = v'"
      unfolding vec_eq_iff
      by simp
    hence "inj_on ind standard_basis"
      unfolding inj_on_def
      by blast
    hence bij: "bij_betw ind standard_basis (ind ` standard_basis)"
      unfolding bij_betw_def
      by simp
    obtain ind_inv :: "'b \<Rightarrow> (real^'b)" where
      char_vec: "ind_inv = (\<lambda> b. (\<chi> i. if i = b then 1 else 0))"
      by blast
    hence in_basis: "\<forall> b. ind_inv b \<in> standard_basis"
      unfolding standard_basis_def
      by simp
    moreover from this
    have ind_inv_map: "\<forall> b. ind (ind_inv b) = b"
      using char_vec ind_0 ind_1 axis_def axis_nth zero_neq_one
      by metis
    ultimately have "\<forall> b. \<exists> v. v \<in> standard_basis \<and> b = ind v"
      by metis
    hence univ: "ind ` standard_basis = UNIV"
      by blast
    have bij_inv: "bij_betw ind_inv UNIV standard_basis"
      using ind_inv_map bij bij_betw_byWitness[of UNIV ind] in_basis inj_ind
      unfolding image_subset_iff
      by simp
    obtain f :: "(real^'b) \<Rightarrow> real" where
      def: "f = (\<lambda> v. if v \<in> standard_basis then x$(ind v) else 0)"
      by blast
    hence "sum f standard_basis = sum (\<lambda> v. x$(ind v)) standard_basis"
      by simp
    also have "sum (\<lambda> v. x$(ind v)) standard_basis = sum (($) x \<circ> ind) standard_basis"
      unfolding comp_def
      by simp
    also have "... = sum (($) x) (ind ` standard_basis)"
      using sum_comp[of "ind" "standard_basis" "ind ` standard_basis" "($) x"] bij
      by simp
    also have "... = sum (($) x) UNIV"
      using univ
      by simp
    finally have "sum f standard_basis = sum (($) x) UNIV"
      using univ
      by simp
    hence sum_1: "sum f standard_basis = 1"
      using convex_comb
      by simp
    have nonneg: "\<forall> v \<in> standard_basis. f v \<ge> 0"
      using def convex_comb
      by simp
    have "\<forall> v \<in> standard_basis. \<forall> i. v$i = (if i = ind v then 1 else 0)"
      using ind_1 ind_0
      by fastforce
    hence "\<forall> v \<in> standard_basis. \<forall> i. x$(ind v) * v$i = (if i = ind v then x$(ind v) else 0)"
      by auto
    hence "\<forall> v \<in> standard_basis. (\<chi> i. x$(ind v) * v$i)
          = (\<chi> i. if i = ind v then x$(ind v) else 0)"
      by fastforce
    moreover have "\<forall> v. (x$(ind v)) *\<^sub>R v = (\<chi> i. x$(ind v) * v$i)"
      unfolding scaleR_vec_def
      by simp
    ultimately have
      "\<forall> v \<in> standard_basis. (x$(ind v)) *\<^sub>R v = (\<chi> i. if i = ind v then x$(ind v) else 0)"
      by simp
    moreover have "sum (\<lambda> x. (f x) *\<^sub>R x) standard_basis
          = sum (\<lambda> v. (x$(ind v)) *\<^sub>R v) standard_basis"
      unfolding def
      by simp
    ultimately have "sum (\<lambda> x. (f x) *\<^sub>R x) standard_basis
          = sum (\<lambda> v. (\<chi> i. if i = ind v then x$(ind v) else 0)) standard_basis"
      by force
    also have "... = sum (\<lambda> b. (\<chi> i. if i = ind (ind_inv b) then x$(ind (ind_inv b)) else 0)) UNIV"
      using bij_inv sum_comp
      unfolding comp_def
      by blast
    also have "... = sum (\<lambda> b. (\<chi> i. if i = b then x$b else 0)) UNIV"
      using ind_inv_map
      by presburger
    finally have "sum (\<lambda> x. (f x) *\<^sub>R x) standard_basis
          = sum (\<lambda> b. (\<chi> i. if i = b then x$b else 0)) UNIV"
      by simp
    moreover have "\<forall> b. (sum (\<lambda> b. (\<chi> i. if i = b then x$b else 0)) UNIV)$b
          = sum (\<lambda> b'. (\<chi> i. if i = b' then x$b' else 0)$b) UNIV"
      using sum_component
      by blast
    moreover have "\<forall> b. (\<lambda> b'. (\<chi> i. if i = b' then x$b' else 0)$b)
          = (\<lambda> b'. if b' = b then x$b else 0)"
      by force
    moreover have "\<forall> b. sum (\<lambda> b'. if b' = b then x$b else 0) UNIV
          = x$b + sum (\<lambda> b'. 0) (UNIV - {b})"
      by simp
    ultimately have "\<forall> b. (sum (\<lambda> x. (f x) *\<^sub>R x) standard_basis)$b = x$b"
      by simp
    hence "sum (\<lambda> x. (f x) *\<^sub>R x) standard_basis = x"
      unfolding vec_eq_iff
      by simp
    hence "\<exists> f::(real^'b) \<Rightarrow> real.
              sum f standard_basis = 1 \<and> (\<forall> x \<in> standard_basis. f x \<ge> 0)
            \<and> x = sum (\<lambda> x. (f x) *\<^sub>R x) standard_basis"
      using sum_1 nonneg
      by blast
    hence "x \<in> convex hull (standard_basis::((real^'b) set))"
      using convex_combination_in_convex_hull
      by blast
    thus "x \<in> \<Inter> {t. (\<forall> x \<in> t. \<forall> y \<in> t. \<forall> u \<ge> 0. \<forall> v \<ge> 0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t)
                  \<and> (standard_basis::((real^'b) set)) \<subseteq> t}"
      unfolding convex_def hull_def
      by blast
  qed
qed

lemma fract_distr_helper:
  fixes
     a :: "int" and
     b :: "int" and 
     c :: "int"
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
    fix
      E :: "('a, 'v) Election" and
      E' :: "('a, 'v) Election" and
      F :: "('a, 'v) Election"
    assume
      rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> X" and
      rel': "(E', F) \<in> anonymity_homogeneity\<^sub>\<R> X"
    hence fin: "finite (voters_\<E> E')"
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
  shows "sum (\<lambda> a. Fract (f a) b) A = Fract (sum f A) b"
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
  hence "sum (\<lambda> a. Fract (f a) b) A = 0 \<and> sum f A = 0"
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
           n = card (A::'x set) \<Longrightarrow>
           finite A \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (\<Sum> a \<in> A. Fract (f a) b) = Fract (sum f A) b"
  hence "A \<noteq> {}"
    by auto
  then obtain c :: "'x" where
    c_in_A: "c \<in> A"
    by blast
  hence "(\<Sum> a \<in> A. Fract (f a) b) = (\<Sum> a \<in> A - {c}. Fract (f a) b) + Fract (f c) b"
    using fin_A
    by (simp add: sum_diff1)
  also have "... = Fract (sum f (A - {c})) b + Fract (f c) b"
    using hyp card_A fin_A b_non_zero c_in_A Diff_empty card_Diff_singleton
          diff_Suc_1 finite_Diff_insert
    by metis
  also have "... = Fract (sum f (A - {c}) + f c) b"
    using c_in_A b_non_zero fract_distr_helper
    by metis
  also have "... = Fract (sum f A) b"
    using c_in_A fin_A
    by (simp add: sum_diff1)
  finally show "(\<Sum> a \<in> A. Fract (f a) b) = Fract (sum f A) b"
    by blast
qed

subsubsection \<open>Simplex Bijection\<close>

text \<open>
  We assume all our elections to consist of a fixed finite alternative set of size n and
  finite subsets of an infinite voter universe. Profiles are linear orders on the alternatives.
  Then we can work on the standard simplex of dimension n! instead of the equivalence
  classes of the equivalence relation for anonymous + homogeneous voting rules (anon hom):
  Each dimension corresponds to one possible linear order on the alternative set,
  i.e., the possible preferences.
  Each equivalence class of elections corresponds to a vector whose entries denote the fraction
  of voters per election in that class who vote the respective corresponding preference.
\<close>
theorem anonymity_homogeneity\<^sub>\<Q>_isomorphism:
  assumes "infinite (UNIV::('v set))"
  shows
    "bij_betw (anonymity_homogeneity_class::('a::finite, 'v) Election set \<Rightarrow>
        rat^('a Ordered_Preference)) (anonymity_homogeneity\<^sub>\<Q> (UNIV::'a set))
          (vote_simplex :: (rat^('a Ordered_Preference)) set)"
proof (unfold bij_betw_def inj_on_def, standard, standard, standard, standard)
  fix
    X :: "('a, 'v) Election set" and
    Y :: "('a, 'v) Election set"
  assume
    class_X: "X \<in> anonymity_homogeneity\<^sub>\<Q> UNIV" and
    class_Y: "Y \<in> anonymity_homogeneity\<^sub>\<Q> UNIV" and
    eq_vec: "anonymity_homogeneity_class X = anonymity_homogeneity_class Y"
  have equiv: "equiv (elections_\<A> UNIV) (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV))"
    using anonymity_homogeneity_is_equivalence CollectD IntD1 inf_commute
    unfolding elections_\<A>.simps
    by (metis (no_types, lifting))
  hence subset: "X \<noteq> {} \<and> X \<subseteq> elections_\<A> UNIV \<and> Y \<noteq> {} \<and> Y \<subseteq> elections_\<A> UNIV"
    using class_X class_Y in_quotient_imp_non_empty in_quotient_imp_subset
    unfolding anonymity_homogeneity\<^sub>\<Q>.simps
    by blast
  then obtain E :: "('a, 'v) Election" and
              E' :: "('a, 'v) Election" where
    E_in_X: "E \<in> X" and
    E'_in_Y: "E' \<in> Y"
    by blast
  hence class_X_E: "anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {E} = X"
    using class_X equiv Image_singleton_iff equiv_class_eq quotientE
    unfolding anonymity_homogeneity\<^sub>\<Q>.simps
    by (metis (no_types, opaque_lifting))
  hence "\<forall> F \<in> X. (E, F) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)"
    unfolding Image_def
    by blast
  hence "\<forall> F \<in> X. \<forall> p. vote_fraction p F = vote_fraction p E"
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by fastforce
  hence "\<forall> p. vote_fraction p ` X = {vote_fraction p E}"
    using E_in_X
    by blast
  hence "\<forall> p. vote_fraction\<^sub>\<Q> p X = vote_fraction p E"
    using is_singletonI singleton_set_def_if_card_one the_elem_eq
    unfolding is_singleton_altdef vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
    by metis
  hence eq_X_E: "\<forall> p. (anonymity_homogeneity_class X)$p = vote_fraction (ord2pref p) E"
    unfolding anonymity_homogeneity_class.simps
    using vec_lambda_beta
    by metis
  have class_Y_E': "anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {E'} = Y"
    using class_Y equiv E'_in_Y Image_singleton_iff equiv_class_eq quotientE
    unfolding anonymity_homogeneity\<^sub>\<Q>.simps
    by (metis (no_types, opaque_lifting))
  hence "\<forall> F \<in> Y. (E', F) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)"
    unfolding Image_def
    by blast
  hence "\<forall> F \<in> Y. \<forall> p. vote_fraction p E' = vote_fraction p F"
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast
  hence "\<forall> p. vote_fraction p ` Y = {vote_fraction p E'}"
    using E'_in_Y
    by fastforce
  hence "\<forall> p. vote_fraction\<^sub>\<Q> p Y = vote_fraction p E'"
    using is_singletonI singleton_set_def_if_card_one the_elem_eq
    unfolding is_singleton_altdef vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
    by metis
  hence eq_Y_E': "\<forall> p. (anonymity_homogeneity_class Y)$p = vote_fraction (ord2pref p) E'"
    unfolding anonymity_homogeneity_class.simps
    using vec_lambda_beta
    by metis
  with eq_X_E eq_vec
  have "\<forall> p. vote_fraction (ord2pref p) E = vote_fraction (ord2pref p) E'"
    by metis
  hence eq_ord: "\<forall> p. linear_order p \<longrightarrow> vote_fraction p E = vote_fraction p E'"
    using mem_Collect_eq pref2ord_inverse
    by metis
  have "(\<forall> v. v \<in> voters_\<E> E \<longrightarrow> linear_order (profile_\<E> E v)) \<and>
      (\<forall> v. v \<in> voters_\<E> E' \<longrightarrow> linear_order (profile_\<E> E' v))"
    using subset E_in_X E'_in_Y
    unfolding elections_\<A>.simps valid_elections_def profile_def
    by fastforce
  hence "\<forall> p. \<not> linear_order p \<longrightarrow> vote_count p E = 0 \<and> vote_count p E' = 0"
    unfolding vote_count.simps
    using card.infinite card_0_eq Collect_empty_eq
    by (metis (mono_tags, lifting))
  hence "\<forall> p. \<not> linear_order p \<longrightarrow> vote_fraction p E = 0 \<and> vote_fraction p E' = 0"
    using int_ops rat_number_collapse
    by simp
  with eq_ord have "\<forall> p. vote_fraction p E = vote_fraction p E'"
    by metis
  hence "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)"
    using subset E_in_X E'_in_Y elections_\<A>.simps
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast
  thus "X = Y"
    using class_X_E class_Y_E' equiv equiv_class_eq
    by (metis (no_types, lifting))
next
  show "(anonymity_homogeneity_class::('a, 'v) Election set \<Rightarrow> rat^('a Ordered_Preference))
        ` anonymity_homogeneity\<^sub>\<Q> UNIV = vote_simplex"
  proof (unfold vote_simplex_def, safe)
    fix X :: "('a, 'v) Election set"
    assume
      quot: "X \<in> anonymity_homogeneity\<^sub>\<Q> UNIV" and
      not_simplex: "anonymity_homogeneity_class X \<notin> rat_vector_set (convex hull standard_basis)"
    have equiv_rel:
      "equiv (elections_\<A> UNIV) (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV))"
      using anonymity_homogeneity_is_equivalence[of "elections_\<A> UNIV"] elections_\<A>.simps
      by blast
    then obtain E :: "('a, 'v) Election" where
      E_in_X: "E \<in> X" and
      "X = anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {E}"
      using quot anonymity_homogeneity\<^sub>\<Q>.simps equiv_Eps_in proj_Eps
      unfolding proj_def
      by metis
    hence rel: "\<forall> E' \<in> X. (E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)"
      by simp
    hence "\<forall> p. \<forall> E' \<in> X. vote_fraction (ord2pref p) E' = vote_fraction (ord2pref p) E"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by fastforce
    hence "\<forall> p. vote_fraction (ord2pref p) ` X = {vote_fraction (ord2pref p) E}"
      using E_in_X
      by blast
    hence repr: "\<forall> p. vote_fraction\<^sub>\<Q> (ord2pref p) X = vote_fraction (ord2pref p) E"
      using is_singletonI singleton_set_def_if_card_one the_elem_eq
      unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps is_singleton_altdef
      by metis
    have "\<forall> p. vote_count (ord2pref p) E \<ge> 0"
      by simp
    hence "\<forall> p. card (voters_\<E> E) > 0 \<longrightarrow>
        Fract (int (vote_count (ord2pref p) E)) (int (card (voters_\<E> E))) \<ge> 0"
      using zero_le_Fract_iff
      by simp
    hence "\<forall> p. vote_fraction (ord2pref p) E \<ge> 0"
      unfolding vote_fraction.simps card_gt_0_iff
      by simp
    hence "\<forall> p. vote_fraction\<^sub>\<Q> (ord2pref p) X \<ge> 0"
      using repr
      by simp
    hence geq_0: "\<forall> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X) \<ge> 0"
      using zero_le_of_rat_iff
      by blast
    have "voters_\<E> E = {} \<or> infinite (voters_\<E> E) \<longrightarrow>
        (\<forall> p. real_of_rat (vote_fraction p E) = 0)"
      by simp
    hence zero_case:
      "voters_\<E> E = {} \<or> infinite (voters_\<E> E) \<longrightarrow>
        (\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = 0"
      using repr
      unfolding zero_vec_def
      by simp
    let ?sum = "sum (\<lambda> p. vote_count p E) UNIV"
    have "finite (UNIV::('a \<times> 'a) set)"
      by simp
    hence eq_card: "finite (voters_\<E> E) \<longrightarrow> card (voters_\<E> E) = ?sum"
      using vote_count_sum
      by metis
    hence "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow>
        sum (\<lambda> p. vote_fraction p E) UNIV =
          sum (\<lambda> p. Fract (vote_count p E) ?sum) UNIV"
      unfolding vote_fraction.simps
      by presburger
    moreover have gt_0: "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow> ?sum > 0"
      using eq_card
      by fastforce
    hence "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow> 
      sum (\<lambda> p. Fract (vote_count p E) ?sum) UNIV = Fract ?sum ?sum"
      using fract_distr[of UNIV ?sum "\<lambda> p. int (vote_count p E)"]
            card_0_eq eq_card finite_class.finite_UNIV 
            of_nat_eq_0_iff of_nat_sum sum.cong
      by (metis (no_types, lifting))
    moreover have "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow> Fract ?sum ?sum = 1"
      using gt_0 One_rat_def eq_rat(1)[of ?sum 1 ?sum 1]
      by linarith
    ultimately have sum_1:
      "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow> sum (\<lambda> p. vote_fraction p E) UNIV = 1"
      by presburger
    have inv_of_rat: "\<forall> x \<in> \<rat>. the_inv of_rat (of_rat x) = x"
      unfolding Rats_def
      using the_inv_f_f injI of_rat_eq_iff
      by metis
    have "E \<in> elections_\<A> UNIV"
      using quot E_in_X equiv_class_eq_iff equiv_rel rel
      unfolding anonymity_homogeneity\<^sub>\<Q>.simps quotient_def
      by fastforce
    hence "\<forall> v \<in> voters_\<E> E. linear_order (profile_\<E> E v)"
      unfolding elections_\<A>.simps valid_elections_def profile_def
      by fastforce
    hence "\<forall> p. \<not> linear_order p \<longrightarrow> vote_count p E = 0"
      unfolding vote_count.simps
      using card.infinite card_0_eq
      by blast
    hence "\<forall> p. \<not> linear_order p \<longrightarrow> vote_fraction p E = 0"
      using rat_number_collapse
      by simp
    moreover have "sum (\<lambda> p. vote_fraction p E) UNIV =
      sum (\<lambda> p. vote_fraction p E) {p. linear_order p} + 
      sum (\<lambda> p. vote_fraction p E) (UNIV - {p. linear_order p})"
      using finite CollectD Collect_mono UNIV_I add.commute sum.subset_diff top_set_def
      by metis
    ultimately have "sum (\<lambda> p. vote_fraction p E) UNIV = 
      sum (\<lambda> p. vote_fraction p E) {p. linear_order p}"
      by simp
    moreover have "bij_betw ord2pref UNIV {p. linear_order p}"
      using inj_def ord2pref_inject range_ord2pref
      unfolding bij_betw_def
      by blast
    ultimately have
      "sum (\<lambda> p. vote_fraction p E) UNIV = sum (\<lambda> p. vote_fraction (ord2pref p) E) UNIV"
      using comp_def[of "\<lambda> p. vote_fraction p E" ord2pref]
            sum_comp[of ord2pref UNIV "{p. linear_order p}" "\<lambda> p. vote_fraction p E"]
      by auto
    hence "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow>
      sum (\<lambda> p. vote_fraction (ord2pref p) E) UNIV = 1"
      using sum_1
      by presburger
    hence "finite (voters_\<E> E) \<and> voters_\<E> E \<noteq> {} \<longrightarrow>
        sum (\<lambda> p. real_of_rat (vote_fraction (ord2pref p) E)) UNIV = 1"
      using of_rat_1 of_rat_sum
      by metis
    with zero_case
    have "(\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = 0 \<or>
            sum (\<lambda> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) UNIV = 1"
      using repr
      by force
    hence "(\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = 0 \<or>
        ((\<forall> p. (\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))$p \<ge> 0) \<and>
          sum (($) (\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))) UNIV = 1)"
      using geq_0
      by force
    moreover have rat_entries: "\<forall> p. (\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))$p \<in> \<rat>"
      by simp
    ultimately have simplex_el:
      "(\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) \<in>
        {x \<in> insert 0 (convex hull standard_basis). \<forall> i. x$i \<in> \<rat>}"
      using standard_simplex_rewrite
      by blast
    moreover have
      "\<forall> p. (rat_vector (\<chi> p. of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)))$p
        = the_inv real_of_rat ((\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) $ p)"
      unfolding rat_vector.simps
      using vec_lambda_beta
      by blast
    moreover have
      "\<forall> p. the_inv real_of_rat ((\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) $ p) =
        the_inv real_of_rat (real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))"
      by simp
    moreover have
      "\<forall> p. the_inv real_of_rat (real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) =
        vote_fraction\<^sub>\<Q> (ord2pref p) X"
      using rat_entries inv_of_rat Rats_eq_range_nat_to_rat_surj surj_nat_to_rat_surj
      by blast
    moreover have "\<forall> p. vote_fraction\<^sub>\<Q> (ord2pref p) X = (anonymity_homogeneity_class X)$p"
      by simp
    ultimately have
      "\<forall> p. (rat_vector (\<chi> p. of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)))$p =
            (anonymity_homogeneity_class X)$p"
      by metis
    hence "rat_vector (\<chi> p. of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))
            = anonymity_homogeneity_class X"
      by simp
    with simplex_el
    have "\<exists> x \<in> {x \<in> insert 0 (convex hull standard_basis). \<forall> i. x $ i \<in> \<rat>}.
        rat_vector x = anonymity_homogeneity_class X"
      by blast
    with not_simplex
    have "rat_vector 0 = anonymity_homogeneity_class X"
      using image_iff insertE mem_Collect_eq
      unfolding rat_vector_set.simps
      by (metis (mono_tags, lifting))
    thus "anonymity_homogeneity_class X = 0"
      unfolding rat_vector.simps
      using Rats_0 inv_of_rat of_rat_0 vec_lambda_unique zero_index
      by (metis (no_types, lifting))
  next
    have non_empty:
      "(UNIV, {}, \<lambda> v. {}) \<in> (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})})"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps Image_def elections_\<A>.simps
                valid_elections_def profile_def
      by simp
    have in_els: "(UNIV, {}, \<lambda> v. {}) \<in> elections_\<A> UNIV"
      unfolding elections_\<A>.simps valid_elections_def profile_def
      by simp
    have "\<forall> r::('a Preference_Relation). vote_fraction r (UNIV, {}, (\<lambda> v. {})) = 0"
      by simp
    hence
      "\<forall> E \<in> (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)) `` {(UNIV, {}, (\<lambda> v. {}))}.
        \<forall> r. vote_fraction r E = 0"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by auto
    moreover have
      "\<forall> E \<in> (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)) `` {(UNIV, {}, (\<lambda> v. {}))}.
          finite (voters_\<E> E)"
      unfolding Image_def anonymity_homogeneity\<^sub>\<R>.simps
      by fastforce
    ultimately have all_zero:
      "\<forall> r. \<forall> E \<in> (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)) `` {(UNIV, {}, (\<lambda> v. {}))}.
        vote_fraction r E = 0"
      by blast
    hence "\<forall> r. 0 \<in>
        vote_fraction r ` (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)) `` {(UNIV, {}, (\<lambda> v. {}))}"
      using non_empty image_eqI
      by (metis (mono_tags, lifting))
    hence "\<forall> r. {0} \<subseteq> vote_fraction r `
        (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})})"
      by blast
    moreover have "\<forall> r. {0} \<supseteq> vote_fraction r `
        (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})})"
      using all_zero
      by blast
    ultimately have "\<forall> r.
      vote_fraction r ` (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})}) = {0}"
      by blast
    hence
      "\<forall> r.
      card (vote_fraction r
        ` (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})})) = 1
      \<and> the_inv (\<lambda> x. {x})
        (vote_fraction r `
          (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})})) = 0"
      using is_singletonI singleton_insert_inj_eq' singleton_set_def_if_card_one
      unfolding is_singleton_altdef singleton_set.simps
      by metis
    hence
      "\<forall> r. vote_fraction\<^sub>\<Q> r
        (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})}) = 0"
      unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
      by metis
    hence "\<forall> r::('a Ordered_Preference). vote_fraction\<^sub>\<Q> (ord2pref r)
          (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})}) = 0"
      by metis
    hence "\<forall> r::('a Ordered_Preference).
        (anonymity_homogeneity_class ((anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)
            `` {(UNIV, {}, \<lambda> v. {})})))$r = 0"
      unfolding anonymity_homogeneity_class.simps
      using vec_lambda_beta
      by (metis (no_types))
    moreover have "\<forall> r::('a Ordered_Preference). 0$r = 0"
      by simp
    ultimately have "\<forall> r::('a Ordered_Preference).
        (anonymity_homogeneity_class
          ((anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})})))$r
        = (0::(rat^('a Ordered_Preference)))$r"
      by (metis (no_types))
    hence "anonymity_homogeneity_class
      ((anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})}))
        = (0::(rat^('a Ordered_Preference)))"
      using vec_eq_iff
      by blast
    moreover have
      "(anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, {}, \<lambda> v. {})})
          \<in> anonymity_homogeneity\<^sub>\<Q> UNIV"
      unfolding anonymity_homogeneity\<^sub>\<Q>.simps quotient_def
      using in_els
      by blast
    ultimately show "(0::(rat^('a Ordered_Preference)))
          \<in> anonymity_homogeneity_class ` anonymity_homogeneity\<^sub>\<Q> UNIV"
      using image_eqI
      by (metis (no_types))
  next
    fix x :: "rat^('a Ordered_Preference)"
    assume "x \<in> rat_vector_set (convex hull standard_basis)"
    \<comment> \<open>Convert rational vector x to real vector x'.\<close>
    then obtain x' :: "real^('a Ordered_Preference)" where
      conv: "x' \<in> convex hull standard_basis" and
      inv: "\<forall> p. x$p = the_inv real_of_rat (x'$p)" and
      rat: "\<forall> p. x'$p \<in> \<rat>"
      unfolding rat_vector_set.simps rat_vector.simps
      by force
    hence convex: "(\<forall> p. 0 \<le> x'$p) \<and> sum (($) x') UNIV = 1"
      using standard_simplex_rewrite
      by blast
    have map: "\<forall> p. real_of_rat (x$p) = x'$p"
      using inv rat the_inv_f_f[of real_of_rat] f_the_inv_into_f inj_onCI of_rat_eq_iff
      unfolding Rats_def
      by metis
    have "\<forall> p. \<exists> fract. Fract (fst fract) (snd fract) = x$p \<and> 0 < snd fract"
      using quotient_of_unique
      by metis
    then obtain fraction' :: "'a Ordered_Preference \<Rightarrow> (int \<times> int)" where
      "\<forall> p. x$p = Fract (fst (fraction' p)) (snd (fraction' p))" and
      pos': "\<forall> p. 0 < snd (fraction' p)"
      by metis
    with map
    have fract': "\<forall> p. x'$p = (fst (fraction' p)) / (snd (fraction' p))"
      using div_by_0 divide_less_cancel of_int_0 of_int_pos of_rat_rat
      by metis
    with convex
    have "\<forall> p. (fst (fraction' p)) / (snd (fraction' p)) \<ge> 0"
      by fastforce
    with pos'
    have "\<forall> p. fst (fraction' p) \<ge> 0"
      using not_less of_int_0_le_iff of_int_pos zero_le_divide_iff
      by metis
    with pos'
      have "\<forall> p. fst (fraction' p) \<in> \<nat> \<and> snd (fraction' p) \<in> \<nat>"
      using nonneg_int_cases of_nat_in_Nats order_less_le
      by metis
    hence "\<forall> p. \<exists> (n::nat) (m::nat). fst (fraction' p) = n \<and> snd (fraction' p) = m"
      using Nats_cases
      by metis
    hence "\<forall> p. \<exists> m::nat \<times> nat. fst (fraction' p) = int (fst m) \<and> snd (fraction' p) = int (snd m)"
      by simp
    then obtain fraction :: "'a Ordered_Preference \<Rightarrow> (nat \<times> nat)" where
      eq: "\<forall> p. fst (fraction' p) = int (fst (fraction p)) \<and>
                snd (fraction' p) = int (snd (fraction p))"
      by metis
    with fract'
    have fract: "\<forall> p. x'$p = (fst (fraction p)) / (snd (fraction p))"
      by simp
    from eq pos'
    have pos: "\<forall> p. 0 < snd (fraction p)"
      by simp
    let ?prod = "prod (\<lambda> p. snd (fraction p)) UNIV"
    have fin: "finite (UNIV::('a Ordered_Preference set))"
      by simp
    hence "finite {snd (fraction p) | p. p \<in> UNIV}"
      using finite_Atleast_Atmost_nat
      by simp
    have pos_prod: "?prod > 0"
      using pos
      by simp
    hence "\<forall> p. ?prod mod (snd (fraction p)) = 0"
      using pos finite UNIV_I bits_mod_0 mod_prod_eq mod_self prod_zero
      by (metis (mono_tags, lifting))
    hence div: "\<forall> p. (?prod div (snd (fraction p))) * (snd (fraction p)) = ?prod"
      using add.commute add_0 div_mult_mod_eq
      by metis
    obtain voter_amount :: "'a Ordered_Preference \<Rightarrow> nat" where
      def: "voter_amount = (\<lambda> p. (fst (fraction p)) * (?prod div (snd (fraction p))))"
      by blast
    have rewrite_div: "\<forall> p. ?prod div (snd (fraction p)) = ?prod / (snd (fraction p))"
      using div less_imp_of_nat_less nonzero_mult_div_cancel_right
            of_nat_less_0_iff of_nat_mult pos
      by metis
    hence "sum voter_amount UNIV =
              sum (\<lambda> p. (fst (fraction p)) * (?prod / (snd (fraction p)))) UNIV"
      using def
      by simp
    hence "sum voter_amount UNIV =
              ?prod * (sum (\<lambda> p. (fst (fraction p)) / (snd (fraction p))) UNIV)"
      using mult_of_nat_commute sum.cong times_divide_eq_right
            vector_space_over_itself.scale_sum_right
      by (metis (mono_tags, lifting))
    hence rewrite_sum: "sum voter_amount UNIV = ?prod"
      using fract convex mult_cancel_left1 of_nat_eq_iff sum.cong
      by (metis (mono_tags, lifting))
    obtain V :: "'v set" where
      fin_V: "finite V" and
      card_V_eq_sum: "card V = sum voter_amount UNIV"
      using assms infinite_arbitrarily_large
      by metis
    then obtain part :: "'a Ordered_Preference \<Rightarrow> 'v set" where
      partition: "V = \<Union> {part p | p. p \<in> UNIV}" and
      disjoint: "\<forall> p p'. p \<noteq> p' \<longrightarrow> part p \<inter> part p' = {}" and
      card: "\<forall> p. card (part p) = voter_amount p"
      using obtain_partition[of V UNIV voter_amount]
      by auto
    hence exactly_one_prof: "\<forall> v \<in> V. \<exists>!p. v \<in> part p"
      by blast
    then obtain prof' :: "'v \<Rightarrow> 'a Ordered_Preference" where
      maps_to_prof': "\<forall> v \<in> V. v \<in> part (prof' v)"
      by metis
    then obtain prof :: "'v \<Rightarrow> 'a Preference_Relation" where
      prof: "prof = (\<lambda> v. if v \<in> V then ord2pref (prof' v) else {})"
      by blast
    hence election: "(UNIV, V, prof) \<in> elections_\<A> UNIV"
      unfolding elections_\<A>.simps valid_elections_def profile_def
      using fin_V ord2pref
      by auto
    have "\<forall> p. {v \<in> V. prof' v = p} = {v \<in> V. v \<in> part p}"
      using maps_to_prof' exactly_one_prof
      by blast
    hence "\<forall> p. {v \<in> V. prof' v = p} = part p"
      using partition
      by fastforce
    hence "\<forall> p. card {v \<in> V. prof' v = p} = voter_amount p"
      using card
      by presburger
    moreover have "\<forall> p. \<forall> v. (v \<in> {v \<in> V. prof' v = p}) = (v \<in> {v \<in> V. prof v = (ord2pref p)})"
      using prof
      by (simp add: ord2pref_inject)
    ultimately have "\<forall> p. card {v \<in> V. prof v = (ord2pref p)} = voter_amount p"
      by simp
    hence "\<forall> p::'a Ordered_Preference.
      vote_fraction (ord2pref p) (UNIV, V, prof) = Fract (voter_amount p) (card V)"
      using rat_number_collapse fin_V
      by simp
    moreover have "\<forall> p. Fract (voter_amount p) (card V) = (voter_amount p) / (card V)"
      unfolding Fract_of_int_quotient of_rat_divide
      by simp
    moreover have
      "\<forall> p. (voter_amount p) / (card V) =
            ((fst (fraction p)) * (?prod div (snd (fraction p)))) / ?prod"
      using card def card_V_eq_sum rewrite_sum
      by presburger
    moreover have
      "\<forall> p. ((fst (fraction p)) * (?prod div (snd (fraction p)))) / ?prod =
            (fst (fraction p)) / (snd (fraction p))"
      using rewrite_div pos_prod
      by auto
    \<comment> \<open>The percentages of voters voting for each linearly ordered profile in
        (UNIV, V, prof) equal the entries of the given vector.\<close>
    ultimately have eq_vec:
      "\<forall> p :: 'a Ordered_Preference. vote_fraction (ord2pref p) (UNIV, V, prof) = x'$p"
      using fract
      by presburger
    moreover have "\<forall> E \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}.
        \<forall> p. vote_fraction (ord2pref p) E = vote_fraction (ord2pref p) (UNIV, V, prof)"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by fastforce
    ultimately have "\<forall> E \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}.
        \<forall> p. vote_fraction (ord2pref p) E = x'$p"
      by simp
    hence "\<forall> E \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}.
        \<forall> p. vote_fraction (ord2pref p) E = x'$p"
      using eq_vec
      by metis
    hence vec_entries_match_E_vote_frac:
      "\<forall> p. \<forall> E \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}.
        vote_fraction (ord2pref p) E = x'$p"
      by blast
    have "\<forall> x \<in> \<rat>. \<forall> y. complex_of_rat y = complex_of_real x \<longrightarrow> real_of_rat y = x"
      using Re_complex_of_real Re_divide_of_real of_rat.rep_eq of_real_of_int_eq
      by metis
    hence "\<forall> x \<in> \<rat>. \<forall> y. complex_of_rat y = complex_of_real x \<longrightarrow> y = the_inv real_of_rat x"
      using injI of_rat_eq_iff the_inv_f_f
      by metis
    with vec_entries_match_E_vote_frac
    have all_eq_vec:
      "\<forall> p. \<forall> E \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}.
        vote_fraction (ord2pref p) E = x$p"
      using rat inv
      by metis
    moreover have
      "(UNIV, V, prof) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}"
      using anonymity_homogeneity\<^sub>\<R>.simps election
      by blast
    ultimately have "\<forall> p. vote_fraction (ord2pref p) `
        anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)} \<supseteq> {x$p}"
      using image_insert insert_iff mk_disjoint_insert singletonD subsetI
      by (metis (no_types, lifting))
    with all_eq_vec
    have "\<forall> p. vote_fraction (ord2pref p) `
      anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)} = {x$p}"
      by blast
    hence "\<forall> p. vote_fraction\<^sub>\<Q> (ord2pref p)
      (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)}) = x$p"
      using is_singletonI singleton_inject singleton_set_def_if_card_one
      unfolding is_singleton_altdef vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps
      by metis
    hence "x = anonymity_homogeneity_class
                  (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV) `` {(UNIV, V, prof)})"
      unfolding anonymity_homogeneity_class.simps
      using vec_lambda_unique
      by (metis (no_types, lifting))
    moreover have "(anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)) `` {(UNIV, V, prof)}
                      \<in> anonymity_homogeneity\<^sub>\<Q> UNIV"
      unfolding anonymity_homogeneity\<^sub>\<Q>.simps quotient_def
      using election
      by blast
    ultimately show
      "x \<in> (anonymity_homogeneity_class :: ('a, 'v) Election set \<Rightarrow> rat^('a Ordered_Preference))
              ` anonymity_homogeneity\<^sub>\<Q> UNIV"
      by blast
  qed
qed

end
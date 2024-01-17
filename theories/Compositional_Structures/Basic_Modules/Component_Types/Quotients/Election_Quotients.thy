section \<open>Quotients of Equivalence Relations on Election Sets\<close>

theory Election_Quotients
  imports Relation_Quotients
          "../Social_Choice_Types/Voting_Symmetry"
          "../Social_Choice_Types/Ordered_Relation"
          "HOL-Library.Extended_Real"
          "HOL-Analysis.Cartesian_Euclidean_Space"
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
  shows
    "\<exists>\<X>. X = \<Union>{\<X> i |i. i \<in> Y} \<and> (\<forall>i \<in> Y. card (\<X> i) = N i) \<and> 
         (\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
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
  let ?\<X> = "\<lambda>y. {}"
  have "Y = {}"
    using 0 fin_Y card_Y
    by simp
  hence "sum N Y = 0"
    by simp
  hence "X = {}"
    using fin_X card_X
    by simp
  hence "X = \<Union> {?\<X> i |i. i \<in> Y}"
    by blast
  moreover have 
    "\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> ?\<X> i \<inter> ?\<X> j = {}"
    by blast
  ultimately show
    "\<exists>\<X>. X = \<Union> {\<X> i |i. i \<in> Y} \<and>
                (\<forall>i\<in>Y. card (\<X> i) = N i) \<and> (\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"   
    by (simp add: \<open>Y = {}\<close>)
next
  case (Suc x)
  fix
    x :: nat and
    X :: "'x set" and
    Y :: "'y set"
  assume
    card_Y: "Suc x = card Y" and
    fin_Y: "finite Y" and
    fin_X: "finite X" and 
    card_X: "sum N Y = card X" and
    hyp: 
      "\<And>Y (X::'x set). 
         x = card Y \<Longrightarrow>
         finite X \<Longrightarrow>
         finite Y \<Longrightarrow>
         sum N Y = card X \<Longrightarrow>
         \<exists>\<X>. 
          X = \<Union> {\<X> i |i. i \<in> Y} \<and>
                  (\<forall>i\<in>Y. card (\<X> i) = N i) \<and> (\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
  then obtain Y' :: "'y set" and y :: 'y where 
    "Y = insert y Y'" and "card Y' = x" and "finite Y'" and "y \<notin> Y'"
    using card_Suc_eq_finite
    by (metis (no_types, lifting))
  hence "N y \<le> card X"
    using card_X card_Y fin_Y le_add1 n_not_Suc_n sum.insert
    by metis
  then obtain X' :: "'x set" where "X' \<subseteq> X" and "card X' = N y"
    using fin_X ex_card
    by meson
  hence "finite (X - X') \<and> card (X - X') = sum N Y'"
    using card_Y card_X fin_X fin_Y \<open>Y = insert y Y'\<close> \<open>card Y' = x\<close> \<open>finite Y'\<close> 
          Suc_n_not_n add_diff_cancel_left' card_Diff_subset card_insert_if 
          finite_Diff finite_subset sum.insert
    by metis
  then obtain \<X> :: "'y \<Rightarrow> 'x set" where
    part: "X - X' = \<Union>{\<X> i |i. i \<in> Y'}" and 
    disj: "\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y' \<and> j \<in> Y' \<longrightarrow> \<X> i \<inter> \<X> j = {}" and
    card: "\<forall>i \<in> Y'. card (\<X> i) = N i"
    using hyp[of Y' "X - X'"] \<open>finite Y'\<close> \<open>card Y' = x\<close>
    by auto
  then obtain \<X>' :: "'y \<Rightarrow> 'x set" where 
    map': "\<X>' = (\<lambda>z. if (z = y) then X' else \<X> z)"
    by simp
  hence eq_\<X>: "\<forall>i \<in> Y'. \<X>' i = \<X> i"
    using \<open>y \<notin> Y'\<close>
    by auto
  have "Y = {y} \<union> Y'"
    using \<open>Y = insert y Y'\<close>
    by fastforce
  hence "\<forall>f. {f i |i. i \<in> Y} = {f y} \<union> {f i |i. i \<in> Y'}"
    by auto
  hence "{\<X>' i |i. i \<in> Y} = {\<X>' y} \<union> {\<X>' i |i. i \<in> Y'}"
    by metis
  hence "\<Union>{\<X>' i |i. i \<in> Y} = \<X>' y \<union> \<Union>{\<X>' i |i. i \<in> Y'}"
    by simp
  also have "\<X>' y = X'"
    using map'
    by presburger
  also have "\<Union>{\<X>' i |i. i \<in> Y'} = \<Union>{\<X> i |i. i \<in> Y'}"
    using eq_\<X>
    by blast
  finally have part': "X = \<Union>{\<X>' i |i. i \<in> Y}"
    using part
    by (metis Diff_partition \<open>X' \<subseteq> X\<close>)
  have "\<forall>i \<in> Y'. \<X>' i \<subseteq> X - X'"
    using part eq_\<X>
    by (metis Setcompr_eq_image UN_upper)
  hence "\<forall>i \<in> Y'. \<X>' i \<inter> X' = {}"
    by blast
  hence "\<forall>i \<in> Y'. \<X>' i \<inter> \<X>' y = {}"
    using map'
    by simp
  hence "\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X>' i \<inter> \<X>' j = {}"
    using map' disj \<open>Y = insert y Y'\<close> inf.commute insertE
    by (metis (no_types, lifting))
  moreover have "\<forall>i \<in> Y. card (\<X>' i) = N i"
    using map' card \<open>card X' = N y\<close> \<open>Y = insert y Y'\<close>
    by simp
  ultimately show
    "\<exists>\<X>. X = \<Union> {\<X> i |i. i \<in> Y} \<and>
                (\<forall>i\<in>Y. card (\<X> i) = N i) \<and> (\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
    using part'
    by blast
qed

subsection \<open>Anonymity Quotient - Grid\<close>

\<comment> \<open>The election equivalence classes of the anonymity equivalence relation.\<close>
fun anonymity\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anonymity\<^sub>\<Q> A = quotient (fixed_alt_elections A) (anonymity\<^sub>\<R> (fixed_alt_elections A))"

\<comment> \<open>Counts the occurrences of a ballot per election in a set of elections
    if the occurrences of the ballot per election coincide for all elections in the set.\<close>      
fun vote_count\<^sub>\<Q> :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election set \<Rightarrow> nat" where
  "vote_count\<^sub>\<Q> p = \<pi>\<^sub>\<Q> (vote_count p)"

fun anon_cls_to_vec :: 
  "('a::finite, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec" where
  "anon_cls_to_vec X = (\<chi> p. vote_count\<^sub>\<Q> (ord2pref p) X)"

text \<open>
  We assume all our elections to consist of a fixed finite alternative set of size n and
  finite subsets of an infinite voter universe. Profiles are linear orders on the alternatives.
  Then we can work on the natural-number-vectors of dimension n! instead of the equivalence 
  classes of the anonymity relation:
  Each dimension corresponds to one possible linear order on the alternative set, 
  i.e. the possible preferences.
  Each equivalence class of elections corresponds to a vector whose entries denote the amount 
  of voters per election in that class who vote the respective corresponding preference.
\<close>
theorem anonymity\<^sub>\<Q>_iso:
  assumes
    "infinite (UNIV::('v set))" 
    \<comment> \<open>Assume an infinite voter universe so that we can choose arbitrarily large voter sets.\<close>
  shows
    "bij_betw (anon_cls_to_vec::('a::finite, 'v) Election set \<Rightarrow> nat^('a Ordered_Preference)) 
              (anonymity\<^sub>\<Q> (UNIV::'a set)) (UNIV::(nat^('a Ordered_Preference)) set)"
proof (unfold bij_betw_def inj_on_def, standard, standard, standard, standard)
  fix
    X :: "('a, 'v) Election set" and
    Y :: "('a, 'v) Election set"
  assume
    cls_X: "X \<in> anonymity\<^sub>\<Q> UNIV" and
    cls_Y: "Y \<in> anonymity\<^sub>\<Q> UNIV" and
    eq_vec: "anon_cls_to_vec X = anon_cls_to_vec Y"
  have "\<forall>E \<in> fixed_alt_elections UNIV. finite (votrs_\<E> E)"
    by simp
  hence "\<forall>(E, E') \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV). finite (votrs_\<E> E)"
    unfolding anonymity\<^sub>\<R>.simps rel_induced_by_action.simps fixed_alt_elections.simps
    by force
  moreover have subset: "fixed_alt_elections UNIV \<subseteq> valid_elections"
    by simp
  ultimately have
    "\<forall>(E, E') \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV). \<forall>p. vote_count p E = vote_count p E'"
    using anon_rel_vote_count[of _ _ "fixed_alt_elections UNIV"]
    by blast
  hence vote_count_invar:
    "\<forall>p. (vote_count p) respects (anonymity\<^sub>\<R> (fixed_alt_elections UNIV))"
    unfolding congruent_def
    by blast  
  have 
    "equiv valid_elections (anonymity\<^sub>\<R> valid_elections)"
    using rel_ind_by_grp_act_equiv[of anonymity\<^sub>\<G> valid_elections "\<phi>_anon valid_elections"]
          rel_ind_by_action_subset[of "fixed_alt_elections UNIV" valid_elections
                                      "carrier anonymity\<^sub>\<G>" "\<phi>_anon valid_elections"]
    by (simp add: anon_grp_act.group_action_axioms)
  moreover have
    "\<forall>\<pi> \<in> carrier anonymity\<^sub>\<G>.
      \<forall>E\<in>fixed_alt_elections UNIV. 
        \<phi>_anon (fixed_alt_elections UNIV) \<pi> E = \<phi>_anon valid_elections \<pi> E"
    using subset
    unfolding \<phi>_anon.simps
    by simp
  ultimately have equiv_rel:
    "equiv (fixed_alt_elections UNIV) (anonymity\<^sub>\<R> (fixed_alt_elections UNIV))"
    using subset rel_ind_by_action_subset[of
            "fixed_alt_elections UNIV" valid_elections "carrier anonymity\<^sub>\<G>" 
            "\<phi>_anon (fixed_alt_elections UNIV)" "\<phi>_anon valid_elections"]
          equiv_rel_restr[
            of valid_elections "anonymity\<^sub>\<R> valid_elections" "fixed_alt_elections UNIV"]
    unfolding anonymity\<^sub>\<R>.simps
    by (metis (no_types))
  with vote_count_invar have quotient_count:
    "\<forall>X \<in> anonymity\<^sub>\<Q> UNIV. \<forall>p. \<forall>E \<in> X. vote_count\<^sub>\<Q> p X = vote_count p E"
    using pass_to_quotient[of 
            "anonymity\<^sub>\<R> (fixed_alt_elections UNIV)" "vote_count _" "fixed_alt_elections UNIV"]
    unfolding anonymity\<^sub>\<Q>.simps anonymity\<^sub>\<R>.simps vote_count\<^sub>\<Q>.simps
    by blast
  moreover from equiv_rel 
  obtain E :: "('a, 'v) Election" and E' :: "('a, 'v) Election" where 
    "E \<in> X" and "E' \<in> Y"
    using cls_X cls_Y equiv_Eps_in
    unfolding anonymity\<^sub>\<Q>.simps
    by blast
  ultimately have 
    "\<forall>p. vote_count\<^sub>\<Q> p X = vote_count p E \<and> vote_count\<^sub>\<Q> p Y = vote_count p E'"
    using cls_X cls_Y
    by blast
  moreover with eq_vec have 
    "\<forall>p. vote_count\<^sub>\<Q> (ord2pref p) X = vote_count\<^sub>\<Q> (ord2pref p) Y"
    unfolding anon_cls_to_vec.simps
    using UNIV_I vec_lambda_inverse
    by metis
  ultimately have
    "\<forall>p. vote_count (ord2pref p) E = vote_count (ord2pref p) E'"
    by simp
  hence eq:
    "\<forall>p \<in> {p. linear_order_on (UNIV::'a set) p}.
       vote_count p E = vote_count p E'"
    by (metis pref2ord_inverse)
  from equiv_rel cls_X cls_Y have subset_fixed_alts:
    "X \<subseteq> fixed_alt_elections UNIV \<and> Y \<subseteq> fixed_alt_elections UNIV"
    unfolding anonymity\<^sub>\<Q>.simps
    using in_quotient_imp_subset 
    by blast
  hence eq_alts:
    "alts_\<E> E = UNIV \<and> alts_\<E> E' = UNIV"
    using \<open>E \<in> X\<close> \<open>E' \<in> Y\<close>
    unfolding fixed_alt_elections.simps
    by blast
  with subset_fixed_alts have eq_complement:
    "\<forall>p \<in> UNIV - {p. linear_order_on (UNIV::'a set) p}. 
      {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {} \<and> {v \<in> votrs_\<E> E'. prof_\<E> E' v = p} = {}"
    using \<open>E \<in> X\<close> \<open>E' \<in> Y\<close>
    unfolding fixed_alt_elections.simps valid_elections_def profile_def
    by auto
  hence 
    "\<forall>p \<in> UNIV - {p. linear_order_on (UNIV::'a set) p}. 
      vote_count p E = 0 \<and> vote_count p E' = 0"
    unfolding vote_count.simps
    by (simp add: card_eq_0_iff)
  with eq have eq_vote_count: 
    "\<forall>p. vote_count p E = vote_count p E'"
    by (metis DiffI UNIV_I)
  moreover from subset_fixed_alts \<open>E \<in> X\<close> \<open>E' \<in> Y\<close> have 
    "finite (votrs_\<E> E) \<and> finite (votrs_\<E> E')"
    unfolding fixed_alt_elections.simps
    by blast
  moreover from subset_fixed_alts \<open>E \<in> X\<close> \<open>E' \<in> Y\<close> have
    "(E, E') \<in> (fixed_alt_elections UNIV) \<times> (fixed_alt_elections UNIV)"
    by blast
  moreover from this have 
    "(\<forall>v. v \<notin> votrs_\<E> E \<longrightarrow> prof_\<E> E v = {}) \<and> (\<forall>v. v \<notin> votrs_\<E> E' \<longrightarrow> prof_\<E> E' v = {})"
    unfolding fixed_alt_elections.simps
    by force
  ultimately have
    "(E, E') \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV)"
    using eq_alts vote_count_anon_rel
    by metis
  hence 
    "anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {E} = anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {E'}"
    using equiv_rel
    by (metis equiv_class_eq)
  also have "anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {E} = X"
    using \<open>E \<in> X\<close> cls_X equiv_rel
    unfolding anonymity\<^sub>\<Q>.simps
    by (metis (no_types, lifting) Image_singleton_iff equiv_class_eq quotientE)
  also have "anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {E'} = Y"
    using \<open>E' \<in> Y\<close> cls_Y equiv_rel
    unfolding anonymity\<^sub>\<Q>.simps
    by (metis (no_types, lifting) Image_singleton_iff equiv_class_eq quotientE)
  finally show "X = Y"
    by simp
next
  have subset: "fixed_alt_elections UNIV \<subseteq> valid_elections"
      by simp
  have 
    "equiv valid_elections (anonymity\<^sub>\<R> valid_elections)"
    using rel_ind_by_grp_act_equiv[of anonymity\<^sub>\<G> valid_elections "\<phi>_anon valid_elections"]
          rel_ind_by_action_subset[of "fixed_alt_elections UNIV" valid_elections
                                      "carrier anonymity\<^sub>\<G>" "\<phi>_anon valid_elections"]
    by (simp add: anon_grp_act.group_action_axioms)
  \<comment> \<open>TODO: Remove this duplicate, already shown in the previous subgoal...\<close>
  moreover have
    "\<forall>\<pi> \<in> carrier anonymity\<^sub>\<G>.
      \<forall>E\<in>fixed_alt_elections UNIV. 
        \<phi>_anon (fixed_alt_elections UNIV) \<pi> E = \<phi>_anon valid_elections \<pi> E"
    using subset
    unfolding \<phi>_anon.simps
    by simp
  ultimately have equiv_rel:
    "equiv (fixed_alt_elections UNIV) (anonymity\<^sub>\<R> (fixed_alt_elections UNIV))"
    using subset rel_ind_by_action_subset[of
            "fixed_alt_elections UNIV" valid_elections "carrier anonymity\<^sub>\<G>" 
            "\<phi>_anon (fixed_alt_elections UNIV)" "\<phi>_anon valid_elections"]
          equiv_rel_restr[
            of valid_elections "anonymity\<^sub>\<R> valid_elections" "fixed_alt_elections UNIV"]
    unfolding anonymity\<^sub>\<R>.simps
    by (metis (no_types))
  have 
    "(UNIV::((nat, 'a Ordered_Preference) vec set)) \<subseteq> 
      (anon_cls_to_vec::('a, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec) ` 
      anonymity\<^sub>\<Q> UNIV"
  proof (unfold anon_cls_to_vec.simps, safe)
    fix
      x :: "(nat, 'a Ordered_Preference) vec"
    have "finite (UNIV::('a Ordered_Preference set))"
      by simp
    hence "finite {x$i |i. i \<in> UNIV}"
      using finite_Atleast_Atmost_nat 
      by blast
    hence "sum (\<lambda>i. x$i) UNIV < \<infinity>"
      using enat_ord_code(4) 
      by blast
    moreover have "0 \<le> sum (\<lambda>i. x$i) UNIV"
      by blast
    ultimately obtain V :: "'v set" where 
      "finite V" and "card V = sum (\<lambda>i. x$i) UNIV"
      using assms infinite_arbitrarily_large
      by meson
    then obtain X' :: "'a Ordered_Preference \<Rightarrow> 'v set" where
      card': "\<forall>i. card (X' i) = x$i" and
      partition': "V = \<Union>{X' i |i. i \<in> UNIV}" and
      disjoint': "\<forall>i j. i \<noteq> j \<longrightarrow> X' i \<inter> X' j = {}"
      using obtain_partition[of V UNIV "($) x"]
      by auto  
    obtain X :: "'a Preference_Relation \<Rightarrow> 'v set" where
      def_X: "X = (\<lambda>i. if (i \<in> {i. linear_order i}) then X' (pref2ord i) else {})"
      by simp
    hence "{X i |i. i \<notin> {i. linear_order i}} \<subseteq> {{}}"
      by auto
    moreover have 
      "{X i |i. i \<in> {i. linear_order i}} = {X' (pref2ord i) |i. i \<in> {i. linear_order i}}"
      using def_X
      by auto
    moreover have
      "{X i |i. i \<in> UNIV} = {X i |i. i \<in> {i. linear_order i}} \<union> 
                              {X i |i. i \<in> UNIV - {i. linear_order i}}"
      by blast
    ultimately have 
      "{X i |i. i \<in> UNIV} = {X' (pref2ord i) |i. i \<in> {i. linear_order i}} \<or> 
        {X i |i. i \<in> UNIV} = {X' (pref2ord i) |i. i \<in> {i. linear_order i}} \<union> {{}}"
      by auto
    also have 
      "{X' (pref2ord i) |i. i \<in> {i. linear_order i}} = {X' i |i. i \<in> UNIV}"
      by (metis iso_tuple_UNIV_I pref2ord_cases)
    finally have
      "{X i |i. i \<in> UNIV} = {X' i |i. i \<in> UNIV} \<or> 
        {X i |i. i \<in> UNIV} = {X' i |i. i \<in> UNIV} \<union> {{}}"
      by simp
    hence "\<Union>{X i |i. i \<in> UNIV} = \<Union>{X' i |i. i \<in> UNIV}"
      by (metis (no_types, lifting) Sup_union_distrib ccpo_Sup_singleton sup_bot.right_neutral)
    hence partition: "V = \<Union>{X i |i. i \<in> UNIV}"
      using partition'
      by simp
    moreover have "\<forall>i j. i \<noteq> j \<longrightarrow> X i \<inter> X j = {}"
      using disjoint' def_X pref2ord_inject
      by auto
    ultimately have "\<forall>v \<in> V. \<exists>!i. v \<in> X i"
      by auto
    then obtain p' :: "'v \<Rightarrow> 'a Preference_Relation" where
      p_X: "\<forall>v \<in> V. v \<in> X (p' v)" and 
      p_disj: "\<forall>v \<in> V. \<forall>i. i \<noteq> p' v \<longrightarrow> v \<notin> X i"
      by metis
    then obtain p :: "'v \<Rightarrow> 'a Preference_Relation" where
      p_def: "p = (\<lambda>v. if v \<in> V then p' v else {})"
      by simp
    hence lin_ord: "\<forall>v \<in> V. linear_order (p v)"
      using def_X p_X p_disj
      by fastforce
    hence valid:
      "(UNIV, V, p) \<in> fixed_alt_elections UNIV"
      using \<open>finite V\<close> p_def
      unfolding fixed_alt_elections.simps valid_elections_def profile_def
      by auto
    hence
      "\<forall>i. \<forall>E \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}.
        vote_count i E = vote_count i (UNIV, V, p)"
      using anon_rel_vote_count[of "(UNIV, V, p)" _ "fixed_alt_elections UNIV" ]
            \<open>finite V\<close> subset
      by simp
    moreover have 
      "(UNIV, V, p) \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}"
      using equiv_rel valid
      unfolding Image_def equiv_def refl_on_def
      by blast
    ultimately have eq_vote_count:
      "\<forall>i. vote_count i ` (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = 
            {vote_count i (UNIV, V, p)}"
      by blast
    have "\<forall>i. \<forall>v \<in> V. p v = i \<longleftrightarrow> v \<in> X i"
      using p_X p_disj p_def
      by auto
    hence "\<forall>i. {v \<in> V. p v = i} = {v \<in> V. v \<in> X i}"
      by blast
    moreover have "\<forall>i. X i \<subseteq> V"
      using partition
      by blast
    ultimately have rewr_preimg: "\<forall>i. {v \<in> V. p v = i} = X i"
      by auto
    hence "\<forall>i \<in> {i. linear_order i}. vote_count i (UNIV, V, p) = x$(pref2ord i)"
      unfolding vote_count.simps
      using def_X card'
      by auto
    hence
      "\<forall>i \<in> {i. linear_order i}.
       vote_count i ` (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = {x$(pref2ord i)}"
      using eq_vote_count
      by metis
    hence 
      "\<forall>i \<in> {i. linear_order i}. 
        vote_count\<^sub>\<Q> i (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = x$(pref2ord i)"
      unfolding vote_count\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
      using is_singleton_altdef singleton_set_def_if_card_one 
      by fastforce
    hence 
      "\<forall>i. vote_count\<^sub>\<Q> (ord2pref i) (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = x$i"
      by (metis ord2pref ord2pref_inverse)
    hence 
      "anon_cls_to_vec (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = x"
      by simp
    moreover have 
      "anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)} \<in> anonymity\<^sub>\<Q> UNIV"
      using valid
      unfolding anonymity\<^sub>\<Q>.simps quotient_def
      by blast
    ultimately show 
      "x \<in> (\<lambda>X::(('a, 'v) Election set). \<chi> p. vote_count\<^sub>\<Q> (ord2pref p) X) ` anonymity\<^sub>\<Q> UNIV"
      using anon_cls_to_vec.elims 
      by blast
  qed
  thus
    "(anon_cls_to_vec::('a, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec) ` 
      anonymity\<^sub>\<Q> UNIV = (UNIV::((nat, 'a Ordered_Preference) vec set))"
    by blast
qed

subsection \<open>Homogeneity Quotient - Simplex\<close>

fun vote_fraction :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election \<Rightarrow> rat" where
  "vote_fraction r E = 
    (if (finite (votrs_\<E> E) \<and> votrs_\<E> E \<noteq> {}) 
      then (Fract (vote_count r E) (card (votrs_\<E> E))) else 0)"

fun anon_hom\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "anon_hom\<^sub>\<R> X = 
    {(E, E') |E E'. E \<in> X \<and> E' \<in> X \<and> (finite (votrs_\<E> E) = finite (votrs_\<E> E')) \<and>
                    (\<forall>r. vote_fraction r E = vote_fraction r E')}"

fun anon_hom\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anon_hom\<^sub>\<Q> A = quotient (fixed_alt_elections A) (anon_hom\<^sub>\<R> (fixed_alt_elections A))"

fun vote_fraction\<^sub>\<Q> :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election set \<Rightarrow> rat" where
  "vote_fraction\<^sub>\<Q> p = \<pi>\<^sub>\<Q> (vote_fraction p)"

fun anon_hom_cls_to_vec ::
"('a::finite, 'v) Election set \<Rightarrow> (rat, 'a Ordered_Preference) vec" where
  "anon_hom_cls_to_vec X = (\<chi> p. vote_fraction\<^sub>\<Q> (ord2pref p) X)"

text \<open>
  Maps each rational real vector entry to the corresponding rational.
  If the entry is not rational, the corresponding entry will be undefined.
\<close>
fun rat_vec :: "real^'b \<Rightarrow> rat^'b" where
  "rat_vec v = (\<chi> p. the_inv of_rat (v$p))"
  
fun rat_vec_set :: "(real^'b) set \<Rightarrow> (rat^'b) set" where
  "rat_vec_set V = rat_vec ` {v \<in> V. \<forall>i. v$i \<in> \<rat>}"

definition standard_basis :: "(real^'b) set" where
  "standard_basis = {v. (\<exists>b. v$b = 1 \<and> (\<forall>c \<noteq> b. v$c = 0))}"

text \<open>
  The rational points in the simplex.
\<close>
definition vote_simplex :: "(rat^'b) set" where
  "vote_simplex = insert 0 (rat_vec_set (convex hull (standard_basis :: (real^'b) set)))"

subsubsection \<open>Auxiliary Lemmas\<close>
  
lemma convex_combination_in_convex_hull:
  fixes
    X :: "(real^'b) set" and
    x :: "real^'b"
  assumes
    "\<exists>f::(real^'b) \<Rightarrow> real. 
      sum f X = 1 \<and> (\<forall>x \<in> X. f x \<ge> 0) \<and> x = sum (\<lambda>x. (f x) *\<^sub>R x) X"
  shows
    "x \<in> convex hull X"
  using assms
proof (induction "card X" arbitrary: X x)
  case 0
  fix
    X :: "(real^'b) set" and
    x :: "real^'b" 
  assume
    "0 = card X" and
    "\<exists>f. sum f X = 1 \<and> (\<forall>x\<in>X. 0 \<le> f x) \<and> x = (\<Sum>x\<in>X. f x *\<^sub>R x)"
  hence "(\<forall>f. sum f X = 0) \<and> (\<exists>f. sum f X = 1)"
    by (metis card_0_eq empty_iff sum.infinite sum.neutral zero_neq_one)
  hence "\<exists>f. sum f X = 1 \<and> sum f X = 0"
    by blast
  hence "False"
    using zero_neq_one
    by metis
  thus?case
    by blast
next
  case (Suc n)
  fix
    X :: "(real^'b) set" and
    x :: "real^'b" and
    n :: nat
  assume
    card: "Suc n = card X" and
    "\<exists>f. sum f X = 1 \<and> (\<forall>x\<in>X. 0 \<le> f x) \<and> x = (\<Sum>x\<in>X. f x *\<^sub>R x)" and
    hyp:
     "\<And>(X::(real^'b) set) x.
        n = card X \<Longrightarrow>
        \<exists>f. sum f X = 1 \<and> (\<forall>x\<in>X. 0 \<le> f x) \<and> x = (\<Sum>x\<in>X. f x *\<^sub>R x) \<Longrightarrow>
        x \<in> convex hull X"
  then obtain f :: "(real^'b) \<Rightarrow> real" where
    sum: "sum f X = 1" and
    nonneg: "\<forall>x \<in> X. 0 \<le> f x" and 
    x_sum: "x = (\<Sum>x \<in> X. f x *\<^sub>R x)"
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
  hence "n = 0 \<longrightarrow> (\<exists>y. X = {y} \<and> f y = 1)"
    using sum nonneg One_nat_def add.right_neutral 
          card_1_singleton_iff empty_iff finite.emptyI sum.insert sum.neutral
    by (metis (no_types, opaque_lifting))
  hence "n = 0 \<longrightarrow> (\<exists>y. X = {y} \<and> x = y)"
    using x_sum
    by fastforce
  hence "n = 0 \<longrightarrow> x \<in> X"
    by blast
  moreover have "n > 0 \<longrightarrow> x \<in> convex hull X"
  proof (safe)
    assume
      "0 < n"
    hence "card X > 1"
      using card
      by simp
    have "(\<forall>y \<in> X. f y \<ge> 1) \<longrightarrow> sum f X \<ge> sum (\<lambda>x. 1) X"
      using fin
      by (meson sum_mono)
    moreover have "sum (\<lambda>x. 1) X = card X"
      by force
    ultimately have "(\<forall>y \<in> X. f y \<ge> 1) \<longrightarrow> card X \<le> sum f X"
      by force
    hence "(\<forall>y \<in> X. f y \<ge> 1) \<longrightarrow> 1 < sum f X"
      using \<open>card X > 1\<close>
      by linarith
    then obtain y :: "real^'b" where
      "y \<in> X" and
      "f y < 1"
      using sum 
      by auto
    hence "1 - f y \<noteq> 0 \<and> x = f y *\<^sub>R y + (\<Sum>x \<in> X - {y}. f x *\<^sub>R x)"
      by (simp add: fin sum.remove x_sum)
    moreover have
      "\<forall>\<alpha> \<noteq> 0. (\<Sum>x \<in> X - {y}. f x *\<^sub>R x) = \<alpha> *\<^sub>R (\<Sum>x \<in> X - {y}. (f x / \<alpha>) *\<^sub>R x)"
      by (simp add: scaleR_sum_right)
    ultimately have convex_comb:
      "x = f y *\<^sub>R y + (1 - f y) *\<^sub>R (\<Sum>x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x)"
      by auto
    obtain f' :: "real^'b \<Rightarrow> real" where
      def': "f' = (\<lambda>x. f x / (1 - f y))"
      by simp
    hence "\<forall>x \<in> X - {y}. f' x \<ge> 0"
      using nonneg \<open>f y < 1\<close>
      by fastforce
    moreover have 
      "sum f' (X - {y}) = (sum (\<lambda>x. f x) (X - {y}))/(1 - f y)"
      by (simp add: def' sum_divide_distrib)
    moreover have
      "(sum (\<lambda>x. f x) (X - {y}))/(1 - f y) = (1 - f y)/(1 - f y)"
      using sum \<open>y \<in> X\<close>
      by (simp add: fin sum.remove)
    moreover have "(1 - f y)/(1 - f y) = 1"
      using \<open>f y < 1\<close>
      by simp
    ultimately have
      "sum f' (X - {y}) = 1 \<and> (\<forall>x \<in> X - {y}. 0 \<le> f' x) \<and> 
            (\<Sum>x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) = (\<Sum>x \<in> X - {y}. f' x *\<^sub>R x)"
      using def' 
      by fastforce
    hence
      "\<exists>f'. sum f' (X - {y}) = 1 \<and> (\<forall>x \<in> X - {y}. 0 \<le> f' x) \<and> 
            (\<Sum>x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) = (\<Sum>x \<in> X - {y}. f' x *\<^sub>R x)"
      by blast
    moreover have "card (X - {y}) = n"
      using card
      by (simp add: \<open>y \<in> X\<close>)
    ultimately have 
      "(\<Sum>x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) \<in> convex hull (X - {y})"
      using hyp
      by blast 
    hence
      "(\<Sum>x \<in> X - {y}. (f x / (1 - f y)) *\<^sub>R x) \<in> convex hull X"
      by (meson Diff_subset hull_mono in_mono)
    moreover have "f y \<ge> 0 \<and> 1 - f y \<ge> 0"
      using \<open>f y < 1\<close> nonneg \<open>y \<in> X\<close>
      by simp
    moreover have "f y + (1 - f y) \<ge> 0"
      by simp
    moreover have "y \<in> convex hull X"
      using \<open>y \<in> X\<close>
      by (simp add: hull_inc)
    moreover have 
      "\<forall>x y. x \<in> convex hull X \<and> y \<in> convex hull X \<longrightarrow> 
        (\<forall>a \<ge> 0. \<forall>b \<ge> 0. a + b = 1 \<longrightarrow> a *\<^sub>R x + b *\<^sub>R y \<in> convex hull X)"
      using convex_def convex_convex_hull
      by (metis (no_types, opaque_lifting))
    ultimately show "x \<in> convex hull X"
      using convex_comb 
      by auto     
  qed
  ultimately show "x \<in> convex hull X"
    using hull_inc
    by fastforce
qed

lemma standard_simplex_rewrite:
  "convex hull standard_basis = 
    {v::(real^'b). (\<forall>i. v$i \<ge> 0) \<and> sum (($) v) UNIV = 1}"
proof (unfold convex_def hull_def, standard)
  let ?simplex = "{v:: (real^'b). (\<forall>i. v$i \<ge> 0) \<and> sum (($) v) UNIV = 1}"
  have fin_dim: "finite (UNIV::'b set)"
    by simp
  have
    "\<forall>x::(real^'b). \<forall>y. 
      sum (($) (x + y)) UNIV = sum (($) x) UNIV + sum (($) y) UNIV"    
    by (simp add: sum.distrib)
  hence "\<forall>x::(real^'b). \<forall>y. \<forall>u v. 
    sum (($) (u *\<^sub>R x + v *\<^sub>R y)) UNIV =
    sum (($) (u *\<^sub>R x)) UNIV + sum (($) (v *\<^sub>R y)) UNIV"
    by blast
  moreover have
    "\<forall>x u. sum (($) (u *\<^sub>R x)) UNIV = u *\<^sub>R (sum (($) x) UNIV)"
    by (metis (mono_tags, lifting) scaleR_right.sum sum.cong vector_scaleR_component)
  ultimately have "\<forall>x::(real^'b). \<forall>y. \<forall>u v. 
    sum (($) (u *\<^sub>R x + v *\<^sub>R y)) UNIV =
    u *\<^sub>R (sum (($) x) UNIV) + v *\<^sub>R (sum (($) y) UNIV)"
    by (metis (no_types))
  moreover have
    "\<forall>x \<in> ?simplex. sum (($) x) UNIV = 1"
    by simp
  ultimately have
    "\<forall>x \<in> ?simplex. \<forall>y \<in> ?simplex. \<forall>u v.
      sum (($) (u *\<^sub>R x + v *\<^sub>R y)) UNIV = u *\<^sub>R 1 + v *\<^sub>R 1"
    by (metis (no_types, lifting))
  hence 
    "\<forall>x \<in> ?simplex. \<forall>y \<in> ?simplex. \<forall>u v. sum (($) (u *\<^sub>R x + v *\<^sub>R y)) UNIV = u + v"
    by simp
  moreover have 
    "\<forall>x \<in> ?simplex. \<forall>y \<in> ?simplex. \<forall>u \<ge> 0. \<forall>v \<ge> 0. 
      u + v = 1 \<longrightarrow> (\<forall>i. (u *\<^sub>R x + v *\<^sub>R y)$i \<ge> 0)"
    by simp
  ultimately have simplex_convex:
    "\<forall>x \<in> ?simplex. \<forall>y \<in> ?simplex. \<forall>u \<ge> 0. \<forall>v \<ge> 0.
      u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> ?simplex"
    by simp
  have entries:
    "\<forall>v::(real^'b) \<in> standard_basis. \<exists>b. v$b = 1 \<and> (\<forall>c. c \<noteq> b \<longrightarrow> v$c = 0)"
    unfolding standard_basis_def
    by simp
  then obtain one :: "real^'b \<Rightarrow> 'b" where
    def: "\<forall>v \<in> standard_basis. v$(one v) = 1 \<and> (\<forall>i \<noteq> one v. v$i = 0)"
    by metis
  hence "\<forall>v::(real^'b) \<in> standard_basis. \<forall>b. v$b = 0 \<or> v$b = 1"
    by metis
  hence geq_0: 
    "\<forall>v::(real^'b) \<in> standard_basis. \<forall>b. v$b \<ge> 0"
    by (metis dual_order.refl zero_less_one_class.zero_le_one)
  moreover have
    "\<forall>v::(real^'b) \<in> standard_basis. 
      sum (($) v) UNIV = sum (($) v) (UNIV - {one v}) + v$(one v)"
    using def
    by (metis add.commute finite insert_UNIV sum.insert_remove)
  moreover have
    "\<forall>v \<in> standard_basis. sum (($) v) (UNIV - {one v}) + v$(one v) = 1"
    using def
    by fastforce
  ultimately have "standard_basis \<subseteq> ?simplex"
    by force
  with simplex_convex have
    "?simplex \<in> 
      {t. (\<forall>x\<in>t. \<forall>y\<in>t. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t) \<and>
          standard_basis \<subseteq> t}"
    by blast
  thus
    "\<Inter> {t. (\<forall>x\<in>t. \<forall>y\<in>t. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t) \<and>
           standard_basis \<subseteq> t} \<subseteq> ?simplex"
    by blast
next
  show
    "{v. (\<forall>i. 0 \<le> v $ i) \<and> sum (($) v) UNIV = 1} \<subseteq> 
      \<Inter> {t. (\<forall>x\<in>t. \<forall>y\<in>t. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t) \<and> 
              (standard_basis::((real^'b) set)) \<subseteq> t}"
  proof
    fix
      x :: "real^'b" and
      X :: "(real^'b) set"
    assume
      convex_comb: "x \<in> {v. (\<forall>i. 0 \<le> v $ i) \<and> sum (($) v) UNIV = 1}"
    have 
      "\<forall>v \<in> standard_basis. (\<exists>b. v$b = 1 \<and> (\<forall>b' \<noteq> b. v$b' = 0))"
      using standard_basis_def
      by auto
    then obtain ind :: "(real^'b) \<Rightarrow> 'b" where
      ind_1: "\<forall>v \<in> standard_basis. v$(ind v) = 1" and
      ind_0: "\<forall>v \<in> standard_basis. \<forall>b \<noteq> (ind v). v$b = 0"
      by metis
    hence 
      "\<forall>v v'. v \<in> standard_basis \<and> v' \<in> standard_basis \<longrightarrow> ind v = ind v' \<longrightarrow>   
        (\<forall>b. v$b = v'$b)"
      by metis
    hence inj_ind:
      "\<forall>v v'. v \<in> standard_basis \<and> v' \<in> standard_basis \<longrightarrow> ind v = ind v' \<longrightarrow> v = v'"
      by (simp add: vec_eq_iff)
    hence "inj_on ind standard_basis"
      unfolding inj_on_def
      by blast
    hence bij: "bij_betw ind standard_basis (ind ` standard_basis)"
      unfolding bij_betw_def
      by blast
    obtain ind_inv :: "'b \<Rightarrow> (real^'b)" where
      char_vec: "ind_inv = (\<lambda>b. (\<chi> i. if i = b then 1 else 0))"
      by blast
    hence in_basis: "\<forall>b. ind_inv b \<in> standard_basis"
      unfolding standard_basis_def
      by simp
    moreover with this have ind_inv_map: "\<forall>b. ind (ind_inv b) = b"
      using char_vec ind_0 ind_1
      by (metis axis_def axis_nth zero_neq_one)
    ultimately have "\<forall>b. \<exists>v. v \<in> standard_basis \<and> b = ind v"
      by auto
    hence univ: "ind ` standard_basis = UNIV"
      by blast
    have bij_inv: "bij_betw ind_inv UNIV standard_basis"
      using ind_inv_map bij bij_betw_byWitness[of UNIV ind ind_inv standard_basis]
      by (simp add: in_basis inj_ind image_subset_iff)
    obtain f :: "(real^'b) \<Rightarrow> real" where
      def: "f = (\<lambda>v. if v \<in> standard_basis then x$(ind v) else 0)"
      by blast
    hence
      "sum f standard_basis = sum (\<lambda>v. x$(ind v)) standard_basis"
      by simp
    also have
      "sum (\<lambda>v. x$(ind v)) standard_basis = sum (($) x \<circ> ind) standard_basis"
      using comp_def
      by auto
    also have
      "... = sum (($) x) (ind ` standard_basis)"
      using sum_comp[of ind standard_basis "ind ` standard_basis" "($) x"] bij
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
    have nonneg: "\<forall>v \<in> standard_basis. f v \<ge> 0"
      using def convex_comb
      by simp
    have "\<forall>v \<in> standard_basis. \<forall>i. v$i = (if i = ind v then 1 else 0)"
      using ind_1 ind_0
      by fastforce
    hence "\<forall>v \<in> standard_basis. \<forall>i. x$(ind v) * v$i = 
      (if i = ind v then x$(ind v) else 0)"
      by auto
    hence "\<forall>v \<in> standard_basis. (\<chi> i. x$(ind v) * v$i) = 
      (\<chi> i. if i = ind v then x$(ind v) else 0)"
      by fastforce
    moreover have 
      "\<forall>v. (x$(ind v)) *\<^sub>R v = (\<chi> i. x$(ind v) * v$i)"
      by (simp add: scaleR_vec_def) 
    ultimately have
      "\<forall>v \<in> standard_basis. 
        (x$(ind v)) *\<^sub>R v = (\<chi> i. if i = ind v then x$(ind v) else 0)"
      by simp
    moreover have 
      "sum (\<lambda>x. (f x) *\<^sub>R x) standard_basis = sum (\<lambda>v. (x$(ind v)) *\<^sub>R v) standard_basis"
      using def
      by simp
    ultimately have
      "sum (\<lambda>x. (f x) *\<^sub>R x) standard_basis = 
        sum (\<lambda>v. (\<chi> i. if i = ind v then x$(ind v) else 0)) standard_basis"
      by force
    also have "... = 
      sum (\<lambda>b. (\<chi> i. if i = ind (ind_inv b) then x$(ind (ind_inv b)) else 0)) UNIV"
      using bij_inv
            sum_comp[of ind_inv UNIV standard_basis
              "\<lambda>v. (\<chi> i. if i = ind v then x$(ind v) else 0)"]
      unfolding comp_def
      by blast
    also have "... = sum (\<lambda>b. (\<chi> i. if i = b then x$b else 0)) UNIV"
      using ind_inv_map
      by presburger
    finally have "sum (\<lambda>x. (f x) *\<^sub>R x) standard_basis = 
      sum (\<lambda>b. (\<chi> i. if i = b then x$b else 0)) UNIV"
      by simp
    moreover have 
      "\<forall>b. (sum (\<lambda>b. (\<chi> i. if i = b then x$b else 0)) UNIV)$b = 
        sum (\<lambda>b'. (\<chi> i. if i = b' then x$b' else 0)$b) UNIV"
      using sum_component 
      by blast
    moreover have
      "\<forall>b. (\<lambda>b'. (\<chi> i. if i = b' then x$b' else 0)$b) = 
        (\<lambda>b'. if b' = b then x$b else 0)"
      by force
    moreover have
      "\<forall>b. sum (\<lambda>b'. if b' = b then x$b else 0) UNIV = x$b"
      sorry (* All summands but that one are 0 *)
    ultimately have
      "\<forall>b. (sum (\<lambda>x. (f x) *\<^sub>R x) standard_basis)$b = x$b"
      by simp
    hence "sum (\<lambda>x. (f x) *\<^sub>R x) standard_basis = x"
      by (simp add: vec_eq_iff)
    hence 
      "\<exists>f::(real^'b) \<Rightarrow> real. 
          sum f standard_basis = 1 \<and> 
          (\<forall>x \<in> standard_basis. f x \<ge> 0) \<and> 
          x = sum (\<lambda>x. (f x) *\<^sub>R x) standard_basis"
      using sum_1 nonneg
      by blast
    hence
      "x \<in> convex hull (standard_basis::((real^'b) set))"
      using convex_combination_in_convex_hull[of standard_basis]
      by blast
    thus
      "x \<in> \<Inter> {t. (\<forall>x \<in> t. \<forall>y \<in> t. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> t) \<and>
                    (standard_basis::((real^'b) set)) \<subseteq> t}"
      unfolding convex_def hull_def
      by blast
  qed
qed

lemma anon_hom_equiv_rel:
  fixes
    X :: "('a, 'v) Election set"
  assumes
    "\<forall>E \<in> X. finite (votrs_\<E> E)"
  shows
    "equiv X (anon_hom\<^sub>\<R> X)"
proof (unfold equiv_def, safe)
  show "refl_on X (anon_hom\<^sub>\<R> X)"
    unfolding refl_on_def anon_hom\<^sub>\<R>.simps
    by blast
next
  show "sym (anon_hom\<^sub>\<R> X)"
    unfolding sym_def anon_hom\<^sub>\<R>.simps
    by (simp add: sup_commute)
next
  show "Relation.trans (anon_hom\<^sub>\<R> X)"
  proof 
    fix
      E :: "('a, 'v) Election" and
      E' :: "('a, 'v) Election" and
      F :: "('a, 'v) Election"
    assume
      rel: "(E, E') \<in> anon_hom\<^sub>\<R> X" and
      rel': "(E', F) \<in> anon_hom\<^sub>\<R> X"
    hence fin: "finite (votrs_\<E> E')"
      unfolding anon_hom\<^sub>\<R>.simps
      using assms 
      by fastforce
    from rel rel' have eq_frac:
      "(\<forall>r. vote_fraction r E = vote_fraction r E') \<and>
        (\<forall>r. vote_fraction r E' = vote_fraction r F)"
      unfolding anon_hom\<^sub>\<R>.simps
      by blast
    hence
      "\<forall>r. vote_fraction r E = vote_fraction r F"
      by metis
    thus "(E, F) \<in> anon_hom\<^sub>\<R> X"
      using rel rel' snd_conv
      unfolding anon_hom\<^sub>\<R>.simps 
      by blast
  qed
qed

subsubsection \<open>Simplex Bijection\<close>

text \<open>
  We assume all our elections to consist of a fixed finite alternative set of size n and
  finite subsets of an infinite voter universe. Profiles are linear orders on the alternatives.
  Then we can work on the standard simplex of dimension n! instead of the equivalence 
  classes of the equivalence relation for anonymous + homogeneous voting rules (anon hom):
  Each dimension corresponds to one possible linear order on the alternative set, 
  i.e. the possible preferences.
  Each equivalence class of elections corresponds to a vector whose entries denote the fraction 
  of voters per election in that class who vote the respective corresponding preference.
\<close>
theorem anon_hom\<^sub>\<Q>_iso:
  assumes
    "infinite (UNIV::('v set))" 
    \<comment> \<open>Assume an infinite voter universe so that we can choose arbitrarily large voter sets.\<close>
  shows
    "bij_betw (anon_hom_cls_to_vec::('a::finite, 'v) Election set \<Rightarrow> rat^('a Ordered_Preference)) 
              (anon_hom\<^sub>\<Q> (UNIV::'a set)) (vote_simplex :: (rat^('a Ordered_Preference)) set)"
proof (unfold bij_betw_def inj_on_def, standard, standard, standard, standard)
  fix
    X :: "('a, 'v) Election set" and
    Y :: "('a, 'v) Election set"
  assume
    cls_X: "X \<in> anon_hom\<^sub>\<Q> UNIV" and
    cls_Y: "Y \<in> anon_hom\<^sub>\<Q> UNIV" and
    eq_vec: "anon_hom_cls_to_vec X = anon_hom_cls_to_vec Y"
  have equiv:
    "equiv (fixed_alt_elections UNIV) (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV))"
    using anon_hom_equiv_rel
    unfolding fixed_alt_elections.simps
    by (metis (no_types, lifting) CollectD IntD1 inf_commute)
  hence subset: 
    "X \<noteq> {} \<and> X \<subseteq> fixed_alt_elections UNIV \<and> Y \<noteq> {} \<and> Y \<subseteq> fixed_alt_elections UNIV"
    using cls_X cls_Y in_quotient_imp_non_empty in_quotient_imp_subset
    unfolding anon_hom\<^sub>\<Q>.simps
    by blast
  then obtain E :: "('a, 'v) Election" and E' :: "('a, 'v) Election" where
    "E \<in> X" and "E' \<in> Y"
    by blast
  hence cls_X_E:
    "anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {E} = X"
    using cls_X equiv
    unfolding anon_hom\<^sub>\<Q>.simps
    by (metis (no_types, opaque_lifting) Image_singleton_iff equiv_class_eq quotientE)
  hence
    "\<forall>F \<in> X. (E, F) \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)"
    unfolding Image_def
    by blast
  hence
    "\<forall>F \<in> X. \<forall>p. vote_fraction p F = vote_fraction p E"
    unfolding anon_hom\<^sub>\<R>.simps
    by fastforce
  hence "\<forall>p. vote_fraction p ` X = {vote_fraction p E}"
    using \<open>E \<in> X\<close>
    by blast
  hence "\<forall>p. vote_fraction\<^sub>\<Q> p X = vote_fraction p E"
    unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
    using is_singletonI is_singleton_altdef singleton_set.simps 
          singleton_set_def_if_card_one the_elem_eq
    by metis
  hence eq_X_E: "\<forall>p. (anon_hom_cls_to_vec X)$p = vote_fraction (ord2pref p) E"
    unfolding anon_hom_cls_to_vec.simps
    by (metis vec_lambda_beta)
  have cls_Y_E':
    "anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {E'} = Y"
    using cls_Y equiv \<open>E' \<in> Y\<close>
    unfolding anon_hom\<^sub>\<Q>.simps
    by (metis (no_types, opaque_lifting) Image_singleton_iff equiv_class_eq quotientE)
  hence
    "\<forall>F \<in> Y. (E', F) \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)"
    unfolding Image_def
    by blast
  hence
    "\<forall>F \<in> Y. \<forall>p. vote_fraction p E' = vote_fraction p F"
    unfolding anon_hom\<^sub>\<R>.simps
    by blast
  hence "\<forall>p. vote_fraction p ` Y = {vote_fraction p E'}"
    using \<open>E' \<in> Y\<close>
    by fastforce
  hence "\<forall>p. vote_fraction\<^sub>\<Q> p Y = vote_fraction p E'"
    unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
    using is_singletonI is_singleton_altdef singleton_set.simps 
          singleton_set_def_if_card_one the_elem_eq
    by metis
  hence eq_Y_E': "\<forall>p. (anon_hom_cls_to_vec Y)$p = vote_fraction (ord2pref p) E'"
    unfolding anon_hom_cls_to_vec.simps
    by (metis vec_lambda_beta)
  with eq_X_E eq_vec have
    "\<forall>p. vote_fraction (ord2pref p) E = vote_fraction (ord2pref p) E'"
    by metis
  hence eq_ord:
    "\<forall>p. linear_order p \<longrightarrow> vote_fraction p E = vote_fraction p E'"
    by (metis mem_Collect_eq pref2ord_inverse)
  have
    "(\<forall>v. v \<in> votrs_\<E> E \<longrightarrow> linear_order (prof_\<E> E v)) \<and>
      (\<forall>v. v \<in> votrs_\<E> E' \<longrightarrow> linear_order (prof_\<E> E' v))"
    using subset \<open>E \<in> X\<close> \<open>E' \<in> Y\<close>
    unfolding fixed_alt_elections.simps valid_elections_def profile_def
    by fastforce
  hence "\<forall>p. \<not> (linear_order p) \<longrightarrow> vote_count p E = 0 \<and> vote_count p E' = 0"
    unfolding vote_count.simps
    using card.infinite card_0_eq 
    by auto
  hence "\<forall>p. \<not> (linear_order p) \<longrightarrow> vote_fraction p E = 0 \<and> vote_fraction p E' = 0"
    unfolding vote_fraction.simps
    using int_ops(1) rat_number_collapse(1) 
    by presburger
  with eq_ord have "\<forall>p. vote_fraction p E = vote_fraction p E'"
    by metis
  hence "(E, E') \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)"
    using subset \<open>E \<in> X\<close> \<open>E' \<in> Y\<close> fixed_alt_elections.simps
    unfolding anon_hom\<^sub>\<R>.simps
    by blast
  thus "X = Y"
    using cls_X_E cls_Y_E' equiv
    by (metis (no_types, lifting) equiv_class_eq)
next
  show 
    "(anon_hom_cls_to_vec::('a, 'v) Election set \<Rightarrow> rat^('a Ordered_Preference))
        ` anon_hom\<^sub>\<Q> UNIV = vote_simplex"
  proof (unfold vote_simplex_def, safe)
    fix
      X :: "('a, 'v) Election set"
    assume
      quot: "X \<in> anon_hom\<^sub>\<Q> UNIV" and
      not_simplex: 
        "anon_hom_cls_to_vec X \<notin> rat_vec_set (convex hull standard_basis)"
    have equiv_rel:
      "equiv (fixed_alt_elections UNIV) (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV))"
      using anon_hom_equiv_rel[of "fixed_alt_elections UNIV"] fixed_alt_elections.simps
      by blast
    then obtain E :: "('a, 'v) Election" where 
      "E \<in> X" and
      "X = anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {E}"
      using quot
      by (metis anon_hom\<^sub>\<Q>.simps equiv_Eps_in proj_Eps proj_def)
    hence rel: "\<forall>E' \<in> X. (E, E') \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)"
      by blast   
    hence "\<forall>p. \<forall>E' \<in> X. vote_fraction (ord2pref p) E' = vote_fraction (ord2pref p) E"
      unfolding anon_hom\<^sub>\<R>.simps
      by fastforce
    hence "\<forall>p. vote_fraction (ord2pref p) ` X = {vote_fraction (ord2pref p) E}"
      using \<open>E \<in> X\<close> 
      by blast
    hence repr:
      "\<forall>p. vote_fraction\<^sub>\<Q> (ord2pref p) X = vote_fraction (ord2pref p) E"
      unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
      by (metis is_singletonI is_singleton_altdef singleton_set.simps 
                singleton_set_def_if_card_one the_elem_eq)
    have "\<forall>p. vote_count (ord2pref p) E \<ge> 0"
      unfolding vote_count.simps
      by blast
    hence
      "\<forall>p. card (votrs_\<E> E) > 0 \<longrightarrow> 
        Fract (int (vote_count (ord2pref p) E)) (int (card (votrs_\<E> E))) \<ge> 0"
      using zero_le_Fract_iff 
      by auto
    hence
      "\<forall>p. vote_fraction (ord2pref p) E \<ge> 0"
      unfolding vote_fraction.simps
      by (simp add: card_gt_0_iff)
    hence
      "\<forall>p. vote_fraction\<^sub>\<Q> (ord2pref p) X \<ge> 0"
      using repr
      by simp
    hence geq_0:
      "\<forall>p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X) \<ge> 0"
      using zero_le_of_rat_iff 
      by blast 
    have 
      "(votrs_\<E> E = {} \<or> infinite (votrs_\<E> E)) \<longrightarrow> 
        (\<forall>p. real_of_rat (vote_fraction p E) = 0)"
      by simp
    hence zero_case:
      "(votrs_\<E> E = {} \<or> infinite (votrs_\<E> E)) \<longrightarrow> 
        (\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = 0"
      using repr
      by (simp add: zero_vec_def)
    have "finite (UNIV::('a \<times> 'a) set)"
      by simp
    hence eq_card:
      "finite (votrs_\<E> E) \<longrightarrow>
        card (votrs_\<E> E) = sum (\<lambda>p. vote_count p E) UNIV"
      using vote_count_sum
      by metis
    hence
      "(finite (votrs_\<E> E) \<and> votrs_\<E> E \<noteq> {}) \<longrightarrow>
        sum (\<lambda>p. vote_fraction p E) UNIV = 
          sum (\<lambda>p. Fract (vote_count p E) (sum (\<lambda>p. vote_count p E) UNIV)) UNIV"
      unfolding vote_fraction.simps
      by presburger
    moreover have gt_0:
      "(finite (votrs_\<E> E) \<and> votrs_\<E> E \<noteq> {}) \<longrightarrow> sum (\<lambda>p. vote_count p E) UNIV > 0"
      using eq_card
      by fastforce
    moreover with this have
      "sum (\<lambda>p. Fract (vote_count p E) (sum (\<lambda>p. vote_count p E) UNIV)) UNIV =
        Fract (sum (\<lambda>p. (vote_count p E)) UNIV) (sum (\<lambda>p. vote_count p E) UNIV)"
      sorry (* Use that addition of rationals is distributive? *)
    moreover have
      "Fract (sum (\<lambda>p. (vote_count p E)) UNIV) (sum (\<lambda>p. vote_count p E) UNIV) = 1"
      using gt_0 One_rat_def
            Fract_coprime[of 
              "sum (\<lambda>p. (vote_count p E)) UNIV" "sum (\<lambda>p. (vote_count p E)) UNIV"]
      sorry (* Fract n n = 1 if n isn't 0, which it isn't here. *)
    ultimately have sum_1:
      "(finite (votrs_\<E> E) \<and> votrs_\<E> E \<noteq> {}) \<longrightarrow>
        sum (\<lambda>p. vote_fraction p E) UNIV = 1"
      by presburger     
    have inv_of_rat: "\<forall>x \<in> \<rat>. the_inv of_rat (of_rat x) = x"
      unfolding Rats_def 
      using the_inv_f_f
      by (metis injI of_rat_eq_iff)
    have "E \<in> fixed_alt_elections UNIV"
      using quot \<open>E \<in> X\<close> equiv_class_eq_iff equiv_rel rel
      unfolding anon_hom\<^sub>\<Q>.simps quotient_def
      by meson
    hence "\<forall>v \<in> votrs_\<E> E. linear_order (prof_\<E> E v)"
      unfolding fixed_alt_elections.simps valid_elections_def profile_def
      by auto
    hence "\<forall>p. (\<not> linear_order p) \<longrightarrow> vote_count p E = 0"
      unfolding vote_count.simps 
      using card.infinite card_0_eq 
      by auto
    hence "\<forall>p. (\<not> linear_order p) \<longrightarrow> vote_fraction p E = 0"
      unfolding vote_fraction.simps
      by (simp add: rat_number_collapse)
    hence 
      "sum (\<lambda>p. vote_fraction p E) UNIV = 
        sum (\<lambda>p. vote_fraction p E) {p. linear_order p}"
      sorry 
      (* Decompose into sums over disjoint sets where the sum over non-linear orders is 0.*)
    moreover have "bij_betw ord2pref UNIV {p. linear_order p}"
      using inj_def ord2pref_inject range_ord2pref
      unfolding bij_betw_def
      by blast
    ultimately have
      "sum (\<lambda>p. vote_fraction p E) UNIV =
        sum (\<lambda>p. vote_fraction (ord2pref p) E) UNIV"
      using comp_def[of "\<lambda>p. vote_fraction p E" ord2pref]
            sum_comp[of ord2pref UNIV "{p. linear_order p}" "\<lambda>p. vote_fraction p E"]
      by auto
    hence "(finite (votrs_\<E> E) \<and> votrs_\<E> E \<noteq> {}) \<longrightarrow>
      sum (\<lambda>p. vote_fraction (ord2pref p) E) UNIV = 1"
      using sum_1
      by presburger
    hence
      "(finite (votrs_\<E> E) \<and> votrs_\<E> E \<noteq> {}) \<longrightarrow>
        sum (\<lambda>p. real_of_rat (vote_fraction (ord2pref p) E)) UNIV = 1"
      by (metis of_rat_1 of_rat_sum)
    with zero_case have
      "(\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = 0 \<or>
        sum (\<lambda>p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) UNIV = 1"
      using repr 
      by force
    hence
      "(\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = 0 \<or>
        ((\<forall>p. (\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))$p \<ge> 0) \<and>
          sum (($) (\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))) UNIV = 1)"
      using geq_0
      by force
    moreover have rat_entries:
      "\<forall>p. (\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))$p \<in> \<rat>"
      by simp
    ultimately have simplex_el:
      "(\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) \<in>
        {x \<in> insert 0 (convex hull standard_basis). \<forall>i. x$i \<in> \<rat>}"
      using standard_simplex_rewrite
      by blast
    moreover have
      "\<forall>p. (rat_vec (\<chi> p. of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)))$p
        = the_inv real_of_rat ((\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) $ p)"
      unfolding rat_vec.simps
      using vec_lambda_beta 
      by blast
    moreover have
      "\<forall>p. the_inv real_of_rat ((\<chi> p. real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) $ p) =
        the_inv real_of_rat (real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X))"
      by simp
    moreover have
      "\<forall>p. the_inv real_of_rat (real_of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) =
        vote_fraction\<^sub>\<Q> (ord2pref p) X"
      using rat_entries inv_of_rat Rats_eq_range_nat_to_rat_surj surj_nat_to_rat_surj 
      by blast   
    moreover have
      "\<forall>p. vote_fraction\<^sub>\<Q> (ord2pref p) X = (anon_hom_cls_to_vec X)$p"
      by simp
    ultimately have
      "\<forall>p. (rat_vec (\<chi> p. of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)))$p = 
            (anon_hom_cls_to_vec X)$p"
      by metis
    hence
      "rat_vec (\<chi> p. of_rat (vote_fraction\<^sub>\<Q> (ord2pref p) X)) = anon_hom_cls_to_vec X"
      by simp
    with simplex_el have
      "\<exists>x \<in> {x \<in> insert 0 (convex hull standard_basis). \<forall>i. x $ i \<in> \<rat>}. 
        rat_vec x = anon_hom_cls_to_vec X"
      by blast
    with not_simplex have
      "rat_vec 0 = anon_hom_cls_to_vec X"
      using image_iff insertE mem_Collect_eq rat_vec_set.simps
      by (metis (mono_tags, lifting))
    thus "anon_hom_cls_to_vec X = 0"
      unfolding rat_vec.simps
      using Rats_0 inv_of_rat of_rat_0 vec_lambda_unique zero_index
      by (metis (no_types, lifting))      
  next
    have non_empty:
      "(UNIV, {}, \<lambda>v. {}) \<in> 
        (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})"
      unfolding anon_hom\<^sub>\<R>.simps Image_def fixed_alt_elections.simps 
                valid_elections_def profile_def
      by simp
    have in_els:
      "(UNIV, {}, \<lambda>v. {}) \<in> fixed_alt_elections UNIV"
      unfolding fixed_alt_elections.simps valid_elections_def profile_def
      by auto
    have
      "\<forall>r::('a Preference_Relation). vote_fraction r (UNIV, {}, (\<lambda>v. {})) = 0"
      by simp
    hence
      "\<forall>E \<in> (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)) `` {(UNIV, {}, (\<lambda>v. {}))}.
        \<forall>r. vote_fraction r E = 0"
      unfolding anon_hom\<^sub>\<R>.simps
      by auto
    moreover have
       "\<forall>E \<in> (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)) `` {(UNIV, {}, (\<lambda>v. {}))}.
          finite (votrs_\<E> E)"
      unfolding Image_def anon_hom\<^sub>\<R>.simps
      by fastforce
    ultimately have all_zero:
      "\<forall>r. \<forall>E \<in> (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)) `` {(UNIV, {}, (\<lambda>v. {}))}.
        vote_fraction r E = 0" 
      by blast
    hence
      "\<forall>r. 0 \<in> 
        vote_fraction r ` 
          (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)) `` {(UNIV, {}, (\<lambda>v. {}))}"
      using non_empty
      by (metis (mono_tags, lifting) image_eqI)
    hence
      "\<forall>r. {0} \<subseteq> vote_fraction r ` 
        (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})"
      by blast
    moreover have 
       "\<forall>r. {0} \<supseteq> vote_fraction r ` 
        (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})"
      using all_zero
      by blast
    ultimately have
      "\<forall>r. {0} = vote_fraction r ` 
        (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})"
      by blast
    with this have
      "\<forall>r.
        card (vote_fraction r ` 
          (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})) = 1 \<and>
        0 = the_inv (\<lambda>x. {x}) 
        (vote_fraction r ` 
          (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})}))"
      by (metis is_singletonI is_singleton_altdef singleton_insert_inj_eq' 
                singleton_set.simps singleton_set_def_if_card_one)
    hence
      "\<forall>r. 0 = vote_fraction\<^sub>\<Q> r
        (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})"
      unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
      by metis
    hence
      "\<forall>r::('a Ordered_Preference). 0 = vote_fraction\<^sub>\<Q> (ord2pref r)
        (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})"
      by metis
    hence 
      "\<forall>r::('a Ordered_Preference).  
        (anon_hom_cls_to_vec 
          ((anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})))$r = 0"
      unfolding anon_hom_cls_to_vec.simps
      using vec_lambda_beta
      by (metis (no_types))
    moreover have 
       "\<forall>r::('a Ordered_Preference). 0$r = 0"
      by simp
    ultimately have
      "\<forall>r::('a Ordered_Preference). 
        (anon_hom_cls_to_vec 
          ((anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})))$r = 
        (0::(rat^('a Ordered_Preference)))$r"
      by (metis (no_types))
    hence
      "anon_hom_cls_to_vec 
          ((anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})})) = 
        (0::(rat^('a Ordered_Preference)))"
      using vec_eq_iff 
      by blast
    moreover have 
      "(anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, {}, \<lambda>v. {})}) \<in> anon_hom\<^sub>\<Q> UNIV"
      unfolding anon_hom\<^sub>\<Q>.simps quotient_def
      using in_els
      by blast
    ultimately show
      "(0::(rat^('a Ordered_Preference))) \<in> anon_hom_cls_to_vec ` anon_hom\<^sub>\<Q> UNIV"
      by (metis (no_types) image_eqI)
  next
    fix
      x :: "rat^('a Ordered_Preference)"
    assume
      "x \<in> rat_vec_set (convex hull standard_basis)"
    then obtain x' :: "real^('a Ordered_Preference)" where
      conv: "x' \<in> convex hull standard_basis" and
      inv: "\<forall>p. x$p = the_inv real_of_rat (x'$p)" and rat: "\<forall>p. x'$p \<in> \<rat>"
      unfolding rat_vec_set.simps rat_vec.simps
      by force
    hence convex: "(\<forall>p. 0 \<le> x'$p) \<and> sum (($) x') UNIV = 1"
      using standard_simplex_rewrite    
      by blast
    have map: "\<forall>p. x'$p = real_of_rat (x$p)"
      using inv rat the_inv_f_f[of real_of_rat]
      unfolding Rats_def
      by (metis f_the_inv_into_f inj_onCI of_rat_eq_iff)
    have "\<forall>p. \<exists>fract. x$p = Fract (fst fract) (snd fract) \<and> 0 < snd fract"
      using quotient_of_unique
      by blast
    then obtain fraction' :: "'a Ordered_Preference \<Rightarrow> (int \<times> int)" where
      "\<forall>p. x$p = Fract (fst (fraction' p)) (snd (fraction' p))" and
      pos': "\<forall>p. 0 < snd (fraction' p)"
      by metis
    with map have fract':
      "\<forall>p. x'$p = (fst (fraction' p))/(snd (fraction' p))"
      by (metis div_by_0 divide_less_cancel of_int_0 of_int_pos of_rat_rat)
    with convex have "\<forall>p. fst (fraction' p)/(snd (fraction' p)) \<ge> 0"
      by fastforce
    with pos' have "\<forall>p. fst (fraction' p) \<ge> 0"
      by (meson not_less of_int_0_le_iff of_int_pos zero_le_divide_iff)
    with pos' have "\<forall>p. fst (fraction' p) \<in> \<nat> \<and> snd (fraction' p) \<in> \<nat>"
      by (metis nonneg_int_cases of_nat_in_Nats order_less_le)
    hence "\<forall>p. \<exists>(n::nat) m::nat. fst (fraction' p) = n \<and> snd (fraction' p) = m"
      by (meson Nats_cases)
    hence 
      "\<forall>p. \<exists>m::nat \<times> nat. fst (fraction' p) = int (fst m) \<and> 
                            snd (fraction' p) = int (snd m)"
      by simp
    then obtain fraction :: "'a Ordered_Preference \<Rightarrow> (nat \<times> nat)" where
      eq: "\<forall>p. fst (fraction' p) = int (fst (fraction p)) \<and> 
                snd (fraction' p) = int (snd (fraction p))"
      by metis
    with fract' have fract: 
      "\<forall>p. x'$p = (fst (fraction p))/(snd (fraction p))"
      by simp
    from eq pos' have pos:
      "\<forall>p. 0 < snd (fraction p)"
      by simp
    let ?prod = "prod (\<lambda>p. snd (fraction p)) UNIV"
    have fin: "finite (UNIV::('a Ordered_Preference set))"
      by simp
    hence "finite {snd (fraction p) |p. p \<in> UNIV}"
      using finite_Atleast_Atmost_nat 
      by fastforce
    (* TODO Why does this work?
    have "prod (\<lambda>x. x) {n::nat. n > 0} > 0"
      by (simp add: prod_pos) 
    *)
    have pos_prod: "?prod > 0"
      using pos
      by (simp add: prod_pos)
    hence
      "\<forall>p. ?prod mod (snd (fraction p)) = 0"
      using pos finite UNIV_I bits_mod_0 mod_prod_eq mod_self prod_zero
      by (metis (mono_tags, lifting))
    hence div: "\<forall>p. (?prod div (snd (fraction p))) * (snd (fraction p)) = ?prod"
      by (metis add.commute add_0 div_mult_mod_eq)
    obtain voter_amount :: "'a Ordered_Preference \<Rightarrow> nat" where
      def: "voter_amount = (\<lambda>p. (fst (fraction p)) * (?prod div (snd (fraction p))))"
      by blast
        have rewrite_div:
      "\<forall>p. ?prod div (snd (fraction p)) = ?prod/(snd (fraction p))"
      using div less_imp_of_nat_less nonzero_mult_div_cancel_right 
            of_nat_less_0_iff of_nat_mult pos
      by metis
    hence
      "sum voter_amount UNIV = 
        sum (\<lambda>p. (fst (fraction p)) * (?prod/(snd (fraction p)))) UNIV"
      using def
      by simp
    hence
      "sum voter_amount UNIV = 
        ?prod * (sum (\<lambda>p. (fst (fraction p))/(snd (fraction p))) UNIV)"
      by (metis (mono_tags, lifting) mult_of_nat_commute sum.cong times_divide_eq_right vector_space_over_itself.scale_sum_right)
    hence rewrite_sum:
      "sum voter_amount UNIV = ?prod"
      using fract convex
      by (metis (mono_tags, lifting) mult_cancel_left1 of_nat_eq_iff sum.cong)
    obtain V :: "'v set" where
      "finite V" and
      "card V = sum voter_amount UNIV"
      by (meson assms infinite_arbitrarily_large)
    then obtain part :: "'a Ordered_Preference \<Rightarrow> 'v set" where
      partition: "V = \<Union>{part p |p. p \<in> UNIV}" and
      disjoint: "\<forall>p p'. p \<noteq> p' \<longrightarrow> part p \<inter> part p' = {}" and
      card: "\<forall>p. card (part p) = voter_amount p"
      using obtain_partition[of V UNIV voter_amount]
      by auto
    hence exactly_one_prof: "\<forall>v \<in> V. \<exists>!p. v \<in> part p"
      by blast
    then obtain prof' :: "'v \<Rightarrow> 'a Ordered_Preference" where
      maps_to_prof': "\<forall>v \<in> V. v \<in> part (prof' v)"
      by metis
    then obtain prof :: "'v \<Rightarrow> 'a Preference_Relation" where
      prof: "prof = (\<lambda>v. if v \<in> V then ord2pref (prof' v) else {})"
      by blast
    hence election: "(UNIV, V, prof) \<in> fixed_alt_elections UNIV"
      unfolding fixed_alt_elections.simps valid_elections_def profile_def 
      using \<open>finite V\<close> ord2pref 
      by auto
    have "\<forall>p. {v \<in> V. prof' v = p} = {v \<in> V. v \<in> part p}"
      using maps_to_prof' exactly_one_prof
      by fastforce
    hence "\<forall>p. {v \<in> V. prof' v = p} = part p"
      using partition
      by fastforce
    hence "\<forall>p. card {v \<in> V. prof' v = p} = voter_amount p"
      using card
      by presburger 
    moreover have
      "\<forall>p. \<forall>v. (v \<in> {v \<in> V. prof' v = p}) = (v \<in> {v \<in> V. prof v = (ord2pref p)})"
      using prof
      by (simp add: ord2pref_inject)
    ultimately have "\<forall>p. card {v \<in> V. prof v = (ord2pref p)} = voter_amount p"
      by simp
    hence "\<forall>p::'a Ordered_Preference. 
      vote_fraction (ord2pref p) (UNIV, V, prof) = Fract (voter_amount p) (card V)"
      using \<open>finite V\<close> vote_fraction.simps
      by (simp add: rat_number_collapse)
    moreover have
      "\<forall>p. Fract (voter_amount p) (card V) = (voter_amount p)/(card V)"
      by (simp add: Fract_of_int_quotient of_rat_divide)
    moreover have
      "\<forall>p. (voter_amount p)/(card V) = 
            ((fst (fraction p)) * (?prod div (snd (fraction p))))/?prod"
      using card def \<open>card V = sum voter_amount UNIV\<close> rewrite_sum
      by presburger
    moreover have
      "\<forall>p.  ((fst (fraction p)) * (?prod div (snd (fraction p))))/?prod = 
            (fst (fraction p))/(snd (fraction p))"
      using rewrite_div pos_prod 
      by auto
    \<comment> \<open>The percentages of voters voting for each linearly ordered profile in
        (UNIV, V, prof) equal the entries of the given vector.\<close>
    ultimately have eq_vec:
      "\<forall>p::'a Ordered_Preference. 
        vote_fraction (ord2pref p) (UNIV, V, prof) = x'$p"
      using fract
      by presburger
    moreover have
      "\<forall>E \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)}.
        \<forall>p. vote_fraction (ord2pref p) E = vote_fraction (ord2pref p) (UNIV, V, prof)"
      unfolding anon_hom\<^sub>\<R>.simps
      by fastforce
    ultimately have
      "\<forall>E \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)}.
        \<forall>p. vote_fraction (ord2pref p) E = x'$p"
      by simp
    \<comment> \<open>The percentages of voters voting for each linearly ordered profile in
        any election related to (UNIV, V, prof) under the anonymity relation
        equal the entries of the given vector.\<close>
    hence
      "\<forall>E \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)}.
        \<forall>p. vote_fraction (ord2pref p) E = x'$p"
      using eq_vec
      by metis
    hence
      "\<forall>p. \<forall>E \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)}.
       vote_fraction (ord2pref p) E = x'$p"
      by blast
    moreover have
      "\<forall>x \<in> \<rat>. \<forall>y. complex_of_rat y = complex_of_real x \<longrightarrow> y = the_inv real_of_rat x"
      unfolding Rats_def
      sorry (* Do some type magic? *)
    ultimately have all_eq_vec:
      "\<forall>p. \<forall>E \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)}.
       vote_fraction (ord2pref p) E = x$p"
      using rat inv
      by metis      
    moreover have 
      "(UNIV, V, prof) \<in> anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)}"
      using anon_hom\<^sub>\<R>.simps election
      by blast
    ultimately have 
      "\<forall>p. vote_fraction (ord2pref p) ` 
         anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)} \<supseteq> {x$p}"
      using image_insert insert_iff mk_disjoint_insert singletonD subsetI
      by (metis (no_types, lifting))
    with all_eq_vec have
      "\<forall>p. vote_fraction (ord2pref p) ` 
         anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)} = {x$p}"
      by blast
    hence "\<forall>p. vote_fraction\<^sub>\<Q> (ord2pref p)
      (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)}) = x$p"
      unfolding vote_fraction\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
      using is_singletonI is_singleton_altdef 
            singleton_inject singleton_set.simps singleton_set_def_if_card_one
      by metis
    hence 
      "x = anon_hom_cls_to_vec (anon_hom\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, prof)})"
      unfolding anon_hom_cls_to_vec.simps
      using vec_lambda_unique
      by (metis (no_types, lifting))
    moreover have 
      "(anon_hom\<^sub>\<R> (fixed_alt_elections UNIV)) `` {(UNIV, V, prof)} \<in> anon_hom\<^sub>\<Q> UNIV"
      unfolding anon_hom\<^sub>\<Q>.simps quotient_def
      using election
      by blast
    ultimately show 
      "x \<in> (anon_hom_cls_to_vec::('a, 'v) Election set \<Rightarrow> rat^('a Ordered_Preference)) ` 
              anon_hom\<^sub>\<Q> UNIV"
      by blast
  qed
qed

end
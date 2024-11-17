(*  File:       Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance Rationalization\<close>

theory Distance_Rationalization
  imports "Social_Choice_Types/Refined_Types/Preference_List"
          "Consensus_Class"
          "Distance"
begin

text \<open>
  A distance rationalization of a voting rule is its interpretation as a
  procedure that elects an uncontroversial winner if there is one, and
  otherwise elects the alternatives that are as close to becoming an
  uncontroversial winner as possible. Within general distance rationalization,
  a voting rule is characterized by a distance on profiles and a consensus
  class.
\<close>

subsection \<open>Definitions\<close>

text \<open>
  Returns the distance of an election to the preimage of a unique winner
  under the given consensus elections and consensus rule.
\<close>

fun score :: "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class \<Rightarrow>
        ('a, 'v) Election \<Rightarrow> 'r \<Rightarrow> ereal" where
  "score d K E w = Inf (d E ` (\<K>\<^sub>\<E> K w))"

fun (in result) \<R>\<^sub>\<W> :: "('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Consensus_Class \<Rightarrow> 'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow>
        'r set" where
  "\<R>\<^sub>\<W> d K V A p = arg_min_set (score d K (A, V, p)) (limit A UNIV)"

fun (in result) distance_\<R> :: "('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Consensus_Class \<Rightarrow>
        ('a, 'v, 'r Result) Electoral_Module" where
  "distance_\<R> d K V A p =
    (\<R>\<^sub>\<W> d K V A p, (limit A UNIV) - \<R>\<^sub>\<W> d K V A p, {})"

subsection \<open>Standard Definitions\<close>

definition standard :: "('a, 'v) Election Distance \<Rightarrow> bool" where
 "standard d \<equiv>
    \<forall> A A' V V' p p'. (V \<noteq> V' \<or> A \<noteq> A') \<longrightarrow> d (A, V, p) (A', V', p') = \<infinity>"

definition voters_determine_distance :: "('a, 'v) Election Distance \<Rightarrow> bool" where
  "voters_determine_distance d \<equiv>
    \<forall> A A' V V' p q p'.
      (\<forall> v \<in> V. p v = q v)
        \<longrightarrow> (d (A, V, p) (A', V', p') = d (A, V, q) (A', V', p')
          \<and> (d (A', V', p') (A, V, p) = d (A', V', p') (A, V, q)))"

text \<open>
  Creates a set of all possible profiles on a finite alternative set
  that are empty everywhere outside of a given finite voter set.
\<close>

fun profiles :: "'v set \<Rightarrow> 'a set \<Rightarrow> (('a, 'v) Profile) set" where
  "profiles V A =
    (if (infinite A \<or> infinite V)
      then {} else {p. p ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)})"

fun \<K>\<^sub>\<E>_std :: "('a, 'v, 'r Result) Consensus_Class \<Rightarrow> 'r \<Rightarrow> 'a set \<Rightarrow> 'v set \<Rightarrow>
        ('a, 'v) Election set" where
  "\<K>\<^sub>\<E>_std K w A V =
      (\<lambda> p. (A, V, p)) ` (Set.filter
          (\<lambda> p. (consensus_\<K> K) (A, V, p) \<and> elect (rule_\<K> K) V A p = {w})
          (profiles V A))"

text \<open>
  Returns those consensus elections on a given alternative and voter set
  from a given consensus that are mapped to the given unique winner by a
  given consensus rule.
\<close>

fun score_std :: "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class \<Rightarrow>
        ('a, 'v) Election \<Rightarrow> 'r \<Rightarrow> ereal" where
  "score_std d K E w =
        (if \<K>\<^sub>\<E>_std K w (alternatives_\<E> E) (voters_\<E> E) = {}
          then \<infinity> else Min (d E ` (\<K>\<^sub>\<E>_std K w (alternatives_\<E> E) (voters_\<E> E))))"

fun (in result) \<R>\<^sub>\<W>_std :: "('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Consensus_Class \<Rightarrow> 'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow>
        'r set" where
  "\<R>\<^sub>\<W>_std d K V A p = arg_min_set (score_std d K (A, V, p)) (limit A UNIV)"

fun (in result) distance_\<R>_std :: "('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Consensus_Class \<Rightarrow>
        ('a, 'v, 'r Result) Electoral_Module" where
  "distance_\<R>_std d K V A p =
    (\<R>\<^sub>\<W>_std d K V A p, (limit A UNIV) - \<R>\<^sub>\<W>_std d K V A p, {})"

subsection \<open>Auxiliary Lemmas\<close>

lemma fin_\<K>\<^sub>\<E>:
  fixes C :: "('a, 'v, 'r Result) Consensus_Class"
  shows "elections_\<K> C \<subseteq> finite_elections"
proof
  fix E :: "('a, 'v) Election"
  assume "E \<in> elections_\<K> C"
  hence "finite_election E"
    unfolding \<K>\<^sub>\<E>.simps
    by force
  thus "E \<in> finite_elections"
    unfolding finite_elections_def
    by simp
qed

lemma univ_\<K>\<^sub>\<E>:
  fixes C :: "('a, 'v, 'r Result) Consensus_Class"
  shows "elections_\<K> C \<subseteq> UNIV"
  by simp

lemma list_cons_presv_finiteness:
  fixes
    A :: "'a set" and
    S :: "'a list set"
  assumes
    fin_A: "finite A" and
    fin_B: "finite S"
  shows "finite {a#l | a l. a \<in> A \<and> l \<in> S}"
proof -
  let ?P = "\<lambda> A. finite {a#l | a l. a \<in> A \<and> l \<in> S}"
  have "\<forall> a A'. finite A' \<longrightarrow> a \<notin> A' \<longrightarrow> ?P A' \<longrightarrow> ?P (insert a A')"
  proof (clarify)
    fix
      a :: "'a" and
      A' :: "'a set"
    assume
      fin: "finite A'" and
      not_in: "a \<notin> A'" and
      fin_set: "finite {a#l | a l. a \<in> A' \<and> l \<in> S}"
    have "{a'#l | a' l. a' \<in> insert a A' \<and> l \<in> S}
            = {a#l | a l. a \<in> A' \<and> l \<in> S} \<union> {a#l | l. l \<in> S}"
      by auto
    moreover have "finite {a#l | l. l \<in> S}"
      using fin_B
      by simp
    ultimately have "finite {a'#l | a' l. a' \<in> insert a A' \<and> l \<in> S}"
      using fin_set
      by simp
    thus "?P (insert a A')"
      by simp
  qed
  moreover have "?P {}"
    by simp
  ultimately show "?P A"
    using finite_induct[of A ?P] fin_A
    by simp
qed

lemma listset_finiteness:
  fixes l :: "'a set list"
  assumes "\<forall> i :: nat. i < length l \<longrightarrow> finite (l!i)"
  shows "finite (listset l)"
  using assms
proof (induct l)
  case Nil
  show "finite (listset [])"
    by simp
next
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list"
  assume "\<forall> i :: nat < length (a#l). finite ((a#l)!i)"
  hence
    "finite a" and
    "\<forall> i < length l. finite (l!i)"
    by auto
  moreover assume
    "\<forall> i :: nat < length l. finite (l!i) \<Longrightarrow> finite (listset l)"
  ultimately have "finite {a'#l' | a' l'. a' \<in> a \<and> l' \<in> (listset l)}"
    using list_cons_presv_finiteness
    by blast
  thus "finite (listset (a#l))"
    by (simp add: set_Cons_def)
qed

lemma ls_entries_empty_imp_ls_set_empty:
  fixes l :: "'a set list"
  assumes
    "0 < length l" and
    "\<forall> i :: nat. i < length l \<longrightarrow> l!i = {}"
  shows "listset l = {}"
  using assms
proof (induct l)
  case Nil
  thus "listset [] = {}"
    by simp
next
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list" and
    l' :: "'a list"
  assume all_elems_empty: "\<forall> i :: nat < length (a#l). (a#l)!i = {}"
  hence "a = {}"
    by auto
  moreover from all_elems_empty
  have "\<forall> i < length l. l!i = {}"
    by auto
  ultimately have "{a'#l' | a' l'. a' \<in> a \<and> l' \<in> (listset l)} = {}"
    by simp
  thus "listset (a#l) = {}"
    by (simp add: set_Cons_def)
qed

lemma all_ls_elems_same_len:
  fixes l :: "'a set list"
  shows "\<forall> l' :: 'a list. l' \<in> listset l \<longrightarrow> length l' = length l"
proof (induct l, safe)
  case Nil
  fix l :: "'a list"
  assume "l \<in> listset []"
  thus "length l = length []"
    by simp
next
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list" and
    l' :: "'a list"
  assume
    "\<forall> l'. l' \<in> listset l \<longrightarrow> length l' = length l" and
    "l' \<in> listset (a#l)"
  moreover have
    "\<forall> a' l' :: 'a set list.
      listset (a'#l') = {b#m | b m. b \<in> a' \<and> m \<in> listset l'}"
    by (simp add: set_Cons_def)
  ultimately show "length l' = length (a#l)"
    using local.Cons
    by fastforce
qed

lemma fin_all_profs:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    x :: "'a Preference_Relation"
  assumes
    fin_A: "finite A" and
    fin_V: "finite V"
  shows "finite (profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = x})"
proof (cases "A = {}")
  let ?profs = "profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = x}"
  case True
  hence "permutations_of_set A = {[]}"
    unfolding permutations_of_set_def
    by fastforce
  hence "pl_\<alpha> ` permutations_of_set A = {{}}"
    unfolding pl_\<alpha>_def
    by simp
  hence "\<forall> p \<in> profiles V A. \<forall> v. v \<in> V \<longrightarrow> p v = {}"
    by (simp add: image_subset_iff)
  hence "\<forall> p \<in> ?profs. (\<forall> v. v \<in> V \<longrightarrow> p v = {}) \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = x)"
    by simp
  hence "\<forall> p \<in> ?profs. p = (\<lambda> v. if v \<in> V then {} else x)"
    by (metis (no_types, lifting))
  hence "?profs \<subseteq> {\<lambda> v. if v \<in> V then {} else x}"
    by blast
  thus "finite ?profs"
    using finite.emptyI finite_insert finite_subset
    by (metis (no_types, lifting))
next
  let ?profs = "(profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = x})"
  case False
  from fin_V obtain ord :: "'v rel" where
    "linear_order_on V ord"
    using finite_list lin_ord_equiv lin_order_equiv_list_of_alts
    by metis
  then obtain list_V :: "'v list" where
    len: "length list_V = card V" and
    pl: "ord = pl_\<alpha> list_V" and
    perm: "list_V \<in> permutations_of_set V"
    using lin_order_pl_\<alpha> fin_V image_iff length_finite_permutations_of_set
    by metis
  let ?map = "\<lambda> p :: ('a, 'v) Profile. map p list_V"
  have "\<forall> p \<in> profiles V A. \<forall> v \<in> V. p v \<in> (pl_\<alpha> ` permutations_of_set A)"
    by (simp add: image_subset_iff)
  hence "\<forall> p \<in> profiles V A. (\<forall> v \<in> V. linear_order_on A (p v))"
    using pl_\<alpha>_lin_order fin_A False
    by metis
  moreover have "\<forall> p \<in> ?profs. \<forall> i < length (?map p). (?map p)!i = p (list_V!i)"
    by simp
  moreover have "\<forall> i < length list_V. list_V!i \<in> V"
    using perm nth_mem
    unfolding permutations_of_set_def
    by safe
  moreover have lens_eq: "\<forall> p \<in> ?profs. length (?map p) = length list_V"
    by simp
  ultimately have
    "\<forall> p \<in> ?profs. \<forall> i < length (?map p). linear_order_on A ((?map p)!i)"
    by simp
  hence subset_map_profs: "?map ` ?profs \<subseteq> {xs. length xs = card V \<and>
                            (\<forall> i < length xs. linear_order_on A (xs!i))}"
    using len lens_eq
    by fastforce
  have "\<forall> p1 p2.
      p1 \<in> ?profs \<and> p2 \<in> ?profs \<and> p1 \<noteq> p2 \<longrightarrow> (\<exists> v \<in> V. p1 v \<noteq> p2 v)"
    by fastforce
  hence "\<forall> p1 p2.
      p1 \<in> ?profs \<and> p2 \<in> ?profs \<and> p1 \<noteq> p2
        \<longrightarrow> (\<exists> v \<in> set list_V. p1 v \<noteq> p2 v)"
    using perm
    unfolding permutations_of_set_def
    by simp
  hence "\<forall> p1 p2. p1 \<in> ?profs \<and> p2 \<in> ?profs \<and> p1 \<noteq> p2 \<longrightarrow> ?map p1 \<noteq> ?map p2"
    by simp
  hence "inj_on ?map ?profs"
    unfolding inj_on_def
    by blast
  moreover have
    "finite {xs. length xs = card V \<and> (\<forall> i < length xs. linear_order_on A (xs!i))}"
  proof -
    have "finite {r. linear_order_on A r}"
      using fin_A
      unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by simp
    hence fin_supset:
      "\<forall> n. finite {xs. length xs = n \<and> set xs \<subseteq> {r. linear_order_on A r}}"
      using Collect_mono finite_lists_length_eq rev_finite_subset
      by (metis (no_types, lifting))
    have "\<forall> l \<in> {xs. length xs = card V \<and>
                            (\<forall> i < length xs. linear_order_on A (xs!i))}.
                    set l \<subseteq> {r. linear_order_on A r}"
      using in_set_conv_nth mem_Collect_eq subsetI
      by (metis (no_types, lifting))
    hence "{xs. length xs = card V \<and>
                            (\<forall> i < length xs. linear_order_on A (xs!i))}
           \<subseteq> {xs. length xs = card V \<and> set xs \<subseteq> {r. linear_order_on A r}}"
      by blast
    thus ?thesis
      using fin_supset rev_finite_subset
      by blast
  qed
  moreover have "\<forall> f X Y. inj_on f X \<and> finite Y \<and> f ` X \<subseteq> Y \<longrightarrow> finite X"
    using finite_imageD finite_subset
    by metis
  ultimately show "finite ?profs"
    using subset_map_profs
    by blast
qed

lemma profile_permutation_set:
  fixes
    A :: "'a set" and
    V :: "'v set"
  shows "profiles V A = {p :: ('a, 'v) Profile. finite_profile V A p}"
proof (cases "finite A \<and> finite V \<and> A \<noteq> {}")
  case True
  assume "finite A \<and> finite V \<and> A \<noteq> {}"
  hence
    fin_A: "finite A" and
    fin_V: "finite V" and
    non_empty: "A \<noteq> {}"
    by safe
  show "profiles V A = {p'. finite_profile V A p'}"
  proof (standard, clarify)
    fix p :: "'v \<Rightarrow> 'a Preference_Relation"
    assume "p \<in> profiles V A"
    hence "\<forall> v \<in> V. p v \<in> pl_\<alpha> ` permutations_of_set A"
      using fin_A fin_V
      by auto
    hence "\<forall> v \<in> V. linear_order_on A (p v)"
      using fin_A pl_\<alpha>_lin_order non_empty
      by metis
    thus "finite_profile V A p"
      unfolding profile_def
      using fin_A fin_V
      by blast
  next
    show "{p. finite_profile V A p} \<subseteq> profiles V A"
    proof (standard, clarify)
      fix p :: "('a, 'v) Profile"
      assume prof: "profile V A p"
      have "p \<in> {p. p ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)}"
        using fin_A lin_order_pl_\<alpha> prof
        unfolding profile_def
        by blast
      thus "p \<in> profiles V A"
        using fin_A fin_V
        unfolding profiles.simps
        by metis
    qed
  qed
next
  case False
  assume not_fin_empty: "\<not> (finite A \<and> finite V \<and> A \<noteq> {})"
  have "finite A \<and> finite V \<and> A = {} \<longrightarrow> permutations_of_set A = {[]}"
    unfolding permutations_of_set_def
    by fastforce
  hence pl_empty:
    "finite A \<and> finite V \<and> A = {} \<longrightarrow> pl_\<alpha> ` permutations_of_set A = {{}}"
    unfolding pl_\<alpha>_def
    by simp
  hence "finite A \<and> finite V \<and> A = {} \<longrightarrow>
    (\<forall> \<pi> \<in> {\<pi>. \<pi> ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)}. \<forall> v \<in> V. \<pi> v = {})"
    by fastforce
  hence "finite A \<and> finite V \<and> A = {} \<longrightarrow>
    {\<pi>. \<pi> ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)} = {\<pi>. \<forall> v \<in> V. \<pi> v = {}}"
    using image_subset_iff singletonD singletonI pl_empty
    by fastforce
  moreover have "finite A \<and> finite V \<and> A = {}
    \<longrightarrow> profiles V A = {\<pi>. \<pi> ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)}"
    by simp
  ultimately have all_prof_eq: "finite A \<and> finite V \<and> A = {}
    \<longrightarrow> profiles V A = {\<pi>. \<forall> v \<in> V. \<pi> v = {}}"
    by simp
  have "finite A \<and> finite V \<and> A = {}
    \<longrightarrow> (\<forall> p \<in> {p. finite_profile V A p \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = {})}.
      (\<forall> v \<in> V. linear_order_on {} (p v)))"
    unfolding profile_def
    by simp
  moreover have "\<forall> r. linear_order_on {} r \<longrightarrow> r = {}"
    using lin_ord_not_empty
    by metis
  ultimately have non_voters:
    "finite A \<and> finite V \<and> A = {}
    \<longrightarrow> (\<forall> p \<in> {p. finite_profile V A p \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = {})}.
      \<forall> v. p v = {})"
    by blast
  hence "(\<forall> p. profile V {} p \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = {})
            \<longrightarrow> (\<forall> v. p v = {})) \<longrightarrow> finite V \<longrightarrow> A = {}
    \<longrightarrow> {p. profile V {} p} = {p. \<forall> v \<in> V. p v = {}}"
    unfolding profile_def
    using lin_ord_not_empty
    by auto
  hence "finite A \<and> finite V \<and> A = {}
    \<longrightarrow> ({p. finite_profile V A p} = {p. \<forall> v \<in> V. p v = {}})"
    using non_voters
    by blast
  hence "finite A \<and> finite V \<and> A = {}
    \<longrightarrow> profiles V A = {p. finite_profile V A p}"
    using all_prof_eq
    by simp
  moreover have "infinite A \<or> infinite V \<longrightarrow> profiles V A = {}"
    by simp
  moreover have "infinite A \<or> infinite V \<longrightarrow>
    {p. finite_profile V A p \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = {})} = {}"
    by auto
  moreover have "infinite A \<or> infinite V \<or> A = {}"
    using not_fin_empty
    by simp
  ultimately show "profiles V A = {p. finite_profile V A p}"
    by blast
qed

subsection \<open>Soundness\<close>

lemma (in result) \<R>_sound:
  fixes
    K :: "('a, 'v, 'r Result) Consensus_Class" and
    d :: "('a, 'v) Election Distance"
  shows "electoral_module (distance_\<R> d K)"
proof (unfold electoral_module.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  have "\<R>\<^sub>\<W> d K V A p \<subseteq> (limit A UNIV)"
    using \<R>\<^sub>\<W>.simps arg_min_subset
    by metis
  hence "set_equals_partition (limit A UNIV) (distance_\<R> d K V A p)"
    by auto
  moreover have "disjoint3 (distance_\<R> d K V A p)"
    by simp
  ultimately show "well_formed A (distance_\<R> d K V A p)"
    using result_axioms
    unfolding result_def
    by simp
qed

subsection \<open>Properties\<close>

fun distance_decisiveness :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Electoral_Module \<Rightarrow> bool" where
  "distance_decisiveness X d m =
    (\<nexists> E. E \<in> X
    \<and> (\<exists> \<delta> > 0. \<forall> E' \<in> X. d E E' < \<delta> \<longrightarrow> card (elect_r (fun\<^sub>\<E> m E')) > 1))"

subsection \<open>Inference Rules\<close>

lemma (in result) standard_distance_imp_equal_score:
  fixes
    d :: "('a, 'v) Election Distance" and
    K :: "('a, 'v, 'r Result) Consensus_Class" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'r"
  assumes
    irr_non_V: "voters_determine_distance d" and
    std: "standard d"
  shows "score d K (A, V, p) w = score_std d K (A, V, p) w"
proof -
  have profile_perm_set:
    "profiles V A =
      {p' :: ('a, 'v) Profile. finite_profile V A p'}"
    using profile_permutation_set
    by metis
  hence eq_intersect: "\<K>\<^sub>\<E>_std K w A V =
           \<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p' :: ('a, 'v) Profile. finite_profile V A p'}"
    by force
  have "(\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p' :: ('a, 'v) Profile. finite_profile V A p'})
          \<subseteq> (\<K>\<^sub>\<E> K w)"
    by simp
  hence "Inf (d (A, V, p) ` (\<K>\<^sub>\<E> K w)) \<le>
                 Inf (d (A, V, p) ` (\<K>\<^sub>\<E> K w \<inter>
                  Pair A ` Pair V ` {p' :: ('a, 'v) Profile. finite_profile V A p'}))"
    using INF_superset_mono dual_order.refl
    by metis
  moreover have "Inf (d (A, V, p) ` (\<K>\<^sub>\<E> K w)) \<ge>
                 Inf (d (A, V, p) ` (\<K>\<^sub>\<E> K w \<inter>
                  Pair A ` Pair V ` {p' :: ('a, 'v) Profile. finite_profile V A p'}))"
  proof (rule INF_greatest)
    let ?inf = "Inf (d (A, V, p) `
      (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p'. finite_profile V A p'}))"
    let ?compl = "(\<K>\<^sub>\<E> K w) -
      (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p'. finite_profile V A p'})"
    fix i :: "('a, 'v) Election"
    assume el: "i \<in> \<K>\<^sub>\<E> K w"
    have in_intersect:
      "i \<in> (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p'. finite_profile V A p'})
            \<longrightarrow> ?inf \<le> d (A, V, p) i"
      using Complete_Lattices.complete_lattice_class.INF_lower
      by metis
    have compl_imp_neither_voter_nor_alt_nor_infinite_prof:
         "i \<in> ?compl \<longrightarrow> (V \<noteq> fst (snd i)
                            \<or> A \<noteq> fst i
                            \<or> \<not> finite_profile V A (snd (snd i)))"
      by fastforce
    moreover have not_voters_imp_infty: "V \<noteq> fst (snd i) \<longrightarrow> d (A, V, p) i = \<infinity>"
      using std prod.collapse
      unfolding standard_def
      by metis
    moreover have not_alts_imp_infty: "A \<noteq> fst i \<longrightarrow> d (A, V, p) i = \<infinity>"
      using std prod.collapse
      unfolding standard_def
      by metis
    moreover have "V = fst (snd i) \<and> A = fst i
                    \<and> \<not> finite_profile V A (snd (snd i)) \<longrightarrow> False"
      using el
      by fastforce
    hence "i \<in> ?compl \<longrightarrow> d (A, V, p) i = \<infinity>"
      using not_alts_imp_infty not_voters_imp_infty
            compl_imp_neither_voter_nor_alt_nor_infinite_prof
      by fastforce
    ultimately have
      "i \<in> ?compl
        \<longrightarrow> Inf (d (A, V, p)
              ` (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p'. finite_profile V A p'}))
            \<le> d (A, V, p) i"
      using ereal_less_eq
      by (metis (no_types, lifting))
    thus "Inf (d (A, V, p) `
            (\<K>\<^sub>\<E> K w \<inter>
             Pair A ` Pair V ` {p'. finite_profile V A p'}))
           \<le> d (A, V, p) i"
      using in_intersect el
      by blast
  qed
  ultimately have "Inf (d (A, V, p) ` \<K>\<^sub>\<E> K w) =
          Inf (d (A, V, p) `
            (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p'. finite_profile V A p'}))"
    using order_antisym
    by simp
  also have inf_eq_min_for_std_cons:
    "\<dots> = score_std d K (A, V, p) w"
  proof (cases "\<K>\<^sub>\<E>_std K w A V = {}")
    case True
    hence "Inf (d (A, V, p) `
          (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V `
            {p'. finite_profile V A p'})) = \<infinity>"
      using eq_intersect
      using top_ereal_def
      by simp
    also have "score_std d K (A, V, p) w = \<infinity>"
      using True
      unfolding Let_def
      by simp
    finally show ?thesis
      by simp
  next
    case False
    hence fin: "finite A \<and> finite V"
      using eq_intersect
      by blast
    have "\<K>\<^sub>\<E>_std K w A V =
            (\<K>\<^sub>\<E> K w) \<inter> {(A, V, p') | p'. finite_profile V A p'}"
      using eq_intersect
      by blast
    hence subset_dist_\<K>\<^sub>\<E>_std:
        "d (A, V, p) `(\<K>\<^sub>\<E>_std K w A V) \<subseteq>
            d (A, V, p) ` {(A, V, p') | p'. finite_profile V A p'}"
      by blast
    let ?finite_prof = "\<lambda> p' v. (if (v \<in> V) then p' v else {})"
    have "\<forall> p'. finite_profile V A p' \<longrightarrow>
                  finite_profile V A (?finite_prof p')"
      unfolding If_def profile_def
      by simp
    moreover have "\<forall> p'. (\<forall> v. v \<notin> V \<longrightarrow> ?finite_prof p' v = {})"
      by simp
    ultimately have
      "\<forall> (A', V', p') \<in> {(A', V', p'). A' = A \<and> V' = V \<and> finite_profile V A p'}.
            (A', V', ?finite_prof p') \<in> {(A, V, p') | p'. finite_profile V A p'}"
      by force
    moreover have
      "\<forall> p'. d (A, V, p) (A, V, p') = d (A, V, p) (A, V, ?finite_prof p')"
      using irr_non_V
      unfolding voters_determine_distance_def
      by simp
    ultimately have
      "\<forall> (A', V', p') \<in> {(A, V, p') | p'. finite_profile V A p'}.
            (\<exists> (X, Y, z) \<in> {(A, V, p') | p'.
                finite_profile V A p' \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}.
                d (A, V, p) (A', V', p') = d (A, V, p) (X, Y, z))"
      by fastforce
    hence
      "\<forall> (A', V', p')
          \<in> {(A', V', p'). A' = A \<and> V' = V \<and> finite_profile V A p'}.
              d (A, V, p) (A', V', p') \<in>
                d (A, V, p) ` {(A, V, p') | p'.
                  finite_profile V A p' \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}"
      by fastforce
    hence subset_dist_restrict_non_voters:
      "d (A, V, p) ` {(A, V, p') | p'. finite_profile V A p'}
            \<subseteq> d (A, V, p) ` {(A, V, p') | p'.
                  finite_profile V A p' \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}"
      by fastforce
    have "\<forall> (A', V', p') \<in> {(A, V, p') | p'.
            finite_profile V A p' \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}.
              (\<forall> v \<in> V. linear_order_on A (p' v))
                          \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})"
      using fin
      unfolding profile_def
      by simp
    hence subset_lin_ord:
      "{(A, V, p') | p'. finite_profile V A p' \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}
            \<subseteq> {(A, V, p') | p'. p' \<in> {p'.
                (\<forall> v \<in> V. linear_order_on A (p' v)) \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}}"
      by blast
    have "{p'. (\<forall> v \<in> V. linear_order_on A (p' v))
                  \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}
                \<subseteq> profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = {}}"
      using lin_order_pl_\<alpha> fin
      by fastforce
    moreover have "finite (profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = {}})"
      using fin fin_all_profs
      by blast
    ultimately have
      "finite {p'. (\<forall> v \<in> V.
          linear_order_on A (p' v)) \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}"
      using rev_finite_subset
      by blast
    hence "finite {(A, V, p') | p'. p' \<in> {p'.
            (\<forall> v \<in> V. linear_order_on A (p' v)) \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}}"
      by simp
    hence "finite {(A, V, p') | p'.
              finite_profile V A p' \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}"
      using subset_lin_ord rev_finite_subset
      by simp
    hence "finite (d (A, V, p) ` {(A, V, p') | p'.
              finite_profile V A p' \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})})"
      by simp
    hence "finite (d (A, V, p) ` {(A, V, p') | p'. finite_profile V A p'})"
      using subset_dist_restrict_non_voters rev_finite_subset
      by simp
    hence "finite (d (A, V, p) `(\<K>\<^sub>\<E>_std K w A V))"
      using subset_dist_\<K>\<^sub>\<E>_std rev_finite_subset
      by blast
    moreover have "d (A, V, p) ` (\<K>\<^sub>\<E>_std K w A V) \<noteq> {}"
      using False
      by simp
    ultimately have
      "Inf (d (A, V, p) ` (\<K>\<^sub>\<E>_std K w A V)) =
          Min (d (A, V, p) ` (\<K>\<^sub>\<E>_std K w A V))"
      using Min_Inf False
      by metis
    also have "\<dots> = score_std d K (A, V, p) w"
      using False
      by simp
    also have "Inf (d (A, V, p) ` (\<K>\<^sub>\<E>_std K w A V)) =
      Inf (d (A, V, p) ` (\<K>\<^sub>\<E> K w \<inter>
        Pair A ` Pair V ` {p'. finite_profile V A p'}))"
      using eq_intersect
      by simp
    ultimately show ?thesis
      by simp
  qed
  finally show "score d K (A, V, p) w = score_std d K (A, V, p) w"
    by simp
qed

lemma (in result) anonymous_distance_and_consensus_imp_rule_anonymity:
  fixes
    d :: "('a, 'v) Election Distance" and
    K :: "('a, 'v, 'r Result) Consensus_Class"
  assumes
    d_anon: "distance_anonymity d" and
    K_anon: "consensus_rule_anonymity K"
  shows "anonymity (distance_\<R> d K)"
proof (unfold anonymity_def Let_def, safe)
  show "electoral_module (distance_\<R> d K)"
    using \<R>_sound
    by metis
next
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    bijective: "bij \<pi>" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)"
  hence eq_univ: "limit A UNIV = limit A' UNIV"
    by simp
  have dist_rename_inv:
    "\<forall> E :: ('a, 'v) Election. d (A, V, p) E = d (A', V', q) (rename \<pi> E)"
    using d_anon bijective renamed surj_pair
    unfolding distance_anonymity_def
    by metis
  hence "\<forall> S :: ('a, 'v) Election set.
            (d (A, V, p) ` S) \<subseteq> (d (A', V', q) ` (rename \<pi> ` S))"
    by blast
  moreover have
    "\<forall> S :: ('a, 'v) Election set.
        ((d (A', V', q) ` (rename \<pi> ` S)) \<subseteq> (d (A, V, p) ` S))"
  proof (clarify)
    fix
      S :: "('a, 'v) Election set" and
      X X' :: "'a set" and
      Y Y' :: "'v set" and
      z z' :: "('a, 'v) Profile"
    assume "(X', Y', z') = rename \<pi> (X, Y, z)"
    hence "d (A', V', q) (X', Y', z') = d (A, V, p) (X, Y, z)"
      using dist_rename_inv
      by metis
    moreover assume "(X, Y, z) \<in> S"
    ultimately show "d (A', V', q) (X', Y', z') \<in> d (A, V, p) ` S"
      by simp
  qed
  ultimately have eq_range:
    "\<forall> S :: ('a, 'v) Election set.
        (d (A, V, p) ` S) = (d (A', V', q) ` (rename \<pi> ` S))"
    by blast
  have "\<forall> w. rename \<pi> ` (\<K>\<^sub>\<E> K w) \<subseteq> (\<K>\<^sub>\<E> K w)"
  proof (clarify)
    fix
      w :: "'r" and
      A A' :: "'a set" and
      V V' :: "'v set" and
      p p' :: "('a, 'v) Profile"
    assume "(A, V, p) \<in> \<K>\<^sub>\<E> K w"
    hence cons:
      "(consensus_\<K> K) (A, V, p) \<and> finite_profile V A p
        \<and> elect (rule_\<K> K) V A p = {w}"
      by simp
    moreover assume renamed: "(A', V', p') = rename \<pi> (A, V, p)"
    ultimately have "finite_profile V' A' p'"
      using bijective fst_conv rename_finite rename_prof
      unfolding rename.simps
      by metis
    moreover from this have cons_img:
      "consensus_\<K> K (A', V', p') \<and> (rule_\<K> K V A p = rule_\<K> K V' A' p')"
      using K_anon renamed bijective cons
      unfolding consensus_rule_anonymity_def Let_def
      by simp
    ultimately show "(A', V', p') \<in> \<K>\<^sub>\<E> K w"
      using cons
      by simp
  qed
  moreover have "\<forall> w. (\<K>\<^sub>\<E> K w) \<subseteq> rename \<pi> ` (\<K>\<^sub>\<E> K w)"
  proof (clarify)
    fix
      w :: "'r" and
      A :: "'a set" and
      V :: "'v set" and
      p :: "('a, 'v) Profile"
    assume "(A, V, p) \<in> \<K>\<^sub>\<E> K w"
    hence cons:
      "(consensus_\<K> K) (A, V, p) \<and> finite_profile V A p
            \<and> elect (rule_\<K> K) V A p = {w}"
      by simp
    let ?inv = "rename (the_inv \<pi>) (A, V, p)"
    have inv_inv_id: "the_inv (the_inv \<pi>) = \<pi>"
      using the_inv_f_f bijective bij_betw_imp_inj_on bij_betw_imp_surj
            inj_on_the_inv_into surj_imp_inv_eq the_inv_into_onto
      by (metis (no_types, opaque_lifting))
    hence "?inv = (A, ((the_inv \<pi>) ` V), p \<circ> (the_inv (the_inv \<pi>)))"
      by simp
    moreover have "(p \<circ> (the_inv (the_inv \<pi>))) \<circ> (the_inv \<pi>) = p"
      using bijective inv_inv_id
      unfolding bij_betw_def comp_def
      by (simp add: f_the_inv_into_f)
    moreover have "\<pi> ` (the_inv \<pi>) ` V = V"
      using bijective the_inv_f_f image_inv_into_cancel top_greatest
            surj_imp_inv_eq
      unfolding bij_betw_def
      by (metis (no_types, opaque_lifting))
    ultimately have preimg: "rename \<pi> ?inv = (A, V, p)"
      unfolding Let_def
      by simp
    have "bij (the_inv \<pi>)"
      using bijective bij_betw_the_inv_into
      by metis
    moreover from this have fin_preimg:
      "finite_profile (fst (snd ?inv)) (fst ?inv) (snd (snd ?inv))"
      using rename_prof cons
      by fastforce
    ultimately have
      "consensus_\<K> K ?inv \<and>
          (rule_\<K> K V A p =
              rule_\<K> K (fst (snd ?inv)) (fst ?inv) (snd (snd ?inv)))"
      using K_anon renamed bijective cons
      unfolding consensus_rule_anonymity_def Let_def
      by simp
    moreover from this have
      "elect (rule_\<K> K) (fst (snd ?inv)) (fst ?inv) (snd (snd ?inv)) = {w}"
      using cons
      by simp
    ultimately have "?inv \<in> \<K>\<^sub>\<E> K w"
      using fin_preimg
      by simp
    thus "(A, V, p) \<in> rename \<pi> ` \<K>\<^sub>\<E> K w"
      using preimg image_eqI
      by metis
  qed
  ultimately have "\<forall> w. (\<K>\<^sub>\<E> K w) = rename \<pi> ` (\<K>\<^sub>\<E> K w)"
    by blast
  hence "\<forall> w. score d K (A, V, p) w = score d K (A', V', q) w"
    using eq_range
    by simp
  hence "arg_min_set (score d K (A, V, p)) (limit A UNIV) =
            arg_min_set (score d K (A', V', q)) (limit A' UNIV)"
    using eq_univ
    by presburger
  hence "\<R>\<^sub>\<W> d K V A p = \<R>\<^sub>\<W> d K V' A' q"
    by simp
  thus "distance_\<R> d K V A p = distance_\<R> d K V' A' q"
    using eq_univ
    by simp
qed

end
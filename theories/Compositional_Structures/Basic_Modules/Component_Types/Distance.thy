(*  File:       Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Component Types\<close>

section \<open>Distance\<close>

theory Distance
  imports "HOL-Library.Extended_Real"
          "Social_Choice_Types/Voting_Symmetry"
begin

text \<open>
  A general distance on a set X is a mapping \<open>d: X \<times> X \<mapsto> R \<union> {+\<infinity>}\<close> such
  that for every \<open>x, y, z\<close> in X, the following four conditions are satisfied:
  \<^item> \<open>d(x, y) \<ge> 0\<close> (non-negativity);
  \<^item> \<open>d(x, y) = 0\<close> if and only if \<open>x = y\<close> (identity of indiscernibles);
  \<^item> \<open>d(x, y) = d(y, x)\<close> (symmetry);
  \<^item> \<open>d(x, y) \<le> d(x, z) + d(z, y)\<close> (triangle inequality).

  Moreover, a mapping that satisfies all but the second conditions is called
  a pseudo-distance, whereas a quasi-distance needs to satisfy the first three
  conditions (and not necessarily the last one).
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Distance = "'a \<Rightarrow> 'a \<Rightarrow> ereal"

text \<open>The un-curried version of a distance is defined on tuples.\<close>

fun tup :: "'a Distance \<Rightarrow> ('a * 'a \<Rightarrow> ereal)" where
  "tup d = (\<lambda> pair. d (fst pair) (snd pair))"

definition distance :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "distance S d \<equiv> \<forall> x y. x \<in> S \<and> y \<in> S \<longrightarrow> d x x = 0 \<and> 0 \<le> d x y"

subsection \<open>Conditions\<close>

definition symmetric :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "symmetric S d \<equiv> \<forall> x y. x \<in> S \<and> y \<in> S \<longrightarrow> d x y = d y x"

definition triangle_ineq :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "triangle_ineq S d \<equiv> \<forall> x y z. x \<in> S \<and> y \<in> S \<and> z \<in> S \<longrightarrow> d x z \<le> d x y + d y z"

definition eq_if_zero :: "'a set \<Rightarrow> 'a Distance \<Rightarrow> bool" where
  "eq_if_zero S d \<equiv> \<forall> x y. x \<in> S \<and> y \<in> S \<longrightarrow> d x y = 0 \<longrightarrow> x = y"

definition vote_distance :: "('a Vote set \<Rightarrow> 'a Vote Distance \<Rightarrow> bool) \<Rightarrow>
        'a Vote Distance \<Rightarrow> bool" where
  "vote_distance \<pi> d \<equiv> \<pi> {(A, p). linear_order_on A p \<and> finite A} d"

definition election_distance :: "(('a, 'v) Election set \<Rightarrow>
        ('a, 'v) Election Distance \<Rightarrow> bool) \<Rightarrow>
            ('a, 'v) Election Distance \<Rightarrow> bool" where
  "election_distance \<pi> d \<equiv> \<pi> {(A, V, p). finite_profile V A p} d"

subsection \<open>Standard-Distance Property\<close>

definition standard :: "('a, 'v) Election Distance \<Rightarrow> bool" where
 "standard d \<equiv>
    \<forall> A A' V V' p p'. A \<noteq> A' \<or> V \<noteq> V' \<longrightarrow> d (A, V, p) (A', V', p') = \<infinity>"

subsection \<open>Auxiliary Lemmas\<close>

fun arg_min_set :: "('b \<Rightarrow> 'a :: ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "arg_min_set f A = Collect (is_arg_min f (\<lambda> a. a \<in> A))"

lemma arg_min_subset:
  fixes
    B :: "'b set" and
    f :: "'b \<Rightarrow> 'a :: ord"
  shows "arg_min_set f B \<subseteq> B"
  unfolding arg_min_set.simps is_arg_min_def
  by safe

lemma sum_monotone:
  fixes
    A :: "'a set" and
    f g :: "'a \<Rightarrow> int"
  assumes "\<forall> a \<in> A. f a \<le> g a"
  shows "(\<Sum> a \<in> A. f a) \<le> (\<Sum> a \<in> A. g a)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (infinite A)
  fix A :: "'a set"
  show ?case
    using infinite
    by simp
next
  case empty
  show ?case
    by simp
next
  case (insert x F)
  fix
    x :: "'a" and
    F :: "'a set"
  show ?case
    using insert
    by simp
qed

lemma distrib:
  fixes
    A :: "'a set" and
    f g :: "'a \<Rightarrow> int"
  shows "(\<Sum> a \<in> A. f a) + (\<Sum> a \<in> A. g a) = (\<Sum> a \<in> A. f a + g a)"
  using sum.distrib
  by metis

lemma distrib_ereal:
  fixes
    A :: "'a set" and
    f g :: "'a \<Rightarrow> int"
  shows "ereal (real_of_int ((\<Sum> a \<in> A. (f :: 'a \<Rightarrow> int) a) + (\<Sum> a \<in> A. g a))) =
    ereal (real_of_int (\<Sum> a \<in> A. f a + g a))"
  using distrib
  by metis

lemma uneq_ereal:
  fixes x y :: "int"
  assumes "x \<le> y"
  shows "ereal (real_of_int x) \<le> ereal (real_of_int y)"
  using assms
  by simp

subsection \<open>Swap Distance\<close>

fun neq_ord :: "'a Preference_Relation \<Rightarrow> 'a Preference_Relation \<Rightarrow>
        'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "neq_ord r s a b = ((a \<preceq>\<^sub>r b \<and> b \<preceq>\<^sub>s a) \<or> (b \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s b))"

fun pairwise_disagreements :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow>
        'a Preference_Relation \<Rightarrow> ('a \<times> 'a) set" where
  "pairwise_disagreements A r s = {(a, b) \<in> A \<times> A. a \<noteq> b \<and> neq_ord r s a b}"

fun pairwise_disagreements' :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow>
        'a Preference_Relation \<Rightarrow> ('a \<times> 'a) set" where
  "pairwise_disagreements' A r s =
      Set.filter (\<lambda> (a, b). a \<noteq> b \<and> neq_ord r s a b) (A \<times> A)"

lemma set_eq_filter:
  fixes
    X :: "'a set" and
    P :: "'a \<Rightarrow> bool"
  shows "{x \<in> X. P x} = Set.filter P X"
  by auto

lemma pairwise_disagreements_eq[code]: "pairwise_disagreements = pairwise_disagreements'"
  unfolding pairwise_disagreements.simps pairwise_disagreements'.simps
  by fastforce

fun swap :: "'a Vote Distance" where
  "swap (A, r) (A', r') =
    (if A = A'
    then card (pairwise_disagreements A r r')
    else \<infinity>)"

lemma swap_case_infinity:
  fixes x y :: "'a Vote"
  assumes "alts_\<V> x \<noteq> alts_\<V> y"
  shows "swap x y = \<infinity>"
  using assms
  by (induction rule: swap.induct, simp)

lemma swap_case_fin:
  fixes x y :: "'a Vote"
  assumes "alts_\<V> x = alts_\<V> y"
  shows "swap x y = card (pairwise_disagreements (alts_\<V> x) (pref_\<V> x) (pref_\<V> y))"
  using assms
  by (induction rule: swap.induct, simp)

subsection \<open>Spearman Distance\<close>

fun spearman :: "'a Vote Distance" where
  "spearman (A, x) (A', y) =
    (if A = A'
    then \<Sum> a \<in> A. abs (int (rank x a) - int (rank y a))
    else \<infinity>)"

lemma spearman_case_inf:
  fixes x y :: "'a Vote"
  assumes "alts_\<V> x \<noteq> alts_\<V> y"
  shows "spearman x y = \<infinity>"
  using assms
  by (induction rule: spearman.induct, simp)

lemma spearman_case_fin:
  fixes x y :: "'a Vote"
  assumes "alts_\<V> x = alts_\<V> y"
  shows "spearman x y =
    (\<Sum> a \<in> alts_\<V> x. abs (int (rank (pref_\<V> x) a) - int (rank (pref_\<V> y) a)))"
  using assms
  by (induction rule: spearman.induct, simp)

subsection \<open>Properties\<close>

text \<open>
  Distances that are invariant under specific relations induce symmetry
  properties in distance rationalized voting rules.
\<close>

subsubsection \<open>Definitions\<close>

fun total_invariance\<^sub>\<D> :: "'x Distance \<Rightarrow> 'x rel \<Rightarrow> bool" where
  "total_invariance\<^sub>\<D> d rel = is_symmetry (tup d) (Invariance (product rel))"

fun invariance\<^sub>\<D> :: "'y Distance \<Rightarrow> 'x set \<Rightarrow> 'y set \<Rightarrow>
        ('x, 'y) binary_fun \<Rightarrow> bool" where
  "invariance\<^sub>\<D> d X Y \<phi> = is_symmetry (tup d) (Invariance (equivariance X Y \<phi>))"

definition distance_anonymity :: "('a, 'v) Election Distance \<Rightarrow> bool" where
  "distance_anonymity d \<equiv>
    \<forall> A A' V V' p p' \<pi> :: ('v \<Rightarrow> 'v).
      (bij \<pi> \<longrightarrow>
        (d (A, V, p) (A', V', p')) =
          (d (rename \<pi> (A, V, p))) (rename \<pi> (A', V', p')))"

fun distance_anonymity' :: "('a, 'v) Election set \<Rightarrow>
        ('a, 'v) Election Distance \<Rightarrow> bool" where
  "distance_anonymity' X d = invariance\<^sub>\<D> d (carrier bijection\<^sub>\<V>\<^sub>\<G>) X (\<phi>_anon X)"

fun distance_neutrality :: "('a, 'v) Election set \<Rightarrow>
        ('a, 'v) Election Distance \<Rightarrow> bool" where
  "distance_neutrality X d = invariance\<^sub>\<D> d (carrier bijection\<^sub>\<A>\<^sub>\<G>) X (\<phi>_neutral X)"

fun distance_reversal_symmetry :: "('a, 'v) Election set \<Rightarrow>
        ('a, 'v) Election Distance \<Rightarrow> bool" where
  "distance_reversal_symmetry X d =
        invariance\<^sub>\<D> d (carrier reversal\<^sub>\<G>) X (\<phi>_reverse X)"

definition distance_homogeneity' :: "('a, 'v :: linorder) Election set \<Rightarrow>
        ('a, 'v) Election Distance \<Rightarrow> bool" where
  "distance_homogeneity' X d \<equiv> total_invariance\<^sub>\<D> d (homogeneity\<^sub>\<R>' X)"

definition distance_homogeneity :: "('a, 'v) Election set \<Rightarrow>
        ('a, 'v) Election Distance \<Rightarrow> bool" where
  "distance_homogeneity X d \<equiv> total_invariance\<^sub>\<D> d (homogeneity\<^sub>\<R> X)"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma rewrite_total_invariance\<^sub>\<D>:
  fixes
    d :: "'x Distance" and
    r :: "'x rel"
  shows "total_invariance\<^sub>\<D> d r = (\<forall> (x, y) \<in> r. \<forall> (a, b) \<in> r. d a x = d b y)"
proof (unfold total_invariance\<^sub>\<D>.simps is_symmetry.simps product.simps, safe)
  fix a b x y :: "'x"
  assume
    "\<forall> x y. (x, y) \<in> {(p, p').
      (fst p, fst p') \<in> r \<and> (snd p, snd p') \<in> r}
        \<longrightarrow> tup d x = tup d y" and
    "(a, b) \<in> r" and
    "(x, y) \<in> r"
  thus "d a x = d b y"
    unfolding total_invariance\<^sub>\<D>.simps is_symmetry.simps
    by simp
next
  fix a b x y :: "'x"
  assume
    "\<forall> (x, y) \<in> r. \<forall> (a, b) \<in> r. d a x = d b y" and
    "(fst (x, a), fst (y, b)) \<in> r" and
    "(snd (x, a), snd (y, b)) \<in> r"
  hence "d x a = d y b"
    by auto
  thus "tup d (x, a) = tup d (y, b)"
    by simp
qed

lemma rewrite_invariance\<^sub>\<D>:
  fixes
    d :: "'y Distance" and
    X :: "'x set" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  shows "invariance\<^sub>\<D> d X Y \<phi> =
            (\<forall> x \<in> X. \<forall> y \<in> Y. \<forall> z \<in> Y. d y z = d (\<phi> x y) (\<phi> x z))"
proof (unfold invariance\<^sub>\<D>.simps is_symmetry.simps equivariance.simps, safe)
  fix
    x :: "'x" and
    y z :: "'y"
  assume
    "x \<in> X" and
    "y \<in> Y" and
    "z \<in> Y" and
    "\<forall> x y. (x, y) \<in> {((u, v), x, y). (u, v) \<in> Y \<times> Y
                    \<and> (\<exists> z \<in> X. x = \<phi> z u \<and> y = \<phi> z v)}
          \<longrightarrow> tup d x = tup d y"
  thus "d y z = d (\<phi> x y) (\<phi> x z)"
    by fastforce
next
  fix
    x :: "'x" and
    a b :: "'y"
  assume
    "\<forall> x \<in> X. \<forall> y \<in> Y. \<forall> z \<in> Y. d y z = d (\<phi> x y) (\<phi> x z)" and
    "x \<in> X" and
    "a \<in> Y" and
    "b \<in> Y"
  hence "d a b = d (\<phi> x a) (\<phi> x b)"
    by blast
  thus "tup d (a, b) = tup d (\<phi> x a, \<phi> x b)"
    by simp
qed

lemma invar_dist_image:
  fixes
    d :: "'y Distance" and
    G :: "'x monoid" and
    Y Y' :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun" and
    y :: "'y" and
    g :: "'x"
  assumes
    invar_d: "invariance\<^sub>\<D> d (carrier G) Y \<phi>" and
    Y'_in_Y: "Y' \<subseteq> Y" and
    action_\<phi>: "group_action G Y \<phi>" and
    g_carrier: "g \<in> carrier G" and
    y_in_Y: "y \<in> Y"
  shows "d (\<phi> g y) ` (\<phi> g) ` Y' = d y ` Y'"
proof (safe)
  fix y' :: "'y"
  assume y'_in_Y': "y' \<in> Y'"
  hence "((y, y'), ((\<phi> g y), (\<phi> g y'))) \<in> equivariance (carrier G) Y \<phi>"
    using Y'_in_Y y_in_Y g_carrier
    unfolding equivariance.simps
    by blast
  hence eq_dist: "tup d ((\<phi> g y), (\<phi> g y')) = tup d (y, y')"
    using invar_d
    unfolding invariance\<^sub>\<D>.simps
    by fastforce
  thus "d (\<phi> g y) (\<phi> g y') \<in> d y ` Y'"
    using y'_in_Y'
    by simp
  have "\<phi> g y' \<in> \<phi> g ` Y'"
    using y'_in_Y'
    by simp
  thus "d y y' \<in> d (\<phi> g y) ` \<phi> g ` Y'"
    using eq_dist
    by (simp add: rev_image_eqI)
qed

lemma swap_neutral: "invariance\<^sub>\<D> swap (carrier bijection\<^sub>\<A>\<^sub>\<G>)
                        UNIV (\<lambda> \<pi> (A, q). (\<pi> ` A, rel_rename \<pi> q))"
proof (unfold rewrite_invariance\<^sub>\<D>, safe)
  fix
    \<pi> :: "'a \<Rightarrow> 'a" and
    A A' :: "'a set" and
    q q' :: "'a rel"
  assume "\<pi> \<in> carrier bijection\<^sub>\<A>\<^sub>\<G>"
  hence bij_\<pi>: "bij \<pi>"
    unfolding bijection\<^sub>\<A>\<^sub>\<G>_def
    using rewrite_carrier
    by blast
  show "swap (A, q) (A', q') =
          swap (\<pi> ` A, rel_rename \<pi> q) (\<pi> ` A', rel_rename \<pi> q')"
  proof (cases "A = A'")
    let ?f = "(\<lambda> (a, b). (\<pi> a, \<pi> b))"
    let ?swap_set = "{(a, b) \<in> A \<times> A. a \<noteq> b \<and> neq_ord q q' a b}"
    let ?swap_set' =
      "{(a, b) \<in> \<pi> ` A \<times> \<pi> ` A. a \<noteq> b
          \<and> neq_ord (rel_rename \<pi> q) (rel_rename \<pi> q') a b}"
    let ?rel = "{(a, b) \<in> A \<times> A. a \<noteq> b \<and> neq_ord q q' a b}"
    case True
    hence "\<pi> ` A = \<pi> ` A'"
      by simp
    hence "swap (\<pi> ` A, rel_rename \<pi> q) (\<pi> ` A', rel_rename \<pi> q') = card ?swap_set'"
      by simp
    moreover have "bij_betw ?f ?swap_set ?swap_set'"
    proof (unfold bij_betw_def inj_on_def, intro conjI impI ballI)
      fix x y :: "'a \<times> 'a"
      assume
        "x \<in> ?swap_set" and
        "y \<in> ?swap_set" and
        "?f x = ?f y"
      hence
        "\<pi> (fst x) = \<pi> (fst y)" and
        "\<pi> (snd x) = \<pi> (snd y)"
        by auto
      hence
        "fst x = fst y" and
        "snd x = snd y"
        using bij_\<pi> bij_pointE
        by (metis, metis)
      thus "x = y"
        using prod.expand
        by metis
    next
      show "?f ` ?swap_set = ?swap_set'"
      proof
        have "\<forall> a b. (a, b) \<in> A \<times> A \<longrightarrow> (\<pi> a, \<pi> b) \<in> \<pi> ` A \<times> \<pi> ` A"
          by simp
        moreover have "\<forall> a b. a \<noteq> b \<longrightarrow>  \<pi> a \<noteq> \<pi> b"
          using bij_\<pi> bij_pointE
          by metis
        moreover have
          "\<forall> a b. neq_ord q q' a b
            \<longrightarrow> neq_ord (rel_rename \<pi> q) (rel_rename \<pi> q') (\<pi> a) (\<pi> b)"
          unfolding neq_ord.simps rel_rename.simps
          by auto
        ultimately show "?f ` ?swap_set \<subseteq> ?swap_set'"
          by auto
      next
        have "\<forall> a b. (a, b) \<in> (rel_rename \<pi> q) \<longrightarrow> (the_inv \<pi> a, the_inv \<pi> b) \<in> q"
          unfolding rel_rename.simps
          using bij_\<pi> bij_is_inj the_inv_f_f
          by fastforce
        moreover have
          "\<forall> a b. (a, b) \<in> (rel_rename \<pi> q') \<longrightarrow> (the_inv \<pi> a, the_inv \<pi> b) \<in> q'"
          unfolding rel_rename.simps
          using bij_\<pi> bij_is_inj the_inv_f_f
          by fastforce
        ultimately have
          "\<forall> a b. neq_ord (rel_rename \<pi> q) (rel_rename \<pi> q') a b
                  \<longrightarrow> neq_ord q q' (the_inv \<pi> a) (the_inv \<pi> b)"
          by simp
        moreover have
          "\<forall> a b. (a, b) \<in> \<pi> ` A \<times> \<pi> ` A \<longrightarrow> (the_inv \<pi> a, the_inv \<pi> b) \<in> A \<times> A"
          using bij_\<pi> bij_is_inj f_the_inv_into_f inj_image_mem_iff
          by fastforce
        moreover have "\<forall> a b. a \<noteq> b \<longrightarrow> the_inv \<pi> a \<noteq> the_inv \<pi> b"
          using bij_\<pi> UNIV_I bij_betw_imp_surj bij_is_inj f_the_inv_into_f
          by metis
        ultimately have
          "\<forall> a b. (a, b) \<in> ?swap_set' \<longrightarrow> (the_inv \<pi> a, the_inv \<pi> b) \<in> ?swap_set"
          by blast
        moreover have "\<forall> a b. (a, b) = ?f (the_inv \<pi> a, the_inv \<pi> b)"
          using f_the_inv_into_f_bij_betw bij_\<pi>
          by fastforce
        ultimately show "?swap_set' \<subseteq> ?f ` ?swap_set"
          by blast
      qed
    qed
    moreover have "card ?swap_set = swap (A, q) (A', q')"
      using True
      by simp
    ultimately show ?thesis
      by (simp add: bij_betw_same_card)
  next
    case False
    hence "\<pi> ` A \<noteq> \<pi> ` A'"
      using bij_\<pi> bij_is_inj inj_image_eq_iff
      by metis
    thus ?thesis
      using False
      by simp
  qed
qed

end
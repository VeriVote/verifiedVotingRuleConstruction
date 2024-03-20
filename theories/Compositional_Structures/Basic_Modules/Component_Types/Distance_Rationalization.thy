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

fun score :: "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class
        \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'r \<Rightarrow> ereal" where
  "score d K E w = Inf (d E ` (\<K>\<^sub>\<E> K w))"

fun (in result) \<R>\<^sub>\<W> :: "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class \<Rightarrow>
      'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r set" where
  "\<R>\<^sub>\<W> d K V A p = arg_min_set (score d K (A, V, p)) (limit_set A UNIV)"

fun (in result) distance_\<R> :: "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class \<Rightarrow>
      ('a, 'v, 'r Result) Electoral_Module" where
  "distance_\<R> d K V A p = (\<R>\<^sub>\<W> d K V A p, (limit_set A UNIV) - \<R>\<^sub>\<W> d K V A p, {})"

subsection \<open>Standard Definitions\<close>

definition standard :: "('a, 'v) Election Distance \<Rightarrow> bool" where
 "standard d \<equiv> \<forall> A A' V V' p p'. (V \<noteq> V' \<or> A \<noteq> A') \<longrightarrow> d (A, V, p) (A', V', p') = \<infinity>"

definition voters_determine_distance :: "('a, 'v) Election Distance \<Rightarrow> bool" where
  "voters_determine_distance d \<equiv> \<forall> A A' V V' p q p'.
    (\<forall> v \<in> V. p v = q v) \<longrightarrow> (d (A, V, p) (A', V', p') = d (A, V, q) (A', V', p')
                              \<and> (d (A', V', p') (A, V, p) = d (A', V', p') (A, V, q)))"

(*
  We want "profile_permutations n A = {}" for infinite A.
  We have "permutations_of_set A = {} \<longleftrightarrow> \<not> finite A"
    (Multiset_Permutations.permutations_of_set_empty_iff).
    "listset (replicate 0 (list_to_rel ` {})" is "{[]}", not "{}".
  This is why we make the case where "permutations_of_set A = {}" explicit.
  Open question: Would "finite A" instead of "permutations_of_set A = {}"
                 also work for code generation?
*)
(* creates all possible profiles of finite length n on the finite alternative set *)
(* fun profile_permutations :: "nat \<Rightarrow> 'a set \<Rightarrow> (('a, 'v) Profile) set" where
  "profile_permutations n A =
    (if permutations_of_set A = {}
      then {} else listset (replicate n (pl_\<alpha> ` permutations_of_set A)))" *)

text \<open>
  Creates a set of all possible profiles on a finite alternative set
  that are empty everywhere outside of a given finite voter set.
\<close>

fun all_profiles :: "'v set \<Rightarrow> 'a set \<Rightarrow> (('a, 'v) Profile) set" where
  "all_profiles V A =
    (if (infinite A \<or> infinite V)
      then {} else {p. p ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)})"

fun \<K>\<^sub>\<E>_std :: "('a, 'v, 'r Result) Consensus_Class \<Rightarrow> 'r \<Rightarrow> 'a set \<Rightarrow> 'v set
          \<Rightarrow> ('a, 'v) Election set" where
  "\<K>\<^sub>\<E>_std K w A V =
    (\<lambda> p. (A, V, p)) ` (Set.filter
                          (\<lambda> p. (consensus_\<K> K) (A, V, p) \<and> elect (rule_\<K> K) V A p = {w})
                          (all_profiles V A))"

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

fun (in result) \<R>\<^sub>\<W>_std :: "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class \<Rightarrow>
        'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'r set" where
  "\<R>\<^sub>\<W>_std d K V A p = arg_min_set (score_std d K (A, V, p)) (limit_set A UNIV)"

fun (in result) distance_\<R>_std :: "('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Consensus_Class \<Rightarrow> ('a, 'v, 'r Result) Electoral_Module" where
  "distance_\<R>_std d K V A p = (\<R>\<^sub>\<W>_std d K V A p, (limit_set A UNIV) - \<R>\<^sub>\<W>_std d K V A p, {})"

subsection \<open>Auxiliary Lemmas\<close>

lemma fin_\<K>\<^sub>\<E>:
  fixes C :: "('a, 'v, 'r Result) Consensus_Class"
  shows "elections_\<K> C \<subseteq> finite_elections"
proof
  fix E :: "('a,'v) Election"
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
  have "\<And> a A'. finite A' \<Longrightarrow> a \<notin> A' \<Longrightarrow> ?P A' \<Longrightarrow> ?P (insert a A')"
  proof -
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
  assumes "\<forall> i::nat. i < length l \<longrightarrow> finite (l!i)"
  shows "finite (listset l)"
  using assms
proof (induct l, simp)
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list"
  assume
    elems_fin_then_set_fin: "\<forall> i::nat < length l. finite (l!i) \<Longrightarrow> finite (listset l)" and
    fin_all_elems: "\<forall> i::nat < length (a#l). finite ((a#l)!i)"
  hence "finite a"
    by auto
  moreover from fin_all_elems
  have "\<forall> i < length l. finite (l!i)"
    by auto
  hence "finite (listset l)"
    using elems_fin_then_set_fin
    by simp
  ultimately have "finite {a'#l' | a' l'. a' \<in> a \<and> l' \<in> (listset l)}"
    using list_cons_presv_finiteness
    by auto
  thus "finite (listset (a#l))"
    by (simp add: set_Cons_def)
qed

lemma ls_entries_empty_imp_ls_set_empty:
  fixes l :: "'a set list"
  assumes
    "0 < length l" and
    "\<forall> i ::nat. i < length l \<longrightarrow> l!i = {}"
  shows "listset l = {}"
  using assms
proof (induct l, simp)
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list"
  assume all_elems_empty: "\<forall> i::nat < length (a#l). (a#l)!i = {}"
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
  shows "\<forall> l'::('a list). l' \<in> listset l \<longrightarrow> length l' = length l"
proof (induct l, simp)
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list"
  assume "\<forall> l'. l' \<in> listset l \<longrightarrow> length l' = length l"
  moreover have
    "\<forall> a' l'::('a set list). listset (a'#l') = {b#m | b m. b \<in> a' \<and> m \<in> listset l'}"
    by (simp add: set_Cons_def)
  ultimately show "\<forall> l'. l' \<in> listset (a#l) \<longrightarrow> length l' = length (a#l)"
    using local.Cons
    by fastforce
qed

lemma all_ls_elems_in_ls_set:
  fixes l :: "'a set list"
  shows "\<forall> l' i::nat. l' \<in> listset l \<and> i < length l' \<longrightarrow> l'!i \<in> l!i"
proof (induct l, simp, safe)
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list" and
    l' :: "'a list" and
    i :: "nat"
  assume elems_in_set_then_elems_pos:
    "\<forall> l' i::nat. l' \<in> listset l \<and> i < length l' \<longrightarrow> l'!i \<in> l!i" and
    l_prime_in_set_a_l: "l' \<in> listset (a#l)" and
    i_lt_len_l_prime: "i < length l'"
  have "l' \<in> set_Cons a (listset l)"
    using l_prime_in_set_a_l
    by simp
  hence "l' \<in> {m. \<exists> b m'. m = b#m' \<and> b \<in> a \<and> m' \<in> (listset l)}"
    unfolding set_Cons_def
    by simp
  hence "\<exists> b m. l' = b#m \<and> b \<in> a \<and> m \<in> (listset l)"
    by simp
  thus "l'!i \<in> (a#l)!i"
    using elems_in_set_then_elems_pos i_lt_len_l_prime nth_Cons_Suc
          Suc_less_eq gr0_conv_Suc length_Cons nth_non_equal_first_eq
    by metis
qed

lemma fin_all_profs:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    x :: "'a Preference_Relation"
  assumes
    fin_A: "finite A" and
    fin_V: "finite V"
  shows "finite (all_profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = x})"
proof (cases "A = {}")
  let ?profs = "all_profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = x}"
  case True
  hence "permutations_of_set A = {[]}"
    unfolding permutations_of_set_def
    by fastforce
  hence "pl_\<alpha> ` permutations_of_set A = {{}}"
    unfolding pl_\<alpha>_def
    by simp
  hence "\<forall> p \<in> all_profiles V A. \<forall> v. v \<in> V \<longrightarrow> p v = {}"
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
  let ?profs = "(all_profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = x})"
  case False
  from fin_V obtain ord where "linear_order_on V ord"
    using finite_list lin_ord_equiv lin_order_equiv_list_of_alts
    by metis
  then obtain list_V where
    len: "length list_V = card V" and
    pl: "ord = pl_\<alpha> list_V" and
    perm: "list_V \<in> permutations_of_set V"
    using lin_order_pl_\<alpha> fin_V image_iff length_finite_permutations_of_set
    by metis
  let ?map = "\<lambda> p::('a, 'v) Profile. map p list_V"
  have "\<forall> p \<in> all_profiles V A. \<forall> v \<in> V. p v \<in> (pl_\<alpha> ` permutations_of_set A)"
    by (simp add: image_subset_iff)
  hence "\<forall> p \<in> all_profiles V A. (\<forall> v \<in> V. linear_order_on A (p v))"
    using pl_\<alpha>_lin_order fin_A False
    by metis
  moreover have "\<forall> p \<in> ?profs. \<forall> i < length (?map p). (?map p)!i = p (list_V!i)"
    by simp
  moreover have "\<forall> i < length list_V. list_V!i \<in> V"
    using perm nth_mem permutations_of_setD(1)
    by metis
  moreover have lens_eq: "\<forall> p \<in> ?profs. length (?map p) = length list_V"
    by simp
  ultimately have "\<forall> p \<in> ?profs. \<forall> i < length (?map p). linear_order_on A ((?map p)!i)"
    by simp
  hence subset: "?map ` ?profs \<subseteq> {xs. length xs = card V \<and>
                            (\<forall> i < length xs. linear_order_on A (xs!i))}"
    using len lens_eq
    by fastforce
  have "\<forall> p1 p2. p1 \<in> ?profs \<and> p2 \<in> ?profs \<and> p1 \<noteq> p2 \<longrightarrow> (\<exists> v \<in> V. p1 v \<noteq> p2 v)"
    by fastforce
  hence "\<forall> p1 p2. p1 \<in> ?profs \<and> p2 \<in> ?profs \<and> p1 \<noteq> p2 \<longrightarrow> (\<exists> v \<in> set list_V. p1 v \<noteq> p2 v)"
    using perm
    unfolding permutations_of_set_def
    by simp
  hence "\<forall> p1 p2. p1 \<in> ?profs \<and> p2 \<in> ?profs \<and> p1 \<noteq> p2 \<longrightarrow> ?map p1 \<noteq> ?map p2"
    by simp
  hence "inj_on ?map ?profs"
    unfolding inj_on_def
    by blast
  moreover have "finite {xs. length xs = card V \<and> (\<forall> i < length xs. linear_order_on A (xs!i))}"
  proof -
    have "finite {r. linear_order_on A r}"
      using fin_A
      unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by simp
    hence finSupset: "\<forall> n. finite {xs. length xs = n \<and> set xs \<subseteq> {r. linear_order_on A r}}"
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
      using finSupset rev_finite_subset
      by blast
  qed
  moreover have "\<forall> f X Y. inj_on f X \<and> finite Y \<and> f ` X \<subseteq> Y \<longrightarrow> finite X"
    using finite_imageD finite_subset
    by metis
  ultimately show "finite ?profs"
    using subset
    by blast
qed

lemma profile_permutation_set:
  fixes
    A :: "'a set" and
    V :: "'v set"
  shows "all_profiles V A =
          {p' :: ('a, 'v) Profile. finite_profile V A p'}"
proof (cases "finite A \<and> finite V \<and> A \<noteq> {}", clarsimp)
  assume
    fin_A: "finite A" and
    fin_V: "finite V" and
    non_empty: "A \<noteq> {}"
  show "{\<pi>. \<pi> ` V \<subseteq> pl_\<alpha> ` permutations_of_set A} = {p'. profile V A p'}"
  proof
    show "{\<pi>. \<pi> ` V \<subseteq> pl_\<alpha> ` permutations_of_set A} \<subseteq> {p'. profile V A p'}"
    proof (rule, clarify)
      fix p' :: "'v \<Rightarrow> 'a Preference_Relation"
      assume
        subset: "p' ` V \<subseteq> pl_\<alpha> ` permutations_of_set A"
      hence "\<forall> v \<in> V. p' v \<in> pl_\<alpha> ` permutations_of_set A"
        by blast
      hence "\<forall> v \<in> V. linear_order_on A (p' v)"
        using fin_A pl_\<alpha>_lin_order non_empty
        by metis
      thus "profile V A p'"
        unfolding profile_def
        by simp
    qed
  next
    show "{p'. profile V A p'} \<subseteq> {\<pi>. \<pi> ` V \<subseteq> pl_\<alpha> ` permutations_of_set A}"
    proof (rule, clarify)
      fix
        p' :: "('a, 'v) Profile" and
        v :: "'v"
      assume
        prof: "profile V A p'" and
        el: "v \<in> V"
      hence "linear_order_on A (p' v)"
        unfolding profile_def
        by simp
      thus "(p' v) \<in> pl_\<alpha> ` permutations_of_set A"
        using fin_A lin_order_pl_\<alpha>
        by simp
    qed
  qed
next
  assume not_fin_empty: "\<not> (finite A \<and> finite V \<and> A \<noteq> {})"
  have "finite A \<and> finite V \<and> A = {} \<Longrightarrow> permutations_of_set A = {[]}"
    unfolding permutations_of_set_def
    by fastforce
  hence pl_empty: "finite A \<and> finite V \<and> A = {} \<Longrightarrow> pl_\<alpha> ` permutations_of_set A = {{}}"
    unfolding pl_\<alpha>_def
    by simp
  hence "finite A \<and> finite V \<and> A = {} \<Longrightarrow>
    \<forall> \<pi> \<in> {\<pi>. \<pi> ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)}. \<forall> v \<in> V. \<pi> v = {}"
    by fastforce
  hence "finite A \<and> finite V \<and> A = {} \<Longrightarrow>
    {\<pi>. \<pi> ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)} = {\<pi>. \<forall> v \<in> V. \<pi> v = {}}"
    using image_subset_iff singletonD singletonI pl_empty
      (* TODO make this proof step more understandable *)
    by fastforce
  moreover have "finite A \<and> finite V \<and> A = {}
    \<Longrightarrow> all_profiles V A = {\<pi>. \<pi> ` V \<subseteq> (pl_\<alpha> ` permutations_of_set A)}"
    by simp
  ultimately have all_prof_eq: "finite A \<and> finite V \<and> A = {}
    \<Longrightarrow> all_profiles V A = {\<pi>. \<forall> v \<in> V. \<pi> v = {}}"
    by simp
  have "finite A \<and> finite V \<and> A = {}
    \<Longrightarrow> \<forall> p' \<in> {p'. finite_profile V A p' \<and> (\<forall> v'. v' \<notin> V \<longrightarrow> p' v' = {})}.
      (\<forall> v \<in> V. linear_order_on {} (p' v))"
    unfolding profile_def
    by simp
  moreover have "\<forall> r. linear_order_on {} r \<longrightarrow> r = {}"
    using lin_ord_not_empty
    by metis
  ultimately have "finite A \<and> finite V \<and> A = {}
    \<Longrightarrow> \<forall> p' \<in> {p'. finite_profile V A p' \<and> (\<forall> v'. v' \<notin> V \<longrightarrow> p' v' = {})}.
      \<forall> v. p' v = {}"
    by blast
  hence "finite A \<and> finite V \<and> A = {}
    \<Longrightarrow> {p'. finite_profile V A p'} = {p'. \<forall> v \<in> V. p' v = {}}"
    using lin_ord_not_empty lnear_order_on_empty
    unfolding profile_def
    by (metis (no_types, opaque_lifting))
  hence "finite A \<and> finite V \<and> A = {}
    \<Longrightarrow> all_profiles V A = {p'. finite_profile V A p'}"
    using all_prof_eq
    by simp
  moreover have "infinite A \<or> infinite V \<Longrightarrow> all_profiles V A = {}"
    by simp
  moreover have "infinite A \<or> infinite V \<Longrightarrow>
    {p'. finite_profile V A p' \<and> (\<forall> v'. v' \<notin> V \<longrightarrow> p' v' = {})} = {}"
    by auto
  moreover have "infinite A \<or> infinite V \<or> A = {}"
    using not_fin_empty
    by simp
  ultimately show "all_profiles V A = {p'. finite_profile V A p'}"
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
  have "\<R>\<^sub>\<W> d K V A p \<subseteq> (limit_set A UNIV)"
    using \<R>\<^sub>\<W>.simps arg_min_subset
    by metis
  hence "set_equals_partition (limit_set A UNIV) (distance_\<R> d K V A p)"
    by auto
  moreover have "disjoint3 (distance_\<R> d K V A p)"
    by simp
  ultimately show "well_formed A (distance_\<R> d K V A p)"
    using result_axioms
    unfolding result_def
    by simp
qed

subsection \<open>Inference Rules\<close>

lemma is_arg_min_equal:
  fixes
    f :: "'a \<Rightarrow> 'b::ord" and
    g :: "'a \<Rightarrow> 'b" and
    S :: "'a set" and
    x :: "'a"
  assumes "\<forall> x \<in> S. f x = g x"
  shows "is_arg_min f (\<lambda> s. s \<in> S) x = is_arg_min g (\<lambda> s. s \<in> S) x"
proof (unfold is_arg_min_def, cases "x \<in> S")
  case False
  thus "(x \<in> S \<and> (\<nexists> y. y \<in> S \<and> f y < f x)) = (x \<in> S \<and> (\<nexists> y. y \<in> S \<and> g y < g x))"
    by simp
next
  case x_in_S: True
  thus "(x \<in> S \<and> (\<nexists> y. y \<in> S \<and> f y < f x)) = (x \<in> S \<and> (\<nexists> y. y \<in> S \<and> g y < g x))"
  proof (cases "\<exists> y. (\<lambda> s. s \<in> S) y \<and> f y < f x")
    case y: True
    then obtain y :: "'a" where
      "(\<lambda> s. s \<in> S) y \<and> f y < f x"
      by metis
    hence "(\<lambda> s. s \<in> S) y \<and> g y < g x"
      using x_in_S assms
      by metis
    thus ?thesis
      using y
      by metis
  next
    case not_y: False
    have "\<not> (\<exists> y. (\<lambda> s. s \<in> S) y \<and> g y < g x)"
    proof (safe)
      fix y :: "'a"
      assume
        y_in_S: "y \<in> S" and
        g_y_lt_g_x: "g y < g x"
      have f_eq_g_for_elems_in_S: "\<forall> a. a \<in> S \<longrightarrow> f a = g a"
        using assms
        by simp
      hence "g x = f x"
        using x_in_S
        by presburger
      thus False
        using f_eq_g_for_elems_in_S g_y_lt_g_x not_y y_in_S
        by (metis (no_types))
    qed
    thus ?thesis
      using x_in_S not_y
      by simp
  qed
qed

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
    "all_profiles V A =
      {p' :: ('a, 'v) Profile. finite_profile V A p'}"
    using profile_permutation_set
    by metis
  hence eq_intersect: "\<K>\<^sub>\<E>_std K w A V =
           \<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p' :: ('a, 'v) Profile. finite_profile V A p'}"
    by force
  have inf_eq_inf_for_std_cons:
    "Inf (d (A, V, p) ` (\<K>\<^sub>\<E> K w)) =
       Inf (d (A, V, p) ` (\<K>\<^sub>\<E> K w \<inter>
        Pair A ` Pair V ` {p' :: ('a, 'v) Profile. finite_profile V A p'}))"
  proof -
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
      have in_intersect: "i \<in> (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p'. finite_profile V A p'})
              \<Longrightarrow> ?inf \<le> d (A, V, p) i"
        using Complete_Lattices.complete_lattice_class.INF_lower
        by metis
      have "i \<in> ?compl \<Longrightarrow> (V \<noteq> fst (snd i)
                              \<or> A \<noteq> fst i
                              \<or> \<not> finite_profile V A (snd (snd i)))"
        by fastforce
      moreover have "V \<noteq> fst (snd i) \<Longrightarrow> d (A, V, p) i = \<infinity>"
        using std prod.collapse
        unfolding standard_def
        by metis
      moreover have "A \<noteq> fst i \<Longrightarrow> d (A, V, p) i = \<infinity>"
        using std prod.collapse
        unfolding standard_def
        by metis
      moreover have "V = fst (snd i) \<and> A = fst i
                      \<and> \<not> finite_profile V A (snd (snd i)) \<longrightarrow> False"
        using el
        by fastforce
      ultimately have
        "i \<in> ?compl \<Longrightarrow> Inf (d (A, V, p) `
                          (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p'. finite_profile V A p'}))
                        \<le> d (A, V, p) i"
        using ereal_less_eq
        by metis
      thus "Inf (d (A, V, p) `
              (\<K>\<^sub>\<E> K w \<inter>
               Pair A ` Pair V ` {p'. finite_profile V A p'}))
             \<le> d (A, V, p) i"
        using in_intersect el
        by blast
    qed
    ultimately show
      "Inf (d (A, V, p) ` \<K>\<^sub>\<E> K w) =
        Inf (d (A, V, p) `
          (\<K>\<^sub>\<E> K w \<inter> Pair A ` Pair V ` {p'. finite_profile V A p'}))"
      by simp
  qed
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
    have "finite (d (A, V, p) `(\<K>\<^sub>\<E>_std K w A V))"
    proof -
      have "\<K>\<^sub>\<E>_std K w A V = (\<K>\<^sub>\<E> K w) \<inter>
                              {(A, V, p') | p'. finite_profile V A p'}"
        using eq_intersect
        by blast
      hence subset: "d (A, V, p) `(\<K>\<^sub>\<E>_std K w A V) \<subseteq>
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
      moreover have "\<forall> p'. d (A, V, p) (A, V, p') = d (A, V, p) (A, V, ?finite_prof p')"
        using irr_non_V
        unfolding voters_determine_distance_def
        by simp
      ultimately have
        "\<forall> (A', V', p') \<in> {(A, V, p') | p'. finite_profile V A p'}.
           (\<exists> (X, Y, z) \<in> {(A, V, p') | p'. finite_profile V A p'
                              \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}.
                d (A, V, p) (A', V', p') = d (A, V, p) (X, Y, z))"
        by fastforce
      hence "\<forall> (A', V', p') \<in> {(A', V', p'). A' = A \<and> V' = V \<and> finite_profile V A p'}.
                d (A, V, p) (A', V', p') \<in>
                d (A, V, p) ` {(A, V, p') | p'. finite_profile V A p'
                                  \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}"
        by fastforce
      hence subset_2: "d (A, V, p) ` {(A, V, p') | p'. finite_profile V A p'}
              \<subseteq> d (A, V, p) ` {(A, V, p') | p'. finite_profile V A p'
                                  \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}"
        by fastforce
      have "\<forall> (A', V', p') \<in> {(A, V, p') | p'. finite_profile V A p'
                                \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}.
                (\<forall> v \<in> V. linear_order_on A (p' v))
                \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})"
        using fin
        unfolding profile_def
        by simp
      hence "{(A, V, p') | p'. finite_profile V A p'
                                \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}
              \<subseteq> {(A, V, p') | p'. p' \<in> {p'. (\<forall> v \<in> V. linear_order_on A (p' v))
                                              \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}}"
        by blast
      moreover have "finite {(A, V, p') | p'. p' \<in> {p'. (\<forall> v \<in> V. linear_order_on A (p' v))
                                              \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}}"
      proof -
        have "{p'. (\<forall> v \<in> V. linear_order_on A (p' v)) \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}
                \<subseteq> all_profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = {}}"
          using lin_order_pl_\<alpha> fin
          by fastforce
        moreover have "finite (all_profiles V A \<inter> {p. \<forall> v. v \<notin> V \<longrightarrow> p v = {}})"
          using fin fin_all_profs
          by blast
        ultimately have "finite {p'. (\<forall> v \<in> V. linear_order_on A (p' v))
                                        \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}"
          using rev_finite_subset
          by blast
        thus ?thesis
          by simp
      qed
      ultimately have "finite {(A, V, p') | p'. finite_profile V A p'
                                \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})}"
        using rev_finite_subset
        by simp
      hence "finite (d (A, V, p) ` {(A, V, p') | p'. finite_profile V A p'
                                \<and> (\<forall> v. v \<notin> V \<longrightarrow> p' v = {})})"
        by simp
      hence "finite (d (A, V, p) ` {(A, V, p') | p'. finite_profile V A p'})"
        using subset_2 rev_finite_subset
        by simp
      thus ?thesis
        using subset rev_finite_subset
        by blast
    qed
    moreover have "d (A, V, p) ` (\<K>\<^sub>\<E>_std K w A V) \<noteq> {}"
      using False
      by simp
    ultimately have "Inf (d (A, V, p) ` (\<K>\<^sub>\<E>_std K w A V)) = Min (d (A, V, p) ` (\<K>\<^sub>\<E>_std K w A V))"
      using Min_Inf False
      by metis
    also have "... = score_std d K (A, V, p) w"
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
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    fin_A: "finite A" and
    fin_V: "finite V" and
    profile_p: "profile V A p" and
    profile_q: "profile V' A' q" and
    bij: "bij \<pi>" and
    renamed: "rename \<pi> (A, V, p) = (A', V', q)"
  have "A = A'"
    using bij renamed
    by simp
  hence eq_univ: "limit_set A UNIV = limit_set A' UNIV"
    by simp
  hence "\<R>\<^sub>\<W> d K V A p = \<R>\<^sub>\<W> d K V' A' q"
  proof -
    have dist_rename_inv:
      "\<forall> E::('a, 'v) Election. d (A, V, p) E = d (A', V', q) (rename \<pi> E)"
      using d_anon bij renamed surj_pair
      unfolding distance_anonymity_def
      by metis
    hence "\<forall> S::('a, 'v) Election set.
            (d (A, V, p) ` S) \<subseteq> (d (A', V', q) ` (rename \<pi> ` S))"
      by blast
    moreover have "\<forall> S::('a, 'v) Election set.
            ((d (A', V', q) ` (rename \<pi> ` S)) \<subseteq> (d (A, V, p) ` S))"
    proof (clarify)
      fix
        S :: "('a, 'v) Election set" and
        X :: "'a set" and
        X' :: "'a set" and
        Y :: "'v set" and
        Y' :: "'v set" and
        z :: "('a, 'v) Profile" and
        z' :: "('a, 'v) Profile"
      assume
        "(X', Y', z') = rename \<pi> (X, Y, z)" and
        el: "(X, Y, z) \<in> S"
      hence "d (A', V', q) (X', Y', z') = d (A, V, p) (X, Y, z)"
        using dist_rename_inv
        by simp
      thus "d (A', V', q) (X', Y', z') \<in> d (A, V, p) ` S"
        using el
        by simp
    qed
    ultimately have eq_range: "\<forall> S::('a, 'v) Election set.
            (d (A, V, p) ` S) = (d (A', V', q) ` (rename \<pi> ` S))"
      by blast
    have "\<forall> w. rename \<pi> ` (\<K>\<^sub>\<E> K w) \<subseteq> (\<K>\<^sub>\<E> K w)"
    proof (clarify)
      fix
        w :: 'r and
        A :: "'a set" and
        A' :: "'a set" and
        V :: "'v set" and
        V' :: "'v set" and
        p :: "('a, 'v) Profile" and
        p' :: "('a, 'v) Profile"
      assume
        renamed: "(A', V', p') = rename \<pi> (A, V, p)" and
        consensus: "(A, V, p) \<in> \<K>\<^sub>\<E> K w"
      hence cons:
        "(consensus_\<K> K) (A, V, p) \<and> finite_profile V A p \<and> elect (rule_\<K> K) V A p = {w}"
        by simp
      hence fin_img: "finite_profile V' A' p'"
        using renamed bij rename.simps fst_conv rename_finite
        by metis
      hence cons_img: "consensus_\<K> K (A', V', p') \<and> (rule_\<K> K V A p = rule_\<K> K V' A' p')"
        using K_anon renamed bij cons
        unfolding consensus_rule_anonymity_def Let_def
        by simp
      hence "elect (rule_\<K> K) V' A' p' = {w}"
        using cons
        by simp
      thus "(A', V', p') \<in> \<K>\<^sub>\<E> K w"
        using cons_img fin_img
        by simp
    qed
    moreover have "\<forall> w. (\<K>\<^sub>\<E> K w) \<subseteq> rename \<pi> ` (\<K>\<^sub>\<E> K w)"
    proof (clarify)
      fix
        w :: 'r and
        A :: "'a set" and
        V :: "'v set" and
        p :: "('a, 'v) Profile"
      assume consensus: "(A, V, p) \<in> \<K>\<^sub>\<E> K w"
      let ?inv = "rename (the_inv \<pi>) (A, V, p)"
      have inv_inv_id: "the_inv (the_inv \<pi>) = \<pi>"
        using the_inv_f_f bij bij_betw_imp_inj_on bij_betw_imp_surj
              inj_on_the_inv_into surj_imp_inv_eq the_inv_into_onto
        by (metis (no_types, opaque_lifting))
      hence "?inv = (A, ((the_inv \<pi>) ` V), p \<circ> (the_inv (the_inv \<pi>)))"
        by simp
      moreover have "(p \<circ> (the_inv (the_inv \<pi>))) \<circ> (the_inv \<pi>) = p"
        using bij inv_inv_id
        unfolding bij_betw_def comp_def
        by (simp add: f_the_inv_into_f)
      moreover have "\<pi> ` (the_inv \<pi>) ` V = V"
        using bij the_inv_f_f bij_betw_def image_inv_into_cancel
              surj_imp_inv_eq top_greatest
        by (metis (no_types, opaque_lifting))
      ultimately have preimg: "rename \<pi> ?inv = (A, V, p)"
        unfolding Let_def
        by simp
      moreover have "?inv \<in> \<K>\<^sub>\<E> K w"
      proof -
        have cons:
          "(consensus_\<K> K) (A, V, p) \<and> finite_profile V A p \<and> elect (rule_\<K> K) V A p = {w}"
          using consensus
          by simp
        moreover have bij_inv: "bij (the_inv \<pi>)"
          using bij bij_betw_the_inv_into
          by metis
        moreover have fin_preimg: "finite_profile (fst (snd ?inv)) (fst ?inv) (snd (snd ?inv))"
          using bij_inv rename.simps fst_conv rename_finite cons
          by fastforce
        ultimately have cons_preimg:
          "consensus_\<K> K ?inv \<and>
              (rule_\<K> K V A p = rule_\<K> K (fst (snd ?inv)) (fst ?inv) (snd (snd ?inv)))"
          using K_anon renamed bij cons
          unfolding consensus_rule_anonymity_def Let_def
          by simp
        hence "elect (rule_\<K> K) (fst (snd ?inv)) (fst ?inv) (snd (snd ?inv)) = {w}"
          using cons
          by simp
        thus ?thesis
          using cons_preimg fin_preimg
          by simp
        qed
        ultimately show "(A, V, p) \<in> rename \<pi> ` \<K>\<^sub>\<E> K w"
          using image_eqI
          by metis
    qed
    ultimately have "\<forall> w. (\<K>\<^sub>\<E> K w) = rename \<pi> ` (\<K>\<^sub>\<E> K w)"
      by blast
    hence "\<forall> w. score d K (A, V, p) w = score d K (A', V', q) w"
      using eq_range
      by simp
    hence "arg_min_set (score d K (A, V, p)) (limit_set A UNIV)
            = arg_min_set (score d K (A', V', q)) (limit_set A' UNIV)"
      using eq_univ
      by presburger
    thus "\<R>\<^sub>\<W> d K V A p = \<R>\<^sub>\<W> d K V' A' q"
      by simp
  qed
  thus "distance_\<R> d K V A p = distance_\<R> d K V' A' q"
    using eq_univ
    by simp
qed

end
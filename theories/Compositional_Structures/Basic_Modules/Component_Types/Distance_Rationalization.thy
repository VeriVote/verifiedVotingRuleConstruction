(*  File:       Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance Rationalization\<close>

theory Distance_Rationalization
  imports "HOL-Combinatorics.Multiset_Permutations"
          "Social_Choice_Types/Refined_Types/Preference_List"
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

fun \<K>\<^sub>\<E> :: "'a Consensus_Class \<Rightarrow> 'a \<Rightarrow> 'a Election set" where
  "\<K>\<^sub>\<E> K a =
    {(A, p) | A p. (consensus_\<K> K) (A, p) \<and> finite_profile A p \<and> elect (rule_\<K> K) A p = {a}}"

fun score :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a Election \<Rightarrow> 'a \<Rightarrow> ereal" where
  "score d K E a = Inf (d E ` (\<K>\<^sub>\<E> K a))"

fun arg_min_set :: "('b \<Rightarrow> 'a :: ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "arg_min_set f A = Collect (is_arg_min f (\<lambda> a. a \<in> A))"

(* fun arg_min_set' :: "('b \<Rightarrow> 'a::ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
   "arg_min_set_' f A = Set.filter (is_arg_min f (\<lambda> a. a \<in> A)) A" *)

fun \<R>\<^sub>\<W> :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "\<R>\<^sub>\<W> d K A p = arg_min_set (score d K (A, p)) A"

fun distance_\<R> :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a Electoral_Module" where
  "distance_\<R> d K A p = (\<R>\<^sub>\<W> d K A p, A - \<R>\<^sub>\<W> d K A p, {})"

subsection \<open>Standard Definitions\<close>

definition standard :: "'a Election Distance \<Rightarrow> bool" where
 "standard d \<equiv> \<forall> A A' p p'. (length p \<noteq> length p' \<or> A \<noteq> A') \<longrightarrow> d (A, p) (A', p') = \<infinity>"

(*
  We want "profile_permutations n A = {}" for infinite A.
  We have "permutations_of_set A = {} \<longleftrightarrow> \<not> finite A"
    (Multiset_Permutations.permutations_of_set_empty_iff).
    "listset (replicate 0 (list_to_rel ` {})" is "{[]}", not "{}".
  This is why we make the case where "permutations_of_set A = {}" explicit.
  Open question: Would "finite A" instead of "permutations_of_set A = {}"
                 also work for code generation?
*)
fun profile_permutations :: "nat \<Rightarrow> 'a set \<Rightarrow> ('a Profile) set" where
  "profile_permutations n A =
    (if permutations_of_set A = {}
      then {} else listset (replicate n (pl_\<alpha> ` permutations_of_set A)))"

fun \<K>\<^sub>\<E>_std :: "'a Consensus_Class \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a Election set" where
  "\<K>\<^sub>\<E>_std K a A n =
    (\<lambda> p. (A, p)) ` (Set.filter (\<lambda> p. (consensus_\<K> K) (A, p) \<and> elect (rule_\<K> K) A p = {a})
                                (profile_permutations n A))"

fun score_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a Election \<Rightarrow> 'a \<Rightarrow> ereal" where
  "score_std d K E a =
    (if \<K>\<^sub>\<E>_std K a (alts_\<E> E) (length (prof_\<E> E)) = {}
      then \<infinity> else Min (d E ` (\<K>\<^sub>\<E>_std K a (alts_\<E> E) (length (prof_\<E> E)))))"

fun \<R>\<^sub>\<W>_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a set
                          \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "\<R>\<^sub>\<W>_std d K A p = arg_min_set (score_std d K (A, p)) A"

fun distance_\<R>_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a Electoral_Module" where
  "distance_\<R>_std d K A p = (\<R>\<^sub>\<W>_std d K A p, A - \<R>\<^sub>\<W>_std d K A p, {})"

subsection \<open>Auxiliary Lemmas\<close>

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
    by force
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
    i :: nat
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

lemma all_ls_in_ls_set:
  fixes l :: "'a set list"
  shows "\<forall> l'. (length l' = length l \<and> (\<forall> i < length l'. l'!i \<in> l!i)) \<longrightarrow> l' \<in> listset l"
proof (induction l, safe, simp)
  case (Cons a l)
  fix
    l :: "'a set list" and
    l' :: "'a list" and
    s :: "'a set"
  assume
    all_ls_in_ls_set_induct:
    "\<forall> m. length m = length l \<and> (\<forall> i < length m. m!i \<in> l!i) \<longrightarrow> m \<in> listset l" and
    len_eq: "length l' = length (s#l)" and
    elems_pos_in_cons_ls_pos: "\<forall> i < length l'. l'!i \<in> (s#l)!i"
  then obtain t and x where
    l'_cons: "l' = x#t"
    using length_Cons list.exhaust list.size(3) nat.simps(3)
    by metis
  hence "x \<in> s"
    using elems_pos_in_cons_ls_pos
    by force
  moreover have "t \<in> listset l"
    using l'_cons all_ls_in_ls_set_induct len_eq diff_Suc_1 diff_Suc_eq_diff_pred
          elems_pos_in_cons_ls_pos length_Cons nth_Cons_Suc zero_less_diff
    by metis
  ultimately show "l' \<in> listset (s#l)"
    using l'_cons
    unfolding listset_def set_Cons_def
    by simp
qed

lemma lin_ord_pl_\<alpha>:
  fixes
    r :: "'a rel" and
    A :: "'a set"
  assumes
    lin_ord_r: "linear_order_on A r" and
    fin_A: "finite A"
  shows "r \<in> pl_\<alpha> ` permutations_of_set A"
proof -
  let ?\<phi> = "\<lambda> a. card ((underS r a) \<inter> A)"
  let ?inv = "the_inv_into A ?\<phi>"
  let ?l = "map (\<lambda> x. ?inv x) (rev [0 ..< card A])"
  have antisym: "\<forall> a b. a \<notin> (underS r b) \<inter> A \<or> b \<notin> (underS r a) \<inter> A"
    using lin_ord_r
    unfolding underS_def linear_order_on_def partial_order_on_def antisym_def
    by simp
  hence "\<forall> a b c. a \<in> (underS r b) \<inter> A \<longrightarrow> b \<in> (underS r c) \<inter> A \<longrightarrow> a \<in> (underS r c) \<inter> A"
    using lin_ord_r CollectD CollectI transD IntE IntI
    unfolding underS_def linear_order_on_def partial_order_on_def preorder_on_def trans_def
    by (metis (mono_tags, lifting))
  hence "\<forall> a b. a \<in> (underS r b) \<inter> A \<longrightarrow> (underS r a) \<inter> A \<subset> (underS r b) \<inter> A"
    using antisym
    by blast
  hence mono: "\<forall> a b. a \<in> (underS r b) \<inter> A \<longrightarrow> ?\<phi> a < ?\<phi> b"
    using fin_A
    by (simp add: psubset_card_mono)
  moreover have total_underS:
    "\<forall> a b. a \<in> A \<and> b \<in> A \<and> a \<noteq> b \<longrightarrow> a \<in> (underS r b) \<inter> A \<or> b \<in> (underS r a) \<inter> A"
    using lin_ord_r totalp_onD totalp_on_total_on_eq
    unfolding underS_def linear_order_on_def partial_order_on_def antisym_def
    by fastforce
  ultimately have "\<forall> a b. a \<in> A \<and> b \<in> A \<and> a \<noteq> b \<longrightarrow> ?\<phi> a \<noteq> ?\<phi> b"
    using order_less_imp_not_eq2
    by metis
  hence inj: "inj_on ?\<phi> A"
    unfolding inj_on_def
    by metis
  have in_bounds: "\<forall> a \<in> A. ?\<phi> a < card A"
    using CollectD IntD1 card_seteq fin_A inf_sup_ord(2) linorder_le_less_linear
    unfolding underS_def
    by (metis (mono_tags, lifting))
  hence "?\<phi> ` A \<subseteq> {0 ..< card A}"
    using atLeast0LessThan
    by blast
  moreover have "card (?\<phi> ` A) = card A"
    using inj fin_A card_image
    by metis
  ultimately have "?\<phi> ` A = {0 ..< card A}"
    by (simp add: card_subset_eq)
  hence bij: "bij_betw ?\<phi> A {0 ..< card A}"
    using inj
    unfolding bij_betw_def
    by presburger
  hence bij_inv: "bij_betw ?inv {0 ..< card A} A"
    using bij_betw_the_inv_into
    by metis
  hence "?inv ` {0 ..< card A} = A"
    using bij_inv
    unfolding bij_betw_def
    by presburger
  hence "set ?l = A"
    by simp
  moreover have dist_inv_of_rev: "distinct ?l"
    using bij_inv bij_betw_imp_inj_on
    by (simp add: distinct_map)
  ultimately have "?l \<in> permutations_of_set A"
    by blast
  moreover have index_eq: "\<forall> a \<in> A. index ?l a = card A - 1 - ?\<phi> a"
  proof (safe)
    fix a :: 'a
    assume a_in_A: "a \<in> A"
    have "\<forall> l. \<forall> i < length l. (rev l)!i = l!(length l - 1 - i)"
      using rev_nth
      by auto
    hence "\<forall> i < length [0 ..< card A].
      (rev [0 ..< card A])!i = [0 ..< card A]!(length [0 ..< card A] - 1 - i)"
      by blast
    moreover have "\<forall> i < card A. [0 ..< card A]!i = i"
      by simp
    moreover have len_card_A: "length [0 ..< card A] = card A"
      by simp
    ultimately have "\<forall> i < card A. (rev [0 ..< card A])!i = card A - 1 - i"
      using diff_Suc_eq_diff_pred diff_less diff_self_eq_0 less_imp_diff_less zero_less_Suc
      by metis
    moreover have "\<forall> i < card A. ?l!i = ?inv ((rev [0 ..< card A])!i)"
      by simp
    ultimately have "\<forall> i < card A. ?l!i = ?inv (card A - 1 - i)"
      by presburger
    moreover have "card A - 1 - (card A - 1 - card (underS r a \<inter> A)) = card (underS r a \<inter> A)"
      using in_bounds a_in_A
      by auto
    moreover have "?inv (card (underS r a \<inter> A)) = a"
      using a_in_A inj the_inv_into_f_f
      by fastforce
    ultimately have "?l!(card A - 1 - card (underS r a \<inter> A)) = a"
      using in_bounds a_in_A card_Diff_singleton card_Suc_Diff1 diff_less_Suc fin_A
      by metis
    thus "index ?l a = card A - 1 - card (underS r a \<inter> A)"
      using bij_inv dist_inv_of_rev a_in_A len_card_A card_Diff_singleton card_Suc_Diff1
            diff_less_Suc fin_A index_nth_id length_map length_rev
      by metis
  qed
  moreover have "pl_\<alpha> ?l = r"
  proof
    show "r \<subseteq> pl_\<alpha> ?l"
    proof (unfold pl_\<alpha>_def, auto)
      fix
        a :: 'a and
        b :: 'a
      assume "(a, b) \<in> r"
      hence "a \<in> A"
        using lin_ord_r
        unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
        by blast
      thus "a \<in> ?inv ` {0 ..< card A}"
        using bij_inv bij_betw_def
        by metis
    next
      fix
        a :: 'a and
        b :: 'a
      assume "(a, b) \<in> r"
      hence "b \<in> A"
        using lin_ord_r
        unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
        by blast
      thus "b \<in> ?inv ` {0 ..< card A}"
        using bij_inv bij_betw_def
        by metis
    next
      fix
        a :: 'a and
        b :: 'a
      assume rel: "(a, b) \<in> r"
      hence a_b_in_A: "a \<in> A \<and> b \<in> A"
        using lin_ord_r
        unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
        by blast
      moreover have "a \<notin> underS r b \<longrightarrow> a = b"
        using lin_ord_r rel
        unfolding underS_def
        by simp
      ultimately have "?\<phi> a \<le> ?\<phi> b"
        using mono le_eq_less_or_eq
        by blast
      thus "index ?l b \<le> index ?l a"
        using index_eq a_b_in_A diff_le_mono2
        by metis
    qed
  next
    show "pl_\<alpha> ?l \<subseteq> r"
    proof (unfold pl_\<alpha>_def, clarsimp)
      fix
        a :: nat and
        b :: nat
      assume
        a_lt_card_A: "a < card A" and
        b_lt_card_A: "b < card A" and
        index_b_lte_a: "index ?l (?inv b) \<le> index ?l (?inv a)"
      have inv_a_in_A: "(?inv a) \<in> A"
        using bij_inv a_lt_card_A atLeast0LessThan
        unfolding bij_betw_def
        by blast
      moreover have inv_b_in_A: "(?inv b) \<in> A"
        using bij_inv b_lt_card_A atLeast0LessThan
        unfolding bij_betw_def
        by blast
      ultimately have "card A - 1 - ?\<phi> (?inv b) \<le> card A - 1 - ?\<phi> (?inv a)"
        using index_b_lte_a index_eq
        by metis
      moreover have "\<forall> a < card A. ?\<phi> (?inv a) < card A"
        using fin_A bij_inv bij
        unfolding bij_betw_def
        by fastforce
      hence "?\<phi> (?inv b) \<le> card A - 1 \<and> ?\<phi> (?inv a) \<le> card A - 1"
        using a_lt_card_A b_lt_card_A fin_A
        by fastforce
      ultimately have "?\<phi> (?inv b) \<ge> ?\<phi> (?inv a)"
        using fin_A le_diff_iff'
        by blast
      hence "?\<phi> (?inv a) < ?\<phi> (?inv b) \<or> ?\<phi> (?inv a) = ?\<phi> (?inv b)"
        by auto
      moreover have "\<forall> a b. a \<in> A \<and> b \<in> A \<and> ?\<phi> a < ?\<phi> b \<longrightarrow> a \<in> underS r b"
        using mono total_underS antisym IntD1 order_less_not_sym
        by metis
      hence "?\<phi> (?inv a) < ?\<phi> (?inv b) \<longrightarrow> (?inv a, ?inv b) \<in> r"
        using inv_a_in_A inv_b_in_A
        unfolding underS_def
        by blast
      moreover have "\<forall> a b. a \<in> A \<and> b \<in> A \<and> ?\<phi> a = ?\<phi> b \<longrightarrow> a = b"
        using mono total_underS antisym order_less_not_sym
        by metis
      hence "?\<phi> (?inv a) = ?\<phi> (?inv b) \<longrightarrow> (?inv a, ?inv b) \<in> r"
        using lin_ord_r inv_a_in_A inv_b_in_A
        unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
        by metis
      ultimately show "(?inv a, ?inv b) \<in> r"
        by metis
    qed
  qed
  ultimately show "r \<in> pl_\<alpha> ` permutations_of_set A"
    by blast
qed

lemma profile_permutation_set:
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  shows "profile_permutations (length p) A =
          {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
proof (cases "\<not> finite A", clarsimp)
  case fin_A: False
  show ?thesis
  proof (induction p, safe)
    case not_zero_lt_len_p': Nil
    show "finite A"
      using fin_A
      by simp
    fix p' :: "'a Profile"
    assume p'_in_prof: "p' \<in> profile_permutations (length []) A"
    hence "profile_permutations (length []) A \<noteq> {}"
      by force
    hence perms_nonempty: "pl_\<alpha> ` permutations_of_set A \<noteq> {}"
      by auto
    thus len_eq: "length p' = length []"
      using p'_in_prof
      by simp
    thus "profile A p'"
      unfolding profile_def
      by force
  next
    case not_zero_lt_len_p': Nil
    fix p' :: "'a Profile"
    assume "length p' = length []"
    hence "[] = p'"
      by simp
    moreover have "{q. finite_profile A q \<and> length q = length []} \<subseteq> {[]}"
      using not_zero_lt_len_p'
      by auto
    moreover have "profile_permutations (length []) A = {[]}"
      using fin_A not_zero_lt_len_p'
      by simp
    ultimately show "p'\<in> profile_permutations (length []) A"
      by simp
  next
    case zero_lt_len_p: (Cons r p')
    fix p' :: "'a Profile"
    from fin_A
    show "finite A"
      by simp
    fix
      r :: "'a Preference_Relation" and
      q :: "'a Profile"
    assume
      prof_perms_eq_set_induct:
        "profile_permutations (length q) A = {q'. finite_profile A q' \<and> length q' = length q}" and
      p'_in_prof: "p' \<in> profile_permutations (length (r#q)) A"
    show len_eq: "length p' = length (r#q)"
      using all_ls_elems_same_len fin_A length_replicate p'_in_prof
            permutations_of_set_empty_iff profile_permutations.simps
      by (metis (no_types))
    have perms_nonempty: "pl_\<alpha> ` permutations_of_set A \<noteq> {}"
      using p'_in_prof prof_perms_eq_set_induct
      by auto
    have "length (replicate (length q) (pl_\<alpha> ` permutations_of_set A)) = length q"
      by simp
    hence "\<forall> q' \<in> listset (replicate (length q) (pl_\<alpha> ` permutations_of_set A)).
              length q' = length q"
      using all_ls_elems_same_len
      by metis
    show "profile A p'"
    proof (unfold profile_def, safe)
      fix i :: nat
      assume i_lt_len_p': "i < length p'"
      hence "p'!i \<in> replicate (length p') (pl_\<alpha> ` permutations_of_set A)!i"
        using p'_in_prof perms_nonempty all_ls_elems_in_ls_set image_is_empty length_replicate
              all_ls_elems_same_len
        unfolding profile_permutations.simps
        by metis
      hence "p'!i \<in> pl_\<alpha> ` permutations_of_set A"
        using i_lt_len_p'
        by simp
      hence relation_of:
        "p'!i \<in> {relation_of (\<lambda> a a'. rank_l l a' \<le> rank_l l a) (set l) |
                  l. l \<in> permutations_of_set A}"
      proof (safe)
        fix l :: "'a Preference_List"
        assume
          i_th_rel: "p'!i = pl_\<alpha> l" and
          perm_l: "l \<in> permutations_of_set A"
        have rel_of_set_l_eq_l_list: "relation_of (\<lambda> a a'. a \<lesssim>\<^sub>l a') (set l) = pl_\<alpha> l"
          using rel_of_pref_pred_for_set_eq_list_to_rel
          by blast
        have "relation_of (\<lambda> a a'. rank_l l a' \<le> rank_l l a) (set l) = pl_\<alpha> l"
        proof (unfold relation_of_def rank_l.simps, safe)
          fix
            a :: "'a" and
            b :: "'a"
          assume
            idx_b_lte_idx_a: "(if b \<in> set l then index l b + 1 else 0) \<le>
                                (if a \<in> set l then index l a + 1 else 0)" and
            a_in_l: "a \<in> set l" and
            b_in_l : "b \<in> set l"
          moreover have "{(a', b'). (a', b') \<in> set l \<times> set l \<and> a' \<lesssim>\<^sub>l b'} = pl_\<alpha> l"
            using rel_of_set_l_eq_l_list
            unfolding relation_of_def
            by simp
          moreover have "a \<in> set l"
            using a_in_l
            by simp
          ultimately show "(a, b) \<in> pl_\<alpha> l"
            by fastforce
        next
          fix
            a :: "'a" and
            b :: "'a"
          assume "(a, b) \<in> pl_\<alpha> l"
          thus "a \<in> set l"
            using Collect_mem_eq case_prod_eta in_rel_Collect_case_prod_eq
                  is_less_preferred_than_l.elims(2)
            unfolding pl_\<alpha>_def
            by (metis (no_types))
        next
          fix
            a :: "'a" and
            b :: "'a"
          assume "(a, b) \<in> pl_\<alpha> l"
          moreover have "{(a', b'). (a', b') \<in> set l \<times> set l \<and> a' \<lesssim>\<^sub>l b'} = pl_\<alpha> l"
            using rel_of_set_l_eq_l_list
            unfolding relation_of_def
            by simp
          ultimately show "b \<in> set l"
            using is_less_preferred_than_l.elims(2)
            by blast
        next
          fix
            a :: "'a" and
            b :: "'a"
          assume "(a, b) \<in> pl_\<alpha> l"
          moreover have "{(a', b'). (a', b') \<in> set l \<times> set l \<and> a' \<lesssim>\<^sub>l b'} = pl_\<alpha> l"
            using rel_of_set_l_eq_l_list
            unfolding relation_of_def
            by simp
          ultimately have "a \<lesssim>\<^sub>l b"
            using case_prodE mem_Collect_eq prod.inject
            by blast
          thus "(if b \<in> set l then index l b + 1 else 0) \<le>
                  (if a \<in> set l then index l a + 1 else 0)"
            by simp
        qed
        show "\<exists> l'.
          p'!i = relation_of (\<lambda> a b. rank_l l' b \<le> rank_l l' a) (set l') \<and>
          l' \<in> permutations_of_set A"
        proof
          have "relation_of (\<lambda> a b. rank_l l b \<le> rank_l l a) (set l) = pl_\<alpha> l"
          proof (unfold relation_of_def rank_l.simps, safe)
            fix
              a :: "'a" and
              b :: "'a"
            assume
              idx_b_lte_idx_a: "(if b \<in> set l then index l b + 1 else 0) \<le>
                                  (if a \<in> set l then index l a + 1 else 0)" and
              a_in_l: "a \<in> set l" and
              b_in_l : "b \<in> set l"
            moreover have "{(a', b'). (a', b') \<in> set l \<times> set l \<and> a' \<lesssim>\<^sub>l b'} = pl_\<alpha> l"
              using rel_of_set_l_eq_l_list
              unfolding relation_of_def
              by simp
            moreover have "a \<in> set l"
              using a_in_l
              by simp
            ultimately show "(a, b) \<in> pl_\<alpha> l"
              by fastforce
          next
            fix
              a :: "'a" and
              b :: "'a"
            assume "(a, b) \<in> pl_\<alpha> l"
            thus "a \<in> set l"
              using Collect_mem_eq case_prod_eta in_rel_Collect_case_prod_eq
                    is_less_preferred_than_l.elims(2)
              unfolding pl_\<alpha>_def
              by (metis (no_types))
          next
            fix
              a :: "'a" and
              b :: "'a"
            assume "(a, b) \<in> pl_\<alpha> l"
            moreover have "{(a', b'). (a', b') \<in> set l \<times> set l \<and> a' \<lesssim>\<^sub>l b'} = pl_\<alpha> l"
              using rel_of_set_l_eq_l_list
              unfolding relation_of_def
              by simp
            ultimately show "b \<in> set l"
              using is_less_preferred_than_l.elims(2)
              by blast
          next
            fix
              a :: "'a" and
              b :: "'a"
            assume "(a, b) \<in> pl_\<alpha> l"
            moreover have "{(a', b'). (a', b') \<in> set l \<times> set l \<and> a' \<lesssim>\<^sub>l b'} = pl_\<alpha> l"
              using rel_of_set_l_eq_l_list
              unfolding relation_of_def
              by simp
            ultimately have "a \<lesssim>\<^sub>l b"
              using case_prodE mem_Collect_eq prod.inject
              by blast
            thus "(if b \<in> set l then index l b + 1 else 0) \<le>
                    (if a \<in> set l then index l a + 1 else 0)"
              by force
          qed
          thus "p'!i = relation_of (\<lambda> a b. rank_l l b \<le> rank_l l a) (set l) \<and>
                  l \<in> permutations_of_set A"
            using perm_l i_th_rel
            by presburger
        qed
      qed
      let ?P = "\<lambda> l a b. rank_l l b \<le> rank_l l a"
      have "\<And> l a. a \<in> (set l) \<Longrightarrow> ?P l a a"
        by simp
      moreover have
        "\<And> l a b c.
          \<lbrakk> a \<in> (set l); b \<in> (set l); c \<in> (set l) \<rbrakk> \<Longrightarrow> ?P l a b \<Longrightarrow> ?P l b c \<Longrightarrow> ?P l a c"
        by simp
      moreover have
        "\<And> l a b. \<lbrakk> a \<in> (set l); b \<in> (set l) \<rbrakk> \<Longrightarrow> ?P l a b \<Longrightarrow> ?P l b a \<Longrightarrow> a = b"
        using pos_in_list_yields_pos le_antisym
        by metis
      ultimately have "\<And> l. partial_order_on (set l) (relation_of (?P l) (set l))"
        using partial_order_on_relation_ofI
        by (smt (verit, best))
      moreover have set: "\<And> l. l \<in> permutations_of_set A \<Longrightarrow> set l = A"
        unfolding permutations_of_setD
        by simp
      ultimately have "partial_order_on A (p'!i)"
        using relation_of
        by fastforce
      moreover have "\<And> l. total_on (set l) (relation_of (?P l) (set l))"
        using relation_of
        unfolding total_on_def relation_of_def
        by auto
      hence "total_on A (p'!i)"
        using relation_of set
        by fastforce
      ultimately show "linear_order_on A (p'!i)"
        unfolding linear_order_on_def
        by simp
    qed
  next
    fix
      r :: "'a Preference_Relation" and
      q :: "'a Profile" and
      p' :: "'a Profile"
    assume
      prof_perms_eq_set_induct:
      "profile_permutations (length q) A = {q'. finite_profile A q' \<and> length q' = length q}" and
      len_eq: "length p' = length (r#q)" and
      fin_A: "finite A" and
      prof_p': "profile A p'"
    have "\<forall> i < length (r#q). linear_order_on A (p'!i)"
      using prof_p' len_eq
      unfolding profile_def
      by simp
    hence "\<forall> i < length (r#q). p'!i \<in> (pl_\<alpha> ` permutations_of_set A)"
      using fin_A lin_ord_pl_\<alpha>
      by blast
    hence "p' \<in> listset (replicate (length (r#q)) (pl_\<alpha> ` permutations_of_set A))"
      using all_ls_in_ls_set len_eq length_replicate nth_replicate fin_A
      by (metis (no_types, lifting))
    thus "p' \<in> profile_permutations (length (r#q)) A"
      using fin_A
      unfolding len_eq
      by simp
  qed
qed

subsection \<open>Soundness\<close>

lemma \<R>_sound:
  fixes
    K :: "'a Consensus_Class" and
    d :: "'a Election Distance"
  shows "electoral_module (distance_\<R> d K)"
  unfolding electoral_module_def
  by (auto simp add: is_arg_min_def)

subsection \<open>Inference Rules\<close>

lemma is_arg_min_equal:
  fixes
    f :: "'a \<Rightarrow> 'b::ord" and
    g :: "'a \<Rightarrow> 'b" and
    S :: "'a set" and
    x :: 'a
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
    then obtain y :: 'a where
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
      fix  y :: "'a"
      assume
        y_in_S: "y \<in> S" and
        g_y_lt_g_x: "g y < g x"
      have f_eq_g_for_elems_in_S: "\<forall> a. a \<in> S \<longrightarrow> f a = g a"
        using assms
        by simp
      hence "g x = f x"
        using x_in_S
        by presburger
      thus "False"
        using f_eq_g_for_elems_in_S g_y_lt_g_x not_y y_in_S
        by (metis (no_types))
    qed
    thus ?thesis
      using x_in_S not_y
      by simp
  qed
qed

lemma standard_distance_imp_equal_score:
  fixes
    d :: "'a Election Distance" and
    K :: "'a Consensus_Class" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes std: "standard d"
  shows "score d K (A, p) a = score_std d K (A, p) a"
proof -
  have "\<K>\<^sub>\<E> K a \<inter> Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p} \<subseteq> \<K>\<^sub>\<E> K a"
    by simp
  hence inf_lte_inf_int_pair:
    "Inf (d (A, p) ` (\<K>\<^sub>\<E> K a)) \<le>
      Inf (d (A, p) ` (\<K>\<^sub>\<E> K a \<inter>
        Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}))"
    using INF_superset_mono dual_order.refl
    by blast
  moreover have inf_gte_inf_int_pair:
    "Inf (d (A, p) ` (\<K>\<^sub>\<E> K a)) \<ge>
      Inf (d (A, p) ` ((\<K>\<^sub>\<E> K a) \<inter>
        Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}))"
  proof (rule INF_greatest)
    let ?inf =
      "Inf (d (A, p) ` (\<K>\<^sub>\<E> K a \<inter> Pair A ` {p'. finite_profile A p' \<and> length p' = length p}))"
    let ?compl = "(\<K>\<^sub>\<E> K a) - (\<K>\<^sub>\<E> K a \<inter> Pair A ` {p'. finite_profile A p' \<and> length p' = length p})"
    fix i :: "'a Election"
    assume i_in_\<K>\<^sub>\<E>: "i \<in> \<K>\<^sub>\<E> K a"
    have in_intersect:
      "i \<in> (\<K>\<^sub>\<E> K a \<inter> Pair A ` {p'. finite_profile A p' \<and> length p' = length p}) \<Longrightarrow>
        ?inf \<le> d (A, p) i"
      using INF_lower
      by (metis (no_types, lifting))
    have "i \<in> ?compl \<Longrightarrow> \<not> (A = fst i \<and> finite_profile A (snd i) \<and> length (snd i) = length p)"
      by fastforce
    moreover have "A \<noteq> fst i \<Longrightarrow> d (A, p) i = \<infinity>"
      using std
      unfolding standard_def
      using prod.collapse
      by metis
    moreover have "length (snd i) \<noteq> length p \<Longrightarrow> d (A, p) i = \<infinity>"
      using std
      unfolding standard_def
      using prod.exhaust_sel
      by metis
    moreover have "A = fst i \<and> length (snd i) = length p \<longrightarrow> finite_profile A (snd i)"
      using i_in_\<K>\<^sub>\<E> \<K>\<^sub>\<E>.simps
      by auto
    ultimately have
      "i \<in> ?compl \<Longrightarrow>
        Inf (d (A, p) ` (\<K>\<^sub>\<E> K a \<inter> Pair A ` {p'. finite_profile A p' \<and> length p' = length p})) \<le>
          d (A, p) i"
      by (metis (no_types, lifting) ereal_less_eq(1))
    thus "Inf (d (A, p) `
      (\<K>\<^sub>\<E> K a \<inter> Pair A ` {p'. finite_profile A p' \<and> length p' = length p})) \<le> d (A, p) i"
      using in_intersect i_in_\<K>\<^sub>\<E>
      by blast
  qed
  have profile_perm_set:
    "profile_permutations (length p) A =
      {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
    using profile_permutation_set
    by blast
  hence eq_intersect: "\<K>\<^sub>\<E>_std K a A (length p) =
           \<K>\<^sub>\<E> K a \<inter> Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
    by force
  moreover have
    "Inf (d (A, p) ` (\<K>\<^sub>\<E> K a)) =
                   Inf (d (A, p) ` (\<K>\<^sub>\<E> K a \<inter>
                    Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}))"
    using inf_gte_inf_int_pair order_antisym inf_lte_inf_int_pair
    by blast
  ultimately have inf_eq_inf_for_std_cons:
    "Inf (d (A, p) ` (\<K>\<^sub>\<E> K a)) =
      Inf (d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p)))"
    by simp
  also have inf_eq_min_for_std_cons: "... = score_std d K (A, p) a"
  proof (cases "\<K>\<^sub>\<E>_std K a A (length p) = {}")
    case True
    hence "(d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p))) = {}"
      by simp
    hence "Inf (d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p))) = \<infinity>"
      using top_ereal_def
      by simp
    also have "score_std d K (A, p) a = \<infinity>"
      using True score_std.simps
      unfolding Let_def
      by simp
    finally show ?thesis
      by simp
  next
    case False
    hence "d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p)) \<noteq> {}"
      by simp
    moreover have "finite (\<K>\<^sub>\<E>_std K a A (length p))"
    proof -
      have "finite (pl_\<alpha> ` permutations_of_set A)"
        by simp
      moreover have fin_A_imp_fin_all:
        "\<forall> n A. finite A \<longrightarrow> finite (profile_permutations n A)"
        using listset_finiteness
        by force
      hence "finite (profile_permutations (length p) A)"
      proof (cases "finite A")
        case True
        thus ?thesis
          using fin_A_imp_fin_all
          by metis
      next
        case False
        hence "permutations_of_set A = {}"
          using permutations_of_set_infinite
          by simp
        hence list_perm_A_empty: "pl_\<alpha> ` permutations_of_set A = {}"
          by simp
        let ?xs = "replicate (length p) (pl_\<alpha> ` permutations_of_set A)"
        from list_perm_A_empty
        have "\<forall> i < length ?xs. ?xs!i = {}"
          by simp
        hence "finite (listset (replicate (length p) (pl_\<alpha> ` permutations_of_set A)))"
          by (simp add: listset_finiteness)
        thus ?thesis
          by simp
      qed
      hence "finite (Set.filter (\<lambda> p. (consensus_\<K> K) (A, p) \<and> elect (rule_\<K> K) A p = {a})
                (profile_permutations (length p) A))"
        using finite_filter
        by blast
      thus ?thesis
        by simp
    qed
    hence "finite (d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p)))"
      by simp
    ultimately show ?thesis
      by (simp add: Lattices_Big.complete_linorder_class.Min_Inf)
  qed
  finally show "score d K (A, p) a = score_std d K (A, p) a"
    using inf_eq_inf_for_std_cons inf_eq_min_for_std_cons top_ereal_def
    by simp
qed

lemma anonymous_distance_and_consensus_imp_rule_anonymity:
  fixes
    d :: "'a Election Distance" and
    K :: "'a Consensus_Class"
  assumes
    d_anon: "distance_anonymity d" and
    K_anon: "consensus_rule_anonymity K"
  shows "anonymity (distance_\<R> d K)"
proof (unfold anonymity_def, safe)
  show "electoral_module (distance_\<R> d K)"
    by (simp add: \<R>_sound)
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    fin: "finite A" and
    profile_p: "profile A p" and
    profile_q: "profile A q" and
    p_q_perm: "p <~~> q"
  from p_q_perm
  obtain pi where
    pi_perm: "pi permutes {..< length p}" and
    pq: "permute_list pi p = q"
    using mset_eq_permutation
    by metis
  let ?listpi = "permute_list pi"
  let ?pi' = "\<lambda> n. (if n = length p then pi else id)"
  have perm: "\<forall> n. (?pi' n) permutes {..< n}"
    using pi_perm
    by simp
  let ?listpi' = "\<lambda> xs. permute_list (?pi' (length xs)) xs"
  let ?m = "distance_\<R> d K"
  let ?P = "\<lambda> a A' p'. (A', p') \<in> \<K>\<^sub>\<E> K a"
  have "\<forall> a. {(A', p') | A' p'. ?P a A' p'} = {(A', ?listpi' p') | A' p'. ?P a A' p'}"
  proof (clarify)
    fix a :: "'a"
    have apply_perm: "\<And> S x y. x <~~> y \<Longrightarrow> ?P a S x \<Longrightarrow> ?P a S y"
    proof -
      fix
        S :: "'a set" and
        x :: "'a Profile" and
        y :: "'a Profile"
      assume
        perm: "x <~~> y"  and
        fav_cons: "(S, x) \<in> \<K>\<^sub>\<E> K a"
      hence fin_S_x: "finite_profile S x"
        by simp
      from perm
      have fin_S_y: "finite_profile S y"
        unfolding profile_def
        using fin_S_x nth_mem perm_set_eq profile_set
        by metis
      moreover have "(consensus_\<K> K) (S, x) \<and> elect (rule_\<K> K) S x = {a}"
        using perm fav_cons
        by simp
      hence "(consensus_\<K> K) (S, y) \<and> elect (rule_\<K> K) S y = {a}"
        using K_anon
        unfolding consensus_rule_anonymity_def anonymity_def
        using perm fin_S_x fin_S_y calculation
        by (metis (no_types))
      ultimately show "(S, y) \<in> \<K>\<^sub>\<E> K a"
        by simp
    qed
    show "{(A', p') | A' p'. ?P a A' p'} = {(A', ?listpi' p') | A' p'. ?P a A' p'}" (is "?X = ?Y")
    proof
      show "?X \<subseteq> ?Y"
      proof
        fix E :: "'a Election"
        let
          ?A = "alts_\<E> E" and
          ?p = "prof_\<E> E"
        assume consensus_election_E: "E \<in> {(A', p') | A' p'. ?P a A' p'}"
        hence consens_elect_E_inst: "?P a ?A ?p"
          by simp
        show "E \<in> {(A', ?listpi' p') | A' p'. ?P a A' p'}"
        proof (cases "length ?p = length p")
          case True
          hence "permute_list (inv pi) ?p <~~> ?p"
            using pi_perm
            by (simp add: permutes_inv)
          hence "?P a ?A (permute_list (inv pi) ?p)"
            using consens_elect_E_inst apply_perm
            by presburger
          moreover have "length (permute_list (inv pi) ?p) = length p"
            using True
            by simp
          ultimately have
            "(?A, ?listpi (permute_list (inv pi) ?p)) \<in>
                {(A', ?listpi p') | A' p'. length p' = length p \<and> ?P a A' p'}"
            by auto
          also have "permute_list pi (permute_list (inv pi) ?p) = ?p"
            using permute_list_compose True pi_perm permute_list_id permutes_inv_o(2) pi_perm(1)
            by metis
          finally show ?thesis
            by auto
        next
          case False
          thus ?thesis
            using consensus_election_E
            by fastforce (* because ?listpi ?p = ?p *)
        qed
      qed
    next
      show "?Y \<subseteq> ?X"
      proof
        fix E :: "'a Election"
        let
          ?A = "alts_\<E> E" and
          ?r = "prof_\<E> E"
        assume consensus_elect_permut_E: "E \<in> {(A', ?listpi' p') | A' p'. ?P a A' p'}"
        hence "\<exists> p'. ?r = ?listpi' p' \<and> ?P a ?A p'"
          by auto
        then obtain p' where
          rp': "?r = ?listpi' p'" and
          consens_elect_inst: "?P a ?A p'"
          by metis
        show "E \<in> {(A', p') | A' p'. ?P a A' p'}"
        proof (cases "length p' = length p")
          case True
          have "?r <~~> p'"
            using pi_perm rp'
            by simp
          hence "?P a ?A ?r"
            unfolding rp'
            using consens_elect_inst apply_perm
            by presburger
          moreover have "length ?r = length p"
            using rp' True
            by simp
          ultimately show "E \<in> {(A', p') | A' p'. ?P a A' p'}"
            by simp
        next
          case False
          thus ?thesis
            using consensus_elect_permut_E rp'
            by fastforce (* because ?listpi ?p = ?p *)
        qed
      qed
    qed
  qed
  hence "\<forall> a \<in> A. d (A, q) ` {(A', p') | A' p'. ?P a A' p'}
             = d (A, q) ` {(A', ?listpi' p') | A' p'. ?P a A' p'}"
    by (metis (no_types, lifting))
  hence "\<forall> a \<in> A. {d (A, q) (A', p') | A' p'. ?P a A' p'}
             = {d (A, q) (A', ?listpi' p') | A' p'. ?P a A' p'}"
    by blast
  moreover from d_anon
  have "\<forall> a \<in> A. {d (A, p) (A', p') | A' p'. ?P a A' p'} =
          {d (A, ?listpi' p) (A', ?listpi' p') | A' p'. ?P a A' p'}"
  proof (clarify)
    fix a :: "'a"
    have "?listpi' = (\<lambda> p. permute_list (?pi' (length p)) p)"
      by simp
    from d_anon
    have anon:
      "\<And> A' p' A p pi. (\<forall> n. (pi n) permutes {..< n})
          \<longrightarrow> d (A, p) (A', p')
                = d (A, permute_list (pi (length p)) p) (A', permute_list (pi (length p')) p')"
      unfolding distance_anonymity_def
      by blast
    show "{d (A, p) (A', p') | A' p'. ?P a A' p'} =
            {d (A, ?listpi' p) (A', ?listpi' p') | A' p'. ?P a A' p'}"
      using perm anon[of ?pi' A p]
      unfolding distance_anonymity_def
      by simp
  qed
  hence "\<forall> a \<in> A. {d (A, p) (A', p') | A' p'. ?P a A' p'} =
          {d (A, q) (A', ?listpi' p') | A' p'. ?P a A' p'}"
    using pq
    by simp
  ultimately have
    "\<forall> a \<in> A. {d (A, q) (A', p') | A' p'. (A', p') \<in> \<K>\<^sub>\<E> K a} =
                {d (A, p) (A', p') | A' p'. (A', p') \<in> \<K>\<^sub>\<E> K a}"
    by simp
  hence "\<forall> a \<in> A. d (A, q) ` \<K>\<^sub>\<E> K a = d (A, p) ` \<K>\<^sub>\<E> K a"
    by fast
  hence "\<forall> a \<in> A. score d K (A, p) a = score d K (A, q) a"
    by simp
  thus "distance_\<R> d K A p = distance_\<R> d K A q"
    using is_arg_min_equal[of A "score d K (A, p)" "score d K (A, q)"]
    by auto
qed

end

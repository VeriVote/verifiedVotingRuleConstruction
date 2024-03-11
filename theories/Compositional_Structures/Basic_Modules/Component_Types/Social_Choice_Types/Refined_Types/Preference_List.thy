(*  File:       Preference_List.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Preference List\<close>

theory Preference_List
  imports "../Preference_Relation"
          "HOL-Combinatorics.Multiset_Permutations"
          "List-Index.List_Index"
begin

text \<open>
  Preference lists derive from preference relations, ordered from most to
  least preferred alternative.
\<close>

subsection \<open>Well-Formedness\<close>

type_synonym 'a Preference_List = "'a list"

abbreviation well_formed_l :: "'a Preference_List \<Rightarrow> bool" where
  "well_formed_l l \<equiv> distinct l"

subsection \<open>Auxiliary Lemmas About Lists\<close>

lemma is_arg_min_equal:
  fixes
    f :: "'a \<Rightarrow> 'b::ord" and
    g :: "'a \<Rightarrow> 'b" and
    S :: "'a set" and
    x :: "'a"
  assumes "\<forall> x \<in> S. f x = g x"
  shows "is_arg_min f (\<lambda> s. s \<in> S) x = is_arg_min g (\<lambda> s. s \<in> S) x"
proof (unfold is_arg_min_def, cases "x \<notin> S", clarsimp)
  case x_in_S: False
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
  proof (safe)
    fix
      a :: "'a" and
      A' :: "'a set"
    assume "finite {a#l | a l. a \<in> A' \<and> l \<in> S}"
    moreover have
      "{a'#l | a' l. a' \<in> insert a A' \<and> l \<in> S} =
          {a#l | a l. a \<in> A' \<and> l \<in> S} \<union> {a#l | l. l \<in> S}"
      by blast
    moreover have "finite {a#l | l. l \<in> S}"
      using fin_B
      by simp
    ultimately have "finite {a'#l | a' l. a' \<in> insert a A' \<and> l \<in> S}"
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

lemma all_ls_in_ls_set:
  fixes l :: "'a set list"
  shows "\<forall> l'. length l' = length l \<and> (\<forall> i < length l'. l'!i \<in> l!i) \<longrightarrow> l' \<in> listset l"
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
    using length_Suc_conv
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

subsection \<open>Ranking\<close>

text \<open>
  Rank 1 is the top preference, rank 2 the second, and so on. Rank 0 does not exist.
\<close>

fun rank_l :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank_l l a = (if a \<in> set l then index l a + 1 else 0)"

fun rank_l_idx :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank_l_idx l a =
    (let i = index l a in
      if i = length l then 0 else i + 1)"

lemma rank_l_equiv: "rank_l = rank_l_idx"
  unfolding member_def
  by (simp add: ext index_size_conv)

lemma rank_zero_imp_not_present:
  fixes
    p :: "'a Preference_List" and
    a :: "'a"
  assumes "rank_l p a = 0"
  shows "a \<notin> set p"
  using assms
  by force

definition above_l :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> 'a Preference_List" where
  "above_l r a \<equiv> take (rank_l r a) r"

subsection \<open>Definition\<close>

fun is_less_preferred_than_l :: "'a \<Rightarrow> 'a Preference_List \<Rightarrow> 'a \<Rightarrow> bool"
        ("_ \<lesssim>\<^sub>_ _" [50, 1000, 51] 50) where
    "a \<lesssim>\<^sub>l b = (a \<in> set l \<and> b \<in> set l \<and> index l a \<ge> index l b)"

lemma rank_gt_zero:
  fixes
    l :: "'a Preference_List" and
    a :: "'a"
  assumes "a \<lesssim>\<^sub>l a"
  shows "rank_l l a \<ge> 1"
  using assms
  by simp

definition pl_\<alpha> :: "'a Preference_List \<Rightarrow> 'a Preference_Relation" where
  "pl_\<alpha> l \<equiv> {(a, b). a \<lesssim>\<^sub>l b}"

lemma rel_trans:
  fixes l :: "'a Preference_List"
  shows "Relation.trans (pl_\<alpha> l)"
  unfolding Relation.trans_def pl_\<alpha>_def
  by simp

lemma pl_\<alpha>_lin_order:
  fixes
    A :: "'a set" and
    r :: "'a rel"
  assumes el: "r \<in> pl_\<alpha> ` permutations_of_set A"
  shows "linear_order_on A r"
proof (cases "A = {}")
  case True
  thus ?thesis
    using assms
    unfolding pl_\<alpha>_def is_less_preferred_than_l.simps
    by simp
next
  case False
  thus ?thesis
  proof (unfold linear_order_on_def total_on_def antisym_def
    partial_order_on_def preorder_on_def, safe)
    have "A \<noteq> {}"
      using False
      by simp
    hence "\<forall> l \<in> permutations_of_set A. l \<noteq> []"
      using assms permutations_of_setD(1)
      by force
    hence "\<forall> a \<in> A. \<forall> l \<in> permutations_of_set A. a \<lesssim>\<^sub>l a"
      using is_less_preferred_than_l.simps
      unfolding permutations_of_set_def
      by simp
    hence "\<forall> a \<in> A. \<forall> l \<in> permutations_of_set A. (a, a) \<in> pl_\<alpha> l"
      unfolding pl_\<alpha>_def
      by simp
    hence "\<forall> a \<in> A. (a, a) \<in> r"
      using el
      by auto
    moreover have "r \<subseteq> A \<times> A"
      using el
      unfolding pl_\<alpha>_def permutations_of_set_def
      by auto
    ultimately show "refl_on A r"
      unfolding refl_on_def
      by simp
  next
    show "Relation.trans r"
      using el rel_trans
      by auto
  next
    fix
      x :: "'a" and
      y :: "'a"
    assume
      x_rel_y: "(x, y) \<in> r" and
      y_rel_x: "(y, x) \<in> r"
    have "\<forall> x y. \<forall> l \<in> permutations_of_set A. x \<lesssim>\<^sub>l y \<and> y \<lesssim>\<^sub>l x \<longrightarrow> x = y"
      using is_less_preferred_than_l.simps index_eq_index_conv nle_le
      unfolding permutations_of_set_def
      by metis
    hence "\<forall> x y. \<forall> l \<in> pl_\<alpha> ` permutations_of_set A. (x, y) \<in> l \<and> (y, x) \<in> l \<longrightarrow> x = y"
      unfolding pl_\<alpha>_def permutations_of_set_def antisym_on_def
      by blast
    thus "x = y"
      using y_rel_x x_rel_y el
      by auto
  next
    fix
      x :: "'a" and
      y :: "'a"
    assume
      x_in_A: "x \<in> A" and
      y_in_A: "y \<in> A" and
      x_neq_y: "x \<noteq> y" and
      not_y_x_rel: "(y, x) \<notin> r"
    have "\<forall> x y. \<forall> l \<in> permutations_of_set A. x \<in> A \<and> y \<in> A \<and> x \<noteq> y \<and> (\<not> y \<lesssim>\<^sub>l x) \<longrightarrow> x \<lesssim>\<^sub>l y"
      using is_less_preferred_than_l.simps
      unfolding permutations_of_set_def
      by auto
    hence "\<forall> x y. \<forall> l \<in> pl_\<alpha> ` permutations_of_set A.
            x \<in> A \<and> y \<in> A \<and> x \<noteq> y \<and> (y, x) \<notin> l \<longrightarrow> (x, y) \<in> l"
      unfolding pl_\<alpha>_def permutations_of_set_def
      by blast
    thus "(x, y) \<in> r"
      using x_in_A y_in_A x_neq_y not_y_x_rel el
      by auto
  qed
qed

lemma lin_order_pl_\<alpha>:
  fixes
    r :: "'a rel" and
    A :: "'a set"
  assumes
    lin_order: "linear_order_on A r" and
    fin: "finite A"
  shows "r \<in> pl_\<alpha> ` permutations_of_set A"
proof -
  let ?\<phi> = "\<lambda> a. card ((underS r a) \<inter> A)"
  let ?inv = "the_inv_into A ?\<phi>"
  let ?l = "map (\<lambda> x. ?inv x) (rev [0 ..< card A])"
  have antisym: "\<forall> a b. a \<in> ((underS r b) \<inter> A) \<and> b \<in> ((underS r a) \<inter> A) \<longrightarrow> False"
    using lin_order
    unfolding underS_def linear_order_on_def partial_order_on_def antisym_def
    by auto
  hence "\<forall> a b c. a \<in> (underS r b) \<inter> A \<longrightarrow> b \<in> (underS r c) \<inter> A \<longrightarrow> a \<in> (underS r c) \<inter> A"
    using lin_order CollectD CollectI transD IntE IntI
    unfolding underS_def linear_order_on_def partial_order_on_def preorder_on_def
    by (metis (mono_tags, lifting))
  hence "\<forall> a b. a \<in> (underS r b) \<inter> A \<longrightarrow> (underS r a) \<inter> A \<subset> (underS r b) \<inter> A"
    using antisym
    by blast
  hence mon: "\<forall> a b. a \<in> (underS r b) \<inter> A \<longrightarrow> ?\<phi> a < ?\<phi> b"
    using fin
    by (simp add: psubset_card_mono)
  moreover have total_underS:
    "\<forall> a b. a \<in> A \<and> b \<in> A \<and> a \<noteq> b \<longrightarrow> a \<in> ((underS r b) \<inter> A) \<or> b \<in> ((underS r a) \<inter> A)"
    using lin_order totalp_onD totalp_on_total_on_eq
    unfolding underS_def linear_order_on_def partial_order_on_def antisym_def
    by fastforce
  ultimately have "\<forall> a b. a \<in> A \<and> b \<in> A \<and> a \<noteq> b \<longrightarrow> ?\<phi> a \<noteq> ?\<phi> b"
    using order_less_imp_not_eq2
    by metis
  hence inj: "inj_on ?\<phi> A"
    using inj_on_def
    by blast
  have in_bounds: "\<forall> a \<in> A. ?\<phi> a < card A"
    using CollectD IntD1 card_seteq fin inf_sup_ord(2) linorder_le_less_linear
    unfolding underS_def
    by (metis (mono_tags, lifting))
  hence "?\<phi> ` A \<subseteq> {0 ..< card A}"
    using atLeast0LessThan
    by blast
  moreover have "card (?\<phi> ` A) = card A"
    using inj fin card_image
    by blast
  ultimately have "?\<phi> ` A = {0 ..< card A}"
    by (simp add: card_subset_eq)
  hence bij: "bij_betw ?\<phi> A {0 ..< card A}"
    using inj
    unfolding bij_betw_def
    by safe
  hence bij_inv: "bij_betw ?inv {0 ..< card A} A"
    using bij_betw_the_inv_into
    by metis
  hence "?inv ` {0 ..< card A} = A"
    unfolding bij_betw_def
    by metis
  hence "set ?l = A"
    by simp
  moreover have dist_l: "distinct ?l"
    using bij_inv
    unfolding distinct_map
    using bij_betw_imp_inj_on
    by simp
  ultimately have "?l \<in> permutations_of_set A"
    by auto
  moreover have index_eq: "\<forall> a \<in> A. index ?l a = card A - 1 - ?\<phi> a"
  proof
    fix a :: "'a"
    assume a_in_A: "a \<in> A"
    have "\<forall> xs. \<forall> i < length xs. (rev xs)!i = xs!(length xs - 1 - i)"
      using rev_nth
      by auto
    hence "\<forall> i < length [0 ..< card A]. (rev [0 ..< card A])!i
              = [0 ..< card A]!(length [0 ..< card A] - 1 - i)"
      by blast
    moreover have "\<forall> i < card A. [0 ..< card A]!i = i"
      by simp
    moreover have card_A_len: "length [0 ..< card A] = card A"
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
      using in_bounds a_in_A card_Diff_singleton card_Suc_Diff1 diff_less_Suc fin
      by metis
    thus "index ?l a = card A - 1 - card (underS r a \<inter> A)"
      using bij_inv dist_l a_in_A card_A_len card_Diff_singleton card_Suc_Diff1
            diff_less_Suc fin index_nth_id length_map length_rev
      by metis
  qed
  moreover have "pl_\<alpha> ?l = r"
  proof
    show "r \<subseteq> pl_\<alpha> ?l"
    proof (unfold pl_\<alpha>_def, auto)
      fix
        a :: "'a" and
        b :: "'a"
      assume "(a, b) \<in> r"
      hence "a \<in> A"
        using lin_order
        unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
        by auto
      thus "a \<in> ?inv ` {0 ..< card A}"
        using bij_inv bij_betw_def
        by metis
    next
      fix
        a :: "'a" and
        b :: "'a"
      assume "(a, b) \<in> r"
      hence "b \<in> A"
        using lin_order
        unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
        by auto
      thus "b \<in> ?inv ` {0 ..< card A}"
        using bij_inv bij_betw_def
        by metis
    next
      fix
        a :: "'a" and
        b :: "'a"
      assume rel: "(a, b) \<in> r"
      hence el_A: "a \<in> A \<and> b \<in> A"
        using lin_order
        unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
        by auto
      moreover have "a \<in> underS r b \<or> a = b"
        using lin_order rel
        unfolding underS_def
        by simp
      ultimately have "?\<phi> a \<le> ?\<phi> b"
        using mon le_eq_less_or_eq
        by auto
      thus "index ?l b \<le> index ?l a"
        using index_eq el_A diff_le_mono2
        by metis
    qed
  next
    show "pl_\<alpha> ?l \<subseteq> r"
    proof (unfold pl_\<alpha>_def, auto)
      fix
        a :: "nat" and
        b :: "nat"
      assume
        in_bnds_a: "a < card A" and
        in_bnds_b: "b < card A" and
        index_rel: "index ?l (?inv b) \<le> index ?l (?inv a)"
      have el_a: "?inv a \<in> A"
        using bij_inv in_bnds_a atLeast0LessThan
        unfolding bij_betw_def
        by auto
      moreover have el_b: "?inv b \<in> A"
        using bij_inv in_bnds_b atLeast0LessThan
        unfolding bij_betw_def
        by auto
      ultimately have leq_diff: "card A - 1 - (?\<phi> (?inv b)) \<le> card A - 1 - (?\<phi> (?inv a))"
        using index_rel index_eq
        by metis
      have "\<forall> a < card A. ?\<phi> (?inv a) < card A"
        using fin bij_inv bij
        unfolding bij_betw_def
        by fastforce
      hence "?\<phi> (?inv b) \<le> card A - 1 \<and> ?\<phi> (?inv a) \<le> card A - 1"
        using in_bnds_a in_bnds_b fin
        by fastforce
      hence "?\<phi> (?inv b) \<ge> ?\<phi> (?inv a)"
        using fin leq_diff le_diff_iff'
        by blast
      hence cases: "?\<phi> (?inv a) < ?\<phi> (?inv b) \<or> ?\<phi> (?inv a) = ?\<phi> (?inv b)"
        by auto
      have "\<forall> a b. a \<in> A \<and> b \<in> A \<and> ?\<phi> a < ?\<phi> b \<longrightarrow> a \<in> underS r b"
        using mon total_underS antisym IntD1 order_less_not_sym
        by metis
      hence "?\<phi> (?inv a) < ?\<phi> (?inv b) \<longrightarrow> ?inv a \<in> underS r (?inv b)"
        using el_a el_b
        by blast
      hence cases_less: "?\<phi> (?inv a) < ?\<phi> (?inv b) \<longrightarrow> (?inv a, ?inv b) \<in> r"
        unfolding underS_def
        by simp
      have "\<forall> a b. a \<in> A \<and> b \<in> A \<and> ?\<phi> a = ?\<phi> b \<longrightarrow> a = b"
        using mon total_underS antisym order_less_not_sym
        by metis
      hence "?\<phi> (?inv a) = ?\<phi> (?inv b) \<longrightarrow> ?inv a = ?inv b"
        using el_a el_b
        by simp
      hence cases_eq: "?\<phi> (?inv a) = ?\<phi> (?inv b) \<longrightarrow> (?inv a, ?inv b) \<in> r"
        using lin_order el_a el_b
        unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
        by auto
      show "(?inv a, ?inv b) \<in> r"
        using cases cases_less cases_eq
        by auto
    qed
  qed
  ultimately show "r \<in> pl_\<alpha> ` permutations_of_set A"
    by auto
qed

lemma index_helper:
  fixes
    xs :: "'x list" and
    x :: "'x"
  assumes
    fin_set_xs: "finite (set xs)" and
    dist_xs: "distinct xs" and
    "x \<in> set xs"
  shows "index xs x = card {y \<in> set xs. index xs y < index xs x}"
proof -
  have bij: "bij_betw (index xs) (set xs) {0 ..< length xs}"
    using assms bij_betw_index
    by blast
  hence "card {y \<in> set xs. index xs y < index xs x}
        = card (index xs ` {y \<in> set xs. index xs y < index xs x})"
    using CollectD bij_betw_same_card bij_betw_subset subsetI
    by (metis (no_types, lifting))
  also have "index xs ` {y \<in> set xs. index xs y < index xs x}
        = {m | m. m \<in> index xs ` (set xs) \<and> m < index xs x}"
    by blast
  also have "{m | m. m \<in> index xs ` (set xs) \<and> m < index xs x} = {m | m. m < index xs x}"
    using bij assms atLeastLessThan_iff bot_nat_0.extremum
          index_image index_less_size_conv order_less_trans
    by metis
  also have "card {m | m. m < index xs x} = index xs x"
    by simp
  finally show ?thesis
    by simp
qed

lemma pl_\<alpha>_eq_imp_list_eq:
  fixes
    xs :: "'x list" and
    ys :: "'x list"
  assumes
    fin_set_xs: "finite (set xs)" and
    set_eq: "set xs = set ys" and
    dist_xs: "distinct xs" and
    dist_ys: "distinct ys" and
    pl_\<alpha>_eq: "pl_\<alpha> xs = pl_\<alpha> ys"
  shows "xs = ys"
proof (rule ccontr)
  assume "xs \<noteq> ys"
  moreover with this
  have "xs \<noteq> [] \<and> ys \<noteq> []"
    using set_eq
    by auto
  ultimately obtain
    i :: "nat" and
    x :: "'x" where
      "i < length xs" and
      "xs!i \<noteq> ys!i" and
      "x = xs!i" and
    x_in_xs: "x \<in> set xs"
    using dist_xs dist_ys distinct_remdups_id
          length_remdups_card_conv nth_equalityI nth_mem set_eq
    by metis
  moreover with this
    have neq_ind: "index xs x \<noteq> index ys x"
    using dist_xs index_nth_id nth_index set_eq
    by metis
  ultimately have
    "card {y \<in> set xs. index xs y < index xs x} \<noteq> card {y \<in> set xs. index ys y < index ys x}"
    using dist_xs dist_ys set_eq index_helper fin_set_xs
    by (metis (mono_tags))
  then obtain y :: "'x" where
    y_in_set_xs: "y \<in> set xs" and
    y_neq_x: "y \<noteq> x" and
    neq_indices:
      "(index xs y < index xs x \<and> index ys y > index ys x) \<or>
        (index ys y < index ys x \<and> index xs y > index xs x)"
    using index_eq_index_conv not_less_iff_gr_or_eq set_eq
    by (metis (mono_tags, lifting))
  hence "(is_less_preferred_than_l x xs y \<and> is_less_preferred_than_l y ys x)
            \<or> (is_less_preferred_than_l x ys y \<and> is_less_preferred_than_l y xs x)"
    unfolding is_less_preferred_than_l.simps
    using y_in_set_xs less_imp_le_nat set_eq x_in_xs
    by blast
  hence "((x, y) \<in> pl_\<alpha> xs \<and> (x, y) \<notin> pl_\<alpha> ys) \<or> ((x, y) \<in> pl_\<alpha> ys \<and> (x, y) \<notin> pl_\<alpha> xs)"
    unfolding pl_\<alpha>_def
    using is_less_preferred_than_l.simps y_neq_x neq_indices
          case_prod_conv linorder_not_less mem_Collect_eq
    by metis
  thus False
    using pl_\<alpha>_eq
    by blast
qed
  
lemma pl_\<alpha>_bij_betw:
  fixes X :: "'x set"
  assumes "finite X"
  shows "bij_betw pl_\<alpha> (permutations_of_set X) {r. linear_order_on X r}"
proof (unfold bij_betw_def, safe)
  show "inj_on pl_\<alpha> (permutations_of_set X)"
    unfolding inj_on_def permutations_of_set_def
    using pl_\<alpha>_eq_imp_list_eq assms
    by fastforce
next
  fix xs :: "'x list"
  assume "xs \<in> permutations_of_set X"
  thus "linear_order_on X (pl_\<alpha> xs)"
    using assms pl_\<alpha>_lin_order
    by blast
next
  fix r :: "'x rel"
  assume "linear_order_on X r"
  thus "r \<in> pl_\<alpha> ` permutations_of_set X"
    using assms lin_order_pl_\<alpha>
    by blast
qed

subsection \<open>Limited Preference\<close>

definition limited :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "limited A r \<equiv> \<forall> a. a \<in> set r \<longrightarrow>  a \<in> A"

fun limit_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> 'a Preference_List" where
  "limit_l A l = List.filter (\<lambda> a. a \<in> A) l"

lemma limited_dest:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List" and
    a :: "'a" and
    b :: "'a"
  assumes
    "a \<lesssim>\<^sub>l b" and
    "limited A l"
  shows "a \<in> A \<and> b \<in> A"
  using assms
  unfolding limited_def
  by simp

lemma limit_equiv:
  fixes
    A :: "'a set" and
    l :: "'a list"
  assumes "well_formed_l l"
  shows "pl_\<alpha> (limit_l A l) = limit A (pl_\<alpha> l)"
  using assms
proof (induction l)
  case Nil
  thus "pl_\<alpha> (limit_l A []) = limit A (pl_\<alpha> [])"
    unfolding pl_\<alpha>_def
    by simp
next
  case (Cons a l)
  fix
    a :: "'a" and
    l :: "'a list"
  assume
    wf_imp_limit: "well_formed_l l \<Longrightarrow> pl_\<alpha> (limit_l A l) = limit A (pl_\<alpha> l)" and
    wf_a_l: "well_formed_l (a#l)"
  show "pl_\<alpha> (limit_l A (a#l)) = limit A (pl_\<alpha> (a#l))"
    using wf_imp_limit wf_a_l
  proof (clarsimp, safe)
    fix
      b :: "'a" and
      c :: "'a"
    assume b_less_c: "(b, c) \<in> pl_\<alpha> (a#(filter (\<lambda> a. a \<in> A) l))"
    have limit_preference_list_assoc: "pl_\<alpha> (limit_l A l) = limit A (pl_\<alpha> l)"
      using wf_a_l wf_imp_limit
      by simp
    thus "(b, c) \<in> pl_\<alpha> (a#l)"
    proof (unfold pl_\<alpha>_def is_less_preferred_than_l.simps, safe)
      show "b \<in> set (a#l)"
        using b_less_c
        unfolding pl_\<alpha>_def
        by fastforce
    next
      show "c \<in> set (a#l)"
        using b_less_c
        unfolding pl_\<alpha>_def
        by fastforce
    next
      have "\<forall> a' l' a''. (a'::'a) \<lesssim>\<^sub>l' a'' =
            (a' \<in> set l' \<and> a'' \<in> set l' \<and> index l' a'' \<le> index l' a')"
        using is_less_preferred_than_l.simps
        by blast
      moreover from this
      have "{(a', b'). a' \<lesssim>\<^sub>(limit_l A l) b'} =
        {(a', a''). a' \<in> set (limit_l A l) \<and> a'' \<in> set (limit_l A l) \<and>
            index (limit_l A l) a'' \<le> index (limit_l A l) a'}"
        by presburger
      moreover from this
      have "{(a', b'). a' \<lesssim>\<^sub>l b'} =
        {(a', a''). a' \<in> set l \<and> a'' \<in> set l \<and> index l a'' \<le> index l a'}"
        using is_less_preferred_than_l.simps
        by auto
      ultimately have "{(a', b').
              a' \<in> set (limit_l A l) \<and> b' \<in> set (limit_l A l) \<and>
                index (limit_l A l) b' \<le> index (limit_l A l) a'} =
                    limit A {(a', b'). a' \<in> set l \<and> b' \<in> set l \<and> index l b' \<le> index l a'}"
        using pl_\<alpha>_def limit_preference_list_assoc
        by (metis (no_types))
      hence idx_imp:
        "b \<in> set (limit_l A l) \<and> c \<in> set (limit_l A l) \<and>
          index (limit_l A l) c \<le> index (limit_l A l) b \<longrightarrow>
            b \<in> set l \<and> c \<in> set l \<and> index l c \<le> index l b"
        by auto
      have "b \<lesssim>\<^sub>(a#(filter (\<lambda> a. a \<in> A) l)) c"
        using b_less_c case_prodD mem_Collect_eq
        unfolding pl_\<alpha>_def
        by metis
      moreover obtain
        f :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" and
        g :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list" and
        h :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
        "\<forall> d s e. d \<lesssim>\<^sub>s e \<longrightarrow>
          d = f e s d \<and> s = g e s d \<and> e = h e s d \<and> f e s d \<in> set (g e s d) \<and>
            index (g e s d) (h e s d) \<le> index (g e s d) (f e s d) \<and>
              h e s d \<in> set (g e s d)"
        by fastforce
      ultimately have
        "b = f c (a#(filter (\<lambda> a. a \<in> A) l)) b \<and>
          a#(filter (\<lambda> a. a \<in> A) l) = g c (a#(filter (\<lambda> a. a \<in> A) l)) b \<and>
          c = h c (a#(filter (\<lambda> a. a \<in> A) l)) b \<and>
          f c (a#(filter (\<lambda> a. a \<in> A) l)) b \<in> set (g c (a#(filter (\<lambda> a. a \<in> A) l)) b) \<and>
          h c (a#(filter (\<lambda> a. a \<in> A) l)) b \<in> set (g c (a#(filter (\<lambda> a. a \<in> A) l)) b) \<and>
          index (g c (a#(filter (\<lambda> a. a \<in> A) l)) b)
              (h c (a#(filter (\<lambda> a. a \<in> A) l)) b) \<le>
            index (g c (a#(filter (\<lambda> a. a \<in> A) l)) b)
              (f c (a#(filter (\<lambda> a. a \<in> A) l)) b)"
        by blast
      moreover have "filter (\<lambda> a. a \<in> A) l = limit_l A l"
        by simp
      ultimately have "a \<noteq> c \<longrightarrow> index (a#l) c \<le> index (a#l) b"
        using idx_imp
        by force
      thus "index (a#l) c \<le> index (a#l) b"
        by force
    qed
  next
    fix
      b :: "'a" and
      c :: "'a"
    assume
       "a \<in> A" and
      "(b, c) \<in> pl_\<alpha> (a#(filter (\<lambda> a. a \<in> A) l))"
    thus "c \<in> A"
      unfolding pl_\<alpha>_def
      by fastforce
  next
    fix
      b :: "'a" and
      c :: "'a"
    assume
      "a \<in> A" and
      "(b, c) \<in> pl_\<alpha> (a#(filter (\<lambda> a. a \<in> A) l))"
    thus "b \<in> A"
      unfolding pl_\<alpha>_def
      using case_prodD insert_iff mem_Collect_eq set_filter inter_set_filter IntE
      by auto
  next
    fix
      b :: "'a" and
      c :: "'a"
    assume
      b_less_c: "(b, c) \<in> pl_\<alpha> (a#l)" and
      b_in_A: "b \<in> A" and
      c_in_A: "c \<in> A"
    show "(b, c) \<in> pl_\<alpha> (a#(filter (\<lambda> a. a \<in> A) l))"
    proof (unfold pl_\<alpha>_def is_less_preferred_than.simps, safe)
      show "b \<lesssim>\<^sub>(a#(filter (\<lambda> a. a \<in> A) l)) c"
      proof (unfold is_less_preferred_than_l.simps, safe)
        show "b \<in> set (a#(filter (\<lambda> a. a \<in> A) l))"
        using b_less_c b_in_A
        unfolding pl_\<alpha>_def
        by fastforce
      next
        show "c \<in> set (a#(filter (\<lambda> a. a \<in> A) l))"
        using b_less_c c_in_A
        unfolding pl_\<alpha>_def
        by fastforce
    next
      have "(b, c) \<in> pl_\<alpha> (a#l)"
        by (simp add: b_less_c)
      hence "b \<lesssim>\<^sub>(a#l) c"
        using case_prodD mem_Collect_eq
        unfolding pl_\<alpha>_def
        by metis
      moreover have
        "pl_\<alpha> (filter (\<lambda> a. a \<in> A) l) = {(a, b). (a, b) \<in> pl_\<alpha> l \<and> a \<in> A \<and> b \<in> A}"
        using wf_a_l wf_imp_limit
        by simp
      ultimately show
        "index (a#(filter (\<lambda> a. a \<in> A) l)) c \<le> index (a#(filter (\<lambda> a. a \<in> A) l)) b"
        unfolding pl_\<alpha>_def
        using add_leE add_le_cancel_right case_prodI c_in_A b_in_A index_Cons set_ConsD
              in_rel_Collect_case_prod_eq linorder_le_cases mem_Collect_eq not_one_le_zero
        by fastforce
    qed
  qed
  next
    fix
      b :: "'a" and
      c :: "'a"
    assume
      a_not_in_A: "a \<notin> A" and
      b_less_c: "(b, c) \<in> pl_\<alpha> l"
    show "(b, c) \<in> pl_\<alpha> (a#l)"
    proof (unfold pl_\<alpha>_def is_less_preferred_than_l.simps, safe)
      show "b \<in> set (a#l)"
        using b_less_c
        unfolding pl_\<alpha>_def
        by fastforce
    next
      show "c \<in> set (a#l)"
        using b_less_c
        unfolding pl_\<alpha>_def
        by fastforce
    next
      show "index (a#l) c \<le> index (a#l) b"
      proof (unfold index_def, simp, safe)
        assume "a = b"
        thus False
          using a_not_in_A b_less_c case_prod_conv is_less_preferred_than_l.elims
                mem_Collect_eq set_filter wf_a_l
          unfolding pl_\<alpha>_def
          by simp
      next
        show "find_index (\<lambda> x. x = c) l \<le> find_index (\<lambda> x. x = b) l"
          using b_less_c case_prodD mem_Collect_eq
          unfolding pl_\<alpha>_def
          by (simp add: index_def)
      qed
    qed
  next
    fix
      b :: "'a" and
      c :: "'a"
    assume
      a_not_in_l: "a \<notin> set l" and
      a_not_in_A: "a \<notin> A" and
      b_in_A: "b \<in> A" and
      c_in_A: "c \<in> A" and
      b_less_c: "(b, c) \<in> pl_\<alpha> (a#l)"
    thus "(b, c) \<in> pl_\<alpha> l"
    proof (unfold pl_\<alpha>_def is_less_preferred_than_l.simps, safe)
      assume "b \<in> set (a#l)"
      thus "b \<in> set l"
        using a_not_in_A b_in_A
        by fastforce
    next
      assume "c \<in> set (a#l)"
      thus "c \<in> set l"
        using a_not_in_A c_in_A
        by fastforce
    next
      assume "index (a#l) c \<le> index (a#l) b"
      thus "index l c \<le> index l b"
        using a_not_in_l a_not_in_A c_in_A add_le_cancel_right
              index_Cons index_le_size size_index_conv
        by (metis (no_types, lifting))
    qed
  qed
qed

subsection \<open>Auxiliary Definitions\<close>

definition total_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "total_on_l A l \<equiv> \<forall> a \<in> A. a \<in> set l"

definition refl_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "refl_on_l A l \<equiv> (\<forall> a. a \<in> set l \<longrightarrow> a \<in> A) \<and> (\<forall> a \<in> A. a \<lesssim>\<^sub>l a)"

definition trans :: "'a Preference_List \<Rightarrow> bool" where
  "trans l \<equiv> \<forall> (a, b, c) \<in> set l \<times> set l \<times> set l. a \<lesssim>\<^sub>l b \<and> b \<lesssim>\<^sub>l c \<longrightarrow> a \<lesssim>\<^sub>l c"

definition preorder_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "preorder_on_l A l \<equiv> refl_on_l A l \<and> trans l"

definition antisym_l :: "'a list \<Rightarrow> bool" where
  "antisym_l l \<equiv> \<forall> a b. a \<lesssim>\<^sub>l b \<and> b \<lesssim>\<^sub>l a \<longrightarrow> a = b"

definition partial_order_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "partial_order_on_l A l \<equiv> preorder_on_l A l \<and> antisym_l l"

definition linear_order_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "linear_order_on_l A l \<equiv> partial_order_on_l A l \<and> total_on_l A l"

definition connex_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "connex_l A l \<equiv> limited A l \<and> (\<forall> a \<in> A. \<forall> b \<in> A. a \<lesssim>\<^sub>l b \<or> b \<lesssim>\<^sub>l a)"

abbreviation ballot_on :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "ballot_on A l \<equiv> well_formed_l l \<and> linear_order_on_l A l"

subsection \<open>Auxiliary Lemmas\<close>

lemma list_trans[simp]:
  fixes l :: "'a Preference_List"
  shows "trans l"
  unfolding trans_def
  by simp

lemma list_antisym[simp]:
  fixes l :: "'a Preference_List"
  shows "antisym_l l"
  unfolding antisym_l_def
  by auto

lemma lin_order_equiv_list_of_alts:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  shows "linear_order_on_l A l = (A = set l)"
  unfolding linear_order_on_l_def total_on_l_def partial_order_on_l_def preorder_on_l_def
            refl_on_l_def
  by auto

lemma connex_imp_refl:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  assumes "connex_l A l"
  shows "refl_on_l A l"
  unfolding refl_on_l_def
  using assms connex_l_def Preference_List.limited_def
  by metis

lemma lin_ord_imp_connex_l:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  assumes "linear_order_on_l A l"
  shows "connex_l A l"
  using assms linorder_le_cases
  unfolding connex_l_def linear_order_on_l_def preorder_on_l_def limited_def refl_on_l_def
            partial_order_on_l_def is_less_preferred_than_l.simps
  by metis

lemma above_trans:
  fixes
    l :: "'a Preference_List" and
    a :: "'a" and
    b :: "'a"
  assumes
    "trans l" and
    "a \<lesssim>\<^sub>l b"
  shows "set (above_l l b) \<subseteq> set (above_l l a)"
  using assms set_take_subset_set_take rank_l.simps
        Suc_le_mono add.commute add_0 add_Suc
  unfolding above_l_def Preference_List.is_less_preferred_than_l.simps One_nat_def
  by metis

lemma less_preferred_l_rel_equiv:
  fixes
    l :: "'a Preference_List" and
    a :: "'a" and
    b :: "'a"
  shows "a \<lesssim>\<^sub>l b = Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
  unfolding pl_\<alpha>_def
  by simp

theorem above_equiv:
  fixes
    l :: "'a Preference_List" and
    a :: "'a"
  shows "set (above_l l a) = above (pl_\<alpha> l) a"
proof (safe)
  fix b :: "'a"
  assume b_member: "b \<in> set (above_l l a)"
  hence "index l b \<le> index l a"
    unfolding rank_l.simps above_l_def
    using Suc_eq_plus1 Suc_le_eq index_take linorder_not_less
          bot_nat_0.extremum_strict
    by (metis (full_types))
  hence "a \<lesssim>\<^sub>l b"
    using Suc_le_mono add_Suc le_antisym take_0 b_member
          in_set_takeD index_take le0 rank_l.simps
    unfolding above_l_def is_less_preferred_than_l.simps
    by metis
  thus "b \<in> above (pl_\<alpha> l) a"
    using less_preferred_l_rel_equiv pref_imp_in_above
    by metis
next
  fix b :: "'a"
  assume "b \<in> above (pl_\<alpha> l) a"
  hence "a \<lesssim>\<^sub>l b"
    using pref_imp_in_above less_preferred_l_rel_equiv
    by metis
  thus "b \<in> set (above_l l a)"
    unfolding above_l_def is_less_preferred_than_l.simps rank_l.simps
    using Suc_eq_plus1 Suc_le_eq index_less_size_conv set_take_if_index le_imp_less_Suc
    by (metis (full_types))
qed

theorem rank_equiv:
  fixes
    l :: "'a Preference_List" and
    a :: "'a"
  assumes "well_formed_l l"
  shows "rank_l l a = rank (pl_\<alpha> l) a"
proof (simp, safe)
  assume "a \<in> set l"
  moreover have "above (pl_\<alpha> l) a = set (above_l l a)"
    unfolding above_equiv
    by simp
  moreover have "distinct (above_l l a)"
    unfolding above_l_def
    using assms distinct_take
    by blast
  moreover from this
  have "card (set (above_l l a)) = length (above_l l a)"
    using distinct_card
    by blast
  moreover have "length (above_l l a) = rank_l l a"
    unfolding above_l_def
    using Suc_le_eq
    by (simp add: in_set_member)
  ultimately show "Suc (index l a) = card (above (pl_\<alpha> l) a)"
    by simp
next
  assume "a \<notin> set l"
  hence "above (pl_\<alpha> l) a = {}"
    unfolding above_def
    using less_preferred_l_rel_equiv
    by fastforce
  thus "card (above (pl_\<alpha> l) a) = 0"
    by fastforce
qed

lemma lin_ord_equiv:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  shows "linear_order_on_l A l = linear_order_on A (pl_\<alpha> l)"
  unfolding pl_\<alpha>_def linear_order_on_l_def linear_order_on_def refl_on_l_def
            Relation.trans_def preorder_on_l_def partial_order_on_l_def partial_order_on_def
            total_on_l_def preorder_on_def refl_on_def antisym_def total_on_def
            is_less_preferred_than_l.simps
  by auto

subsection \<open>First Occurrence Indices\<close>

lemma pos_in_list_yields_rank:
  fixes
    l :: "'a Preference_List" and
    a :: "'a" and
    n :: "nat"
  assumes
    "\<forall> (j::nat) \<le> n. l!j \<noteq> a" and
    "l!(n - 1) = a"
  shows "rank_l l a = n"
  using assms
proof (induction l arbitrary: n, simp_all) qed

lemma ranked_alt_not_at_pos_before:
  fixes
    l :: "'a Preference_List" and
    a :: "'a" and
    n :: "nat"
  assumes
    "a \<in> set l" and
    "n < (rank_l l a) - 1"
  shows "l!n \<noteq> a"
  using assms add_diff_cancel_right' index_first member_def rank_l.simps
  by metis

lemma pos_in_list_yields_pos:
  fixes
    l :: "'a Preference_List" and
    a :: "'a"
  assumes "a \<in> set l"
  shows "l!(rank_l l a - 1) = a"
  using assms
proof (induction l, simp)
  fix
    l :: "'a Preference_List" and
    b :: "'a"
  case (Cons b l)
  assume "a \<in> set (b#l)"
  moreover from this
  have "rank_l (b#l) a = 1 + index (b#l) a"
    using Suc_eq_plus1 add_Suc add_cancel_left_left rank_l.simps
    by metis
  ultimately show "(b#l)!(rank_l (b#l) a - 1) = a"
    using diff_add_inverse nth_index
    by metis
qed

(* Alternative expression of list_to_rel using relation_of.
  This is used in the proof that list_to_rel produces linear orders.  *)
lemma rel_of_pref_pred_for_set_eq_list_to_rel:
  fixes l :: "'a Preference_List"
  shows "relation_of (\<lambda> y z. y \<lesssim>\<^sub>l z) (set l) = pl_\<alpha> l"
proof (unfold relation_of_def, safe)
  fix
    a :: "'a" and
    b :: "'a"
  assume "a \<lesssim>\<^sub>l b"
  moreover have "(a \<lesssim>\<^sub>l b) = (a \<preceq>\<^sub>(pl_\<alpha> l) b)"
    using less_preferred_l_rel_equiv
    by (metis (no_types))
  ultimately show "(a, b) \<in> pl_\<alpha> l"
    by simp
next
  fix
    a :: "'a" and
    b :: "'a"
  assume "(a, b) \<in> pl_\<alpha> l"
  thus "a \<lesssim>\<^sub>l b"
    using less_preferred_l_rel_equiv
    unfolding is_less_preferred_than.simps
    by metis
  thus
    "a \<in> set l" and
    "b \<in> set l"
    by (simp, simp)
qed

end
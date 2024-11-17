(*  File:       Preference_List.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Refined Types\<close>

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
    f g :: "'a \<Rightarrow> 'b :: ord" and
    S :: "'a set" and
    x :: "'a"
  assumes "\<forall> x \<in> S. f x = g x"
  shows "is_arg_min f (\<lambda> s. s \<in> S) x = is_arg_min g (\<lambda> s. s \<in> S) x"
proof (unfold is_arg_min_def, cases "x \<notin> S")
  case True
  thus "(x \<in> S \<and> (\<nexists>y. y \<in> S \<and> f y < f x)) = (x \<in> S \<and> (\<nexists>y. y \<in> S \<and> g y < g x))"
    by safe
next
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
        "y \<in> S" and
        "g y < g x"
      moreover have "\<forall> a \<in> S. f a = g a"
        using assms
        by simp
      moreover from this have "g x = f x"
        using x_in_S
        by metis
      ultimately show False
        using not_y
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
    using finite_induct[of _ ?P] fin_A
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
  ultimately have
    "finite (listset l)" and
    "finite {a'#l' | a' l'. a' \<in> a \<and> l' \<in> (listset l)}"
    using list_cons_presv_finiteness
    by (blast, blast)
  thus "finite (listset (a#l))"
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
  moreover fix
    a :: "'a set" and
    l :: "'a set list" and
    m :: "'a list"
  assume
    "\<forall> l'. l' \<in> listset l \<longrightarrow> length l' = length l" and
    "m \<in> listset (a#l)"
  moreover have
    "\<forall> a' l' :: 'a set list. listset (a'#l') =
      {b#m | b m. b \<in> a' \<and> m \<in> listset l'}"
    by (simp add: set_Cons_def)
  ultimately show "length m = length (a#l)"
    by force
qed

lemma all_ls_elems_in_ls_set:
  fixes l :: "'a set list"
  shows "\<forall> l' \<in> listset l. \<forall> i :: nat < length l'. l'!i \<in> l!i"
proof (induct l, safe)
  case Nil
  fix
    l' :: "'a list" and
    i :: "nat"
  assume
    "l' \<in> listset []" and
    "i < length l'"
  thus "l'!i \<in> []!i"
    by simp
next
  case (Cons a l)
  moreover fix
    a :: "'a set" and
    l :: "'a set list" and
    l' :: "'a list" and
    i :: "nat"
  assume
    "\<forall> l' \<in> listset l. \<forall> i :: nat < length l'. l'!i \<in> l!i" and
    "l' \<in> listset (a#l)" and
    "i < length l'"
  moreover from this have "l' \<in> set_Cons a (listset l)"
    by simp
  hence "\<exists> b m. l' = b#m \<and> b \<in> a \<and> m \<in> (listset l)"
    unfolding set_Cons_def
    by simp
  ultimately show "l'!i \<in> (a#l)!i"
    using nth_Cons_Suc Suc_less_eq gr0_conv_Suc
          length_Cons nth_non_equal_first_eq
    by metis
qed

lemma all_ls_in_ls_set:
  fixes l :: "'a set list"
  shows "\<forall> l'. length l' = length l
            \<and> (\<forall> i < length l'. l'!i \<in> l!i) \<longrightarrow> l' \<in> listset l"
proof (induction l, safe)
  case Nil
  fix l' :: "'a list"
  assume "length l' = length []"
  thus "l' \<in> listset []"
    by simp
next
  case (Cons a l)
  fix
    l :: "'a set list" and
    l' :: "'a list" and
    s :: "'a set"
  assume "length l' = length (s#l)"
  moreover then obtain
    t :: "'a list" and
    x :: "'a" where
    l'_cons: "l' = x#t"
    using length_Suc_conv
    by metis
  moreover assume
    "\<forall> m. length m = length l \<and> (\<forall> i < length m. m!i \<in> l!i)
            \<longrightarrow> m \<in> listset l" and
    "\<forall> i < length l'. l'!i \<in> (s#l)!i"
  ultimately have
    "x \<in> s" and
    "t \<in> listset l"
    using diff_Suc_1 diff_Suc_eq_diff_pred zero_less_diff
          zero_less_Suc length_Cons
    by (metis nth_Cons_0, metis nth_Cons_Suc)
  thus "l' \<in> listset (s#l)"
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
  shows "trans (pl_\<alpha> l)"
  unfolding Relation.trans_def pl_\<alpha>_def
  by simp

lemma pl_\<alpha>_lin_order:
  fixes
    A :: "'a set" and
    r :: "'a rel"
  assumes "r \<in> pl_\<alpha> ` permutations_of_set A"
  shows "linear_order_on A r"
proof (cases "A = {}", unfold linear_order_on_def total_on_def
        partial_order_on_def antisym_def preorder_on_def,
        intro conjI impI allI ballI)
  case True
  fix x y :: "'a"
  show
    "refl_on A r" and
    "trans r" and
    "(x, y) \<in> r \<Longrightarrow> x = y" and
    "x \<in> A \<Longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
    using assms True
    unfolding pl_\<alpha>_def
    by (simp, simp, simp, simp)
next
  case False
  fix x y :: "'a"
  show "((refl_on A r \<and> trans r)
      \<and> (\<forall> x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y))
      \<and> (\<forall> x \<in> A. \<forall> y \<in> A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r)"
  proof (intro conjI ballI allI impI)
    have "\<forall> l \<in> permutations_of_set A. l \<noteq> []"
      using assms False permutations_of_setD
      by force
    hence "\<forall> a \<in> A. \<forall> l \<in> permutations_of_set A. (a, a) \<in> pl_\<alpha> l"
      unfolding is_less_preferred_than_l.simps
                permutations_of_set_def pl_\<alpha>_def
      by simp
    hence "\<forall> a \<in> A. (a, a) \<in> r"
      using assms
      by blast
    moreover have "r \<subseteq> A \<times> A"
      using assms
      unfolding pl_\<alpha>_def permutations_of_set_def
      by auto
    ultimately show "refl_on A r"
      unfolding refl_on_def
      by safe
  next
    show "trans r"
      using assms rel_trans
      by safe
  next
    fix x y :: "'a"
    assume
      "(x, y) \<in> r" and
      "(y, x) \<in> r"
    moreover have
      "\<forall> x y. \<forall> l \<in> permutations_of_set A. x \<lesssim>\<^sub>l y \<and> y \<lesssim>\<^sub>l x \<longrightarrow> x = y"
      using is_less_preferred_than_l.simps index_eq_index_conv nle_le
      unfolding permutations_of_set_def
      by metis
    hence "\<forall> x y. \<forall> l \<in> pl_\<alpha> ` permutations_of_set A.
                (x, y) \<in> l \<and> (y, x) \<in> l \<longrightarrow> x = y"
      unfolding pl_\<alpha>_def permutations_of_set_def antisym_on_def
      by blast
    ultimately show "x = y"
      using assms
      by metis
  next
    fix x y :: "'a"
    assume
      "x \<in> A" and
      "y \<in> A" and
      "x \<noteq> y"
    moreover have
      "\<forall> x \<in> A. \<forall> y \<in> A. \<forall> l \<in> permutations_of_set A.
              x \<noteq> y \<and> (\<not> y \<lesssim>\<^sub>l x) \<longrightarrow> x \<lesssim>\<^sub>l y"
      using is_less_preferred_than_l.simps
      unfolding permutations_of_set_def
      by auto
    hence "\<forall> x \<in> A. \<forall> y \<in> A. \<forall> l \<in> pl_\<alpha> ` permutations_of_set A.
              x \<noteq> y \<and> (y, x) \<notin> l \<longrightarrow> (x, y) \<in> l"
      using is_less_preferred_than_l.simps
      unfolding permutations_of_set_def
      unfolding pl_\<alpha>_def permutations_of_set_def
      by blast
    ultimately show "(x, y) \<in> r \<or> (y, x) \<in> r"
      using assms
      by metis
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
  have antisym:
    "\<forall> a \<in> A. \<forall> b \<in> A.
        a \<in> (underS r b) \<and> b \<in> (underS r a) \<longrightarrow> False"
    using lin_order
    unfolding underS_def linear_order_on_def partial_order_on_def antisym_def
    by blast
  hence "\<forall> a \<in> A. \<forall> b \<in> A. \<forall> c \<in> A.
            a \<in> (underS r b) \<longrightarrow> b \<in> (underS r c) \<longrightarrow> a \<in> (underS r c)"
    using lin_order CollectD CollectI transD
    unfolding underS_def linear_order_on_def
              partial_order_on_def preorder_on_def
    by (metis (mono_tags, lifting))
  hence a_lt_b_imp:
    "\<forall> a \<in> A. \<forall> b \<in> A. a \<in> (underS r b) \<longrightarrow> (underS r a) \<subset> (underS r b)"
    using preorder_on_def partial_order_on_def linear_order_on_def
          antisym lin_order psubsetI underS_E underS_incr
    by metis
  hence mon: "\<forall> a \<in> A. \<forall> b \<in> A. a \<in> (underS r b) \<longrightarrow> ?\<phi> a < ?\<phi> b"
      using Int_iff Int_mono a_lt_b_imp card_mono card_subset_eq
            fin finite_Int order_le_imp_less_or_eq underS_E
            subset_iff_psubset_eq
      by metis
  moreover have total_underS:
    "\<forall> a \<in> A. \<forall> b \<in> A. a \<noteq> b \<longrightarrow> a \<in> (underS r b) \<or> b \<in> (underS r a)"
    using lin_order totalp_onD totalp_on_total_on_eq
    unfolding underS_def linear_order_on_def partial_order_on_def antisym_def
    by fastforce
  ultimately have "\<forall> a \<in> A. \<forall> b \<in> A. a \<noteq> b \<longrightarrow> ?\<phi> a \<noteq> ?\<phi> b"
    using order_less_imp_not_eq2
    by metis
  hence inj: "inj_on ?\<phi> A"
    using inj_on_def
    by blast
  have in_bounds: "\<forall> a \<in> A. ?\<phi> a < card A"
    using CollectD IntD1 card_seteq fin inf_le2 linorder_le_less_linear
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
  hence bij_A: "bij_betw ?\<phi> A {0 ..< card A}"
    using inj
    unfolding bij_betw_def
    by safe
  hence bij_inv: "bij_betw ?inv {0 ..< card A} A"
    using bij_betw_the_inv_into
    by metis
  hence "?inv ` {0 ..< card A} = A"
    unfolding bij_betw_def
    by metis
  hence set_eq_A: "set ?l = A"
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
    have "\<forall> l. \<forall> i < length l. (rev l)!i = l!(length l - 1 - i)"
      using rev_nth
      by auto
    hence "\<forall> i < length [0 ..< card A]. (rev [0 ..< card A])!i =
                [0 ..< card A]!(length [0 ..< card A] - 1 - i)"
      by blast
    moreover have "\<forall> i < card A. [0 ..< card A]!i = i"
      by simp
    moreover have card_A_len: "length [0 ..< card A] = card A"
      by simp
    ultimately have "\<forall> i < card A. (rev [0 ..< card A])!i = card A - 1 - i"
      using diff_Suc_eq_diff_pred diff_less diff_self_eq_0
            less_imp_diff_less zero_less_Suc
      by metis
    moreover have "\<forall> i < card A. ?l!i = ?inv ((rev [0 ..< card A])!i)"
      by simp
    ultimately have "\<forall> i < card A. ?l!i = ?inv (card A - 1 - i)"
      by presburger
    moreover have
      "card A - 1 - (card A - 1 - card (underS r a \<inter> A)) =
          card (underS r a \<inter> A)"
      using in_bounds a_in_A
      by auto
    moreover have "?inv (card (underS r a \<inter> A)) = a"
      using a_in_A inj the_inv_into_f_f
      by fastforce
    ultimately have "?l!(card A - 1 - card (underS r a \<inter> A)) = a"
      using in_bounds a_in_A card_Diff_singleton
            card_Suc_Diff1 diff_less_Suc fin
      by metis
    thus "index ?l a = card A - 1 - card (underS r a \<inter> A)"
      using bij_inv dist_l a_in_A card_A_len card_Diff_singleton card_Suc_Diff1
            diff_less_Suc fin index_nth_id length_map length_rev
      by metis
  qed
  moreover have "pl_\<alpha> ?l = r"
  proof (intro equalityI, unfold pl_\<alpha>_def is_less_preferred_than_l.simps, safe)
    fix a b :: "'a"
    assume
      in_bounds_a: "a \<in> set ?l" and
      in_bounds_b: "b \<in> set ?l"
    moreover have element_a: "?inv (index ?l a) \<in> A"
      using bij_inv in_bounds_a atLeast0LessThan set_eq_A bij_inv
            cancel_comm_monoid_add_class.diff_cancel diff_Suc_eq_diff_pred
            diff_less in_bounds index_eq lessThan_iff less_imp_diff_less
            zero_less_Suc inj dist_l image_eqI image_eqI length_upt
      unfolding bij_betw_def
      by (metis (no_types, lifting))
    moreover have el_b: "?inv (index ?l b) \<in> A"
      using bij_inv in_bounds_b atLeast0LessThan set_eq_A bij_inv
            cancel_comm_monoid_add_class.diff_cancel diff_Suc_eq_diff_pred
            diff_less in_bounds index_eq lessThan_iff less_imp_diff_less
            zero_less_Suc inj dist_l image_eqI image_eqI length_upt
      unfolding bij_betw_def
      by (metis (no_types, lifting))
    moreover assume "index ?l b \<le> index ?l a"
    ultimately have "card A - 1 - (?\<phi> b) \<le> card A - 1 - (?\<phi> a)"
      using index_eq set_eq_A
      by metis
    moreover have "\<forall> a < card A. ?\<phi> (?inv a) < card A"
      using fin bij_inv bij_A
      unfolding bij_betw_def
      by fastforce
    hence "?\<phi> b \<le> card A - 1 \<and> ?\<phi> a \<le> card A - 1"
      using in_bounds_a in_bounds_b fin
      by fastforce
    ultimately have "?\<phi> b \<ge> ?\<phi> a"
      using fin le_diff_iff'
      by blast
    hence "?\<phi> a < ?\<phi> b \<or> ?\<phi> a = ?\<phi> b"
      by auto
    moreover have
      "\<forall> a \<in> A. \<forall> b \<in> A. ?\<phi> a < ?\<phi> b \<longrightarrow> a \<in> underS r b"
      using mon total_underS antisym order_less_not_sym
      by metis
    hence "?\<phi> a < ?\<phi> b \<longrightarrow> a \<in> underS r b"
      using element_a el_b in_bounds_a in_bounds_b set_eq_A
      by blast
    hence "?\<phi> a < ?\<phi> b \<longrightarrow> (a, b) \<in> r"
      unfolding underS_def
      by simp
    moreover have "\<forall> a \<in> A. \<forall> b \<in> A. ?\<phi> a = ?\<phi> b \<longrightarrow> a = b"
      using mon total_underS antisym order_less_not_sym
      by metis
    hence "?\<phi> a = ?\<phi> b \<longrightarrow> a = b"
      using element_a el_b in_bounds_a in_bounds_b set_eq_A
      by blast
    hence "?\<phi> a = ?\<phi> b \<longrightarrow> (a, b) \<in> r"
      using lin_order element_a el_b in_bounds_a
            in_bounds_b set_eq_A
      unfolding linear_order_on_def partial_order_on_def
                preorder_on_def refl_on_def
      by auto
    ultimately show "(a, b) \<in> r"
      by auto
  next
    fix a b :: "'a"
    assume a_b_rel: "(a, b) \<in> r"
    hence
      a_in_A: "a \<in> A" and
      b_in_A: "b \<in> A" and
      a_under_b_or_eq: "a \<in> underS r b \<or> a = b"
      using lin_order
      unfolding linear_order_on_def partial_order_on_def
                preorder_on_def refl_on_def underS_def
      by auto
    thus
      "a \<in> set ?l" and
      "b \<in> set ?l"
      using bij_inv set_eq_A
      by (metis, metis)
    hence "?\<phi> a \<le> ?\<phi> b"
      using mon le_eq_less_or_eq a_under_b_or_eq
            a_in_A b_in_A
      by auto
    thus "index ?l b \<le> index ?l a"
      using index_eq a_in_A b_in_A diff_le_mono2
      by metis
  qed
  ultimately show "r \<in> pl_\<alpha> ` permutations_of_set A"
    by auto
qed

lemma index_helper:
  fixes
    l :: "'x list" and
    x :: "'x"
  assumes
    "finite (set l)" and
    "distinct l" and
    "x \<in> set l"
  shows "index l x = card {y \<in> set l. index l y < index l x}"
proof -
  have bij_l: "bij_betw (index l) (set l) {0 ..< length l}"
    using assms bij_betw_index
    by blast
  hence "card {y \<in> set l. index l y < index l x} =
            card (index l ` {y \<in> set l. index l y < index l x})"
    using CollectD bij_betw_same_card bij_betw_subset subsetI
    by (metis (no_types, lifting))
  also have "index l ` {y \<in> set l. index l y < index l x} =
        {m | m. m \<in> index l ` (set l) \<and> m < index l x}"
    by blast
  also have
    "{m | m. m \<in> index l ` (set l) \<and> m < index l x} =
        {m | m. m < index l x}"
    using bij_l assms atLeastLessThan_iff bot_nat_0.extremum
          index_image index_less_size_conv order_less_trans
    by metis
  also have "card {m | m. m < index l x} = index l x"
    by simp
  finally show ?thesis
    by simp
qed

lemma pl_\<alpha>_eq_imp_list_eq:
  fixes l l' :: "'x list"
  assumes
    fin_set_l: "finite (set l)" and
    set_eq: "set l = set l'" and
    dist_l: "distinct l" and
    dist_l': "distinct l'" and
    pl_\<alpha>_eq: "pl_\<alpha> l = pl_\<alpha> l'"
  shows "l = l'"
proof (rule ccontr)
  assume "l \<noteq> l'"
  moreover with set_eq
  have "l \<noteq> [] \<and> l' \<noteq> []"
    by auto
  ultimately obtain
    i :: "nat" and
    x :: "'x" where
      "i < length l" and
      "l!i \<noteq> l'!i" and
      "x = l!i" and
    x_in_l: "x \<in> set l"
    using dist_l dist_l' distinct_remdups_id
          length_remdups_card_conv nth_equalityI
          nth_mem set_eq
    by metis
  moreover with set_eq
    have neq_ind: "index l x \<noteq> index l' x"
    using dist_l index_nth_id nth_index
    by metis
  ultimately have
    "card {y \<in> set l. index l y < index l x} \<noteq>
      card {y \<in> set l. index l' y < index l' x}"
    using dist_l dist_l' set_eq index_helper fin_set_l
    by (metis (mono_tags))
  then obtain y :: "'x" where
    y_in_set_l: "y \<in> set l" and
    y_neq_x: "y \<noteq> x" and
    neq_indices:
      "(index l y < index l x \<and> index l' y > index l' x)
      \<or> (index l' y < index l' x \<and> index l y > index l x)"
    using index_eq_index_conv not_less_iff_gr_or_eq set_eq
    by (metis (mono_tags, lifting))
  hence
    "(is_less_preferred_than_l x l y \<and> is_less_preferred_than_l y l' x)
    \<or> (is_less_preferred_than_l x l' y \<and> is_less_preferred_than_l y l x)"
    unfolding is_less_preferred_than_l.simps
    using y_in_set_l less_imp_le_nat set_eq x_in_l
    by blast
  hence "((x, y) \<in> pl_\<alpha> l \<and> (x, y) \<notin> pl_\<alpha> l')
        \<or> ((x, y) \<in> pl_\<alpha> l' \<and> (x, y) \<notin> pl_\<alpha> l)"
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
  fix l :: "'x list"
  assume "l \<in> permutations_of_set X"
  thus "linear_order_on X (pl_\<alpha> l)"
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
    a b :: "'a"
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
  show "pl_\<alpha> (limit_l A []) = limit A (pl_\<alpha> [])"
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
  proof (unfold limit_l.simps limit.simps, intro equalityI, safe)
    fix b c :: "'a"
    assume b_less_c: "(b, c) \<in> pl_\<alpha> (filter (\<lambda> a. a \<in> A) (a#l))"
    moreover have limit_preference_list_assoc:
      "pl_\<alpha> (limit_l A l) = limit A (pl_\<alpha> l)"
      using wf_a_l wf_imp_limit
      by simp
    ultimately have
      "b \<in> set (a#l)" and
      "c \<in> set (a#l)"
      using case_prodD filter_set mem_Collect_eq member_filter
            is_less_preferred_than_l.simps
      unfolding pl_\<alpha>_def
      by (metis, metis)
    thus "(b, c) \<in> pl_\<alpha> (a#l)"
    proof (unfold pl_\<alpha>_def is_less_preferred_than_l.simps, safe)
      have idx_set_eq:
        "\<forall> a' l' a''. (a' :: 'a) \<lesssim>\<^sub>l' a'' =
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
              a' \<in> set (limit_l A l) \<and> b' \<in> set (limit_l A l)
              \<and> index (limit_l A l) b' \<le> index (limit_l A l) a'} =
                    limit A {(a', b'). a' \<in> set l
              \<and> b' \<in> set l \<and> index l b' \<le> index l a'}"
        using pl_\<alpha>_def limit_preference_list_assoc
        by (metis (no_types))
      hence idx_imp:
        "b \<in> set (limit_l A l) \<and> c \<in> set (limit_l A l)
            \<and> index (limit_l A l) c \<le> index (limit_l A l) b
        \<longrightarrow> b \<in> set l \<and> c \<in> set l \<and> index l c \<le> index l b"
        by auto
      have "b \<lesssim>\<^sub>(filter (\<lambda> a. a \<in> A) (a#l)) c"
        using b_less_c case_prodD mem_Collect_eq
        unfolding pl_\<alpha>_def
        by (metis (no_types))
      moreover obtain
        f h :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" and
        g :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
        "\<forall> d s e. d \<lesssim>\<^sub>s e \<longrightarrow>
          d = f e s d \<and> s = g e s d \<and> e = h e s d
          \<and> f e s d \<in> set (g e s d) \<and> h e s d \<in> set (g e s d)
          \<and> index (g e s d) (h e s d) \<le> index (g e s d) (f e s d)"
        by fastforce
      ultimately have
        "b = f c (filter (\<lambda> a. a \<in> A) (a#l)) b
          \<and> filter (\<lambda> a. a \<in> A) (a#l) =
              g c (filter (\<lambda> a. a \<in> A) (a#l)) b
          \<and> c = h c (filter (\<lambda> a. a \<in> A) (a#l)) b
          \<and> f c (filter (\<lambda> a. a \<in> A) (a#l)) b
              \<in> set (g c (filter (\<lambda> a. a \<in> A) (a#l)) b)
          \<and> h c (filter (\<lambda> a. a \<in> A) (a#l)) b
              \<in> set (g c (filter (\<lambda> a. a \<in> A) (a#l)) b)
          \<and> index (g c (filter (\<lambda> a. a \<in> A) (a#l)) b)
              (h c (filter (\<lambda> a. a \<in> A) (a#l)) b)
            \<le> index (g c (filter (\<lambda> a. a \<in> A) (a#l)) b)
                (f c (filter (\<lambda> a. a \<in> A) (a#l)) b)"
        by blast
      moreover have "filter (\<lambda> a. a \<in> A) l = limit_l A l"
        by simp
      moreover have
        "index (limit_l A l) c \<noteq>
          index (g c (filter (\<lambda> a. a \<in> A) (a#l)) b)
              (h c (filter (\<lambda> a. a \<in> A) (a # l)) b)
        \<or> index (limit_l A l) b \<noteq>
          index (g c (filter (\<lambda> a. a \<in> A) (a#l)) b)
              (f c (filter (\<lambda> a. a \<in> A) (a#l)) b)
        \<or> index (limit_l A l) c \<le> index (limit_l A l) b
        \<or> \<not> index (g c (filter (\<lambda> a. a \<in> A) (a # l)) b)
          (h c (filter (\<lambda> a. a \<in> A) (a#l)) b)
            \<le> index (g c (filter (\<lambda> a. a \<in> A) (a#l)) b)
                  (f c (filter (\<lambda> a. a \<in> A) (a#l)) b)"
        by presburger
      ultimately have "a \<noteq> c \<longrightarrow> index (a#l) c \<le> index (a#l) b"
          using add_le_cancel_right idx_imp index_Cons le_zero_eq
                nth_index set_ConsD wf_a_l
          unfolding filter.simps is_less_preferred_than_l.elims
                    distinct.simps
          by metis
      thus "index (a#l) c \<le> index (a#l) b"
        by force
    qed
    show
      "b \<in> A" and
      "c \<in> A"
      using b_less_c case_prodD mem_Collect_eq set_filter
      unfolding pl_\<alpha>_def is_less_preferred_than_l.simps
      by (metis (no_types, lifting),
          metis (no_types, lifting))
  next
    fix b c :: "'a"
    assume
      b_less_c: "(b, c) \<in> pl_\<alpha> (a#l)" and
      b_in_A: "b \<in> A" and
      c_in_A: "c \<in> A"
    have "(b, c) \<in> pl_\<alpha> (a#l)"
      by (simp add: b_less_c)
    hence "b \<lesssim>\<^sub>(a#l) c"
      using case_prodD mem_Collect_eq
      unfolding pl_\<alpha>_def
      by metis
    moreover have
      "pl_\<alpha> (filter (\<lambda> a. a \<in> A) l) =
          {(a, b). (a, b) \<in> pl_\<alpha> l \<and> a \<in> A \<and> b \<in> A}"
      using wf_a_l wf_imp_limit
      by simp
    ultimately have
      "index (filter (\<lambda> a. a \<in> A) (a#l)) c
          \<le> index (filter (\<lambda> a. a \<in> A) (a#l)) b"
      unfolding pl_\<alpha>_def
      using add_leE add_le_cancel_right case_prodI c_in_A
            b_in_A index_Cons set_ConsD not_one_le_zero
            in_rel_Collect_case_prod_eq mem_Collect_eq
            linorder_le_cases
      by fastforce
    moreover have
      "b \<in> set (filter (\<lambda> a. a \<in> A) (a#l))" and
      "c \<in> set (filter (\<lambda> a. a \<in> A) (a#l))"
      using b_less_c b_in_A c_in_A
      unfolding pl_\<alpha>_def
      by (fastforce, fastforce)
    ultimately show "(b, c) \<in> pl_\<alpha> (filter (\<lambda> a. a \<in> A) (a#l))"
      unfolding pl_\<alpha>_def
      by simp
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
  unfolding linear_order_on_l_def total_on_l_def
            partial_order_on_l_def preorder_on_l_def
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
  unfolding connex_l_def linear_order_on_l_def preorder_on_l_def
            limited_def refl_on_l_def partial_order_on_l_def
            is_less_preferred_than_l.simps
  by metis

lemma above_trans:
  fixes
    l :: "'a Preference_List" and
    a b :: "'a"
  assumes
    "trans l" and
    "a \<lesssim>\<^sub>l b"
  shows "set (above_l l b) \<subseteq> set (above_l l a)"
  using assms set_take_subset_set_take rank_l.simps
        Suc_le_mono add.commute add_0 add_Suc
  unfolding Preference_List.is_less_preferred_than_l.simps
            above_l_def One_nat_def
  by metis

lemma less_preferred_l_rel_equiv:
  fixes
    l :: "'a Preference_List" and
    a b :: "'a"
  shows "a \<lesssim>\<^sub>l b =
    Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
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
    unfolding above_l_def is_less_preferred_than_l.simps
              rank_l.simps
    using Suc_eq_plus1 Suc_le_eq index_less_size_conv
          set_take_if_index le_imp_less_Suc
    by (metis (full_types))
qed

theorem rank_equiv:
  fixes
    l :: "'a Preference_List" and
    a :: "'a"
  assumes "well_formed_l l"
  shows "rank_l l a = rank (pl_\<alpha> l) a"
proof (unfold rank_l.simps rank.simps, cases "a \<in> set l")
  case True
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
  ultimately show
    "(if a \<in> set l then index l a + 1 else 0) =
        card (above (pl_\<alpha> l) a)"
    by simp
next
  case False
  hence "above (pl_\<alpha> l) a = {}"
    unfolding above_def
    using less_preferred_l_rel_equiv
    by fastforce
  thus "(if a \<in> set l then index l a + 1 else 0) =
          card (above (pl_\<alpha> l) a)"
    using False
    by fastforce
qed

lemma lin_ord_equiv:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  shows "linear_order_on_l A l = linear_order_on A (pl_\<alpha> l)"
  unfolding is_less_preferred_than_l.simps antisym_def total_on_def
            pl_\<alpha>_def linear_order_on_l_def linear_order_on_def
            refl_on_l_def Relation.trans_def preorder_on_l_def
            partial_order_on_l_def partial_order_on_def
            total_on_l_def preorder_on_def refl_on_def
  by auto

subsection \<open>First Occurrence Indices\<close>

lemma pos_in_list_yields_rank:
  fixes
    l :: "'a Preference_List" and
    a :: "'a" and
    n :: "nat"
  assumes
    "\<forall> (j :: nat) \<le> n. l!j \<noteq> a" and
    "l!(n - 1) = a"
  shows "rank_l l a = n"
  using assms
proof (induction l arbitrary: n)
  case Nil
  thus ?case
    by simp
next
  fix
    l :: "'a Preference_List" and
    a :: "'a"
  case (Cons a l)
  thus ?case
    by simp
qed

lemma ranked_alt_not_at_pos_before:
  fixes
    l :: "'a Preference_List" and
    a :: "'a" and
    n :: "nat"
  assumes
    "a \<in> set l" and
    "n < (rank_l l a) - 1"
  shows "l!n \<noteq> a"
  using index_first member_def rank_l.simps
        assms add_diff_cancel_right'
  by metis

lemma pos_in_list_yields_pos:
  fixes
    l :: "'a Preference_List" and
    a :: "'a"
  assumes "a \<in> set l"
  shows "l!(rank_l l a - 1) = a"
  using assms
proof (induction l)
  case Nil
  thus ?case
    by simp
next
  fix
    l :: "'a Preference_List" and
    b :: "'a"
  case (Cons b l)
  assume "a \<in> set (b#l)"
  moreover from this
  have "rank_l (b#l) a = 1 + index (b#l) a"
    using Suc_eq_plus1 add_Suc add_cancel_left_left
          rank_l.simps
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
  fix a b :: "'a"
  assume "a \<lesssim>\<^sub>l b"
  moreover have "(a \<lesssim>\<^sub>l b) = (a \<preceq>\<^sub>(pl_\<alpha> l) b)"
    using less_preferred_l_rel_equiv
    by (metis (no_types))
  ultimately show "(a, b) \<in> pl_\<alpha> l"
    by simp
next
  fix a b :: "'a"
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
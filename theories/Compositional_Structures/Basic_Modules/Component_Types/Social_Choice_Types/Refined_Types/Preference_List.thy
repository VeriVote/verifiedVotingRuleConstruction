(*  File:       Preference_List.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Preference List\<close>

theory Preference_List
  imports "../Preference_Relation"
          "List-Index.List_Index"
begin

text \<open>
  Preference lists derive from preference relations, ordered from most to
  least preferred alternative.
\<close>

subsection \<open>Well-Formedness\<close>

type_synonym 'a Preference_List = "'a list"

abbreviation well_formed_l :: "'a Preference_List \<Rightarrow> bool" where
  "well_formed_l p \<equiv> distinct p"

subsection \<open>Ranking\<close>

text \<open>
  Rank 1 is the top preference, rank 2 the second, and so on. Rank 0 does not exist.
\<close>

fun rank_l :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank_l l x = (if (List.member l x) then (index l x) + 1 else 0)"

definition above_l :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> 'a Preference_List" where
  "above_l r c \<equiv> take (rank_l r c) r"

lemma rank_zero_imp_not_present:
  fixes
    p :: "'a Preference_List" and
    a :: "'a"
  assumes "rank_l p a = 0"
  shows "\<not> List.member p a"
  using assms
  by force

subsection \<open>Definition\<close>

fun is_less_preferred_than_l ::
  "'a \<Rightarrow> 'a Preference_List \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lesssim>\<^sub>_ _" [50, 1000, 51] 50) where
    "x \<lesssim>\<^sub>l y = ((List.member l x) \<and> (List.member l y) \<and> (rank_l l x \<ge> rank_l l y))"

lemma rank_gt_zero:
  fixes
    l :: "'a Preference_List" and
    x :: 'a
  assumes
    wf : "well_formed_l l" and
    refl: "x \<lesssim>\<^sub>l x"
  shows "rank_l l x \<ge> 1"
  using refl
  by simp

definition pl_\<alpha> :: "'a Preference_List \<Rightarrow> 'a Preference_Relation" where
  "pl_\<alpha> l \<equiv> {(a, b). a \<lesssim>\<^sub>l b}"

lemma rel_trans:
  fixes l :: "'a Preference_List"
  shows "Relation.trans (pl_\<alpha> l)"
  unfolding Relation.trans_def pl_\<alpha>_def
  by simp

subsection \<open>Limited Preference\<close>

definition limited :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "limited A r \<equiv> (\<forall> x. (List.member r x) \<longrightarrow>  x \<in> A)"

fun limit_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> 'a Preference_List" where
  "limit_l A pl = List.filter (\<lambda> a. a \<in> A) pl"

lemma limitedI:
  fixes
    l :: "'a Preference_List" and
    A :: "'a set"
  assumes "\<And> x y. x \<lesssim>\<^sub>l y \<Longrightarrow> x \<in> A \<and> y \<in> A"
  shows "limited A l"
  using assms
  unfolding limited_def
  by auto

lemma limited_dest:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List" and
    x :: "'a" and
    y :: "'a"
  assumes
    "x \<lesssim>\<^sub>l y" and
    "limited A l"
  shows "x \<in> A \<and> y \<in> A"
  using assms
  unfolding limited_def
  by simp

subsection \<open>Auxiliary Definitions\<close>

definition total_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "total_on_l A pl \<equiv> (\<forall> x \<in> A. (List.member pl x))"

definition refl_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "refl_on_l A r \<equiv> \<forall>x \<in> A. x \<lesssim>\<^sub>r x"

definition trans :: "'a Preference_List \<Rightarrow> bool" where
  "trans l \<equiv> \<forall> (x, y, z) \<in> ((set l) \<times> (set l) \<times> (set l)). x \<lesssim>\<^sub>l y \<and> y \<lesssim>\<^sub>l z \<longrightarrow> x \<lesssim>\<^sub>l z"

definition preorder_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "preorder_on_l A pl \<equiv> limited A pl \<and> refl_on_l A pl \<and> trans pl"

definition linear_order_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "linear_order_on_l A pl \<equiv> preorder_on_l A pl \<and> total_on_l A pl"

definition connex_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "connex_l A r \<equiv> limited A r \<and> (\<forall> x \<in> A. \<forall> y \<in> A. x \<lesssim>\<^sub>r y \<or> y \<lesssim>\<^sub>r x)"

abbreviation ballot_on :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "ballot_on A pl \<equiv> well_formed_l pl \<and> linear_order_on_l A pl"

subsection \<open>Auxiliary Lemmas\<close>

lemma connex_imp_refl:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  assumes "connex_l A l"
  shows "refl_on_l A l"
  unfolding connex_l_def refl_on_l_def
  using assms connex_l_def
  by metis

lemma lin_ord_imp_connex_l:
  fixes
    A :: "'a set" and
    r :: "'a Preference_List"
  assumes "linear_order_on_l A r"
  shows "connex_l A r"
  using assms Preference_List.connex_l_def is_less_preferred_than_l.simps
        linear_order_on_l_def preorder_on_l_def total_on_l_def assms nle_le
  by metis

lemma above_trans:
  fixes
    l :: "'a Preference_List" and
    a :: 'a and
    b :: 'a
  assumes
    trans: "trans l" and
    less: "a \<lesssim>\<^sub>l b"
  shows "set (above_l l b) \<subseteq> set (above_l l a)"
  using assms above_l_def set_take_subset_set_take
  unfolding Preference_List.is_less_preferred_than_l.simps
  by metis

lemma less_preferred_l_rel_eq:
  fixes
    l :: "'a Preference_List" and
    a :: 'a and
    b :: 'a
  shows "a \<lesssim>\<^sub>l b = Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
  unfolding pl_\<alpha>_def
  by simp

theorem above_eq:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List" and
    a :: 'a
  assumes
    wf: "well_formed_l l" and
    lin_ord: "linear_order_on_l A l"
  shows "set (above_l l a) = Order_Relation.above (pl_\<alpha> l) a"
proof (safe)
  fix b :: "'a"
  assume b_member: "b \<in> set (Preference_List.above_l l a)"
  have "length (above_l l a) = rank_l l a"
    unfolding above_l_def
    using Suc_le_eq
    by (simp add: in_set_member)
  with b_member wf lin_ord
  have "index l b \<le> index l a"
    unfolding rank_l.simps
    using above_l_def Preference_List.rank_l.simps Suc_eq_plus1 Suc_le_eq
          bot_nat_0.extremum_strict index_take linorder_not_less
    by metis
  with b_member
  have "a \<lesssim>\<^sub>l b"
    using above_l_def is_less_preferred_than_l.elims(3) rank_l.simps One_nat_def
          Suc_le_mono add.commute add_0 add_Suc empty_iff find_index_le_size
        in_set_member index_def le_antisym list.set(1) size_index_conv take_0
    by metis
  hence "Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
    using less_preferred_l_rel_eq
    by metis
  thus "b \<in> Order_Relation.above (pl_\<alpha> l) a"
    using pref_imp_in_above
    by metis
next
  fix b :: "'a"
  assume "b \<in> Order_Relation.above (pl_\<alpha> l) a"
  hence "Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
    using pref_imp_in_above
    by metis
  hence a_less_pref_than_b: "a \<lesssim>\<^sub>l b"
    using less_preferred_l_rel_eq
    by metis
  hence "rank_l l b \<le> rank_l l a"
    by auto
  with a_less_pref_than_b
  show "b \<in> set (Preference_List.above_l l a)"
    unfolding Preference_List.above_l_def Preference_List.is_less_preferred_than_l.simps
              Preference_List.rank_l.simps
    using Suc_eq_plus1 Suc_le_eq in_set_member index_less_size_conv set_take_if_index
    by (metis (full_types))
qed

theorem rank_eq:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List" and
    a :: 'a
  assumes
    wf: "well_formed_l l" and
    lin_ord: "linear_order_on_l A l"
  shows "rank_l l a = Preference_Relation.rank (pl_\<alpha> l) a"
proof (simp, safe)
  assume a_in_l: "List.member l a"
  have above_presv_rel: "Order_Relation.above (pl_\<alpha> l) a = set (above_l l a)"
    using wf lin_ord
    by (simp add: above_eq)
  have dist_l: "distinct (above_l l a)"
    unfolding above_l_def
    using wf distinct_take
    by blast
  have above_presv_card: "card (set (above_l l a)) = length (above_l l a)"
    using dist_l distinct_card
    by blast
  have "length (above_l l a) = rank_l l a"
    unfolding above_l_def
    by (simp add: Suc_le_eq in_set_member)
  with a_in_l above_presv_rel dist_l above_presv_card
  show "Suc (index l a) = card (Order_Relation.above (pl_\<alpha> l) a)"
    by simp
next
  assume a_not_in_l: "\<not> List.member l a"
  hence "a \<notin> (set l)"
    unfolding pl_\<alpha>_def in_set_member
    by simp
  hence "a \<notin> Order_Relation.above (pl_\<alpha> l) a"
    unfolding Order_Relation.above_def pl_\<alpha>_def
    using a_not_in_l
    by simp
  hence "Order_Relation.above (pl_\<alpha> l) a = {}"
    unfolding Order_Relation.above_def
    using a_not_in_l less_preferred_l_rel_eq
    by fastforce
  thus "card (Order_Relation.above (pl_\<alpha> l) a) = 0"
    by fastforce
qed

theorem lin_ord_l_imp_rel:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  assumes
    wf: "well_formed_l l" and
    lin_ord: "linear_order_on_l A l"
  shows "Order_Relation.linear_order_on A (pl_\<alpha> l)"
proof (unfold Order_Relation.linear_order_on_def partial_order_on_def
       Order_Relation.preorder_on_def, clarsimp, safe)
  have "refl_on_l A l"
    using lin_ord
    unfolding linear_order_on_l_def preorder_on_l_def
    by simp
  thus "refl_on A (pl_\<alpha> l)"
    using lin_ord
    unfolding refl_on_l_def pl_\<alpha>_def refl_on_def linear_order_on_l_def
              preorder_on_l_def Preference_List.limited_def
    by fastforce
next
  show "Relation.trans (pl_\<alpha> l)"
    unfolding Preference_List.trans_def pl_\<alpha>_def Relation.trans_def
    by simp
next
  show "antisym (pl_\<alpha> l)"
  proof (unfold antisym_def pl_\<alpha>_def is_less_preferred_than.simps, clarsimp)
    fix
      a :: "'a" and
      b :: "'a"
    assume
      "List.member l a" and
      "index l a = index l b"
    thus "a = b"
      unfolding member_def
      by simp
  qed
next
  have "linear_order_on_l A l \<longrightarrow> connex_l A l"
    by (simp add: lin_ord_imp_connex_l)
  hence "connex_l A l"
    using lin_ord
    by metis
  thus "total_on A (pl_\<alpha> l)"
    unfolding connex_l_def pl_\<alpha>_def total_on_def
    by simp
qed

lemma lin_ord_rel_imp_l:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  assumes "Order_Relation.linear_order_on A (pl_\<alpha> l)"
  shows "linear_order_on_l A l"
proof (unfold linear_order_on_l_def preorder_on_l_def, clarsimp, safe)
  show "Preference_List.limited A l"
    unfolding pl_\<alpha>_def linear_order_on_def
    using assms limitedI linear_order_on_def less_preferred_l_rel_eq partial_order_onD(1)
          Preference_Relation.is_less_preferred_than.elims(2) refl_on_def' case_prodD
    by metis
next
  show "refl_on_l A l"
    unfolding pl_\<alpha>_def refl_on_l_def
    using assms Preference_Relation.lin_ord_imp_connex less_preferred_l_rel_eq
          Preference_Relation.connex_def
    by metis
next
  show "Preference_List.trans l"
    unfolding pl_\<alpha>_def Preference_List.trans_def
    by fastforce
next
  show "total_on_l A l"
    unfolding pl_\<alpha>_def
    using connex_def lin_ord_imp_connex assms total_on_l_def less_preferred_l_rel_eq
      is_less_preferred_than_l.elims(2)
    by metis
qed

subsection \<open>First Occurrence Indices\<close>

lemma pos_in_list_yields_rank:
  fixes
    l :: "'a Preference_List" and
    a :: "'a" and
    n :: "nat"
  assumes
    no_idx_before: "\<forall> (j::nat) \<le> n. l!j \<noteq> a" and
    fst_idx: "l!(n - 1) = a"
  shows "rank_l l a = n"
  using assms
proof (induction l arbitrary: n, simp_all) qed

lemma ranked_alt_not_at_pos_before:
  fixes
    l :: "'a Preference_List" and
    a :: "'a" and
    n :: nat
  assumes
    a_in_l: "a \<in> set l" and
    n_plus_one_lt_rank_a: "n < (rank_l l a) - 1"
  shows "l!n \<noteq> a"
  using add_diff_cancel_right' a_in_l n_plus_one_lt_rank_a
        index_first member_def rank_l.simps
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
  assume a_in_b_cons_l: "a \<in> set (b#l)"
  hence "rank_l (b # l) a = 1 + index (b#l) a"
    using Suc_eq_plus1 add_Suc add_cancel_left_left member_def rank_l.simps
    by metis
  thus "(b#l)!(rank_l (b#l) a - 1) = a"
    using a_in_b_cons_l diff_add_inverse nth_index
    by metis
qed

(* Alternative expression of list_to_rel using relation_of.
  This is used in the proof that list_to_rel produces linear orders.  *)
lemma rel_of_pref_pred_for_set_eq_list_to_rel:
  fixes l :: "'a Preference_List"
  assumes
    len_l: "0 < length l" and
    dist_l: "distinct l"
  shows "relation_of (\<lambda> y z. y \<lesssim>\<^sub>l z) (set l) = pl_\<alpha> l"
proof (unfold relation_of_def, safe)
  fix
    a :: "'a" and
    b :: "'a"
  assume b_above_a: "a \<lesssim>\<^sub>l b"
  have "(a \<lesssim>\<^sub>l b) = (a \<preceq>\<^sub>(pl_\<alpha> l) b)"
    using less_preferred_l_rel_eq
    by (metis (no_types))
  hence "a \<preceq>\<^sub>(pl_\<alpha> l) b"
    using b_above_a
    by presburger
  thus "(a, b) \<in> pl_\<alpha> l"
    by simp
next
  fix
    a :: "'a" and
    b :: "'a"
  assume ab_in_l: "(a, b) \<in> pl_\<alpha> l"
  thus "a \<in> set l"
    using is_less_preferred_than.simps is_less_preferred_than_l.elims(2)
          less_preferred_l_rel_eq member_def
    by metis
  show "b \<in> set l"
    using ab_in_l is_less_preferred_than.simps is_less_preferred_than_l.elims(2)
          less_preferred_l_rel_eq member_def
    by (metis (no_types))
  have a_less_preferred_b_l_rel_eq: "(a \<lesssim>\<^sub>l b) = (a \<preceq>\<^sub>(pl_\<alpha> l) b)"
    using less_preferred_l_rel_eq
    by (metis (no_types))
  hence "a \<preceq>\<^sub>(pl_\<alpha> l) b"
    by (simp add: ab_in_l)
  thus "a \<lesssim>\<^sub>l b"
    using a_less_preferred_b_l_rel_eq
    by metis
qed

end

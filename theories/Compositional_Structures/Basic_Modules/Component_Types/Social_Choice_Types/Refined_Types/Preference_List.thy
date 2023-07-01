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
  "well_formed_l l \<equiv> distinct l"

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
  by (simp add: ext index_size_conv member_def)

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

fun is_less_preferred_than_l ::
  "'a \<Rightarrow> 'a Preference_List \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lesssim>\<^sub>_ _" [50, 1000, 51] 50) where
    "a \<lesssim>\<^sub>l b = (a \<in> set l \<and> b \<in> set l \<and> index l a \<ge> index l b)"

lemma rank_gt_zero:
  fixes
    l :: "'a Preference_List" and
    a :: 'a
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

subsection \<open>Limited Preference\<close>

definition limited :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "limited A r \<equiv> \<forall> a. a \<in> set r \<longrightarrow>  a \<in> A"

fun limit_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> 'a Preference_List" where
  "limit_l A l = List.filter (\<lambda> a. a \<in> A) l"

lemma limitedI:
  fixes
    l :: "'a Preference_List" and
    A :: "'a set"
  assumes "\<And> a b. a \<lesssim>\<^sub>l b \<Longrightarrow> a \<in> A \<and> b \<in> A"
  shows "limited A l"
  using assms
  unfolding limited_def
  by auto

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

subsection \<open>Auxiliary Definitions\<close>

definition total_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "total_on_l A l \<equiv> \<forall> a \<in> A. a \<in> set l"

definition refl_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "refl_on_l A l \<equiv> (\<forall> a. a \<in> set l \<longrightarrow> a \<in> A) \<and> (\<forall> a \<in> A. a \<lesssim>\<^sub>l a)"

definition trans :: "'a Preference_List \<Rightarrow> bool" where
  "trans l \<equiv> \<forall> (a, b, c) \<in> (set l \<times> set l \<times> set l). a \<lesssim>\<^sub>l b \<and> b \<lesssim>\<^sub>l c \<longrightarrow> a \<lesssim>\<^sub>l c"

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
    a :: 'a and
    b :: 'a
  assumes
    "trans l" and
    "a \<lesssim>\<^sub>l b"
  shows "set (above_l l b) \<subseteq> set (above_l l a)"
  using assms set_take_subset_set_take add_mono le_numeral_extra(4) rank_l.simps
  unfolding above_l_def Preference_List.is_less_preferred_than_l.simps
  by metis

lemma less_preferred_l_rel_equiv:
  fixes
    l :: "'a Preference_List" and
    a :: 'a and
    b :: 'a
  shows "a \<lesssim>\<^sub>l b = Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
  unfolding pl_\<alpha>_def
  by simp

theorem above_equiv:
  fixes
    l :: "'a Preference_List" and
    a :: 'a
  shows "set (above_l l a) = Order_Relation.above (pl_\<alpha> l) a"
proof (safe)
  fix b :: "'a"
  assume b_member: "b \<in> set (Preference_List.above_l l a)"
  hence "index l b \<le> index l a"
    unfolding rank_l.simps
    using above_l_def Preference_List.rank_l.simps Suc_eq_plus1 Suc_le_eq index_take
          bot_nat_0.extremum_strict linorder_not_less
    by metis
  hence "a \<lesssim>\<^sub>l b"
    using above_l_def is_less_preferred_than_l.elims(3) rank_l.simps One_nat_def Suc_le_mono
          add_Suc empty_iff find_index_le_size in_set_member index_def le_antisym list.set(1)
          size_index_conv take_0 b_member
    by metis
  thus "b \<in> Order_Relation.above (pl_\<alpha> l) a"
    using less_preferred_l_rel_equiv pref_imp_in_above
    by metis
next
  fix b :: "'a"
  assume "b \<in> Order_Relation.above (pl_\<alpha> l) a"
  hence "a \<lesssim>\<^sub>l b"
    using pref_imp_in_above less_preferred_l_rel_equiv
    by metis
  thus "b \<in> set (Preference_List.above_l l a)"
    unfolding Preference_List.above_l_def Preference_List.is_less_preferred_than_l.simps
              Preference_List.rank_l.simps
    using Suc_eq_plus1 Suc_le_eq index_less_size_conv set_take_if_index le_imp_less_Suc
    by (metis (full_types))
qed

theorem rank_equiv:
  fixes
    l :: "'a Preference_List" and
    a :: "'a"
  assumes "well_formed_l l"
  shows "rank_l l a = Preference_Relation.rank (pl_\<alpha> l) a"
proof (simp, safe)
  assume "a \<in> set l"
  moreover have "Order_Relation.above (pl_\<alpha> l) a = set (above_l l a)"
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
  ultimately show "Suc (index l a) = card (Order_Relation.above (pl_\<alpha> l) a)"
    by simp
next
  assume "a \<notin> set l"
  hence "Order_Relation.above (pl_\<alpha> l) a = {}"
    unfolding Order_Relation.above_def
    using less_preferred_l_rel_equiv
    by fastforce
  thus "card (Order_Relation.above (pl_\<alpha> l) a) = 0"
    by fastforce
qed

lemma lin_ord_equiv:
  fixes
    A :: "'a set" and
    l :: "'a Preference_List"
  shows "linear_order_on_l A l = linear_order_on A (pl_\<alpha> l)"
  unfolding pl_\<alpha>_def linear_order_on_l_def linear_order_on_def preorder_on_l_def refl_on_l_def
            Relation.trans_def preorder_on_l_def partial_order_on_l_def partial_order_on_def
            total_on_l_def preorder_on_def refl_on_def trans_def antisym_def total_on_def
            Preference_List.limited_def is_less_preferred_than_l.simps
  by (auto simp add: index_size_conv)

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
    n :: nat
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
  ultimately have "a \<preceq>\<^sub>(pl_\<alpha> l) b"
    by presburger
  thus "(a, b) \<in> pl_\<alpha> l"
    by simp
next
  fix
    a :: "'a" and
    b :: "'a"
  assume a_b_in_l: "(a, b) \<in> pl_\<alpha> l"
  thus "a \<in> set l"
    using is_less_preferred_than.simps is_less_preferred_than_l.elims(2) less_preferred_l_rel_equiv
    by metis
  show "b \<in> set l"
    using a_b_in_l is_less_preferred_than.simps is_less_preferred_than_l.elims(2)
          less_preferred_l_rel_equiv
    by (metis (no_types))
  have "(a \<lesssim>\<^sub>l b) = (a \<preceq>\<^sub>(pl_\<alpha> l) b)"
    using less_preferred_l_rel_equiv
    by (metis (no_types))
  moreover have "a \<preceq>\<^sub>(pl_\<alpha> l) b"
    using a_b_in_l
    by simp
  ultimately show "a \<lesssim>\<^sub>l b"
    by metis
qed

end

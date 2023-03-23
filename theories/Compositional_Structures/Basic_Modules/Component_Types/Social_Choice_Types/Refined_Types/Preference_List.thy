(*  File:       Profile_List.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>


chapter \<open>List Data Type for Ranking\<close>

section \<open>Preference Relation\<close>

theory Preference_List
  imports 
    "../Preference_Relation"
    "List-Index.List_Index"
begin

text \<open>
Express Ranking of Alternatives as ordered list of alternative.
Transfer the required functionality from relations.
\<close>

subsection \<open>Definition\<close>

text \<open>                          
  ordered from most to least preferred candidate
\<close>

type_synonym 'a Preference_List = "'a list"

definition well_formed_pl :: "'a Preference_List \<Rightarrow> bool" where
  "well_formed_pl pl \<equiv> distinct pl"

subsection \<open>Ranking\<close>

text \<open>
  rank 1 is top prefernce, rank 0 is not in list
\<close>
fun rank_alt :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank_alt cs x = (let i = (index cs x) in 
            if (i = length cs) then 0 else i + 1)"

fun rank_l :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank_l cs x = (if x \<in> set cs then (index cs x + 1) else 0)"

lemma rankdef: "rank_l = rank_alt"
  by (simp add: ext index_size_conv member_def)
 

lemma rank0_imp_notpresent:
  fixes ballot :: "'a Preference_List"
  shows "rank_l ballot x = 0 \<longrightarrow>  x \<notin> set ballot"
  by (simp add: index_size_conv)


fun is_less_preferred_than_l ::
  "'a \<Rightarrow> 'a Preference_List \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lesssim>\<^sub>_ _" [50, 1000, 51] 50) where
    "x \<lesssim>\<^sub>l y = ((x \<in> set l) \<and> (y \<in> set l) \<and> (index l x \<ge> index l y))"

definition limited :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "limited A l \<equiv> (\<forall> x. (x \<in> set l) \<longrightarrow> x \<in> A)"


lemma rank_gt_zero:
  fixes l :: "'a Preference_List" and x :: 'a
  assumes
    wf : "well_formed_pl l" and
    refl: "x \<lesssim>\<^sub>l x"
  shows "rank_l l x \<ge> 1"
  using refl rank0_imp_notpresent by force 

definition total_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "total_on_l A l \<equiv> (\<forall> x \<in> A. (x \<in> set l))"

definition refl_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where 
  "refl_on_l A l \<equiv> (\<forall> x. (x \<in> set l) \<longrightarrow> x \<in> A) \<and> (\<forall>x \<in> A. x \<lesssim>\<^sub>l x)"

definition trans_l :: "'a Preference_List \<Rightarrow> bool" where 
  "trans_l l \<equiv> \<forall>(x, y, z) \<in> ((set l) \<times> (set l) \<times> (set l)).
       x \<lesssim>\<^sub>l y \<and> y \<lesssim>\<^sub>l z \<longrightarrow> x \<lesssim>\<^sub>l z"

lemma list_trans[simp]:
  shows "trans_l l"
  unfolding trans_l_def is_less_preferred_than_l.simps
  by auto

definition preorder_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "preorder_on_l A l \<equiv> refl_on_l A l \<and> trans_l l"

definition antisym_l :: "'a list \<Rightarrow> bool"
  where "antisym_l l \<longleftrightarrow> (\<forall>x y. x \<lesssim>\<^sub>l y \<longrightarrow> y \<lesssim>\<^sub>l x \<longrightarrow> x = y)"

lemma list_antisym[simp]: "antisym_l l"
  unfolding antisym_l_def is_less_preferred_than_l.simps
  by auto

definition partial_order_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "partial_order_on_l A l \<equiv> preorder_on_l A l \<and> antisym_l l"

definition linear_order_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "linear_order_on_l A pl \<equiv> partial_order_on_l A pl \<and> total_on_l A pl"

definition connex_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "connex_l A r \<equiv> limited A r \<and> (\<forall> x \<in> A. \<forall> y \<in> A. x \<lesssim>\<^sub>r y \<or> y \<lesssim>\<^sub>r x)"

lemma lin_ord_imp_connex_l:
  fixes A :: "'a set" and l :: "'a Preference_List"
  assumes "linear_order_on_l A r"
  shows "connex_l A r"
  using assms
  unfolding connex_l_def  linear_order_on_l_def nle_le 
        partial_order_on_l_def preorder_on_l_def total_on_l_def Preference_List.limited_def
  refl_on_l_def trans_l_def antisym_l_def is_less_preferred_than_l.simps
  by (metis nat_le_linear)
  
  
  

lemma limitedI:
  fixes l :: "'a Preference_List"
  shows "(\<And> x y. \<lbrakk> x \<lesssim>\<^sub>l y \<rbrakk> \<Longrightarrow>  x \<in> A \<and> y \<in> A) \<Longrightarrow> limited A l"
  unfolding limited_def
  by auto

lemma limited_dest: 
  fixes A :: "'a set" and l :: "'a Preference_List" and a :: 'a
  shows "(\<And> x y. \<lbrakk> is_less_preferred_than_l x l y; limited A l \<rbrakk> \<Longrightarrow>  x \<in> A \<and> y \<in> A)"
  unfolding limited_def by (simp)  


fun limit_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> 'a Preference_List" where
  "limit_l A pl = List.filter (\<lambda> x. x \<in> A) pl"

definition above_l :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> 'a Preference_List" where
  "above_l r c \<equiv> take (rank_l r c) r"

lemma above_trans:
  fixes l :: "'a Preference_List" and a :: 'a and b :: 'a
  assumes
    trans: "trans_l l" and
    less: "a \<lesssim>\<^sub>l b"
  shows "set (above_l l b) \<subseteq> set (above_l l a)"
  using assms
  by (simp add: above_l_def set_take_subset_set_take) 

text \<open>                          
  Valid ballots
\<close>

abbreviation ballot_on :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "ballot_on A pl \<equiv> well_formed_pl pl \<and> linear_order_on_l A pl"

text \<open>                          
  A list based ranking can be abstracted to a relation with the corresponding abstraction function.
\<close>

definition pl_\<alpha> :: "'a Preference_List \<Rightarrow> 'a Preference_Relation" where
  "pl_\<alpha> l = {(a, b). a \<lesssim>\<^sub>l b}"

subsection \<open>Correctness of Transferred Functions\<close>


lemma is_less_preferred_than_eq:
  fixes l :: "'a Preference_List" and a :: 'a and b :: 'a
  shows "a \<lesssim>\<^sub>l b \<longleftrightarrow>  Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
  by (simp add: pl_\<alpha>_def)                   


lemma linord_eq:
  fixes bal :: "'a Preference_List"
  shows "linear_order_on_l A bal \<longleftrightarrow> linear_order_on A (pl_\<alpha> bal)"
unfolding pl_\<alpha>_def linear_order_on_l_def linear_order_on_def
  preorder_on_l_def refl_on_l_def trans_l_def preorder_on_l_def 
  partial_order_on_l_def partial_order_on_def total_on_l_def preorder_on_def
  refl_on_def trans_def antisym_def total_on_def
  Preference_List.limited_def is_less_preferred_than_l.simps
  by (auto simp add: index_size_conv)

lemma limit_eq:
  assumes wf: "well_formed_pl bal"
  shows "pl_\<alpha> (limit_l A bal) = limit A (pl_\<alpha> bal)"
using assms proof (induction bal)
  case Nil
  then show ?case unfolding pl_\<alpha>_def by auto
next
  case (Cons a bal)
  then show ?case unfolding well_formed_pl_def
    apply (clarsimp, safe)
    unfolding pl_\<alpha>_def index_def apply auto
    unfolding is_less_preferred_than_l.simps
    subgoal by blast
    by presburger
qed
  

theorem aboveeq: 
  fixes A :: "'a set" and l :: "'a Preference_List" and a :: 'a
  assumes wf: "well_formed_pl l"
  shows "set (above_l l a) = Order_Relation.above (pl_\<alpha> l) a"
proof (safe, cases "a \<in> set l")
  case la: True
  fix x :: 'a
  assume xmem: "x \<in> set (Preference_List.above_l l a)"
  have leq: "length (above_l l a) = rank_l l a" unfolding above_l_def rank_l.simps
    by (simp add: Suc_leI index_size_conv)    
  from la have ri: "rank_l l a = index l a + 1"
    using member_def size_index_conv by fastforce
  from xmem have xabovel: "List.member (take (rank_l l a) l) x"
    by (simp add: above_l_def in_set_member)
  from this have lx: "List.member l x"
    by (metis in_set_member in_set_takeD)
  from xmem lx xabovel have "index l x < rank_l l a"
    by (metis index_take linorder_not_less member_def)
  from this ri have "index l x + 1 \<le> index l a + 1"
    by simp
  from la lx this have lpl: "a \<lesssim>\<^sub>l x" unfolding Preference_List.is_less_preferred_than_l.simps
    by (simp add: in_set_member)    
  then have "Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) x"
    using is_less_preferred_than_eq by (metis)
  then show "x \<in> Order_Relation.above (pl_\<alpha> l) a"
    using pref_imp_in_above by (metis)
next
  case lna: False
  fix x:: 'a
  assume xa: "x \<in> set (above_l l a)"
  from lna have "above_l l a = []" unfolding above_l_def rank_l.simps
    by simp
  from this xa have "False"
    by simp
  from this show " x \<in> above (pl_\<alpha> l) a" by simp   
next
  fix x :: 'a
  assume xmema: "x \<in> Order_Relation.above (pl_\<alpha> l) a"
  from xmema have "Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) x"
    using pref_imp_in_above by (metis)
  from this have alpx: "a \<lesssim>\<^sub>l x"
    using is_less_preferred_than_eq by (metis)
  from this have "index l x \<le> index l a"
    by (metis Preference_List.is_less_preferred_than_l.elims(2))
  from alpx this show "x \<in> set (above_l l a)" unfolding above_l_def rank_l.simps
    by (metis Suc_eq_plus1 Suc_leI index_less_size_conv is_less_preferred_than_l.elims(2) 
          less_Suc_eq_le set_take_if_index)

qed

lemma rankeq_aux: 
  fixes A :: "'a set" and l :: "'a Preference_List" and a :: 'a
  assumes wf: "well_formed_pl l"
  shows "rank_l l a = Preference_Relation.rank (pl_\<alpha> l) a"
proof (simp, safe)
  assume air: "a \<in> set l"
  from assms have abe: "Order_Relation.above (pl_\<alpha> l) a = set (above_l l a)" 
    by (simp add: aboveeq)
  from wf have dl: "distinct (above_l l a)" unfolding well_formed_pl_def above_l_def
    using distinct_take by blast
  from dl have ce: "card (set (above_l l a)) = length (above_l l a)" unfolding well_formed_pl_def
    using distinct_card
    by blast
  from air abe dl ce this show "Suc (index l a) = card (above (pl_\<alpha> l) a)"
    by (metis above_l_def add.commute index_less_size_conv length_take less_trans_Suc
        linorder_not_less min.absorb2 nat_less_le plus_1_eq_Suc rank_l.elims)
next
  assume anr: "a \<notin> set l"
  from anr have "a \<notin> (set l)" unfolding pl_\<alpha>_def
    by (simp add: in_set_member) 
  from this have "a \<notin> Order_Relation.above (pl_\<alpha> l) a" 
      unfolding Order_Relation.above_def pl_\<alpha>_def
      by (simp add: anr)
  from this have "Order_Relation.above (pl_\<alpha> l) a = {}" 
      unfolding Order_Relation.above_def
      using anr is_less_preferred_than_eq by fastforce
  thus "card (Order_Relation.above (pl_\<alpha> l) a) = 0" by fastforce
qed

theorem rankeq: fixes A :: "'a set" and l :: "'a Preference_List" and a :: 'a
  assumes wf: "well_formed_pl l"
  shows "rank_l l a = Preference_Relation.rank (pl_\<alpha> l) a"
  using rankeq_aux assms by metis


theorem linorder_l_imp_rel:
  fixes l :: "'a Preference_List"
  assumes  lo: "linear_order_on_l A l"
  shows "Order_Relation.linear_order_on A (pl_\<alpha> l)"
  using lo linord_eq
  by auto


lemma linorder_rel_imp_l: 
  fixes A :: "'a set" and l :: "'a Preference_List"
  assumes lol: "Order_Relation.linear_order_on A (pl_\<alpha> l)"
  shows "linear_order_on_l A l"
  using lol linord_eq
  by auto

lemma rel_trans:
  fixes pl :: "'a Preference_List"
  shows "Relation.trans (pl_\<alpha> pl)"
  unfolding Relation.trans_def pl_\<alpha>_def
  by simp

lemma rel_antisym:
  fixes pl :: "'a Preference_List"
  shows "Relation.antisym (pl_\<alpha> pl)"
  unfolding antisym_def pl_\<alpha>_def
  by auto

lemma losimp:
  shows "linear_order_on_l A bal \<longleftrightarrow> (A = set bal)"
  unfolding linear_order_on_l_def total_on_l_def partial_order_on_l_def preorder_on_l_def
  refl_on_l_def
  by auto

lemma limit_presv_lin_ord_l:
  assumes
    "linear_order_on_l S l" and
      "A \<subseteq> S"
    shows "linear_order_on_l A (limit_l A l)"
  using assms 
  unfolding losimp limit_l.simps
  by auto

lemma connex_imp_refl:
  fixes A :: "'a set" and pl :: "'a Preference_List"
  assumes "connex_l A pl"
  shows "refl_on_l A pl"
  using assms 
  unfolding connex_l_def refl_on_l_def limited_def
  by fastforce


end
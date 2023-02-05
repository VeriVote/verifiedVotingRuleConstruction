theory Preference_List
  imports 
    "../Preference_Relation"
    "List-Index.List_Index"
begin

text \<open>                          
  ordered from most to least preferred candidate
\<close>

type_synonym 'a Preference_List = "'a list"

definition well_formed_pl :: "'a Preference_List \<Rightarrow> bool" where
  "well_formed_pl pl \<equiv> distinct pl"

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
  "limited A r \<equiv> (\<forall> x. (x \<in> set r) \<longrightarrow>  x \<in> A)"


lemma rank_gt_zero:
  fixes l :: "'a Preference_List" and x :: 'a
  assumes
    wf : "well_formed_pl l" and
    refl: "x \<lesssim>\<^sub>l x"
  shows "rank_l l x \<ge> 1"
  using refl rank0_imp_notpresent by force 

definition total_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "total_on_l A pl \<equiv> (\<forall> x \<in> A. (x \<in> set pl))"

definition refl_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where 
  "refl_on_l A r \<equiv> \<forall>x \<in> A. x \<lesssim>\<^sub>r x"

definition trans_l :: "'a Preference_List \<Rightarrow> bool" where 
  "trans_l l \<equiv> \<forall>(x, y, z) \<in> ((set l) \<times> (set l) \<times> (set l)).
       x \<lesssim>\<^sub>l y \<and> y \<lesssim>\<^sub>l z \<longrightarrow> x \<lesssim>\<^sub>l z"

definition preorder_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "preorder_on_l A pl \<equiv> limited A pl \<and> refl_on_l A pl \<and> trans_l pl"

definition linear_order_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "linear_order_on_l A pl \<equiv> preorder_on_l A pl \<and> total_on_l A pl"

definition connex_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "connex_l A r \<equiv> limited A r \<and> (\<forall> x \<in> A. \<forall> y \<in> A. x \<lesssim>\<^sub>r y \<or> y \<lesssim>\<^sub>r x)"

lemma lin_ord_imp_connex_l:
  fixes A :: "'a set" and l :: "'a Preference_List"
  assumes "linear_order_on_l A r"
  shows "connex_l A r"
  by (metis assms connex_l_def is_less_preferred_than_l.elims(3) linear_order_on_l_def nle_le preorder_on_l_def total_on_l_def)
  

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
  "limit_l A pl =  List.filter (\<lambda> a. a \<in> A) pl"


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

abbreviation ballot_on :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "ballot_on A pl \<equiv> well_formed_pl pl \<and> linear_order_on_l A pl"

definition pl_\<alpha> :: "'a Preference_List \<Rightarrow> 'a Preference_Relation" where
  "pl_\<alpha> l = {(a, b). a \<lesssim>\<^sub>l b}"


lemma less_preffered_l_rel_eq:
  fixes l :: "'a Preference_List" and a :: 'a and b :: 'a
  shows "a \<lesssim>\<^sub>l b \<longleftrightarrow>  Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
  by (simp add: pl_\<alpha>_def)


lemma linord_eq:
  fixes bal :: "'a Preference_List"
  assumes "well_formed_pl bal"
  shows "linear_order_on_l A bal = linear_order_on A (pl_\<alpha> bal)"
proof (-)
  have dis: "distinct bal" using assms unfolding well_formed_pl_def .
  show ?thesis
  unfolding pl_\<alpha>_def linear_order_on_l_def linear_order_on_def
  preorder_on_l_def refl_on_l_def trans_l_def partial_order_on_def total_on_l_def preorder_on_def
  refl_on_def trans_def antisym_def total_on_def
  Preference_List.limited_def is_less_preferred_than_l.simps
  by (auto simp add: dis index_size_conv)
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
  from this have "Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) x"
    using less_preffered_l_rel_eq by (metis)
  from this show "x \<in> Order_Relation.above (pl_\<alpha> l) a"
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
    using less_preffered_l_rel_eq by (metis)
  from this have "index l x \<le> index l a"
    by (metis Preference_List.is_less_preferred_than_l.elims(2))
  from alpx this show "x \<in> set (above_l l a)" unfolding above_l_def rank_l.simps
    by (metis Suc_eq_plus1 Suc_leI index_less_size_conv is_less_preferred_than_l.elims(2) less_Suc_eq_le set_take_if_index)

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
    by (metis above_l_def add.commute index_less_size_conv length_take less_trans_Suc linorder_not_less min.absorb2 nat_less_le plus_1_eq_Suc rank_l.elims)
    
next
  assume anr: "a \<notin> set l"
  from anr have "a \<notin> (set l)" unfolding pl_\<alpha>_def
    by (simp add: in_set_member) 
  from this have "a \<notin> Order_Relation.above (pl_\<alpha> l) a" 
      unfolding Order_Relation.above_def pl_\<alpha>_def
      by (simp add: anr)
  from this have "Order_Relation.above (pl_\<alpha> l) a = {}" 
      unfolding Order_Relation.above_def
      using anr less_preffered_l_rel_eq by fastforce
  from this show "card (Order_Relation.above (pl_\<alpha> l) a) = 0" by fastforce
qed

theorem rankeq: fixes A :: "'a set" and l :: "'a Preference_List" and a :: 'a
  assumes wf: "well_formed_pl l"
  shows "rank_l l a = Preference_Relation.rank (pl_\<alpha> l) a"
  using rankeq_aux rankdef assms by metis

theorem linorder_l_imp_rel:
  fixes l :: "'a Preference_List"
  assumes wf: "well_formed_pl l" and lo: "linear_order_on_l A l"
  shows "Order_Relation.linear_order_on A (pl_\<alpha> l)"
proof (unfold Order_Relation.linear_order_on_def partial_order_on_def 
    Order_Relation.preorder_on_def, clarsimp, safe)
  from lo have "refl_on_l A l" 
    by (unfold linear_order_on_l_def preorder_on_l_def, simp)
  from this show "refl_on A (pl_\<alpha> l)" 
  proof (unfold refl_on_l_def pl_\<alpha>_def refl_on_def, clarsimp)
    fix a :: 'a  and b :: 'a
    assume ni: "\<forall>x\<in>A. x \<in> set l"
    assume aA: "a \<in> set l" and bA: " b \<in> set l "
    from ni aA bA show "a \<in> A \<and> b \<in> A"
      using lo linear_order_on_l_def preorder_on_l_def Preference_List.limited_def by (metis)
  qed
next
  show "Relation.trans (pl_\<alpha> l)"
    by (unfold Preference_List.trans_l_def pl_\<alpha>_def Relation.trans_def, simp)
next
  show "antisym (pl_\<alpha> l)"
  proof (unfold antisym_def pl_\<alpha>_def is_less_preferred_than_l.simps, clarify)
    fix x :: 'a  and y :: 'a 
    assume xm: "x \<in> set l" and ym: " y \<in> set l"
    assume rxy: "index l y \<le> index l x "
    assume ryx: "index l x \<le> index l y"
    from rxy ryx have "index l x = index l y"
      by fastforce
    from xm ym this show "x = y"
      by simp 
  qed
next
  show "total_on A (pl_\<alpha> l)"
    using lin_ord_imp_connex_l lo connex_l_def pl_\<alpha>_def total_on_def by fastforce
qed


lemma linorder_rel_imp_l: 
  fixes A :: "'a set" and l :: "'a Preference_List"
  assumes "Order_Relation.linear_order_on A (pl_\<alpha> l)"
  shows "linear_order_on_l A l"
  unfolding linear_order_on_l_def preorder_on_l_def
proof (clarsimp, safe)
  show "Preference_List.limited A l" unfolding pl_\<alpha>_def linear_order_on_def 
    using assms limitedI linear_order_on_def less_preffered_l_rel_eq partial_order_onD(1) 
    by (metis Preference_Relation.is_less_preferred_than.elims(2) refl_on_def' case_prodD)
next
  show "refl_on_l A l" unfolding pl_\<alpha>_def 
    using assms refl_on_l_def Preference_Relation.lin_ord_imp_connex less_preffered_l_rel_eq
    by (metis Preference_Relation.connex_def)
next
  show "Preference_List.trans_l l" 
    unfolding pl_\<alpha>_def Preference_List.trans_l_def by fastforce
next
  show "total_on_l A l" unfolding pl_\<alpha>_def 
    using connex_def lin_ord_imp_connex assms total_on_l_def less_preffered_l_rel_eq 
      is_less_preferred_than_l.elims(2)
    by metis
qed

lemma rel_trans:
  fixes pl :: "'a Preference_List"
  shows "Relation.trans (pl_\<alpha> pl)"
  unfolding Relation.trans_def pl_\<alpha>_def
  by auto

lemma connex_imp_refl:
  fixes A :: "'a set" and pl :: "'a Preference_List"
  assumes "connex_l A pl"
  shows "refl_on_l A pl"
  unfolding connex_l_def refl_on_l_def
proof clarsimp
  fix x :: 'a
  assume "x \<in> A"
  from this show "x \<in> set pl" 
    using assms connex_l_def is_less_preferred_than_l.elims(1)
    by metis
qed

end
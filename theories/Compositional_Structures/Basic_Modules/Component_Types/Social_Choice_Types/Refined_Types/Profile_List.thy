theory Profile_List
  imports "../Profile" 
    Preference_List
begin

type_synonym 'a Profile_List = "('a Preference_List) list"

text \<open> Abstraction from Profile List to Profile \<close>
fun pl_to_pr_\<alpha> :: "'a Profile_List \<Rightarrow> 'a Profile" where
  "pl_to_pr_\<alpha> pl = map (Preference_List.pl_\<alpha>) pl"

lemma length_preserving:
  fixes pr:: "'a Profile_List"
  shows "length pl = length (pl_to_pr_\<alpha> pl)"
  by simp

definition profile_l :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> bool" where
  "profile_l A pl \<equiv> (\<forall> i < length pl. ballot_on A (pl!i))"

lemma profile_prop_refine:
  (* Refinement Framework syntax*)
  (*assumes "(pl,pr)\<in>br pl_to_pr_\<alpha> (profile_l A)"*)
  fixes A :: "'a set" and pl :: "'a Profile_List"
  assumes "profile_l A pl"
  shows "profile A (pl_to_pr_\<alpha> pl)"
  unfolding profile_def
  apply(intro allI impI)
proof (-)
  fix i
  assume ir: "i < length (pl_to_pr_\<alpha> pl)"
  from ir assms have wf: "well_formed_pl (pl ! i)" unfolding profile_l_def
    by (simp)
  from ir assms have "linear_order_on_l A (pl ! i)" unfolding profile_l_def
    by (simp) 
  from wf assms this show "linear_order_on A ((pl_to_pr_\<alpha> pl) ! i)"
    using linorder_l_imp_rel
    by (metis (mono_tags, lifting) ir length_map nth_map pl_to_pr_\<alpha>.simps)
qed


end
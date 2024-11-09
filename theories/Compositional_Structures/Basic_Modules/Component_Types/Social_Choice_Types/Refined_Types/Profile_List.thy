(*  File:       Profile_List.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Preference (List) Profile\<close>

theory Profile_List
  imports "../Profile"
          Preference_List
begin

subsection \<open>Definition\<close>

text \<open>
  A profile (list) contains one ballot for each voter.
\<close>

type_synonym 'a Profile_List = "'a Preference_List list"

type_synonym 'a Election_List = "'a set \<times> 'a Profile_List"

text \<open>
  Abstraction from profile list to profile.
\<close>

fun pl_to_pr_\<alpha> :: "'a Profile_List \<Rightarrow> ('a, nat) Profile" where
  "pl_to_pr_\<alpha> pl = (\<lambda> n. if (n < length pl \<and> n \<ge> 0)
                         then (map (Preference_List.pl_\<alpha>) pl)!n
                         else {})"

lemma prof_abstr_presv_size:
  fixes p :: "'a Profile_List"
  shows "length p = length (to_list {0 ..< length p} (pl_to_pr_\<alpha> p))"
  by simp

subsection \<open>Refinement Proof\<close>

text \<open>
  A profile on a finite set of alternatives A contains only ballots that are
  lists of linear orders on A.
\<close>

definition profile_l :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> bool" where
  "profile_l A p \<equiv> \<forall> i < length p. ballot_on A (p!i)"

lemma refinement:
  fixes
    A :: "'a set" and
    p :: "'a Profile_List"
  assumes "profile_l A p"
  shows "profile {0 ..< length p} A (pl_to_pr_\<alpha> p)"
proof (unfold profile_def, safe)
  fix i :: "nat"
  assume in_range: "i \<in> {0 ..< length p}"
  moreover have "well_formed_l (p!i)"
    using assms in_range
    unfolding profile_l_def
    by simp
  moreover have "linear_order_on_l A (p!i)"
    using assms in_range
    unfolding profile_l_def
    by simp
  ultimately show "linear_order_on A (pl_to_pr_\<alpha> p i)"
    using lin_ord_equiv length_map nth_map
    by auto
qed

end

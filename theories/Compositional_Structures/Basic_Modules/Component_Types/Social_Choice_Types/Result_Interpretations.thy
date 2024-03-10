(*  File:       Result_Interpretations.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Specific Electoral Result Types\<close>

theory Result_Interpretations
  imports Social_Choice_Result
          Social_Welfare_Result
          Collections.Locale_Code
begin

text \<open>
  Interpretations of the result locale are placed inside a Locale-Code block 
  in order to enable code generation of later definitions in the locale.
  Those definitions need to be added via a Locale-Code block as well.
\<close>

setup Locale_Code.open_block

global_interpretation social_choice_result:
  result "well_formed_social_choice" "limit_set_social_choice"
proof (unfold_locales, auto) qed

global_interpretation committee_result:
  result "\<lambda> A r. set_equals_partition (Pow A) r \<and> disjoint3 r" "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}"
proof (unfold_locales, safe, auto) qed

global_interpretation social_welfare_result:
  result "well_formed_welfare" "limit_set_welfare"
proof (unfold_locales, safe)
  fix 
    A :: "'a set" and
    e :: "('a Preference_Relation) set" and
    r :: "('a Preference_Relation) set" and
    d :: "('a Preference_Relation) set"
  assume
    partition: "set_equals_partition (limit_set_welfare A UNIV) (e, r, d)" and
    disj: "disjoint3 (e, r, d)"
  have "limit_set_welfare A UNIV =
          {limit A r' | r'. r' \<in> UNIV \<and> linear_order_on A (limit A r')}"
    by simp
  also have "... = {limit A r' | r'. r' \<in> UNIV} \<inter>
                    {limit A r' | r'. linear_order_on A (limit A r')}"
    by blast
  also have "... = {limit A r' | r'. linear_order_on A (limit A r')}"
    by blast
  also have "... = {r'. linear_order_on A r'}"
  proof (safe)
    fix
      r' :: "'a Preference_Relation"
    assume
      lin_ord: "linear_order_on A r'"
    hence "\<forall> a b. (a, b) \<in> r' \<longrightarrow> (a, b) \<in> limit A r'"
      unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by fastforce
    hence "r' \<subseteq> limit A r'"
      by fastforce
    moreover have "limit A r' \<subseteq> r'"
      by fastforce
    ultimately have "r' = limit A r'"
      by simp
    thus "\<exists> x. r' = limit A x \<and> linear_order_on A (limit A x)"
      using lin_ord
      by metis
  qed
  thus "well_formed_welfare A (e, r, d)"
    using partition disj
    by simp
qed

setup Locale_Code.close_block

end
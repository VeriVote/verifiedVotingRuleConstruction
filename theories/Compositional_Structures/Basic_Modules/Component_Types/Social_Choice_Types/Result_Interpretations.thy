section \<open>Specific Electoral Result Types\<close>

theory Result_Interpretations
  imports Result
          Social_Choice_Result
          Social_Welfare_Result
          Collections.Locale_Code
begin

text \<open>
  Interpretations of the result locale are placed inside a Locale_Code block 
  in order to enable code generation of later definitions in the locale.
  Those definitions need to be added via a Locale_Code block as well.
\<close>

setup Locale_Code.open_block

global_interpretation social_choice_result:
  result "well_formed_soc_choice" "limit_set_soc_choice" 
proof (unfold_locales, simp, auto) qed

global_interpretation social_welfare_result:
  result "well_formed_welfare" "limit_set_welfare"
proof (unfold_locales, safe)
  fix 
    A :: "'a set" and
    r1 :: "('a Preference_Relation) set" and
    r2 :: "('a Preference_Relation) set" and
    r3 :: "('a Preference_Relation) set"
  assume
    partition: "set_equals_partition (limit_set_welfare A UNIV) (r1, r2, r3)" and
    disj: "disjoint3 (r1, r2, r3)"
  have "limit_set_welfare A UNIV = 
          {limit A r | r. r \<in> UNIV \<and> linear_order_on A (limit A r)}"
    by simp
  also have "... = {limit A r | r. r \<in> UNIV} \<inter> 
                    {limit A r | r. linear_order_on A (limit A r)}"
    by auto
  also have "... = {limit A r | r. linear_order_on A (limit A r)}"
    by auto
  also have "... = {r. linear_order_on A r}"
  proof (safe)
    fix 
      r :: "'a Preference_Relation"
    assume 
      lin_ord: "linear_order_on A r"
    hence "\<forall> a b. (a, b) \<in> r \<longrightarrow> (a, b) \<in> limit A r"
      unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by auto
    hence "r \<subseteq> limit A r" by auto
    moreover have "limit A r \<subseteq> r" by auto
    ultimately have "r = limit A r" by simp
    thus "\<exists>x. r = limit A x \<and> linear_order_on A (limit A x)"
      using lin_ord
      by metis
  qed
  thus "well_formed_welfare A (r1, r2, r3)"
    using partition disj
    by simp
next
  fix 
    A :: "'a set" and
    B :: "'a set" and
    r1 :: "('a Preference_Relation) set" and
    r2 :: "('a Preference_Relation) set" and
    r3 :: "('a Preference_Relation) set"
  assume 
    subset: "A \<subseteq> B" and
    wf_B: "well_formed_welfare B (r1, r2, r3)"
  hence "\<forall> r \<in> r1 \<union> r2 \<union> r3. linear_order_on B r" 
    by simp
  moreover have "\<forall> r. (linear_order_on B r) \<longrightarrow> linear_order_on A (limit A r)"
    using subset limit_presv_lin_ord
    by blast
  ultimately have "\<forall> r \<in> r1 \<union> r2 \<union> r3. linear_order_on A (limit A r)"
    by blast
(* TODO this doesn't hold with the current limit_set definition... *)
  thus "well_formed_welfare A
        (limit_set_welfare A r1, limit_set_welfare A r2, limit_set_welfare A r3)"  sorry
qed

setup Locale_Code.close_block

end

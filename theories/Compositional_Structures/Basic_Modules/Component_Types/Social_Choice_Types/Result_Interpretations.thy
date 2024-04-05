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

text \<open>
  Results from social choice functions (\<open>\<S>\<C>\<F>s\<close>), for the purpose of composability and
  modularity given as three sets of (potentially tied) alternatives. See
  \<^file>\<open>Social_Choice_Result.thy\<close> for details.
\<close>
global_interpretation \<S>\<C>\<F>_result:
  result "well_formed_\<S>\<C>\<F>" "limit_set_\<S>\<C>\<F>"
proof (unfold_locales, safe)
  fix
    A :: "'a set" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assume
    "set_equals_partition (limit_set_\<S>\<C>\<F> A UNIV) (e, r, d)" and
    "disjoint3 (e, r, d)"
  thus "well_formed_\<S>\<C>\<F> A (e, r, d)"
    by simp
qed

text \<open>
  Results from committee functions, for the purpose of composability and
  modularity given as three sets of (potentially tied) sets of alternatives or committees.
\<close>
global_interpretation committee_result:
  result "\<lambda> A r. set_equals_partition (Pow A) r \<and> disjoint3 r" "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}"
proof (unfold_locales, safe)
  fix
    A :: "'b set" and
    e :: "'b set set" and
    r :: "'b set set" and
    d :: "'b set set"
  assume "set_equals_partition {r \<inter> A |r. r \<in> UNIV} (e, r, d)"
  thus "set_equals_partition (Pow A) (e, r, d)"
    by force
qed

text \<open>
  Results from social welfare functions (\<open>\<S>\<W>\<F>s\<close>), for the purpose of composability and
  modularity given as three sets of (potentially tied) linear orders over the alternatives. See
  \<^file>\<open>Social_Welfare_Result.thy\<close> for details.
\<close>
global_interpretation \<S>\<W>\<F>_result:
  result "well_formed_\<S>\<W>\<F>" "limit_set_\<S>\<W>\<F>"
proof (unfold_locales, safe)
  fix 
    A :: "'a set" and
    e :: "('a Preference_Relation) set" and
    r :: "('a Preference_Relation) set" and
    d :: "('a Preference_Relation) set"
  assume
    partition: "set_equals_partition (limit_set_\<S>\<W>\<F> A UNIV) (e, r, d)" and
    disj: "disjoint3 (e, r, d)"
  have "limit_set_\<S>\<W>\<F> A UNIV =
          {limit A r' | r'. r' \<in> UNIV \<and> linear_order_on A (limit A r')}"
    by simp
  also have "... = {limit A r' | r'. r' \<in> UNIV} \<inter>
                    {limit A r' | r'. linear_order_on A (limit A r')}"
    by blast
  also have "... = {limit A r' | r'. linear_order_on A (limit A r')}"
    by blast
  also have "... = {r'. linear_order_on A r'}"
  proof (safe)
    fix r' :: "'a Preference_Relation"
    assume lin_ord: "linear_order_on A r'"
    hence "\<forall> a b. (a, b) \<in> r' \<longrightarrow> (a, b) \<in> limit A r'"
      unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by force
    hence "r' \<subseteq> limit A r'"
      by slow
    moreover have "limit A r' \<subseteq> r'"
      by auto
    ultimately have "r' = limit A r'"
      by safe
    thus "\<exists> x. r' = limit A x \<and> linear_order_on A (limit A x)"
      using lin_ord
      by metis
  qed
  thus "well_formed_\<S>\<W>\<F> A (e, r, d)"
    using partition disj
    by simp
qed

setup Locale_Code.close_block

end
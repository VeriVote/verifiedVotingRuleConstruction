section \<open>Ordered Relation Type\<close>

theory Ordered_Relation
  imports Preference_Relation
          "./Refined_Types/Preference_List"
          "HOL-Combinatorics.Multiset_Permutations"
begin

lemma fin_ordered:
  fixes
    X :: "'x set" 
  assumes
    "finite X"
  obtains ord :: "'x rel" where "linear_order_on X ord"
proof -
  assume
    ex: "\<And>ord. linear_order_on X ord \<Longrightarrow> thesis"
  obtain l :: "'x list" where "set l = X"
    using finite_list assms
    by blast
  let ?r = "pl_\<alpha> l"
  have "antisym ?r"
    using \<open>set l = X\<close> Collect_mono_iff antisym index_eq_index_conv pl_\<alpha>_def
    unfolding antisym_def
    by fastforce
  moreover have "refl_on X ?r"
    using \<open>set l = X\<close>
    unfolding refl_on_def pl_\<alpha>_def is_less_preferred_than_l.simps
    by blast
  moreover have "Relation.trans ?r"
    unfolding Relation.trans_def pl_\<alpha>_def is_less_preferred_than_l.simps
    by auto
  moreover have "total_on X ?r"
    using \<open>set l = X\<close>
    unfolding total_on_def pl_\<alpha>_def is_less_preferred_than_l.simps
    by force
  ultimately have "linear_order_on X ?r"
    unfolding linear_order_on_def preorder_on_def partial_order_on_def
    by blast
  thus thesis
    using ex
    by blast
qed

typedef 'a Ordered_Preference = 
  "{p :: 'a::finite Preference_Relation. linear_order_on (UNIV::'a set) p}"
  morphisms ord2pref pref2ord
proof (simp)
  have "finite (UNIV::'a set)"
    by simp
  then obtain p :: "'a Preference_Relation" where
    "linear_order_on (UNIV::'a set) p"
    using fin_ordered[of UNIV False]
    by blast
  thus "\<exists>p::'a Preference_Relation. linear_order p"
    by blast
qed

instance Ordered_Preference :: (finite) finite
proof
  have 
    "(UNIV::'a Ordered_Preference set) = 
      pref2ord ` {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    using type_definition.Abs_image type_definition_Ordered_Preference 
    by blast
  moreover have "finite {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    by simp
  ultimately show "finite (UNIV::'a Ordered_Preference set)"
    by (metis finite_imageI)
qed

lemma range_ord2pref:
  "range ord2pref = {p. linear_order p}"
proof -
  have 
    "range ord2pref = {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    by (metis type_definition.Rep_range type_definition_Ordered_Preference)
  also have "... = {p. linear_order p}"
    by simp
  finally show ?thesis
    by (meson type_definition.Rep_range type_definition_Ordered_Preference)
qed

lemma card_ord_pref:
  "card (UNIV::'a::finite Ordered_Preference set) = fact (card (UNIV::'a set))"
proof -
  let ?n = "card (UNIV::'a set)" and
      ?perm = "permutations_of_set (UNIV :: 'a set)"
  have "(UNIV::('a Ordered_Preference set)) = 
    pref2ord ` {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    using type_definition_Ordered_Preference type_definition.Abs_image 
    by blast
  moreover have 
    "inj_on pref2ord {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    by (meson inj_onCI pref2ord_inject)
  ultimately have
    "bij_betw pref2ord 
      {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}
      (UNIV::('a Ordered_Preference set))"
    by (simp add: bij_betw_imageI)
  with finite have "card (UNIV::('a Ordered_Preference set)) = 
    card {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    by (simp add: bij_betw_same_card)
  moreover have "card ?perm = fact ?n"
    by simp
  ultimately show ?thesis
    using bij_betw_same_card pl_\<alpha>_bij_betw[of "UNIV::'a set"] 
    by (metis finite)
qed

end
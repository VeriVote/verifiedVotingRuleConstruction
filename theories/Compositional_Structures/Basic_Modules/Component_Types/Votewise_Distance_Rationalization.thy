(*  File:       Votewise_Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Votewise Distance Rationalization\<close>

theory Votewise_Distance_Rationalization
  imports "Distance_Rationalization"
          "Votewise_Distance"
          Interpretation_Code
begin

text \<open>
  TODO
\<close>

subsection \<open>Common Rationalizations\<close>

fun swap_\<R> :: 
"('a, 'v::linorder, 'a Result) Consensus_Class \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "swap_\<R> K = social_choice_result.distance_\<R> (votewise_distance swap l_one) K"

subsection \<open>Theorems\<close>

lemma votewise_non_voters_irrelevant: 
  fixes 
    d :: "'a Vote Distance" and
    N :: Norm
  shows "non_voters_irrelevant (votewise_distance d N)"
proof (unfold non_voters_irrelevant_def, clarify)
  fix
    A :: "'a set" and
    V :: "'v::linorder set" and
    p :: "('a, 'v) Profile" and
    A' :: "'a set" and
    V' :: "'v set" and
    p' :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile"
  assume 
    coincide: "\<forall>v\<in>V. p v = q v"
  have "\<forall> i < length (sorted_list_of_set V). (sorted_list_of_set V)!i \<in> V"
    using card_eq_0_iff not_less_zero nth_mem 
          sorted_list_of_set.length_sorted_key_list_of_set 
          sorted_list_of_set.set_sorted_key_list_of_set
    by metis
  hence "(to_list V p) = (to_list V q)"
    using index coincide length_inv nth_equalityI to_list.simps
    by (metis (no_types, lifting))
  thus "votewise_distance d N (A, V, p) (A', V', p') = 
            votewise_distance d N (A, V, q) (A', V', p') \<and>
         votewise_distance d N (A', V', p') (A, V, p) = 
            votewise_distance d N (A', V', p') (A, V, q)"
    by auto
qed

lemma swap_standard: "standard (votewise_distance swap l_one)"
proof (unfold standard_def, clarify)
  fix
    A :: "'a set" and
    V :: "'v::linorder set" and
    p :: "('a, 'v) Profile" and
    A' :: "'a set" and
    V' :: "'v set" and
    p' :: "('a, 'v) Profile"
  assume assms: "V \<noteq> V' \<or> A \<noteq> A'"
  let ?l = "(\<lambda> l1 l2. (map2 (\<lambda> q q'. swap (A, q) (A', q')) l1 l2))"
  have "A \<noteq> A' \<and> V = V' \<and> V \<noteq> {} \<and> finite V \<Longrightarrow> \<forall> q q'. swap (A, q) (A', q') = \<infinity>"
    by simp
  hence "A \<noteq> A' \<and> V = V' \<and> V \<noteq> {} \<and> finite V \<Longrightarrow> 
    \<forall> l1 l2. (l1 \<noteq> [] \<and> l2 \<noteq> [] \<longrightarrow> (\<forall>i < length (?l l1 l2). (?l l1 l2)!i = \<infinity>))"
    by simp
  moreover have "V = V' \<and> V \<noteq> {} \<and> finite V \<Longrightarrow> (to_list V p) \<noteq> [] \<and> (to_list V' p') \<noteq> []"
    using card_eq_0_iff length_inv list.size(3) to_list.simps
          sorted_list_of_set.length_sorted_key_list_of_set 
    by metis
  moreover have "\<forall> l. ((\<exists> i < length l. l!i = \<infinity>) \<longrightarrow> l_one l = \<infinity>)"
  proof (safe)
    fix 
      l :: "ereal list" and
      i :: nat
    assume "i < length l" and "l ! i = \<infinity>"
    hence "(\<Sum> j < length l. \<bar>l!j\<bar>) = \<infinity>"
      using sum_Pinfty abs_ereal.simps(3) finite_lessThan lessThan_iff
      by metis
    thus "l_one l = \<infinity>" by auto
  qed
  ultimately have 
    "A \<noteq> A' \<and> V = V' \<and> V \<noteq> {} \<and> finite V \<Longrightarrow> l_one (?l (to_list V p) (to_list V' p)) = \<infinity>" 
    by (metis length_greater_0_conv map_is_Nil_conv zip_eq_Nil_iff)
  hence "A \<noteq> A' \<and> V = V' \<and> V \<noteq> {} \<and> finite V \<Longrightarrow> 
    votewise_distance swap l_one (A, V, p) (A', V', p') = \<infinity>"
    by (simp add: length_inv)
  moreover have "V \<noteq> V' \<Longrightarrow> votewise_distance swap l_one (A, V, p) (A', V', p') = \<infinity>"
    by simp
  moreover have "A \<noteq> A' \<and> V = {} \<Longrightarrow> votewise_distance swap l_one (A, V, p) (A', V', p') = \<infinity>"
    by simp
  moreover have "infinite V \<Longrightarrow> votewise_distance swap l_one (A, V, p) (A', V', p') = \<infinity>"
    by simp
  moreover have "(A \<noteq> A' \<and> V = V' \<and> V \<noteq> {} \<and> finite V) 
                  \<or> infinite V \<or> (A \<noteq> A' \<and> V = {}) \<or> V \<noteq> V'"
    using assms
    by blast
  ultimately show "votewise_distance swap l_one (A, V, p) (A', V', p') = \<infinity>"
    by fastforce
qed

subsection \<open>Equivalence Lemmas\<close>

type_synonym ('a, 'v) score_type = 
  "('a, 'v) Election Distance 
      \<Rightarrow> ('a, 'v, 'a Result) Consensus_Class 
      \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'a \<Rightarrow> ereal"

type_synonym ('a, 'v) dist_rat_type = 
  "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'a Result) Consensus_Class 
      \<Rightarrow> 'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a set"

type_synonym ('a, 'v) dist_rat_std_type =
  "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'a Result) Consensus_Class 
      \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module"

type_synonym ('a, 'v) dist_type =
  "('a, 'v) Election Distance \<Rightarrow> ('a, 'v, 'a Result) Consensus_Class 
      \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module"

lemma equal_score_swap: 
"(score::(('a, 'v::linorder) score_type)) (votewise_distance swap l_one)
    = score_std (votewise_distance swap l_one)"
  using votewise_non_voters_irrelevant swap_standard
        social_choice_result.standard_distance_imp_equal_score 
  by fast
    
lemma swap_\<R>_code[code]: 
"swap_\<R> = 
 (social_choice_result.distance_\<R>_std::(('a, 'v::linorder) dist_rat_std_type))
    (votewise_distance swap l_one)"
proof -
  from equal_score_swap
  have 
    "\<forall> K E a. (score::(('a, 'v::linorder) score_type)) 
                  (votewise_distance swap l_one) K E a =
              score_std (votewise_distance swap l_one) K E a"
    by metis
  hence "\<forall> K V A p. (social_choice_result.\<R>\<^sub>\<W>::(('a, 'v::linorder) dist_rat_type)) 
                        (votewise_distance swap l_one) K V A p =
                    social_choice_result.\<R>\<^sub>\<W>_std 
                        (votewise_distance swap l_one) K V A p"
     by (simp add: equal_score_swap)
  hence "\<forall> K V A p. (social_choice_result.distance_\<R>::(('a, 'v::linorder) dist_type)) 
                        (votewise_distance swap l_one) K V A p
                    = social_choice_result.distance_\<R>_std 
                        (votewise_distance swap l_one) K V A p"
    by fastforce
  thus ?thesis
    unfolding swap_\<R>.simps
    by blast
qed

end

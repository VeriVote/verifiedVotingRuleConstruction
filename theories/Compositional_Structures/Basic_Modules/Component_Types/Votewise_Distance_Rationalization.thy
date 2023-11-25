(*  File:       Votewise_Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Votewise Distance Rationalization\<close>

theory Votewise_Distance_Rationalization
  imports "Distance_Rationalization"
          "Votewise_Distance"
begin

text \<open>
  A votewise distance rationalization of a voting rule is its distance
  rationalization with a distance function that depends on the submitted votes
  in a simple and a transparent manner by using a distance on individual orders
  and combining the components with a norm on R to n.
\<close>

subsection \<open>Common Rationalizations\<close>

fun swap_\<R> :: "('a Election \<Rightarrow> bool) \<times> 'a Electoral_Module \<Rightarrow>
                  'a Electoral_Module" where
  "swap_\<R> A p = distance_\<R> (votewise_distance swap l_one) A p"

subsection \<open>Theorems\<close>

lemma swap_standard: "standard (votewise_distance swap l_one)"
proof (unfold standard_def, clarify)
  fix
    C :: "'a set" and
    B :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume len_p_neq_len_q_or_C_neq_B: "length p \<noteq> length q \<or> C \<noteq> B"
  thus "votewise_distance swap l_one (C, p) (B, q) = \<infinity>"
  proof (cases "length p \<noteq> length q \<or> length p = 0", simp)
    case False
    hence C_neq_B: "C \<noteq> B"
      using len_p_neq_len_q_or_C_neq_B
      by simp
    from False
    have "(map2 (\<lambda> x y. swap (C, x) (B, y)) p q)!0 = swap (C, (p!0)) (B, (q!0))"
      using case_prod_conv length_zip min.idem nth_map nth_zip zero_less_iff_neq_zero
      by (metis (no_types, lifting))
    also have "\<dots> = \<infinity>"
      using C_neq_B
      by simp
    finally have "(map2 (\<lambda> x y. swap (C, x) (B, y)) p q)!0 = \<infinity>"
      by simp
    have len_gt_zero: "0 < length (map2 (\<lambda> x y. swap (C, x) (B, y)) p q)"
      using False
      by force
    moreover have
      "(\<Sum> i::nat < min (length p) (length q). ereal_of_enat (\<infinity>)) = \<infinity>"
      using finite_lessThan sum_Pinfty lessThan_iff min.idem
            False not_gr_zero of_nat_eq_enat ereal_of_enat_simps
      by metis
    ultimately have "l_one (map2 (\<lambda> x y. swap (C, x) (B, y)) p q) = \<infinity>"
      using C_neq_B
      by simp
    thus ?thesis
      using False
      by simp
  qed
qed

subsection \<open>Equivalence Lemmas\<close>

lemma equal_score_swap:
  "score (votewise_distance swap l_one) =
    score_std (votewise_distance swap l_one)"
  using standard_distance_imp_equal_score swap_standard
  by fast

lemma swap_\<R>_code[code]: "swap_\<R> = distance_\<R>_std (votewise_distance swap l_one)"
proof -
  from equal_score_swap
  have "\<forall> K E a. score (votewise_distance swap l_one) K E a =
            score_std (votewise_distance swap l_one) K E a"
    by metis
  hence "\<forall> K A p. \<R>\<^sub>\<W> (votewise_distance swap l_one) K A p =
            \<R>\<^sub>\<W>_std (votewise_distance swap l_one) K A p"
    by (simp add: equal_score_swap)
  hence "\<forall> K A p. distance_\<R> (votewise_distance swap l_one) K A p =
          distance_\<R>_std (votewise_distance swap l_one) K A p"
    by fastforce
  thus ?thesis
    unfolding swap_\<R>.simps
    by blast
qed

end

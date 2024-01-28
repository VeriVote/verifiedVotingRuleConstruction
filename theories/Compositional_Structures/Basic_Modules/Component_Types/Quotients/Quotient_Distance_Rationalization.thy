section \<open>Distance Rationalization on Election Quotients\<close>

theory Quotient_Distance_Rationalization
  imports Quotient_Modules
          "../Distance_Rationalization_Symmetry"
begin

subsection \<open>Quotient Distances\<close>

fun dist\<^sub>\<Q> :: "'x Distance \<Rightarrow> 'x set Distance" where
  "dist\<^sub>\<Q> d A B = (if (A = {} \<and> B = {}) then 0 else
                  (if (A = {} \<or> B = {}) then \<infinity> else
                    \<pi>\<^sub>\<Q> (dist\<^sub>\<T> d) (A \<times> B)))"

fun relation_paths :: "'x rel \<Rightarrow> 'x list set" where
  "relation_paths r = {p. \<exists> k. (length p = 2 * k \<and> (\<forall> i < k. (p!(2 * i), p!(2 * i + 1)) \<in> r))}"

fun admissible_paths :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x set \<Rightarrow> 'x list set" where
  "admissible_paths r X Y = {x#p@[y] | x y p. x \<in> X \<and> y \<in> Y \<and> p \<in> relation_paths r}"

fun path_length :: "'x list \<Rightarrow> 'x Distance \<Rightarrow> ereal" where
  "path_length [] d = 0" |
  "path_length [x] d = 0" |
  "path_length (x#y#xs) d = d x y + path_length xs d"

fun quotient_dist :: "'x rel \<Rightarrow> 'x Distance \<Rightarrow> 'x set Distance" where
  "quotient_dist r d A B = Inf (\<Union> {{path_length p d | p. p \<in> admissible_paths r A B}})"

fun inf_dist\<^sub>\<Q> :: "'x Distance \<Rightarrow> 'x set Distance" where
  "inf_dist\<^sub>\<Q> d A B = Inf {d a b | a b. a \<in> A \<and> b \<in> B}"

fun simple :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> bool" where
  "simple r X d =
    (\<forall> A \<in> X // r. (\<exists> a \<in> A. \<forall> B \<in> X // r. inf_dist\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}))"
\<comment> \<open>We call a distance simple with respect to a relation if for all relation classes,
    there is an a in A minimizing the infimum distance between A and all B
    so that the infimum distance between these sets coincides with the infimum
    distance over all b in B for fixed a.\<close>

(* lemma "Min {Inf {y | y::ereal. y < x} | x. x > 0} = -\<infinity>"
proof -
  have "\<forall> x > 0. Inf {y | y::ereal. y < x} = -\<infinity>"
    by (simp add: Inf_eq_MInfty)
  hence "{Inf {y | y::ereal. y < x} | x. x > 0} = {-\<infinity>}"
    using Collect_cong ereal_less(6) neg_0_less_iff_less_erea singleton_conv
    by (smt (verit))
  thus ?thesis
    by auto
qed *)

fun product_rel' :: "'x rel \<Rightarrow> ('x * 'x) rel" where
  "product_rel' r = {(pair1, pair2). ((fst pair1, fst pair2) \<in> r \<and> snd pair1 = snd pair2) \<or>
                                    ((snd pair1, snd pair2) \<in> r \<and> fst pair1 = fst pair2)}"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma tot_dist_invariance_is_congruence:
  fixes
    d :: "'x Distance" and
    r :: "'x rel"
  shows "(totally_invariant_dist d r) = (dist\<^sub>\<T> d respects (product_rel r))"
  unfolding totally_invariant_dist.simps satisfies.simps congruent_def
  by blast

lemma product_rel_helper:
  fixes
    r :: "'x rel" and
    X :: "'x set"
  shows
    trans_imp: "Relation.trans r \<Longrightarrow> Relation.trans (product_rel r)" and
    refl_imp: "refl_on X r \<Longrightarrow> refl_on (X \<times> X) (product_rel r)" and
    sym: "sym_on X r \<Longrightarrow> sym_on (X \<times> X) (product_rel r)"
  unfolding Relation.trans_def refl_on_def sym_on_def product_rel.simps
  by auto

theorem dist_pass_to_quotient:
  fixes
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    "equiv X r" and
    "totally_invariant_dist d r"
  shows "\<forall> A B. A \<in> X // r \<and> B \<in> X // r \<longrightarrow> (\<forall> a b. a \<in> A \<and> b \<in> B \<longrightarrow> dist\<^sub>\<Q> d A B = d a b)"
proof (safe)
  fix
    A :: "'x set" and
    B :: "'x set" and
    a :: "'x" and
    b :: "'x"
  assume
    a_in_A: "a \<in> A" and
    b_in_B: "b \<in> B" and
    A_in_X_quot: "A \<in> X // r" and
    B_in_X_quot: "B \<in> X // r"
  hence "A = r `` {a} \<and> B = r `` {b}"
    using assms equiv_class_eq_iff quotientI quotient_eq_iff rev_ImageI singleton_iff
    by meson
  hence "A \<times> B = (product_rel r) `` {(a, b)}"
    unfolding product_rel'.simps
    by fastforce
  hence "A \<times> B \<in> (X \<times> X) // (product_rel r)"
    unfolding quotient_def
    using a_in_A b_in_B A_in_X_quot B_in_X_quot assms Union_quotient
    by fastforce
  moreover have "equiv (X \<times> X) (product_rel r)"
    using assms product_rel_helper UNIV_Times_UNIV equivE equivI
    by metis
  moreover have "dist\<^sub>\<T> d respects (product_rel r)"
    using assms tot_dist_invariance_is_congruence[of d r]
    by blast
  moreover have "dist\<^sub>\<Q> d A B = \<pi>\<^sub>\<Q> (dist\<^sub>\<T> d) (A \<times> B)"
    using a_in_A b_in_B
    by auto
  ultimately have "\<forall> (x, y) \<in> A \<times> B. dist\<^sub>\<Q> d A B = d x y"
    unfolding dist\<^sub>\<Q>.simps
    using assms pass_to_quotient
    by fastforce
  thus "dist\<^sub>\<Q> d A B = d a b"
    using a_in_A b_in_B
    by blast
qed

lemma relation_paths_subset:
  fixes
    n :: nat and
    p :: "'x list" and
    r :: "'x rel" and
    X :: "'x set"
  assumes "r \<subseteq> X \<times> X"
  shows "\<forall> p. p \<in> relation_paths r \<longrightarrow> (\<forall> i < length p. p!i \<in> X)"
proof (safe)
  fix
    p :: "'x list" and
    i :: "nat"
  assume
    "p \<in> relation_paths r" and
    range: "i < length p"
  then obtain k :: "nat" where
    len: "length p = 2 * k" and
    rel: "\<forall> i < k. (p!(2 * i), p!(2 * i + 1)) \<in> r"
    by auto
  obtain k' :: "nat" where
    i_cases: "i = 2 * k' \<or> i = 2 * k' + 1"
    using diff_Suc_1 even_Suc oddE odd_two_times_div_two_nat
    by metis
  with len range
  have "k' < k"
    by linarith
  hence "(p!(2 * k'), p!(2 * k' + 1)) \<in> r"
    using rel
    by blast
  hence "p!(2 * k') \<in> X \<and> p!(2 * k' + 1) \<in> X"
    using assms rel
    by blast
  thus "p!i \<in> X"
    using i_cases
    by blast
qed

lemma admissible_path_len:
  fixes
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set" and
    a :: "'x" and
    b :: "'x" and
    p :: "'x list"
  assumes "refl_on X r"
  shows "triangle_ineq X d \<and> p \<in> relation_paths r \<and> totally_invariant_dist d r \<and>
            a \<in> X \<and> b \<in> X \<longrightarrow> path_length (a#p@[b]) d \<ge> d a b"
proof (clarify, induction p d arbitrary: a b rule: path_length.induct)
  case (1 d)
  show "d a b \<le> path_length (a#[]@[b]) d"
    by simp
next
  case (2 x d)
  hence False
    by simp
  thus "d a b \<le> path_length (a#[x]@[b]) d"
    by blast
next
  case (3 x y xs d)
  assume
    ineq: "triangle_ineq X d" and
    a_in_X: "a \<in> X" and
    b_in_X: "b \<in> X" and
    rel: "x#y#xs \<in> relation_paths r" and
    invar: "totally_invariant_dist d r" and
    hyp: "\<And> a b. triangle_ineq X d \<Longrightarrow> xs \<in> relation_paths r \<Longrightarrow> totally_invariant_dist d r \<Longrightarrow>
                  a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> d a b \<le> path_length (a#xs@[b]) d"
  then obtain k :: "nat" where
    len: "length (x#y#xs) = 2 * k"
    by auto
  moreover have "\<forall> i < k - 1. (xs!(2 * i), xs!(2 * i + 1)) =
    ((x#y#xs)!(2 * (i + 1)), (x#y#xs)!(2 * (i + 1) + 1))"
    by simp
  ultimately have "\<forall> i < k - 1. (xs!(2 * i), xs!(2 * i + 1)) \<in> r"
    using rel less_diff_conv
    unfolding relation_paths.simps
    by fastforce
  moreover have "length xs = 2 * (k - 1)"
    using len
    by simp
  ultimately have "xs \<in> relation_paths r"
    by simp
  hence "\<forall> x y. x \<in> X \<and> y \<in> X \<longrightarrow> d x y \<le> path_length (x#xs@[y]) d"
    using ineq invar hyp
    by blast
  moreover have "path_length (a#(x#y#xs)@[b]) d = d a x + path_length (y#xs@[b]) d"
    by simp
  moreover have x_rel_y: "(x, y) \<in> r"
    using rel
    unfolding relation_paths.simps
    by fastforce
  ultimately have "path_length (a#(x#y#xs)@[b]) d \<ge> d a x + d y b"
    using assms add_left_mono assms refl_onD2 b_in_X
    unfolding refl_on_def
    by metis
  moreover have "d a x + d y b = d a x + d x b"
    using invar x_rel_y rewrite_totally_invariant_dist assms b_in_X
    unfolding refl_on_def
    by fastforce
  moreover have "d a x + d x b \<ge> d a b"
    using a_in_X b_in_X x_rel_y assms ineq
    unfolding refl_on_def triangle_ineq_def
    by auto
  ultimately show "d a b \<le> path_length (a#(x#y#xs)@[b]) d"
    by simp
qed

lemma quotient_dist_coincides_with_dist\<^sub>\<Q>:
  fixes
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    equiv: "equiv X r" and
    tri: "triangle_ineq X d" and
    invar: "totally_invariant_dist d r"
  shows "\<forall> A \<in> X // r. \<forall> B \<in> X // r. quotient_dist r d A B = dist\<^sub>\<Q> d A B"
proof (clarify)
  fix
    A :: "'x set" and
    B :: "'x set"
  assume
    A_in_quot_X: "A \<in> X // r" and
    B_in_quot_X: "B \<in> X // r"
  then obtain
    a :: "'x" and
    b :: "'x" where
      el: "a \<in> A \<and> b \<in> B" and
      def_dist: "dist\<^sub>\<Q> d A B = d a b"
    using dist_pass_to_quotient assms in_quotient_imp_non_empty ex_in_conv
    by (metis (full_types))
  hence equiv_cls: "A = r `` {a} \<and> B = r `` {b}"
    using A_in_quot_X B_in_quot_X assms equiv_class_eq_iff equiv_class_self
          quotientI quotient_eq_iff
    by meson
  have subset_X: "r \<subseteq> X \<times> X \<and> A \<subseteq> X \<and> B \<subseteq> X"
    using assms A_in_quot_X B_in_quot_X equiv_def refl_on_def Union_quotient Union_upper
    by metis
  have "\<forall> p \<in> admissible_paths r A B.
          (\<exists> p' x y. x \<in> A \<and> y \<in> B \<and> p' \<in> relation_paths r \<and> p = x#p'@[y])"
    unfolding admissible_paths.simps
    by blast
  moreover have "\<forall> x y. x \<in> A \<and> y \<in> B \<longrightarrow> d x y = d a b"
    using invar equiv_cls
    by auto
  moreover have "refl_on X r"
    using equiv equiv_def
    by blast
  ultimately have "\<forall> p. p \<in> admissible_paths r A B \<longrightarrow> path_length p d \<ge> d a b"
    using admissible_path_len[of X r d] tri subset_X el invar in_mono
    by metis
  hence "\<forall> l. l \<in> \<Union> {{path_length p d | p. p \<in> admissible_paths r A B}} \<longrightarrow> l \<ge> d a b"
    by blast
  hence geq: "quotient_dist r d A B \<ge> d a b"
    unfolding quotient_dist.simps[of r d A B] le_Inf_iff
    by simp
  with el def_dist
  have geq: "quotient_dist r d A B \<ge> dist\<^sub>\<Q> d A B"
    by presburger
  have "[a, b] \<in> admissible_paths r A B"
    using el
    by simp
  moreover have "path_length [a, b] d = d a b"
    by simp
  ultimately have "quotient_dist r d A B \<le> d a b"
    using quotient_dist.simps[of r d A B] CollectI Inf_lower ccpo_Sup_singleton
    by (metis (mono_tags, lifting))
  thus "quotient_dist r d A B = dist\<^sub>\<Q> d A B"
    using geq def_dist nle_le
    by metis
qed

lemma inf_dist_coincides_with_dist\<^sub>\<Q>:
  fixes
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    "equiv X r" and
    "totally_invariant_dist d r"
  shows "\<forall> A \<in> X // r. \<forall> B \<in> X // r. inf_dist\<^sub>\<Q> d A B = dist\<^sub>\<Q> d A B"
proof (clarify)
  fix
    A :: "'x set" and
    B :: "'x set"
  assume
    A_in_quot_X: "A \<in> X // r" and
    B_in_quot_X: "B \<in> X // r"
  then obtain
    a :: "'x" and
    b :: "'x" where
      el: "a \<in> A \<and> b \<in> B" and
      def_dist: "dist\<^sub>\<Q> d A B = d a b"
    using dist_pass_to_quotient assms in_quotient_imp_non_empty ex_in_conv
    by (metis (full_types))
  have "\<forall> x y. x \<in> A \<and> y \<in> B \<longrightarrow> d x y = d a b"
    using def_dist dist_pass_to_quotient assms A_in_quot_X B_in_quot_X
    by force
  hence "{d x y | x y. x \<in> A \<and> y \<in> B} = {d a b}"
    using el
    by blast
  thus "inf_dist\<^sub>\<Q> d A B = dist\<^sub>\<Q> d A B"
    unfolding inf_dist\<^sub>\<Q>.simps
    using def_dist
    by simp
qed

lemma Inf_helper:
  fixes
    A :: "'x set" and
    B :: "'x set" and
    d :: "'x Distance"
  shows "Inf {d a b | a b. a \<in> A \<and> b \<in> B} = Inf {Inf {d a b | b. b \<in> B} | a. a \<in> A}"
proof -
  have "\<forall> a b. a \<in> A \<and> b \<in> B \<longrightarrow> Inf {d a b | b. b \<in> B} \<le> d a b"
    using INF_lower Setcompr_eq_image
    by metis
  hence "\<forall> \<alpha> \<in> {d a b | a b. a \<in> A \<and> b \<in> B}. \<exists> \<beta> \<in> {Inf {d a b | b. b \<in> B} | a. a \<in> A}. \<beta> \<le> \<alpha>"
    by blast
  hence "Inf {Inf {d a b | b. b \<in> B} | a. a \<in> A} \<le> Inf {d a b | a b. a \<in> A \<and> b \<in> B}"
    using Inf_mono
    by meson
  moreover have "\<not> (Inf {Inf {d a b | b. b \<in> B} | a. a \<in> A} < Inf {d a b | a b. a \<in> A \<and> b \<in> B})"
  proof (rule ccontr, simp)
    assume "Inf {Inf {d a b | b. b \<in> B} | a. a \<in> A} < Inf {d a b | a b. a \<in> A \<and> b \<in> B}"
    then obtain \<alpha> :: "ereal" where
      inf: "\<alpha> \<in> {Inf {d a b | b. b \<in> B} | a. a \<in> A}" and
      less: "\<alpha> < Inf {d a b | a b. a \<in> A \<and> b \<in> B}"
      using Inf_less_iff Inf_lower2 leD linorder_le_less_linear
      by meson
    then obtain a :: "'x" where
      a_in_A: "a \<in> A" and
      "\<alpha> = Inf {d a b | b. b \<in> B}"
      by blast
    with less
    have inf_less: "Inf {d a b | b. b \<in> B} < Inf {d a b | a b. a \<in> A \<and> b \<in> B}"
      by blast
    have "{d a b | b. b \<in> B} \<subseteq> {d a b | a b. a \<in> A \<and> b \<in> B}"
      using a_in_A
      by blast
    hence "Inf {d a b | a b. a \<in> A \<and> b \<in> B} \<le> Inf {d a b | b. b \<in> B}"
      using Inf_superset_mono
      by meson
    with inf_less
    show False
      using linorder_not_less
      by simp
  qed
  ultimately show ?thesis
    by simp
qed

lemma invar_dist_simple:
  fixes
    d :: "'y Distance" and
    G :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes
    grp_act: "group_action G Y \<phi>" and
    invar: "invariant_dist d (carrier G) Y \<phi>"
  shows "simple (rel_induced_by_action (carrier G) Y \<phi>) Y d"
proof (unfold simple.simps, safe)
  fix A :: "'y set"
  assume cls: "A \<in> Y // rel_induced_by_action (carrier G) Y \<phi>"
  have equiv_rel: "equiv Y (rel_induced_by_action (carrier G) Y \<phi>)"
    using assms rel_ind_by_grp_act_equiv
    by blast
  with cls obtain a :: "'y" where
    a_in_A: "a \<in> A"
    using equiv_Eps_in
    by blast
  have subset: "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>. B \<subseteq> Y"
    using equiv_rel in_quotient_imp_subset
    by blast
  hence "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
          \<forall> B' \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
            \<forall> b \<in> B. \<forall> c \<in> B'. b \<in> Y \<and> c \<in> Y"
    using cls
    by blast
  hence eq_dist:
    "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
      \<forall> B' \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
        \<forall> b \<in> B. \<forall> c \<in> B'. \<forall> g \<in> carrier G.
          d (\<phi> g c) (\<phi> g b) = d c b"
    using invar rewrite_invariant_dist cls
    by metis
  have "\<forall> b \<in> Y. \<forall> g \<in> carrier G. (b, \<phi> g b) \<in> rel_induced_by_action (carrier G) Y \<phi>"
    unfolding rel_induced_by_action.simps
    using group_action.element_image grp_act
    by fastforce
  hence "\<forall> b \<in> Y. \<forall> g \<in> carrier G. \<phi> g b \<in> rel_induced_by_action (carrier G) Y \<phi> `` {b}"
    unfolding Image_def
    by blast
  moreover have equiv_cls:
    "\<forall> B. B \<in> Y // rel_induced_by_action (carrier G) Y \<phi> \<longrightarrow>
      (\<forall> b \<in> B. B = rel_induced_by_action (carrier G) Y \<phi> `` {b})"
    using equiv_rel Image_singleton_iff equiv_class_eq_iff quotientI quotient_eq_iff
    by meson
  ultimately have closed_cls:
    "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>. \<forall> b \<in> B. \<forall> g \<in> carrier G. \<phi> g b \<in> B"
    using equiv_rel subset
    by blast
  with eq_dist cls
  have a_subset_A:
    "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
      {d a b | b. b \<in> B} \<subseteq> {d a b | a b. a \<in> A \<and> b \<in> B}"
    using a_in_A
    by blast
  have "\<forall> a' \<in> A. A = rel_induced_by_action (carrier G) Y \<phi> `` {a'}"
    using cls equiv_rel equiv_cls
    by presburger
  hence "\<forall> a' \<in> A. (a', a) \<in> rel_induced_by_action (carrier G) Y \<phi>"
    using a_in_A
    by blast
  hence "\<forall> a' \<in> A. \<exists> g \<in> carrier G. \<phi> g a' = a"
    by simp
  hence "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
      \<forall> a' b. a' \<in> A \<and> b \<in> B \<longrightarrow> (\<exists> g \<in> carrier G. d a' b = d a (\<phi> g b))"
    using eq_dist cls
    by metis
  hence "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
      \<forall> a' b. a' \<in> A \<and> b \<in> B \<longrightarrow> d a' b \<in> {d a b | b. b \<in> B}"
    using closed_cls mem_Collect_eq
    by fastforce
  hence "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
      {d a b | b. b \<in> B} \<supseteq> {d a b | a b. a \<in> A \<and> b \<in> B}"
    using closed_cls
    by blast
  with a_subset_A
  have "\<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
          inf_dist\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
    unfolding inf_dist\<^sub>\<Q>.simps
    by fastforce
  thus "\<exists> a \<in> A. \<forall> B \<in> Y // rel_induced_by_action (carrier G) Y \<phi>.
      inf_dist\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
    using a_in_A
    by meson
qed

lemma tot_invar_dist_simple:
  fixes
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    equiv_on_X: "equiv X r" and
    invar: "totally_invariant_dist d r"
  shows "simple r X d"
proof (unfold simple.simps, safe)
  fix A :: "'x set"
  assume A_quot_X: "A \<in> X // r"
  then obtain a :: "'x" where
    a_in_A: "a \<in> A"
    using equiv_on_X equiv_Eps_in
    by blast
  from A_quot_X have "\<forall> a \<in> A. A = r `` {a}"
    using equiv_on_X Image_singleton_iff equiv_class_eq_iff quotientI quotient_eq_iff
    by meson
  hence "\<forall> a a'. a \<in> A \<and> a' \<in> A \<longrightarrow> (a, a') \<in> r"
    by blast
  moreover have "\<forall> B \<in> X // r. \<forall> b \<in> B. (b, b) \<in> r"
    using equiv_on_X quotient_eq_iff
    by metis
  ultimately have "\<forall> B \<in> X // r. \<forall> a a' b. a \<in> A \<and> a' \<in> A \<and> b \<in> B \<longrightarrow> d a b = d a' b"
    using invar rewrite_totally_invariant_dist
    by simp
  hence "\<forall> B \<in> X // r. {d a b | a b. a \<in> A \<and> b \<in> B} = {d a b | a' b. a' \<in> A \<and> b \<in> B}"
    using a_in_A
    by blast
  moreover have "\<forall> B \<in> X // r. {d a b | a' b. a' \<in> A \<and> b \<in> B} = {d a b | b. b \<in> B}"
    using a_in_A
    by blast
  ultimately have "\<forall> B \<in> X // r. Inf {d a b | a b. a \<in> A \<and> b \<in> B} = Inf {d a b | b. b \<in> B}"
    by simp
  hence "\<forall> B \<in> X // r. inf_dist\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
    by simp
  thus "\<exists> a \<in> A. \<forall> B \<in> X // r. inf_dist\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
    using a_in_A
    by blast
qed

subsection \<open>Quotient Consensus and Results\<close>

fun \<K>_els\<^sub>\<Q> :: "('a, 'v) Election rel \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class \<Rightarrow>
          ('a, 'v) Election set set" where
  "\<K>_els\<^sub>\<Q> r C = (\<K>_els C) // r"

fun (in result) limit_set\<^sub>\<Q> :: "('a, 'v) Election set \<Rightarrow> 'r set \<Rightarrow> 'r set" where
  "limit_set\<^sub>\<Q> X res = \<Inter> {limit_set (alts_\<E> E) res | E. E \<in> X}"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma closed_under_equiv_rel_subset:
   fixes
    X :: "'x set" and
    Y :: "'x set" and
    Z :: "'x set" and
    r :: "'x rel"
  assumes
    "equiv X r" and
    "Y \<subseteq> X" and
    "Z \<subseteq> X" and
    "Z \<in> Y // r" and
    "closed_under_restr_rel r X Y"
  shows "Z \<subseteq> Y"
proof (safe)
  fix z :: "'x"
  assume "z \<in> Z"
  then obtain y :: "'x" where
    "y \<in> Y" and
    "(y, z) \<in> r"
    using assms
    unfolding quotient_def Image_def
    by blast
  hence "(y, z) \<in> r \<inter> Y \<times> X"
    using assms
    unfolding equiv_def refl_on_def
    by blast
  hence "z \<in> {z. \<exists> y \<in> Y. (y, z) \<in> r \<inter> Y \<times> X}"
    by blast
  thus "z \<in> Y"
    using assms
    unfolding closed_under_restr_rel.simps restr_rel.simps
    by blast
qed

lemma (in result) limit_set_invar:
  fixes
    d :: "('a, 'v) Election Distance" and
    r :: "('a, 'v) Election rel" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    X :: "('a, 'v) Election set" and
    A :: "('a, 'v) Election set"
  assumes
    cls: "A \<in> X // r" and
    equiv_rel: "equiv X r" and
    cons_subset: "\<K>_els C \<subseteq> X" and
    invar_res: "satisfies (\<lambda> E. limit_set (alts_\<E> E) UNIV) (Invariance r)"
  shows "\<forall> a \<in> A. limit_set (alts_\<E> a) UNIV = limit_set\<^sub>\<Q> A UNIV"
proof
  fix a :: "('a, 'v) Election"
  assume a_in_A: "a \<in> A"
  hence "\<forall> b \<in> A. (a, b) \<in> r"
    using cls equiv_rel quotient_eq_iff
    by metis
  hence "\<forall> b \<in> A. limit_set (alts_\<E> b) UNIV = limit_set (alts_\<E> a) UNIV"
    using invar_res
    unfolding satisfies.simps
    by (metis (mono_tags, lifting))
  hence "limit_set\<^sub>\<Q> A UNIV = \<Inter> {limit_set (alts_\<E> a) UNIV}"
    unfolding limit_set\<^sub>\<Q>.simps
    using a_in_A
    by blast
  thus "limit_set (alts_\<E> a) UNIV = limit_set\<^sub>\<Q> A UNIV"
    by simp
qed

lemma (in result) preimg_invar:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    equiv_rel: "equiv X r" and
    cons_subset: "domain\<^sub>f \<subseteq> X" and
    closed_domain: "closed_under_restr_rel r X domain\<^sub>f" and
    invar_f: "satisfies f (Invariance (Restr r domain\<^sub>f))"
  shows "\<forall> y. (preimg f domain\<^sub>f y) // r = preimg (\<pi>\<^sub>\<Q> f) (domain\<^sub>f // r) y"
proof (safe)
  fix
    A :: "'x set" and
    y :: "'y"
  assume preimg_quot: "A \<in> preimg f domain\<^sub>f y // r"
  hence A_in_dom: "A \<in> domain\<^sub>f // r"
    unfolding preimg.simps quotient_def
    by blast
  obtain x :: "'x" where
    "x \<in> preimg f domain\<^sub>f y" and
    A_eq_img_singleton_r: "A = r `` {x}"
    using equiv_rel preimg_quot quotientE
    unfolding quotient_def
    by blast
  hence x_in_dom_and_f_x_y: "x \<in> domain\<^sub>f \<and> f x = y"
    unfolding preimg.simps
    by blast
  moreover have "r `` {x} \<subseteq> X"
    using equiv_rel equiv_type
    by fastforce
  ultimately have "r `` {x} \<subseteq> domain\<^sub>f"
    using closed_domain A_eq_img_singleton_r A_in_dom
    by fastforce
  hence "\<forall> x' \<in> r `` {x}. (x, x') \<in> Restr r domain\<^sub>f"
    using x_in_dom_and_f_x_y in_mono
    by blast
  hence "\<forall> x' \<in> r `` {x}. f x' = y"
    using invar_f x_in_dom_and_f_x_y
    unfolding satisfies.simps
    by metis
  moreover have "x \<in> A"
    using equiv_rel cons_subset equiv_class_self in_mono
          A_eq_img_singleton_r x_in_dom_and_f_x_y
    by metis
  ultimately have "f ` A = {y}"
    using A_eq_img_singleton_r
    by auto
  hence "\<pi>\<^sub>\<Q> f A = y"
    unfolding \<pi>\<^sub>\<Q>.simps singleton_set.simps
    using insert_absorb insert_iff insert_not_empty singleton_set_def_if_card_one
          is_singletonI is_singleton_altdef singleton_set.simps
    by metis
  thus "A \<in> preimg (\<pi>\<^sub>\<Q> f) (domain\<^sub>f // r) y"
    using A_in_dom
    unfolding preimg.simps
    by blast
next
  fix
    A :: "'x set" and
    y :: "'y"
  assume quot_preimg: "A \<in> preimg (\<pi>\<^sub>\<Q> f) (domain\<^sub>f // r) y"
  hence A_in_dom_rel_r: "A \<in> domain\<^sub>f // r"
    using cons_subset equiv_rel
    by auto
  hence "A \<subseteq> X"
    using equiv_rel cons_subset Image_subset equiv_type quotientE
    by metis
  hence A_in_dom: "A \<subseteq> domain\<^sub>f"
    using closed_under_equiv_rel_subset[of X r domain\<^sub>f A]
          closed_domain cons_subset A_in_dom_rel_r equiv_rel
    by blast
  moreover obtain x :: "'x" where
    x_in_A: "x \<in> A" and
    A_eq_r_img_single_x: "A = r `` {x}"
    using A_in_dom_rel_r equiv_rel cons_subset equiv_class_self in_mono quotientE
    by metis
  ultimately have "\<forall> x' \<in> A. (x, x') \<in> Restr r domain\<^sub>f"
    by blast
  hence "\<forall> x' \<in> A. f x' = f x"
    using invar_f
    by fastforce
  hence "f ` A = {f x}"
    using x_in_A
    by blast
  hence "\<pi>\<^sub>\<Q> f A = f x"
    unfolding \<pi>\<^sub>\<Q>.simps singleton_set.simps
    using is_singleton_altdef singleton_set_def_if_card_one
    by fastforce
  also have "\<pi>\<^sub>\<Q> f A = y"
    using quot_preimg
    unfolding preimg.simps
    by blast
  finally have "f x = y"
    by simp
  moreover have "x \<in> domain\<^sub>f"
    using x_in_A A_in_dom
    by blast
  ultimately have "x \<in> preimg f domain\<^sub>f y"
    by simp
  thus "A \<in> preimg f domain\<^sub>f y // r"
    using A_eq_r_img_single_x
    unfolding quotient_def
    by blast
qed

lemma minimizer_helper:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    d :: "'x Distance" and
    Y :: "'y set" and
    x :: "'x" and
    y :: "'y"
  shows "y \<in> minimizer f domain\<^sub>f d Y x =
      (y \<in> Y \<and> (\<forall> y' \<in> Y. Inf (d x ` (preimg f domain\<^sub>f y)) \<le> Inf (d x ` (preimg f domain\<^sub>f y'))))"
  unfolding is_arg_min_def minimizer.simps arg_min_set.simps
  by auto

lemma rewr_singleton_set_system_union:
  fixes
    Y :: "'x set set" and
    X :: "'x set"
  assumes "Y \<subseteq> singleton_set_system X"
  shows
    singleton_set_union: "x \<in> \<Union> Y \<longleftrightarrow> {x} \<in> Y" and
    obtain_singleton: "A \<in> singleton_set_system X \<longleftrightarrow> (\<exists> x \<in> X. A = {x})"
  unfolding singleton_set_system.simps
  using assms
  by auto

lemma union_inf:
  fixes X :: "ereal set set"
  shows "Inf {Inf A | A. A \<in> X} = Inf (\<Union> X)"
proof -
  let ?inf = "Inf {Inf A | A. A \<in> X}"
  have "\<forall> A \<in> X. \<forall> x \<in> A. ?inf \<le> x"
    using INF_lower2 Inf_lower Setcompr_eq_image
    by metis
  hence "\<forall> x \<in> \<Union> X. ?inf \<le> x"
    by simp
  hence le: "?inf \<le> Inf (\<Union> X)"
    using Inf_greatest
    by meson
  have "\<forall> A \<in> X. Inf (\<Union> X) \<le> Inf A"
    using Inf_superset_mono Union_upper
    by metis
  hence "Inf (\<Union> X) \<le> Inf {Inf A | A. A \<in> X}"
    using le_Inf_iff
    by auto
  thus ?thesis
    using le
    by simp
qed

subsection \<open>Quotient Distance Rationalization\<close>

fun (in result) \<R>\<^sub>\<Q> :: "('a, 'v) Election rel \<Rightarrow> ('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Consensus_Class \<Rightarrow> ('a, 'v) Election set \<Rightarrow> 'r set" where
  "\<R>\<^sub>\<Q> r d C A = \<Union> (minimizer (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C)
                              (inf_dist\<^sub>\<Q> d) (singleton_set_system (limit_set\<^sub>\<Q> A UNIV)) A)"

fun (in result) distance_\<R>\<^sub>\<Q> :: "('a, 'v) Election rel \<Rightarrow> ('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Consensus_Class \<Rightarrow> ('a, 'v) Election set \<Rightarrow> 'r Result" where
  "distance_\<R>\<^sub>\<Q> r d C A =
    (\<R>\<^sub>\<Q> r d C A, \<pi>\<^sub>\<Q> (\<lambda> E. limit_set (alts_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A, {})"

text \<open>
  Hadjibeyli and Wilson 2016 4.17
\<close>

theorem (in result) invar_dr_simple_dist_imp_quotient_dr_winners:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    r :: "('a, 'v) Election rel" and
    X :: "('a, 'v) Election set" and
    A :: "('a, 'v) Election set"
  assumes
    simple: "simple r X d" and
    closed_domain: "closed_under_restr_rel r X (\<K>_els C)" and
    invar_res: "satisfies (\<lambda> E. limit_set (alts_\<E> E) UNIV) (Invariance r)" and
    invar_C: "satisfies (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (Invariance (Restr r (\<K>_els C)))" and
    invar_dr: "satisfies (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance r)" and
    cls: "A \<in> X // r" and
    equiv_rel: "equiv X r" and
    cons_subset: "\<K>_els C \<subseteq> X"
  shows "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = \<R>\<^sub>\<Q> r d C A"
proof -
  have preimg_img_imp_cls:
    "\<forall> y B. B \<in> preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) y \<longrightarrow> B \<in> (\<K>_els C) // r"
    by simp
  have "\<forall> y'. \<forall> E \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y'. E \<in> r `` {E}"
    using equiv_rel cons_subset equiv_class_self equiv_rel in_mono
    unfolding equiv_def preimg.simps
    by fastforce
  hence "\<forall> y'.
      \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r) \<supseteq>
      preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y'"
    unfolding quotient_def
    by blast
  moreover have "\<forall> y'.
      \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r) \<subseteq>
      preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y'"
  proof (standard, standard)
    fix
      Y' :: "'r set" and
      E :: "('a, 'v) Election"
    assume "E \<in> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) Y' // r)"
    then obtain B :: "('a, 'v) Election set" where
      E_in_B: "E \<in> B" and
      "B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) Y' // r"
      by blast
    then obtain E' :: "('a, 'v) Election" where
      "B = r `` {E'}" and
      map_to_Y': "E' \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) Y'"
      using quotientE
      by blast
    hence in_restr_rel: "(E', E) \<in> r \<inter> (\<K>_els C) \<times> X"
      using E_in_B equiv_rel
      unfolding preimg.simps equiv_def refl_on_def
      by blast
    hence "E \<in> \<K>_els C"
      using closed_domain
      unfolding closed_under_restr_rel.simps restr_rel.simps Image_def
      by blast
    hence rel_cons_els: "(E', E) \<in> Restr r (\<K>_els C)"
      using in_restr_rel
      by blast
    hence "(elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) E = (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) E'"
      using invar_C
      unfolding satisfies.simps
      by blast
    hence "(elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) E = Y'"
      using map_to_Y'
      by simp
    thus "E \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<Union> (range (\<K>\<^sub>\<E> C))) Y'"
      unfolding preimg.simps
      using rel_cons_els
      by blast
  qed
  ultimately have preimg_partition: "\<forall> y'.
      \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r) =
      preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y'"
    by blast
  have quot_clses_subset: "(\<K>_els C) // r \<subseteq> X // r"
    using cons_subset
    unfolding quotient_def
    by blast
  obtain a :: "('a, 'v) Election" where
    a_in_A: "a \<in> A" and
    a_def_inf_dist: "\<forall> B \<in> X // r. inf_dist\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
    using simple cls
    unfolding simple.simps
    by meson
  hence inf_dist_preimg_sets:
    "\<forall> y' B. B \<in> preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) y' \<longrightarrow>
              inf_dist\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
    using preimg_img_imp_cls quot_clses_subset
    by blast
  have valid_res_eq: "singleton_set_system (limit_set (alts_\<E> a) UNIV) =
      singleton_set_system (limit_set\<^sub>\<Q> A UNIV)"
    using invar_res a_in_A cls cons_subset equiv_rel limit_set_invar
    by metis
  have inf_le_iff: "\<forall> x.
      (\<forall> y' \<in> singleton_set_system (limit_set (alts_\<E> a) UNIV).
            Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) {x}) \<le>
            Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y')) =
      (\<forall> y' \<in> singleton_set_system (limit_set\<^sub>\<Q> A UNIV).
            Inf (inf_dist\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) {x}) \<le>
            Inf (inf_dist\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) y'))"
  proof -
    have preimg_partition_dist: "\<forall> y'.
        Inf {d a b | b. b \<in> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r)} =
        Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y')"
      using Setcompr_eq_image preimg_partition
      by metis
    have "\<forall> y'.
        {Inf A |A. A \<in> {{d a b | b. b \<in> B} | B.
            B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<Union> (range (\<K>\<^sub>\<E> C))) y' // r}} =
        {Inf {d a b | b. b \<in> B} | B. B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r}"
      by blast
    hence "\<forall> y'.
        Inf {Inf {d a b | b. b \<in> B} | B.
          B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r} =
        Inf (\<Union> {{d a b | b. b \<in> B} | B.
          B \<in> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r)})"
      using union_inf[of
              "{{d a b | b. b \<in> B} | B. B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) _ // r}"]
      by presburger
    moreover have
      "\<forall> y'. {d a b | b. b \<in> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r)} =
            \<Union> {{d a b | b. b \<in> B} | B.
                  B \<in> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r)}"
      by blast
    ultimately have rewrite_inf_dist: "\<forall> y'.
        Inf {Inf {d a b | b. b \<in> B} | B.
          B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r} =
        Inf {d a b | b. b \<in> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r)}"
      by presburger
    have "\<forall> y'. inf_dist\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) y' =
        {Inf {d a b | b. b \<in> B} | B. B \<in> preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) y'}"
      using inf_dist_preimg_sets
      unfolding Image_def
      by auto
    moreover have "\<forall> y'.
        {Inf {d a b | b. b \<in> B} | B.
          B \<in> preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) y'} =
        {Inf {d a b | b. b \<in> B} | B.
          B \<in> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y') // r}"
      unfolding \<K>_els\<^sub>\<Q>.simps
      using preimg_invar closed_domain cons_subset equiv_rel invar_C
      by blast
    ultimately have "\<forall> y'.
        Inf (inf_dist\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) y') =
        Inf {Inf {d a b | b. b \<in> B} | B.
          B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y' // r}"
      by simp
    thus "?thesis"
      using valid_res_eq rewrite_inf_dist preimg_partition_dist
      by presburger
  qed
  from a_in_A
  have "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a"
    using invar_dr equiv_rel cls pass_to_quotient invariance_is_congruence
    by blast
  moreover have "\<forall> x. x \<in> fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a \<longleftrightarrow> x \<in> \<R>\<^sub>\<Q> r d C A"
  proof
    fix x :: "'r"
    have "(x \<in> fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a) =
       (x \<in> \<Union> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d
                         (singleton_set_system (limit_set (alts_\<E> a) UNIV)) a))"
      using \<R>\<^sub>\<W>_is_minimizer
      by metis
    also have "... = ({x} \<in> minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d
                         (singleton_set_system (limit_set (alts_\<E> a) UNIV)) a)"
      using singleton_set_union
      unfolding minimizer.simps arg_min_set.simps is_arg_min_def
      by auto
    also have "... = ({x} \<in> singleton_set_system (limit_set (alts_\<E> a) UNIV) \<and>
          (\<forall> y' \<in> singleton_set_system (limit_set (alts_\<E> a) UNIV).
            Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) {x}) \<le>
            Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y')))"
      using minimizer_helper
      by (metis (no_types, lifting))
    also have "... = ({x} \<in> singleton_set_system (limit_set\<^sub>\<Q> A UNIV) \<and>
          (\<forall> y' \<in> singleton_set_system (limit_set\<^sub>\<Q> A UNIV).
            Inf (inf_dist\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) {x}) \<le>
            Inf (inf_dist\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C) y')))"
      using valid_res_eq inf_le_iff
      by blast
    also have "... =
        ({x} \<in> minimizer (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C)
                              (inf_dist\<^sub>\<Q> d) (singleton_set_system (limit_set\<^sub>\<Q> A UNIV)) A)"
      using minimizer_helper
      by (metis (no_types, lifting))
    also have "... = (x \<in> \<Union> (minimizer (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (\<K>_els\<^sub>\<Q> r C)
                               (inf_dist\<^sub>\<Q> d) (singleton_set_system (limit_set\<^sub>\<Q> A UNIV)) A))"
      using singleton_set_union
      unfolding minimizer.simps arg_min_set.simps is_arg_min_def
      by auto
    finally show "(x \<in> fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a) = (x \<in> \<R>\<^sub>\<Q> r d C A)"
      unfolding \<R>\<^sub>\<Q>.simps
      by blast
  qed
  ultimately show "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = \<R>\<^sub>\<Q> r d C A"
    by blast
qed

theorem (in result) invar_dr_simple_dist_imp_quotient_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    r :: "('a, 'v) Election rel" and
    X :: "('a, 'v) Election set" and
    A :: "('a, 'v) Election set"
  assumes
    simple: "simple r X d" and
    closed_domain: "closed_under_restr_rel r X (\<K>_els C)" and
    invar_res: "satisfies (\<lambda> E. limit_set (alts_\<E> E) UNIV) (Invariance r)" and
    invar_C: "satisfies (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (Invariance (Restr r (\<K>_els C)))" and
    invar_dr: "satisfies (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance r)" and
    cls: "A \<in> X // r" and
    equiv_rel: "equiv X r" and
    cons_subset: "\<K>_els C \<subseteq> X"
  shows "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)) A = distance_\<R>\<^sub>\<Q> r d C A"
proof -
  have "\<forall> E. fun\<^sub>\<E> (distance_\<R> d C) E =
          (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E, limit_set (alts_\<E> E) UNIV - fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E, {})"
    by simp
  moreover have "\<forall> E \<in> A. fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E = \<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A"
    using invar_dr invariance_is_congruence pass_to_quotient cls equiv_rel
    by blast
  moreover have "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = \<R>\<^sub>\<Q> r d C A"
    using invar_dr_simple_dist_imp_quotient_dr_winners assms
    by blast
  moreover have
    "\<forall> E \<in> A. limit_set (alts_\<E> E) UNIV = \<pi>\<^sub>\<Q> (\<lambda> E. limit_set (alts_\<E> E) UNIV) A"
    using invar_res invariance_is_congruence' pass_to_quotient cls equiv_rel
    by blast
  ultimately have all_eq:
    "\<forall> E \<in> A. fun\<^sub>\<E> (distance_\<R> d C) E =
      (\<R>\<^sub>\<Q> r d C A, \<pi>\<^sub>\<Q> (\<lambda> E. limit_set (alts_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A, {})"
    by fastforce
  hence
    "{(\<R>\<^sub>\<Q> r d C A, \<pi>\<^sub>\<Q> (\<lambda> E. limit_set (alts_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A, {})} \<supseteq>
      fun\<^sub>\<E> (distance_\<R> d C) ` A"
    by blast
  moreover have "A \<noteq> {}"
    using cls equiv_rel in_quotient_imp_non_empty
    by metis
  ultimately have single_img:
    "{(\<R>\<^sub>\<Q> r d C A, \<pi>\<^sub>\<Q> (\<lambda> E. limit_set (alts_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A, {})} =
      fun\<^sub>\<E> (distance_\<R> d C) ` A"
    using empty_is_image subset_singletonD
    by (metis (no_types, lifting))
  moreover from this
  have "card (fun\<^sub>\<E> (distance_\<R> d C) ` A) = 1"
    using is_singleton_altdef is_singletonI
    by (metis (no_types, lifting))
  moreover from this single_img
  have "the_inv (\<lambda> x. {x}) (fun\<^sub>\<E> (distance_\<R> d C) ` A) =
          (\<R>\<^sub>\<Q> r d C A, \<pi>\<^sub>\<Q> (\<lambda> E. limit_set (alts_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A, {})"
    using singleton_insert_inj_eq singleton_set.elims singleton_set_def_if_card_one
    by (metis (no_types))
  ultimately show "?thesis"
    unfolding distance_\<R>\<^sub>\<Q>.simps
    using \<pi>\<^sub>\<Q>.simps[of "fun\<^sub>\<E> (distance_\<R> d C)"] singleton_set.simps[of "fun\<^sub>\<E> (distance_\<R> d C) ` A"]
    by presburger
qed

end
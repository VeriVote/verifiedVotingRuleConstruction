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
  "relation_paths r = {p. \<exists>k. (length p = 2*k \<and> (\<forall>i < k. (p!(2*i), p!(2*i+1)) \<in> r))}"

fun admissible_paths :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x set \<Rightarrow> 'x list set" where
  "admissible_paths r X Y = {x#p@[y] | x y p. x \<in> X \<and> y \<in> Y \<and> p \<in> relation_paths r}"

fun path_length :: "'x list \<Rightarrow> 'x Distance \<Rightarrow> ereal" where
  "path_length [] d = 0" |
  "path_length [x] d = 0" |
  "path_length (x#y#xs) d = d x y + path_length xs d"

fun quotient_dist :: "'x rel \<Rightarrow> 'x Distance \<Rightarrow> 'x set Distance" where
  "quotient_dist r d A B = Inf (\<Union>{{path_length p d | p. p \<in> admissible_paths r A B}})"

fun inf_dist\<^sub>\<Q> :: "'x Distance \<Rightarrow> 'x set Distance" where
  "inf_dist\<^sub>\<Q> d A B = Inf {d a b |a b. a \<in> A \<and> b \<in> B}"

fun simple :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> bool" where
  "simple r X d = (\<forall>A B. A \<in> X // r \<and> B \<in> X // r \<longrightarrow> quotient_dist r d A B = inf_dist\<^sub>\<Q> d A B)"

fun product_rel' :: "'x rel \<Rightarrow> ('x * 'x) rel" where
  "product_rel' r = {(pair1, pair2). ((fst pair1, fst pair2) \<in> r \<and> snd pair1 = snd pair2) \<or>
                                    ((snd pair1, snd pair2) \<in> r \<and> fst pair1 = fst pair2)}"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma tot_dist_invariance_is_congruence:
  fixes
    d :: "'x Distance" and
    r :: "'x rel"
  shows
    "(totally_invariant_dist d r) = (dist\<^sub>\<T> d respects (product_rel r))"
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
  shows
    "\<forall>A B. A \<in> X // r \<and> B \<in> X // r \<longrightarrow> (\<forall>a b. a \<in> A \<and> b \<in> B \<longrightarrow> dist\<^sub>\<Q> d A B = d a b)"
proof (safe)
  fix
    A :: "'x set" and
    B :: "'x set" and
    a :: 'x and
    b :: 'x
  assume
    "a \<in> A" and
    "b \<in> B" and
    "A \<in> X // r" and
    "B \<in> X // r"
  hence "A = r `` {a} \<and> B = r `` {b}"
    using assms
    by (meson equiv_class_eq_iff quotientI quotient_eq_iff rev_ImageI singleton_iff)
  hence "A \<times> B = (product_rel r) `` {(a, b)}"
    unfolding product_rel'.simps
    by auto
  hence "A \<times> B \<in> (X \<times> X) // (product_rel r)"
    unfolding quotient_def
    using \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>A \<in> X // r\<close> \<open>B \<in> X // r\<close> assms Union_quotient 
    by fastforce
  moreover have "equiv (X \<times> X) (product_rel r)"
    using assms product_rel_helper
    by (metis UNIV_Times_UNIV equivE equivI)
  moreover have "dist\<^sub>\<T> d respects (product_rel r)"
    using assms tot_dist_invariance_is_congruence[of d r]
    by blast
  moreover have "dist\<^sub>\<Q> d A B = \<pi>\<^sub>\<Q> (dist\<^sub>\<T> d) (A \<times> B)"
    using \<open>a \<in> A\<close> \<open>b \<in> B\<close>
    by auto
  ultimately have "\<forall>(x, y) \<in> A \<times> B. dist\<^sub>\<Q> d A B = d x y"
    unfolding dist\<^sub>\<Q>.simps
    using assms pass_to_quotient
    by fastforce
  thus "dist\<^sub>\<Q> d A B = d a b"
    using \<open>a \<in> A\<close> \<open>b \<in> B\<close>
    by blast
qed

lemma relation_paths_subset:
  fixes
    n :: nat and
    p :: "'x list" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    "r \<subseteq> X \<times> X"
  shows
    "\<forall>p. p \<in> relation_paths r \<longrightarrow> (\<forall>i < length p. p!i \<in> X)"
proof (safe)
  fix
    p :: "'x list" and
    i :: nat
  assume
    "p \<in> relation_paths r" and
    range: "i < length p"
  then obtain k :: nat where 
    len: "length p = 2*k" and rel: "\<forall>i < k. (p!(2*i), p!(2*i+1)) \<in> r" 
    by auto
  obtain k' :: nat where
    i_cases: "i = 2*k' \<or> i = 2*k' + 1"
    by (metis diff_Suc_1 even_Suc oddE odd_two_times_div_two_nat)
  with len range have "k' < k"
    by linarith
  hence "(p!(2*k'), p!(2*k'+1)) \<in> r"
    using rel
    by blast
  hence "p!(2*k') \<in> X \<and> p!(2*k'+1) \<in> X"
    using assms rel
    by blast
  thus "p!i \<in> X"
    using i_cases
    by blast
qed

thm "path_length.induct"

lemma admissible_path_len: 
  fixes
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    "refl_on X r" and
    "triangle_ineq X d" and
    "totally_invariant_dist d r"
  shows
    "\<forall>p a b. p \<in> relation_paths r \<and> a \<in> X \<and> b \<in> X \<longrightarrow> path_length (a#p@[b]) d \<ge> d a b"
  sorry (* induction *)

lemma quotient_dist_coincides_with_dist\<^sub>\<Q>:
  fixes
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    equiv: "equiv X r" and
    tri: "triangle_ineq X d" and
    invar: "totally_invariant_dist d r"
  shows
    "\<forall>A \<in> X // r. \<forall>B \<in> X // r. quotient_dist r d A B = dist\<^sub>\<Q> d A B"
proof (clarify)
  fix
    A :: "'x set" and
    B :: "'x set"
  assume
    "A \<in> X // r" and
    "B \<in> X // r"
  then obtain a :: 'x and b :: 'x where
    el: "a \<in> A \<and> b \<in> B" and def_dist: "dist\<^sub>\<Q> d A B = d a b"
    using dist_pass_to_quotient assms in_quotient_imp_non_empty
    by (metis (full_types) ex_in_conv)
  hence equiv_cls: "A = r `` {a} \<and> B = r `` {b}"
    using \<open>A \<in> X // r\<close> \<open>B \<in> X // r\<close> assms equiv_class_eq_iff 
          equiv_class_self quotientI quotient_eq_iff
    by meson
  have subset_X: "r \<subseteq> X \<times> X \<and> A \<subseteq> X \<and> B \<subseteq> X"
    using assms \<open>A \<in> X // r\<close> \<open>B \<in> X // r\<close> equiv_def refl_on_def Union_quotient Union_upper
    by metis
  have
    "\<forall>p \<in> admissible_paths r A B. (\<exists>p' x y. x \<in> A \<and> y \<in> B \<and> p' \<in> relation_paths r \<and> p = x#p'@[y])"
    unfolding admissible_paths.simps
    by blast
  moreover have "\<forall>x y. x \<in> A \<and> y \<in> B \<longrightarrow> d x y = d a b"
    using invar equiv_cls                 
    by auto
  moreover have "refl_on X r"
    using equiv equiv_def 
    by blast
  ultimately have "\<forall>p. p \<in> admissible_paths r A B \<longrightarrow> path_length p d \<ge> d a b"
    using admissible_path_len[of X r d] tri subset_X el invar
    by (metis in_mono)
  hence "\<forall>l. l \<in> \<Union> {{path_length p d |p. p \<in> admissible_paths r A B}} \<longrightarrow> l \<ge> d a b"
    by blast
  hence geq: "quotient_dist r d A B \<ge> d a b"
    using quotient_dist.simps[of r d A B]
    by (simp add: le_Inf_iff)
  with el def_dist 
  have geq: "quotient_dist r d A B \<ge> dist\<^sub>\<Q> d A B"
    by presburger
  have "[a, b] \<in> admissible_paths r A B"
    using el
    by simp
  moreover have "path_length [a, b] d = d a b"
    by simp
  ultimately have "quotient_dist r d A B \<le> d a b"
    using quotient_dist.simps[of r d A B]  CollectI Inf_lower ccpo_Sup_singleton
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
  shows
    "\<forall>A \<in> X // r. \<forall>B \<in> X // r. inf_dist\<^sub>\<Q> d A B = dist\<^sub>\<Q> d A B"
proof (clarify)
  fix
    A :: "'x set" and
    B :: "'x set"
  assume
    "A \<in> X // r" and
    "B \<in> X // r"
  then obtain a :: 'x and b :: 'x where
    el: "a \<in> A \<and> b \<in> B" and def_dist: "dist\<^sub>\<Q> d A B = d a b"
    using dist_pass_to_quotient assms in_quotient_imp_non_empty
    by (metis (full_types) ex_in_conv)
  have "\<forall>x y. x \<in> A \<and> y \<in> B \<longrightarrow> d x y = d a b"
    using def_dist dist_pass_to_quotient assms \<open>A \<in> X // r\<close> \<open>B \<in> X // r\<close>
    by force
  hence "{d x y |x y. x \<in> A \<and> y \<in> B} = {d a b}"
    using el
    by blast
  thus "inf_dist\<^sub>\<Q> d A B = dist\<^sub>\<Q> d A B"   
    unfolding inf_dist\<^sub>\<Q>.simps
    using def_dist
    by simp
qed

lemma tot_invar_dist_simple: 
  fixes
    d :: "'x Distance" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    "equiv X r" and
    "triangle_ineq X d" and
    "totally_invariant_dist d r"
  shows
    "simple r X d"
proof (unfold simple.simps, clarify)
  fix
    A :: "'x set" and
    B :: "'x set"
  assume
    "A \<in> X // r" and
    "B \<in> X // r"
  thus "quotient_dist r d A B = inf_dist\<^sub>\<Q> d A B"
    using assms inf_dist_coincides_with_dist\<^sub>\<Q>[of X r d] 
          quotient_dist_coincides_with_dist\<^sub>\<Q>[of X r d]
    by metis
qed

subsection \<open>Quotient Consensus and Results\<close>

fun \<K>_els\<^sub>\<Q> :: 
  "('a, 'v) Election rel \<Rightarrow> ('a, 'v, 'r Result) Consensus_Class \<Rightarrow> ('a, 'v) Election set set" where
  "\<K>_els\<^sub>\<Q> r C = {r `` {E} | E. E \<in> \<K>_els C}"

fun C\<^sub>\<Q> :: "('a, 'v, 'r Result) Consensus_Class \<Rightarrow> (('a, 'v) Election set \<Rightarrow> 'r Result)" where
  "C\<^sub>\<Q> C = \<pi>\<^sub>\<Q> (fun\<^sub>\<E> (rule_\<K> C))"

fun (in result) limit_set\<^sub>\<Q> :: "('a, 'v) Election set \<Rightarrow> 'r set \<Rightarrow> 'r set" where
  "limit_set\<^sub>\<Q> X res = \<Inter>{limit_set (alts_\<E> E) res | E. E \<in> X}"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma (in result) limit_set_invar: 
  fixes
    d :: "('a, 'v) Election Distance" and
    r :: "('a, 'v) Election rel" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    X :: "('a, 'v) Election set" and
    A :: "('a, 'v) Election set"
  assumes
    "A \<in> X // r" and equiv_rel: "equiv X r" and cons_subset: "\<K>_els C \<subseteq> X" and
    "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance r)"
  shows 
    "\<forall>a \<in> A. limit_set (alts_\<E> a) UNIV = limit_set\<^sub>\<Q> A UNIV"
  sorry

lemma (in result) preimg_invar: 
  fixes
    d :: "('a, 'v) Election Distance" and
    r :: "('a, 'v) Election rel" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    X :: "('a, 'v) Election set" and
    A :: "('a, 'v) Election set"
  assumes
    "A \<in> X // r" and equiv_rel: "equiv X r" and cons_subset: "\<K>_els C \<subseteq> X" and
    "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance r)"
  shows 
    "\<forall>a \<in> A. (\<forall>y. d a ` (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y) =
                  (dist\<^sub>\<Q> d) A ` (preimg (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) y))"
  sorry

subsection \<open>Quotient Distance Rationalization\<close>

text \<open>
  Hadjibeyli and Wilson 2016 4.9
\<close>

theorem (in result) invar_dr_imp_quotient_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    r :: "('a, 'v) Election rel" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    X :: "('a, 'v) Election set" and
    A :: "('a, 'v) Election set"
  assumes
    invar_C: "satisfies (fun\<^sub>\<E> (rule_\<K> C)) (Invariance r)" and
    invar_d: "totally_invariant_dist d r" and 
    invar_res: "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance r)" and
    cls: "A \<in> X // r" and equiv_rel: "equiv X r" and cons_subset: "\<K>_els C \<subseteq> X"    
  shows
    "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = 
      \<Union>(minimizer (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) (dist\<^sub>\<Q> d) (set_to_set_set (limit_set\<^sub>\<Q> A UNIV)) A)"
proof -
  have "A \<noteq> {}"
    using equiv_rel cls
    by (simp add: in_quotient_imp_non_empty)
  then obtain a :: "('a, 'v) Election" where "a \<in> A"
    by blast
  have "restr_refl_on (\<K>_els C) r"
    using equiv_rel cons_subset 
    unfolding equiv_def
    by (meson in_mono refl_onD restr_refl_on.elims(3))
  hence "satisfies (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance r)"
    using tot_invar_dist_imp_invar_dr_rule assms
    by blast
  hence "satisfies (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance r)"
    by simp
  hence "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a"
    using equiv_rel cls pass_to_quotient invariance_is_congruence \<open>a \<in> A\<close>
    by blast
  also have 
    "fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a = \<Union>(minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d 
                                    (set_to_set_set (limit_set (alts_\<E> a) UNIV)) a)"
    using \<R>\<^sub>\<W>_is_minimizer
    by metis
  also have "minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d 
                       (set_to_set_set (limit_set (alts_\<E> a) UNIV)) a =
    arg_min_set (closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) 
                (\<K>_els C) d a) (set_to_set_set (limit_set (alts_\<E> a) UNIV))"
    by simp
  also have "... = arg_min_set (closest_preimg_dist (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) 
                               (dist\<^sub>\<Q> d) A) (set_to_set_set (limit_set\<^sub>\<Q> A UNIV))"
  proof (safe)
    fix 
      x :: "'r set"
    assume min_el: "x \<in> 
      arg_min_set (closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d a)
                  (set_to_set_set (limit_set (alts_\<E> a) UNIV))"
    hence "\<forall>y \<in> set_to_set_set (limit_set (alts_\<E> a) UNIV). 
      Inf (d a ` (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y)) \<ge> 
      Inf (d a ` (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) x))"
      unfolding closest_preimg_dist.simps arg_min_set.simps
      by (simp add: is_arg_min_linorder)
    hence "\<forall>y \<in> set_to_set_set (limit_set\<^sub>\<Q> A UNIV). 
      Inf (d a ` (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) y)) \<ge> 
      Inf (d a ` (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) x))"
      using assms limit_set_invar \<open>a \<in> A\<close>
      by (metis (mono_tags, lifting))
    hence "\<forall>y \<in> set_to_set_set (limit_set\<^sub>\<Q> A UNIV). 
      Inf ((dist\<^sub>\<Q> d) A ` (preimg (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) y)) \<ge> 
      Inf ((dist\<^sub>\<Q> d) A ` (preimg (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) x))"
      using assms preimg_invar \<open>a \<in> A\<close>
      by (metis (mono_tags, lifting))
    hence min: "\<forall>y \<in> set_to_set_set (limit_set\<^sub>\<Q> A UNIV).
      closest_preimg_dist (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) (dist\<^sub>\<Q> d) A x \<le>
      closest_preimg_dist (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) (dist\<^sub>\<Q> d) A y"
      by auto
    have "x \<in> set_to_set_set (limit_set (alts_\<E> a) UNIV)"
      using min_el
      unfolding arg_min_set.simps
      by (meson CollectD is_arg_min_linorder)
    hence "x \<in> set_to_set_set (limit_set\<^sub>\<Q> A UNIV)"
      using assms limit_set_invar \<open>a \<in> A\<close>
      by (metis (mono_tags, lifting))
    with min show "x \<in> 
      arg_min_set (closest_preimg_dist (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) (dist\<^sub>\<Q> d) A)
                  (set_to_set_set (limit_set\<^sub>\<Q> A UNIV))"
      unfolding arg_min_set.simps
      by (metis (no_types, lifting) CollectI is_arg_min_linorder)
  next
    fix 
      x :: "'r set"
    assume "x \<in> 
      arg_min_set (closest_preimg_dist (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) (dist\<^sub>\<Q> d) A)
                  (set_to_set_set (limit_set\<^sub>\<Q> A UNIV))"
    show "x \<in> 
      arg_min_set (closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<Union> (range (\<K>\<^sub>\<E> C))) d a)
                  (set_to_set_set (limit_set (alts_\<E> a) UNIV))"
      sorry
  qed
  also have "... = 
    minimizer (elect_r \<circ> C\<^sub>\<Q> C) (\<K>_els\<^sub>\<Q> r C) (dist\<^sub>\<Q> d) (set_to_set_set (limit_set\<^sub>\<Q> A UNIV)) A"
    by simp
  finally show ?thesis
    by simp
qed                                      

end
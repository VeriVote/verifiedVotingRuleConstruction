(*  File:       Distance_Rationalization_Symmetry.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Symmetry in Distance-Rationalizable Rules\<close>

theory Distance_Rationalization_Symmetry
  imports Distance_Rationalization
begin

subsection \<open>Minimizer Function\<close>

fun distance_infimum :: "'a Distance \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ereal" where
  "distance_infimum d A a = Inf (d a ` A)"

fun closest_preimg_distance :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a Distance \<Rightarrow>
        'a \<Rightarrow> 'b \<Rightarrow> ereal" where
  "closest_preimg_distance f domain\<^sub>f d a b =
      distance_infimum d (preimg f domain\<^sub>f b) a"

fun minimizer :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a Distance \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "minimizer f domain\<^sub>f d A a =
      arg_min_set (closest_preimg_distance f domain\<^sub>f d a) A"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma rewrite_arg_min_set:
  fixes
    f :: "'a \<Rightarrow> 'b::linorder" and
    A :: "'a set"
  shows "arg_min_set f A = \<Union> (preimg f A ` {y \<in> (f ` A). \<forall> z \<in> f ` A. y \<le> z})"
proof (safe)
  fix x :: "'a"
  assume arg_min: "x \<in> arg_min_set f A"
  hence "is_arg_min f (\<lambda> a. a \<in> A) x"
    by simp
  hence "\<forall> x' \<in> A. f x' \<ge> f x"
    by (simp add: is_arg_min_linorder)
  hence "\<forall> z \<in> f ` A. f x \<le> z"
    by blast
  moreover have "f x \<in> f ` A"
    using arg_min
    by (simp add: is_arg_min_linorder)
  ultimately have "f x \<in> {y \<in> f ` A. \<forall> z \<in> f ` A. y \<le> z}"
    by blast
  moreover have "x \<in> preimg f A (f x)"
    using arg_min
    by (simp add: is_arg_min_linorder)
  ultimately show "x \<in> \<Union> (preimg f A ` {y \<in> (f ` A). \<forall> z \<in> f ` A. y \<le> z})"
    by blast
next
  fix x x' b :: "'a"
  assume
    same_img: "x \<in> preimg f A (f x')" and
    min: "\<forall> z \<in> f ` A. f x' \<le> z"
  hence "f x = f x'"
    by simp
  hence "\<forall> z \<in> f ` A. f x \<le> z"
    using min
    by simp
  moreover have "x \<in> A"
    using same_img
    by simp
  ultimately show "x \<in> arg_min_set f A"
    by (simp add: is_arg_min_linorder)
qed

subsubsection \<open>Equivariance\<close>

abbreviation Restrp :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" where
  "Restrp r A \<equiv> r Int (A \<times> UNIV)"

lemma restr_induced_rel:
  fixes
    A :: "'a set" and
    B B' :: "'b set" and
    \<phi> :: "('a, 'b) binary_fun"
  assumes "B' \<subseteq> B"
  shows "Restrp (action_induced_rel A B \<phi>) B' = action_induced_rel A B' \<phi>"
  using assms
  by auto

theorem group_action_invar_dist_and_equivar_f_imp_equivar_minimizer:
  fixes
    f :: "'a \<Rightarrow> 'b" and
    domain\<^sub>f X :: "'a set" and
    d :: "'a Distance" and
    well_formed_img :: "'a \<Rightarrow> 'b set" and
    G :: "'c monoid" and
    \<phi> :: "('c, 'a) binary_fun" and
    \<psi> :: "('c, 'b) binary_fun"
  defines "equivar_prop_set_valued \<equiv>
      action_induced_equivariance (carrier G) X \<phi> (set_action \<psi>)"
  assumes
    action_\<phi>: "group_action G X \<phi>" and
    group_action_res: "group_action G UNIV \<psi>" and
    dom_in_X: "domain\<^sub>f \<subseteq> X" and
    closed_domain: (* Could the closed_domain requirement be weakened? *)
      "closed_restricted_rel (action_induced_rel (carrier G) X \<phi>) X domain\<^sub>f" and
    equivar_img: "is_symmetry well_formed_img equivar_prop_set_valued" and
    invar_d: "invariance\<^sub>\<D> d (carrier G) X \<phi>" and
    equivar_f:
      "is_symmetry f (action_induced_equivariance (carrier G) domain\<^sub>f \<phi> \<psi>)"
  shows "is_symmetry (\<lambda> x. minimizer f domain\<^sub>f d (well_formed_img x) x) equivar_prop_set_valued"
proof (unfold action_induced_equivariance_def equivar_prop_set_valued_def is_symmetry.simps
              set_action.simps minimizer.simps, clarify)
  fix
    x :: "'a" and
    g :: "'c"
  assume
    group_elem: "g \<in> carrier G" and
    x_in_X: "x \<in> X"
  hence img_X: "\<phi> g x \<in> X"
    using action_\<phi> group_action.element_image
    by metis
  let ?x' = "\<phi> g x"
  let ?c = "closest_preimg_distance f domain\<^sub>f d x" and
      ?c' = "closest_preimg_distance f domain\<^sub>f d ?x'"
  have "\<forall> y. preimg f domain\<^sub>f y \<subseteq> X"
    using dom_in_X
    by fastforce
  hence invar_dist_img:
    "\<forall> y. d x ` (preimg f domain\<^sub>f y) = d ?x' ` (\<phi> g ` (preimg f domain\<^sub>f y))"
    using x_in_X group_elem invar_dist_image invar_d action_\<phi>
    by metis
  have "\<forall> y. preimg f domain\<^sub>f (\<psi> g y) = (\<phi> g) ` (preimg f domain\<^sub>f y)"
    using group_action_equivar_f_imp_equivar_preimg[of G X \<phi> \<psi> domain\<^sub>f f g]
          assms group_elem
    by blast
  hence "\<forall> y. d ?x' ` preimg f domain\<^sub>f (\<psi> g y) =
      d ?x' ` (\<phi> g) ` (preimg f domain\<^sub>f y)"
    by presburger
  hence "\<forall> y. Inf (d ?x' ` preimg f domain\<^sub>f (\<psi> g y)) =
      Inf (d x ` preimg f domain\<^sub>f y)"
    using invar_dist_img
    by metis
  hence "\<forall> y. distance_infimum d (preimg f domain\<^sub>f (\<psi> g y)) ?x' =
      distance_infimum d (preimg f domain\<^sub>f y) x"
    by simp
  hence "\<forall> y. closest_preimg_distance f domain\<^sub>f d ?x' (\<psi> g y) =
                closest_preimg_distance f domain\<^sub>f d x y"
    by simp
  hence comp:
    "closest_preimg_distance f domain\<^sub>f d x =
          (closest_preimg_distance f domain\<^sub>f d ?x') \<circ> (\<psi> g)"
    by auto
  hence "\<forall> Y \<alpha>. preimg ?c' (\<psi> g ` Y) \<alpha> = \<psi> g ` preimg ?c Y \<alpha>"
    using preimg_comp
    by auto
  hence "\<forall> Y A. {preimg ?c' (\<psi> g ` Y) \<alpha> | \<alpha>. \<alpha> \<in> A} =
      {\<psi> g ` preimg ?c Y \<alpha> | \<alpha>. \<alpha> \<in> A}"
    by simp
  moreover have
    "\<forall> Y A. {\<psi> g ` preimg ?c Y \<alpha> | \<alpha>. \<alpha> \<in> A} = {\<psi> g ` \<beta> | \<beta>. \<beta> \<in> preimg ?c Y ` A}"
    by blast
  moreover have
    "\<forall> Y A. preimg ?c' (\<psi> g ` Y) ` A = {preimg ?c' (\<psi> g ` Y) \<alpha> | \<alpha>. \<alpha> \<in> A}"
    by blast
  ultimately have
    "\<forall> Y A. preimg ?c' (\<psi> g ` Y) ` A = {\<psi> g ` \<alpha> | \<alpha>. \<alpha> \<in> preimg ?c Y ` A}"
    by simp
  hence "\<forall> Y A. \<Union> (preimg ?c' (\<psi> g ` Y) ` A) =
              \<Union> {\<psi> g ` \<alpha> | \<alpha>. \<alpha> \<in> preimg ?c Y ` A}"
    by simp
  moreover have
    "\<forall> Y A. \<Union> {\<psi> g ` \<alpha> | \<alpha>. \<alpha> \<in> preimg ?c Y ` A} = \<psi> g ` \<Union> (preimg ?c Y ` A)"
    by blast
  ultimately have eq_preimg_unions:
    "\<forall> Y A. \<Union> (preimg ?c' (\<psi> g ` Y) ` A) = \<psi> g ` \<Union> (preimg ?c Y ` A)"
    by simp
  have "\<forall> Y. ?c' ` \<psi> g ` Y = ?c ` Y"
    using comp
    unfolding image_comp
    by simp
  hence "\<forall> Y. {\<alpha> \<in> ?c ` Y. \<forall> \<beta> \<in> ?c ` Y. \<alpha> \<le> \<beta>} =
            {\<alpha> \<in> ?c' ` \<psi> g ` Y. \<forall> \<beta> \<in> ?c' ` \<psi> g ` Y. \<alpha> \<le> \<beta>}"
    by simp
  hence "\<forall> Y. arg_min_set (closest_preimg_distance f domain\<^sub>f d ?x') (\<psi> g ` Y) =
            (\<psi> g) ` (arg_min_set (closest_preimg_distance f domain\<^sub>f d x) Y)"
    using rewrite_arg_min_set[of ?c'] rewrite_arg_min_set[of ?c] eq_preimg_unions
    by presburger
  moreover have "well_formed_img (\<phi> g x) = \<psi> g ` well_formed_img x"
    using equivar_img x_in_X group_elem img_X rewrite_equivariance
    unfolding equivar_prop_set_valued_def set_action.simps
    by metis
  ultimately show
    "arg_min_set (closest_preimg_distance f domain\<^sub>f d (\<phi> g x))
      (well_formed_img (\<phi> g x)) =
          \<psi> g ` arg_min_set (closest_preimg_distance f domain\<^sub>f d x)
            (well_formed_img x)"
    by presburger
qed

subsubsection \<open>Invariance\<close>

lemma closest_dist_invar_under_refl_rel_and_tot_invar_dist:
  fixes
    f :: "'a \<Rightarrow> 'b" and
    domain\<^sub>f :: "'a set" and
    d :: "'a Distance" and
    rel :: "'a rel"
  assumes
    r_refl: "reflp_on' domain\<^sub>f (Restrp rel domain\<^sub>f)" and
    tot_invar_d: "total_invariance\<^sub>\<D> d rel"
  shows "is_symmetry (closest_preimg_distance f domain\<^sub>f d) (Invariance rel)"
proof (unfold is_symmetry.simps, intro allI impI ext)
  fix
    a b :: "'a" and
    y :: "'b"
  assume rel: "(a, b) \<in> rel"
  have "\<forall> c \<in> domain\<^sub>f. (c, c) \<in> rel"
    using r_refl
    unfolding reflp_on'_def reflp_on_def
    by simp
  hence "\<forall> c \<in> domain\<^sub>f. d a c = d b c"
    using rel tot_invar_d
    unfolding rewrite_total_invariance\<^sub>\<D>
    by blast
  thus "closest_preimg_distance f domain\<^sub>f d a y =
          closest_preimg_distance f domain\<^sub>f d b y"
    by simp
qed

lemma refl_rel_and_tot_invar_dist_imp_invar_minimizer:
 fixes
    f :: "'a \<Rightarrow> 'b" and
    domain\<^sub>f :: "'a set" and
    d :: "'a Distance" and
    rel :: "'a rel" and
    img :: "'b set"
  assumes
    r_refl: "reflp_on' domain\<^sub>f (Restrp rel domain\<^sub>f)" and
    tot_invar_d: "total_invariance\<^sub>\<D> d rel"
  shows "is_symmetry (minimizer f domain\<^sub>f d img) (Invariance rel)"
proof -
  have "is_symmetry (closest_preimg_distance f domain\<^sub>f d) (Invariance rel)"
    using r_refl tot_invar_d closest_dist_invar_under_refl_rel_and_tot_invar_dist
    by metis
  thus ?thesis
    by simp
qed

theorem group_act_invar_dist_and_invar_f_imp_invar_minimizer:
  fixes
    f :: "'a \<Rightarrow> 'b" and
    domain\<^sub>f A :: "'a set" and
    d :: "'a Distance" and
    img :: "'b set" and
    G :: "'c monoid" and
    \<phi> :: "('c, 'a) binary_fun"
  defines
    "rel \<equiv> action_induced_rel (carrier G) A \<phi>" and
    "rel' \<equiv> action_induced_rel (carrier G) domain\<^sub>f \<phi>"
  assumes
    action_\<phi>: "group_action G A \<phi>" and
    "domain\<^sub>f \<subseteq> A" and
    closed_domain: "closed_restricted_rel rel A domain\<^sub>f" and
    (* Could the closed_domain requirement be weakened? *)
    invar_d: "invariance\<^sub>\<D> d (carrier G) A \<phi>" and
    invar_f: "is_symmetry f (Invariance rel')"
  shows "is_symmetry (minimizer f domain\<^sub>f d img) (Invariance rel)"
proof -
  let
    ?\<psi> = "\<lambda> g. id" and
    ?img = "\<lambda> x. img"
  have "is_symmetry f (action_induced_equivariance (carrier G) domain\<^sub>f \<phi> ?\<psi>)"
    using invar_f rewrite_invar_as_equivar
    unfolding rel'_def
    by blast
  moreover have "group_action G UNIV ?\<psi>"
    using const_id_is_group_action action_\<phi>
    unfolding group_action_def group_hom_def
    by blast
  moreover have
    "is_symmetry ?img (action_induced_equivariance (carrier G) A \<phi> (set_action ?\<psi>))"
    unfolding action_induced_equivariance_def
    by fastforce
  ultimately have
    "is_symmetry (\<lambda> x. minimizer f domain\<^sub>f d (?img x) x)
              (action_induced_equivariance (carrier G) A \<phi> (set_action ?\<psi>))"
    using assms
          group_action_invar_dist_and_equivar_f_imp_equivar_minimizer[of
            G A \<phi> ?\<psi> domain\<^sub>f ?img d f]
    by blast
  hence "is_symmetry (minimizer f domain\<^sub>f d img)
                  (action_induced_equivariance (carrier G) A \<phi> (set_action ?\<psi>))"
    by blast
  thus ?thesis
    unfolding rel_def set_action.simps
    using rewrite_invar_as_equivar image_id
    by metis
qed

subsection \<open>Minimizer Translation\<close>

lemma \<K>\<^sub>\<E>_is_preimg:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    E :: "('a, 'v) Election" and
    w :: "'r"
  shows "preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) {w} = \<K>\<^sub>\<E> C w"
proof -
  have "preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) {w} =
    {E \<in> elections_\<K> C. (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) E = {w}}"
    by simp
  also have
    "{E \<in> elections_\<K> C. (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) E = {w}} =
        {E \<in> elections_\<K> C.
          elect (rule_\<K> C) (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E) = {w}}"
    by simp
  also have
    "{E \<in> elections_\<K> C.
        elect (rule_\<K> C) (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E) = {w}} =
      elections_\<K> C
        \<inter> {E. elect (rule_\<K> C) (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E) = {w}}"
    by blast
  also have
    "elections_\<K> C
      \<inter> {E. elect (rule_\<K> C)
          (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E) = {w}} =
      \<K>\<^sub>\<E> C w"
  proof
    show
      "elections_\<K> C
        \<inter> {E. elect (rule_\<K> C) (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E) = {w}}
          \<subseteq> \<K>\<^sub>\<E> C w"
      unfolding \<K>\<^sub>\<E>.simps
      by force
  next
    have
      "\<forall> E \<in> \<K>\<^sub>\<E> C w. E \<in> {E. elect (rule_\<K> C) (voters_\<E> E)
        (alternatives_\<E> E) (profile_\<E> E) = {w}}"
      unfolding \<K>\<^sub>\<E>.simps
      by force
    hence
      "\<forall> E \<in> \<K>\<^sub>\<E> C w.
        E \<in> elections_\<K> C
          \<inter> {E. elect (rule_\<K> C)
              (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E) = {w}}"
      by simp
    thus "\<K>\<^sub>\<E> C w \<subseteq> elections_\<K> C \<inter> {E. elect (rule_\<K> C) (voters_\<E> E)
            (alternatives_\<E> E) (profile_\<E> E) = {w}}"
      by blast
  qed
  finally show "preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) {w} = \<K>\<^sub>\<E> C w"
    by simp
qed

lemma score_is_closest_preimg_dist:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    E :: "('a, 'v) Election" and
    w :: "'r"
  shows "score d C E w =
      closest_preimg_distance (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E {w}"
proof -
  have "score d C E w = Inf (d E ` (\<K>\<^sub>\<E> C w))"
    by simp
  also have "\<K>\<^sub>\<E> C w = preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) {w}"
    using \<K>\<^sub>\<E>_is_preimg
    by metis
  also have
    "Inf (d E ` (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) {w})) =
        closest_preimg_distance (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E {w}"
    by simp
  finally show ?thesis
    by simp
qed

lemma (in result) \<R>\<^sub>\<W>_is_minimizer:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class"
  shows "fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) =
    (\<lambda> E. \<Union> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d
                      (singleton_set_system (limit (alternatives_\<E> E) UNIV)) E))"
proof
  fix E :: "('a, 'v) Election"
  let ?min = "(minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d
                          (singleton_set_system (limit (alternatives_\<E> E) UNIV)) E)"
  have "?min =
    arg_min_set
      (closest_preimg_distance (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E)
          (singleton_set_system (limit (alternatives_\<E> E) UNIV))"
    by simp
  also have
    "\<dots> = singleton_set_system
            (arg_min_set (score d C E) (limit (alternatives_\<E> E) UNIV))"
  proof (safe)
    fix R :: "'r set"
    assume
      min: "R \<in> arg_min_set
                  (closest_preimg_distance
              (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E)
                    (singleton_set_system (limit (alternatives_\<E> E) UNIV))"
    hence "R \<in> singleton_set_system (limit (alternatives_\<E> E) UNIV)"
      using arg_min_subset subsetD
      by (metis (no_types, lifting))
    then obtain r :: "'r" where
      res_singleton: "R = {r}" and
      r_in_lim_set: "r \<in> limit (alternatives_\<E> E) UNIV"
      by auto
    have "\<nexists> R'. R' \<in> singleton_set_system (limit (alternatives_\<E> E) UNIV)
          \<and> closest_preimg_distance
                (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E R'
            < closest_preimg_distance
                (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E R"
      using min arg_min_set.simps is_arg_min_def CollectD
      by (metis (mono_tags, lifting))
    hence "\<nexists> r'. r' \<in> limit (alternatives_\<E> E) UNIV
        \<and> closest_preimg_distance
              (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E {r'}
          < closest_preimg_distance
              (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E {r}"
      using res_singleton
      by auto
    hence
      "\<nexists> r'. r' \<in> limit (alternatives_\<E> E) UNIV
            \<and> score d C E r' < score d C E r"
      using score_is_closest_preimg_dist
      by metis
    hence "r \<in> arg_min_set (score d C E) (limit (alternatives_\<E> E) UNIV)"
      using r_in_lim_set arg_min_set.simps is_arg_min_def CollectI
      by metis
    thus "R \<in> singleton_set_system
                (arg_min_set (score d C E) (limit (alternatives_\<E> E) UNIV))"
      using res_singleton
      by simp
  next
    fix R :: "'r set"
    assume
      "R \<in> singleton_set_system
              (arg_min_set (score d C E) (limit (alternatives_\<E> E) UNIV))"
    then obtain r :: "'r" where
      res_singleton: "R = {r}" and
      r_min_lim_set:
        "r \<in> arg_min_set (score d C E) (limit (alternatives_\<E> E) UNIV)"
      by auto
    hence "\<nexists> r'. r' \<in> limit (alternatives_\<E> E) UNIV
                \<and> score d C E r' < score d C E r"
      using CollectD arg_min_set.simps is_arg_min_def
      by metis
    hence
      "\<nexists> r'. r' \<in> limit (alternatives_\<E> E) UNIV
          \<and> closest_preimg_distance
                (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E {r'}
            < closest_preimg_distance
                (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E {r}"
      using score_is_closest_preimg_dist
      by metis
    moreover have
      "\<forall> R' \<in> singleton_set_system (limit (alternatives_\<E> E) UNIV).
            \<exists> r' \<in> limit (alternatives_\<E> E) UNIV. R' = {r'}"
      by auto
    ultimately have
      "\<nexists> R'. R' \<in> singleton_set_system (limit (alternatives_\<E> E) UNIV)
          \<and> closest_preimg_distance
                (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E R'
            < closest_preimg_distance
                (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E R"
      using res_singleton
      by auto
    moreover have
      "R \<in> singleton_set_system (limit (alternatives_\<E> E) UNIV)"
      using r_min_lim_set res_singleton arg_min_subset
      by fastforce
    ultimately show
      "R \<in> arg_min_set
              (closest_preimg_distance
                (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d E)
              (singleton_set_system (limit (alternatives_\<E> E) UNIV))"
      using arg_min_set.simps is_arg_min_def CollectI
      by (metis (mono_tags, lifting))
  qed
  also have
    "(arg_min_set (score d C E) (limit (alternatives_\<E> E) UNIV)) =
        fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E"
    by simp
  finally have "\<Union> ?min = \<Union> (singleton_set_system (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E))"
    by presburger
  thus "fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E = \<Union> ?min"
    using un_left_inv_singleton_set_system
    by auto
qed

subsubsection \<open>Invariance\<close>

theorem (in result) tot_invar_dist_imp_invar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    rel :: "('a, 'v) Election rel"
  assumes
    r_refl: "reflp_on' (elections_\<K> C) (Restrp rel (elections_\<K> C))" and
    tot_invar_d: "total_invariance\<^sub>\<D> d rel" and
    invar_res:
      "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV) (Invariance rel)"
  shows "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance rel)"
proof -
  let ?min =
    "\<lambda> E. \<Union> \<circ> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d
            (singleton_set_system (limit (alternatives_\<E> E) UNIV)))"
  have "\<forall> E. is_symmetry (?min E) (Invariance rel)"
    using r_refl tot_invar_d invar_comp
          refl_rel_and_tot_invar_dist_imp_invar_minimizer[of
            "elections_\<K> C" rel d "elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)"]
    by blast
  moreover have "is_symmetry ?min (Invariance rel)"
    using invar_res
    by auto
  ultimately have "is_symmetry (\<lambda> E. ?min E E) (Invariance rel)"
    using invar_parameterized_fun[of ?min rel]
    by blast
  also have "(\<lambda> E. ?min E E) = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer
    unfolding comp_def fun\<^sub>\<E>.simps
    by metis
  finally have invar_\<R>\<^sub>\<W>: "is_symmetry (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance rel)"
    by simp
  hence
    "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV - fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E)
            (Invariance rel)"
    using invar_res
    by fastforce
  thus "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance rel)"
    using invar_\<R>\<^sub>\<W>
    by auto
qed

theorem (in result) invar_dist_cons_imp_invar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    G :: "'b monoid" and
    \<phi> :: "('b, ('a, 'v) Election) binary_fun" and
    B :: "('a, 'v) Election set"
  defines
    "rel \<equiv> action_induced_rel (carrier G) B \<phi>" and
    "rel' \<equiv> action_induced_rel (carrier G) (elections_\<K> C) \<phi>"
  assumes
    action_\<phi>: "group_action G B \<phi>" and
    consensus_C_in_B: "elections_\<K> C \<subseteq> B" and
    closed_domain: (* Could the closed_domain requirement be weakened? *)
      "closed_restricted_rel rel B (elections_\<K> C)" and
    invar_res:
      "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV) (Invariance rel)" and
    invar_d: "invariance\<^sub>\<D> d (carrier G) B \<phi>" and
    invar_C_winners: "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (Invariance rel')"
  shows "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance rel)"
proof -
  let ?min =
    "\<lambda> E. \<Union> \<circ> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d
                (singleton_set_system (limit (alternatives_\<E> E) UNIV)))"
  have "\<forall> E. is_symmetry (?min E) (Invariance rel)"
    using action_\<phi> closed_domain consensus_C_in_B invar_d invar_C_winners
          group_act_invar_dist_and_invar_f_imp_invar_minimizer rel_def
          rel'_def invar_comp
    by (metis (no_types, lifting))
  moreover have "is_symmetry ?min (Invariance rel)"
    using invar_res
    by auto
  ultimately have
    "is_symmetry (\<lambda> E. ?min E E) (Invariance rel)"
    using invar_parameterized_fun[of ?min _]
    by blast
  also have "(\<lambda> E. ?min E E) = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer
    unfolding comp_def fun\<^sub>\<E>.simps
    by metis
  finally have invar_\<R>\<^sub>\<W>:
    "is_symmetry (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance rel)"
    by simp
  hence "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV -
    fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E) (Invariance rel)"
    using invar_res
    by fastforce
  thus "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance rel)"
    using invar_\<R>\<^sub>\<W>
    by simp
qed

subsubsection \<open>Equivariance\<close>

theorem (in result) invar_dist_equivar_cons_imp_equivar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    G :: "'b monoid" and
    \<phi> :: "('b, ('a, 'v) Election) binary_fun" and
    \<psi> :: "('b, 'r) binary_fun" and
    B :: "('a, 'v) Election set"
  defines
    "rel \<equiv> action_induced_rel (carrier G) B \<phi>" and
    "rel' \<equiv> action_induced_rel (carrier G) (elections_\<K> C) \<phi>" and
    "equivar_prop \<equiv>
      action_induced_equivariance (carrier G) (elections_\<K> C)
        \<phi> (set_action \<psi>)" and
    "equivar_prop_global_set_valued \<equiv>
        action_induced_equivariance (carrier G) B \<phi> (set_action \<psi>)" and
    "equivar_prop_global_result_valued \<equiv>
        action_induced_equivariance (carrier G) B \<phi> (result_action \<psi>)"
  assumes
    action_\<phi>: "group_action G B \<phi>" and
    group_act_res: "group_action G UNIV \<psi>" and
    cons_elect_set: "elections_\<K> C \<subseteq> B" and
    closed_domain: "closed_restricted_rel rel B (elections_\<K> C)" and
    equivar_res: (* Could the closed_domain requirement be weakened? *)
      "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV)
          equivar_prop_global_set_valued" and
    invar_d: "invariance\<^sub>\<D> d (carrier G) B \<phi>" and
    equivar_C_winners: "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) equivar_prop"
  shows "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) equivar_prop_global_result_valued"
proof -
  let ?min_E =
    "\<lambda> E. minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d
            (singleton_set_system (limit (alternatives_\<E> E) UNIV)) E"
  let ?min =
    "\<lambda> E. \<Union> \<circ> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d
            (singleton_set_system (limit (alternatives_\<E> E) UNIV)))"
  let ?\<psi>' = "set_action (set_action \<psi>)"
  let ?equivar_prop_global_set_valued' =
          "action_induced_equivariance (carrier G) B \<phi> ?\<psi>'"
  have "\<forall> E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
          singleton_set_system (limit (alternatives_\<E> (\<phi> g E)) UNIV) =
            {{r} | r. r \<in> limit (alternatives_\<E> (\<phi> g E)) UNIV}"
    by simp
  moreover have
    "\<forall> E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
        limit (alternatives_\<E> (\<phi> g E)) UNIV =
              \<psi> g ` (limit (alternatives_\<E> E) UNIV)"
    using equivar_res action_\<phi> group_action.element_image
    unfolding equivar_prop_global_set_valued_def action_induced_equivariance_def
    by fastforce
  ultimately have "\<forall> E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
      singleton_set_system (limit (alternatives_\<E> (\<phi> g E)) UNIV) =
        {{r} | r. r \<in> \<psi> g ` (limit (alternatives_\<E> E) UNIV)}"
    by simp
  moreover have
    "\<forall> E g. {{r} | r. r \<in> \<psi> g ` (limit (alternatives_\<E> E) UNIV)} =
          {\<psi> g ` {r} | r. r \<in> limit (alternatives_\<E> E) UNIV}"
    by blast
  moreover have
    "\<forall> E g. {\<psi> g ` {r} | r. r \<in> limit (alternatives_\<E> E) UNIV} =
          ?\<psi>' g {{r} | r. r \<in> limit (alternatives_\<E> E) UNIV}"
    unfolding set_action.simps
    by blast
  ultimately have
    "is_symmetry (\<lambda> E. singleton_set_system (limit (alternatives_\<E> E) UNIV))
                      ?equivar_prop_global_set_valued'"
    using rewrite_equivariance[of
            "\<lambda> E. singleton_set_system (limit (alternatives_\<E> E) UNIV)"
            "carrier G" B \<phi> ?\<psi>']
    by force
  moreover have "group_action G UNIV (set_action \<psi>)"
    unfolding set_action.simps
    using group_act_induces_set_group_act[of _ UNIV _] group_act_res
    by simp
  ultimately have "is_symmetry ?min_E ?equivar_prop_global_set_valued'"
    using action_\<phi> invar_d cons_elect_set closed_domain equivar_C_winners
          group_action_invar_dist_and_equivar_f_imp_equivar_minimizer[of
              G B \<phi> "set_action \<psi>" "elections_\<K> C"
              "\<lambda> E. singleton_set_system (limit (alternatives_\<E> E) UNIV)"
              d "elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)"]
    unfolding rel'_def rel_def equivar_prop_def
    by metis
  moreover have
    "is_symmetry
      \<Union> (action_induced_equivariance
            (carrier G) UNIV ?\<psi>' (set_action \<psi>))"
    using equivar_union_under_image_action[of _ \<psi>]
    by simp
  ultimately have "is_symmetry (\<Union> \<circ> ?min_E) equivar_prop_global_set_valued"
    unfolding equivar_prop_global_set_valued_def
    using equivar_ind_by_action_comp[of _ _ UNIV]
    by simp
  moreover have "(\<lambda> E. ?min E E) = \<Union> \<circ> ?min_E"
    unfolding comp_def
    by simp
  ultimately have
    "is_symmetry (\<lambda> E. ?min E E) equivar_prop_global_set_valued"
    by simp
  moreover have "(\<lambda> E. ?min E E) = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer
    unfolding comp_def fun\<^sub>\<E>.simps
    by metis
  ultimately have equivar_\<R>\<^sub>\<W>:
    "is_symmetry (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) equivar_prop_global_set_valued"
    by simp
  moreover have "\<forall> g \<in> carrier G. bij (\<psi> g)"
    using group_act_res
    unfolding bij_betw_def
    by (simp add: group_action.inj_prop group_action.surj_prop)
  ultimately have
    "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV - fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E)
        equivar_prop_global_set_valued"
    using equivar_res equivar_set_minus
    unfolding action_induced_equivariance_def set_action.simps
              equivar_prop_global_set_valued_def
    by blast
  thus "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) equivar_prop_global_result_valued"
    using equivar_\<R>\<^sub>\<W>
    unfolding equivar_prop_global_result_valued_def
              equivar_prop_global_set_valued_def
              rewrite_equivariance
    by simp
qed

subsection \<open>Inference Rules\<close>

theorem (in result) anon_dist_and_cons_imp_anon_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class"
  assumes
    anon_d: "distance_anonymity' well_formed_elections d" and
    anon_C: "consensus_rule_anonymity' (elections_\<K> C) C" and
    closed_C: "closed_restricted_rel (anonymity\<^sub>\<R> well_formed_elections)
                  well_formed_elections (elections_\<K> C)"
    shows "anonymity' well_formed_elections (distance_\<R> d C)"
proof -
  have "\<forall> \<pi>. \<forall> E \<in> elections_\<K> C.
      \<phi>_anon (elections_\<K> C) \<pi> E = \<phi>_anon well_formed_elections \<pi> E"
    using cons_domain_valid extensional_continuation_subset
    unfolding \<phi>_anon.simps
    by metis
  hence "action_induced_rel (carrier anonymity\<^sub>\<G>) (elections_\<K> C)
            (\<phi>_anon well_formed_elections) =
      action_induced_rel (carrier anonymity\<^sub>\<G>) (elections_\<K> C)
          (\<phi>_anon (elections_\<K> C))"
    using coinciding_actions_ind_equal_rel
    by metis
  hence "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
          (Invariance (action_induced_rel
            (carrier anonymity\<^sub>\<G>) (elections_\<K> C) (\<phi>_anon well_formed_elections)))"
    using anon_C
    unfolding consensus_rule_anonymity'.simps anonymity\<^sub>\<R>.simps
    by presburger
  thus ?thesis
    using cons_domain_valid assms anonymous_group_action.group_action_axioms
          anonymity invar_dist_cons_imp_invar_dr_rule
    unfolding distance_anonymity'.simps anonymity\<^sub>\<R>.simps anonymity'.simps
              consensus_rule_anonymity'.simps
    by blast
qed

theorem (in result_properties) neutr_dist_and_cons_imp_neutr_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'b Result) Consensus_Class"
  assumes
    neutral_d: "distance_neutrality well_formed_elections d" and
    neutral_C: "consensus_rule_neutrality (elections_\<K> C) C" and
    closed_C: "closed_restricted_rel (neutrality\<^sub>\<R> well_formed_elections)
                  well_formed_elections (elections_\<K> C)"
  shows "neutrality well_formed_elections (distance_\<R> d C)"
proof -
  have "\<forall> \<pi>. \<forall> E \<in> elections_\<K> C.
      \<phi>_neutral well_formed_elections \<pi> E = \<phi>_neutral (elections_\<K> C) \<pi> E"
    using cons_domain_valid extensional_continuation_subset
    unfolding \<phi>_neutral.simps
    by metis
  hence "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
          (action_induced_equivariance (carrier neutrality\<^sub>\<G>) (elections_\<K> C)
            (\<phi>_neutral well_formed_elections) (set_action \<psi>_neutral))"
    using neutral_C equivar_ind_by_act_coincide
    unfolding consensus_rule_neutrality.simps
    by (metis (no_types, lifting))
  thus ?thesis
    using neutral_d closed_C \<phi>_neutral_action.group_action_axioms
          neutrality action_neutral cons_domain_valid[of C]
          invar_dist_equivar_cons_imp_equivar_dr_rule[of
            _ _ "\<phi>_neutral well_formed_elections"]
    by simp
qed

theorem reversal_sym_dist_and_cons_imp_reversal_sym_dr:
  fixes
    d :: "('a, 'c) Election Distance" and
    C :: "('a, 'c, 'a rel Result) Consensus_Class"
  assumes
    reverse_sym_d: "distance_reversal_symmetry well_formed_elections d" and
    reverse_sym_C: "consensus_rule_reversal_symmetry (elections_\<K> C) C" and
    closed_C: "closed_restricted_rel (reversal\<^sub>\<R> well_formed_elections)
                  well_formed_elections (elections_\<K> C)"
  shows "reversal_symmetry well_formed_elections (\<S>\<W>\<F>_result.distance_\<R> d C)"
proof -
  have "\<forall> \<pi>. \<forall> E \<in> elections_\<K> C.
      \<phi>_reverse well_formed_elections \<pi> E = \<phi>_reverse (elections_\<K> C) \<pi> E"
    using cons_domain_valid extensional_continuation_subset
    unfolding \<phi>_reverse.simps
    by metis
  hence "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
          (action_induced_equivariance (carrier reversal\<^sub>\<G>) (elections_\<K> C)
            (\<phi>_reverse well_formed_elections) (set_action \<psi>_reverse))"
    using reverse_sym_C equivar_ind_by_act_coincide
    unfolding consensus_rule_reversal_symmetry.simps
    by (metis (no_types, lifting))
  thus ?thesis
    using \<S>\<W>\<F>_result.invar_dist_equivar_cons_imp_equivar_dr_rule
          reversal_symmetry cons_domain_valid reverse_sym_d closed_C
          \<phi>_reverse_action.group_action_axioms
          \<psi>_reverse_action.group_action_axioms
    unfolding reversal_symmetry_def reversal\<^sub>\<R>.simps
              distance_reversal_symmetry.simps
    by metis
qed

theorem (in result) tot_hom_dist_imp_hom_dr:
  fixes
    d :: "('a, nat) Election Distance" and
    C :: "('a, nat, 'r Result) Consensus_Class"
  assumes "distance_homogeneity finite_elections_\<V> d"
  shows "homogeneity finite_elections_\<V> (distance_\<R> d C)"
proof -
  have "Restrp (homogeneity\<^sub>\<R> finite_elections_\<V>) (elections_\<K> C) =
          homogeneity\<^sub>\<R> (elections_\<K> C)"
    using cons_domain_finite
    unfolding homogeneity\<^sub>\<R>.simps finite_elections_\<V>_def
    by blast
  hence "reflp_on' (elections_\<K> C)
      (Restrp (homogeneity\<^sub>\<R> finite_elections_\<V>) (elections_\<K> C))"
    using refl_homogeneity\<^sub>\<R>[of "elections_\<K> C"] cons_domain_finite[of C]
    by presburger
  moreover have
    "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV)
        (Invariance (homogeneity\<^sub>\<R> finite_elections_\<V>))"
    using homogeneity
    by simp
  ultimately show ?thesis
    using assms tot_invar_dist_imp_invar_dr_rule
    unfolding distance_homogeneity_def homogeneity.simps
    by blast
qed

theorem (in result) tot_hom_dist_imp_hom_dr':
  fixes
    d :: "('a, 'v::linorder) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class"
  assumes "distance_homogeneity' finite_elections_\<V> d"
  shows "homogeneity' finite_elections_\<V> (distance_\<R> d C)"
proof (unfold homogeneity'.simps)
  have "Restrp (homogeneity\<^sub>\<R>' finite_elections_\<V>) (elections_\<K> C) =
          homogeneity\<^sub>\<R>' (elections_\<K> C)"
    using cons_domain_finite
    unfolding homogeneity\<^sub>\<R>'.simps finite_elections_\<V>_def
    by blast
  hence "reflp_on' (elections_\<K> C)
      (Restrp (homogeneity\<^sub>\<R>' finite_elections_\<V>) (elections_\<K> C))"
    using refl_homogeneity\<^sub>\<R>'[of "elections_\<K> C"] cons_domain_finite[of C]
    by presburger
  moreover have
    "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV)
        (Invariance (homogeneity\<^sub>\<R>' finite_elections_\<V>))"
    using homogeneity'
    by simp
  ultimately show
    "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance (homogeneity\<^sub>\<R>' finite_elections_\<V>))"
    using assms tot_invar_dist_imp_invar_dr_rule
    unfolding distance_homogeneity'_def
    by blast
qed

subsection \<open>Properties\<close>

fun decisiveness :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election Distance \<Rightarrow>
        ('a, 'v, 'r Result) Electoral_Module \<Rightarrow> bool" where
  "decisiveness X d m =
    (\<nexists> E. E \<in> X \<and> (\<exists> \<delta> > 0. \<forall> E' \<in> X. d E E' < \<delta> \<longrightarrow> card (elect_r (fun\<^sub>\<E> m E')) > 1))"

end
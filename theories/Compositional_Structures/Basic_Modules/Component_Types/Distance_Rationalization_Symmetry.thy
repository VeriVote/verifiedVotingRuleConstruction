section \<open>Symmetry in Distance-Rationalizable Rules\<close>

theory Distance_Rationalization_Symmetry
  imports Distance_Rationalization
begin 

subsection \<open>Minimizer function\<close>

fun inf_dist :: "'x Distance \<Rightarrow> 'x set \<Rightarrow> 'x \<Rightarrow> ereal" where
  "inf_dist d X a = Inf (d a ` X)"

fun closest_preimg_dist :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> ereal" where
  "closest_preimg_dist f domain\<^sub>f d x y = inf_dist d (preimg f domain\<^sub>f y) x"

fun minimizer :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> 'y set \<Rightarrow> 'x \<Rightarrow> 'y set" where
  "minimizer f domain\<^sub>f d Y x = arg_min_set (closest_preimg_dist f domain\<^sub>f d x) Y"
(* arg_min instead of arg_min_set? *)

subsubsection \<open>Auxiliary Lemmas\<close>

lemma rewrite_arg_min_set:
  fixes
    f :: "'x \<Rightarrow> 'y::linorder" and
    X :: "'x set"
  shows
    "arg_min_set f X = \<Union>(preimg f X ` {y \<in> (f ` X). \<forall>z \<in> f ` X. y \<le> z})"
proof (safe)
  fix
    x :: 'x
  assume 
    arg_min: "x \<in> arg_min_set f X"
  hence "is_arg_min f (\<lambda>a. a \<in> X) x"
    by simp
  hence "\<forall>x' \<in> X. f x' \<ge> f x"
    by (simp add: is_arg_min_linorder)
  hence "\<forall>z \<in> f ` X. f x \<le> z"
    by blast
  moreover have "f x \<in> f ` X"
    using arg_min
    by (simp add: is_arg_min_linorder)
  ultimately have "f x \<in> {y \<in> f ` X. \<forall>z \<in> f ` X. y \<le> z}"
    by blast
  moreover have "x \<in> preimg f X (f x)"
    using arg_min
    by (simp add: is_arg_min_linorder)
  ultimately show "x \<in> \<Union>(preimg f X ` {y \<in> (f ` X). \<forall>z \<in> f ` X. y \<le> z})"
    by blast
next
  fix
    x :: 'x and x' :: 'x and b :: 'x
  assume
    same_img: "x \<in> preimg f X (f x')" and
    min: "\<forall>z \<in> f ` X. f x' \<le> z"
  hence "f x = f x'"
    by simp
  hence "\<forall>z \<in> f ` X. f x \<le> z"
    using min
    by simp
  moreover have "x \<in> X"
    using same_img
    by simp
  ultimately show "x \<in> arg_min_set f X"
    by (simp add: is_arg_min_linorder)
qed

subsubsection \<open>Equivariance\<close>

theorem grp_act_invar_dist_and_equivar_f_imp_equivar_minimizer:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    d :: "'x Distance" and
    img :: "'x \<Rightarrow> 'y set" and
    X :: "'x set" and
    G :: "'z monoid" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  defines
    "rel \<equiv> rel_induced_by_action (carrier G) X \<phi>" and
    "restr_rel \<equiv> rel_induced_by_action (carrier G) domain\<^sub>f \<phi>" and
    "equivar_prop \<equiv> equivar_ind_by_act (carrier G) domain\<^sub>f \<phi> \<psi>" and
    "equivar_prop_global_set_valued \<equiv> equivar_ind_by_act (carrier G) X \<phi> (set_action \<psi>)"
  assumes        
    grp_act: "group_action G X \<phi>" and grp_act_res: "group_action G UNIV \<psi>" and
    "domain\<^sub>f \<subseteq> X" and closed_domain: "rel \<inter> (domain\<^sub>f \<times> X) \<subseteq> restr_rel" and
    (* Could the closed_domain requirement be weakened? *)
    equivar_img: "satisfies img equivar_prop_global_set_valued" and
    invar_d: "invariant_dist d (carrier G) X \<phi>" and
    equivar_f: "satisfies f equivar_prop"
  shows 
    "satisfies (\<lambda>x. minimizer f domain\<^sub>f d (img x) x) equivar_prop_global_set_valued"
proof (unfold equivar_prop_global_set_valued_def equivar_ind_by_act_def, 
        simp del: arg_min_set.simps, clarify)
  fix    
    x :: 'x and g :: 'z
  assume
    grp_el: "g \<in> carrier G" and "x \<in> X" and img_X: "\<phi> g x \<in> X"
  let ?x' = "\<phi> g x"
  let ?c = "closest_preimg_dist f domain\<^sub>f d x" and
      ?c' = "closest_preimg_dist f domain\<^sub>f d ?x'"
  have "\<forall>y. preimg f domain\<^sub>f y \<subseteq> X"
    using \<open>domain\<^sub>f \<subseteq> X\<close>
    by auto
  hence invar_dist_img: 
    "\<forall>y. d x ` (preimg f domain\<^sub>f y) = d ?x' ` (\<phi> g ` (preimg f domain\<^sub>f y))"
    using \<open>x \<in> X\<close> grp_el invar_dist_image invar_d grp_act
    by metis
  have "\<forall>y. preimg f domain\<^sub>f (\<psi> g y) = (\<phi> g) ` (preimg f domain\<^sub>f y)"
    using equivar_preimg[of G X \<phi> \<psi> domain\<^sub>f f g] assms grp_el 
    by fastforce
  \<comment> \<open>We want to apply lemma rewrite_arg_min_set to show that the arg_min_set for
    ?x' is the image of the arg_min_set for ?x under \<psi> g, thus showing equivariance
    of the minimizer function.\<close>
  hence "\<forall>y. d ?x' ` preimg f domain\<^sub>f (\<psi> g y) = d ?x' ` (\<phi> g) ` (preimg f domain\<^sub>f y)"
    by presburger
  hence "\<forall>y. Inf (d ?x' ` preimg f domain\<^sub>f (\<psi> g y)) = Inf (d x ` preimg f domain\<^sub>f y)"
    by (metis invar_dist_img)
  hence
    "\<forall>y. inf_dist d (preimg f domain\<^sub>f (\<psi> g y)) ?x' = inf_dist d (preimg f domain\<^sub>f y) x"
    by simp
  hence
    "\<forall>y. closest_preimg_dist f domain\<^sub>f d ?x' (\<psi> g y)
          = closest_preimg_dist f domain\<^sub>f d x y"
    by simp
  hence comp:
    "closest_preimg_dist f domain\<^sub>f d x = (closest_preimg_dist f domain\<^sub>f d ?x') \<circ> (\<psi> g)"
    by auto
  hence "\<forall> Y \<alpha>. preimg ?c' (\<psi> g ` Y) \<alpha> = \<psi> g ` preimg ?c Y \<alpha>"
    using preimg_comp
    by auto
  hence 
    "\<forall> Y A. {preimg ?c' (\<psi> g ` Y) \<alpha> | \<alpha>. \<alpha> \<in> A} = {\<psi> g ` preimg ?c Y \<alpha> | \<alpha>. \<alpha> \<in> A}"
    by simp
  moreover have "\<forall> Y A. {\<psi> g ` preimg ?c Y \<alpha> | \<alpha>. \<alpha> \<in> A} = {\<psi> g ` \<beta> | \<beta>. \<beta> \<in> preimg ?c Y ` A}"
    by blast
  moreover have "\<forall> Y A. preimg ?c' (\<psi> g ` Y) ` A = {preimg ?c' (\<psi> g ` Y) \<alpha> | \<alpha>. \<alpha> \<in> A}"
    by blast
  ultimately have
    "\<forall> Y A. preimg ?c' (\<psi> g ` Y) ` A = {\<psi> g ` \<alpha> | \<alpha>. \<alpha> \<in> preimg ?c Y ` A}"
    by simp
  hence "\<forall> Y A. \<Union>(preimg ?c' (\<psi> g ` Y) ` A) = \<Union>{\<psi> g ` \<alpha> | \<alpha>. \<alpha> \<in> preimg ?c Y ` A}"      
    by simp
  moreover have 
    "\<forall> Y A. \<Union>{\<psi> g ` \<alpha> | \<alpha>. \<alpha> \<in> preimg ?c Y ` A} = \<psi> g ` \<Union>(preimg ?c Y ` A)"
    by blast
  ultimately have eq_preimg_unions:
    "\<forall> Y A. \<Union>(preimg ?c' (\<psi> g ` Y) ` A) = \<psi> g ` \<Union>(preimg ?c Y ` A)"    
    by simp
  have "\<forall> Y. ?c' ` \<psi> g ` Y = ?c ` Y"
    using comp
    by (simp add: image_comp)
  hence
    "\<forall> Y. {\<alpha> \<in> ?c ` Y. \<forall>\<beta> \<in> ?c ` Y. \<alpha> \<le> \<beta>} =
            {\<alpha> \<in> ?c' ` \<psi> g ` Y. \<forall>\<beta> \<in> ?c' ` \<psi> g ` Y. \<alpha> \<le> \<beta>}"
    by simp
  hence
    "\<forall> Y. arg_min_set (closest_preimg_dist f domain\<^sub>f d ?x') (\<psi> g ` Y) = 
            (\<psi> g) ` (arg_min_set (closest_preimg_dist f domain\<^sub>f d x) Y)"
    using rewrite_arg_min_set[of ?c'] rewrite_arg_min_set[of ?c] eq_preimg_unions
    by presburger
  moreover have "img (\<phi> g x) = \<psi> g ` img x"
    using equivar_img \<open>x \<in> X\<close> grp_el img_X rewrite_equivar_ind_by_act
    unfolding equivar_prop_global_set_valued_def set_action.simps
    by metis
  ultimately show
    "arg_min_set (closest_preimg_dist f domain\<^sub>f d (\<phi> g x)) (img (\<phi> g x)) =
       \<psi> g ` arg_min_set (closest_preimg_dist f domain\<^sub>f d x) (img x)"
    by presburger
qed

subsubsection \<open>Invariance\<close>

lemma closest_dist_invar_under_refl_rel_and_tot_invar_dist:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    d :: "'x Distance" and
    rel :: "'x rel"
  assumes
    r_refl: "restr_refl_on domain\<^sub>f rel" and
    tot_invar_d: "totally_invariant_dist d rel"
  shows "satisfies (closest_preimg_dist f domain\<^sub>f d) (Invariance rel)"
proof (simp, safe, standard)
  fix
    a :: 'x and
    b :: 'x and
    y :: 'y
  assume 
    rel: "(a,b) \<in> rel"
  have "\<forall> c \<in> domain\<^sub>f. (c,c) \<in> rel"
    using r_refl 
    by (simp add: refl_onD)
  hence "\<forall> c \<in> domain\<^sub>f. d a c = d b c"
    using rel tot_invar_d
    unfolding rewrite_totally_invariant_dist
    by blast
  thus "closest_preimg_dist f domain\<^sub>f d a y = closest_preimg_dist f domain\<^sub>f d b y"
    by simp
qed

lemma minimizer_invar_under_refl_rel_and_tot_invar_dist:
 fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    d :: "'x Distance" and
    rel :: "'x rel" and
    img :: "'y set"
  assumes
    r_refl: "restr_refl_on domain\<^sub>f rel" and
    tot_invar_d: "totally_invariant_dist d rel"
  shows "satisfies (minimizer f domain\<^sub>f d img) (Invariance rel)"
proof -
  have "satisfies (closest_preimg_dist f domain\<^sub>f d) (Invariance rel)"
    using r_refl tot_invar_d
    by (rule closest_dist_invar_under_refl_rel_and_tot_invar_dist)
  moreover have "minimizer f domain\<^sub>f d img = 
    (\<lambda>x. arg_min_set x img) \<circ> (closest_preimg_dist f domain\<^sub>f d)"
    unfolding comp_def
    by auto
  ultimately show ?thesis
    using invar_comp
    by simp
qed

theorem monoid_tot_invar_dist_imp_invar_minimizer:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    d :: "'x Distance" and
    img :: "'y set" and
    X :: "'x set" and
    G :: "'z monoid" and
    \<phi> :: "('z, 'x) binary_fun"
  defines
    "rel \<equiv> rel_induced_by_action (carrier G) X \<phi>"
  assumes        
    hom: "\<phi> \<in> hom G (map_monoid X)" and
    one: "\<phi> \<one>\<^bsub>G\<^esub> = \<one>\<^bsub>map_monoid X\<^esub>" and
    "monoid G" and "domain\<^sub>f \<subseteq> X" and
    tot_invar_d: "totally_invariant_dist d rel"
  shows "satisfies (minimizer f domain\<^sub>f d img) (Invariance rel)"
proof -
  have "refl_on X rel" 
    using \<open>monoid G\<close> hom one rel_induced_by_monoid_action_refl 
    unfolding rel_def 
    by blast
  hence "restr_refl_on domain\<^sub>f rel"
    using \<open>domain\<^sub>f \<subseteq> X\<close>
    by (simp add: refl_on_def subset_eq)
  thus ?thesis
    using tot_invar_d
    by (rule minimizer_invar_under_refl_rel_and_tot_invar_dist)
qed

theorem grp_act_invar_dist_and_invar_f_imp_invar_minimizer:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    d :: "'x Distance" and
    img :: "'y set" and
    X :: "'x set" and
    G :: "'z monoid" and
    \<phi> :: "('z, 'x) binary_fun"
  defines
    "rel \<equiv> rel_induced_by_action (carrier G) X \<phi>" and
    "restr_rel \<equiv> rel_induced_by_action (carrier G) domain\<^sub>f \<phi>"
  assumes        
    grp_act: "group_action G X \<phi>" and "domain\<^sub>f \<subseteq> X" and
    closed_domain: "rel \<inter> (domain\<^sub>f \<times> X) \<subseteq> restr_rel" and 
    (* Could the closed_domain requirement be weakened? *)
    invar_d: "invariant_dist d (carrier G) X \<phi>" and
    invar_f: "satisfies f (Invariance restr_rel)"
  shows "satisfies (minimizer f domain\<^sub>f d img) (Invariance rel)"
proof -
  let ?\<psi> = "\<lambda>g. id" and ?img = "\<lambda>x. img"
  have "satisfies f (equivar_ind_by_act (carrier G) domain\<^sub>f \<phi> ?\<psi>)"
    using invar_f rewrite_invar_as_equivar
    unfolding restr_rel_def 
    by blast
  moreover have "group_action G UNIV ?\<psi>"
    using const_id_is_grp_act grp_act
    unfolding group_action_def group_hom_def
    by blast
  moreover have 
    "satisfies ?img (equivar_ind_by_act (carrier G) X \<phi> (set_action ?\<psi>))"
    unfolding equivar_ind_by_act_def
    by fastforce
  ultimately have
    "satisfies (\<lambda>x. minimizer f domain\<^sub>f d (?img x) x)
              (equivar_ind_by_act (carrier G) X \<phi> (set_action ?\<psi>))"
    using assms 
          grp_act_invar_dist_and_equivar_f_imp_equivar_minimizer[of G X \<phi> ?\<psi> domain\<^sub>f ?img d f]
    by blast
  hence "satisfies (minimizer f domain\<^sub>f d img)
                  (equivar_ind_by_act (carrier G) X \<phi> (set_action ?\<psi>))"
    by blast
  thus ?thesis
    unfolding rel_def set_action.simps
    using rewrite_invar_as_equivar 
    by (metis image_id)
qed

subsection \<open>Distance Rationalization as Minimizer\<close>

lemma \<K>\<^sub>\<E>_is_preimg:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    E :: "('a, 'v) Election" and
    w :: 'r
  shows 
    "preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) {w} = \<K>\<^sub>\<E> C w"
proof -
  have "preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) {w} = 
    {E \<in> \<K>_els C. (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) E = {w}}"
    by simp
  also have "{E \<in> \<K>_els C. (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) E = {w}} =
    {E \<in> \<K>_els C. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
    by simp
  also have "{E \<in> \<K>_els C. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}} =
    \<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
    by blast
  also have 
    "\<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}} = \<K>\<^sub>\<E> C w"
  proof (standard)
    show 
      "\<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}} \<subseteq> \<K>\<^sub>\<E> C w"
      unfolding \<K>\<^sub>\<E>.simps
      by force
  next
    have "\<forall>E \<in> \<K>\<^sub>\<E> C w. E \<in> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
      unfolding \<K>\<^sub>\<E>.simps
      by force
    hence "\<forall>E \<in> \<K>\<^sub>\<E> C w. E \<in> 
      \<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
      by simp
    thus "\<K>\<^sub>\<E> C w \<subseteq> \<K>_els C \<inter> {E. elect (rule_\<K> C) (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = {w}}"
      by blast
  qed
  finally show "preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) {w} = \<K>\<^sub>\<E> C w"
    by simp
qed
   
lemma score_is_closest_preimg_dist:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    E :: "('a, 'v) Election" and
    w :: 'r
  shows
    "score d C E w = closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E {w}"
proof -
  have "score d C E w = Inf (d E ` (\<K>\<^sub>\<E> C w))" by simp
  also have "\<K>\<^sub>\<E> C w = preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) {w}"
    using \<K>\<^sub>\<E>_is_preimg
    by metis
  also have "Inf (d E ` (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) {w}))
              = closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E {w}"
    by simp
  finally show ?thesis
    by simp
qed

lemma (in result) \<R>\<^sub>\<W>_is_minimizer:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class"
  shows "fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) = 
    (\<lambda>E. \<Union>(minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d 
                      (set_to_set_set (limit_set (alts_\<E> E) UNIV)) E))"
proof (standard)
  fix
    E :: "('a, 'v) Election"
  let ?min = "(minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d 
                          (set_to_set_set (limit_set (alts_\<E> E) UNIV)) E)"
  have 
    "?min = arg_min_set 
              (closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E) 
              (set_to_set_set (limit_set (alts_\<E> E) UNIV))"
    by simp
  also have 
    "arg_min_set 
              (closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E) 
              (set_to_set_set (limit_set (alts_\<E> E) UNIV))
      = set_to_set_set (arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV))"
  proof (safe)
    fix 
      R :: "'r set"
    assume 
      min: "R \<in> arg_min_set 
                  (closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E)
                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))"
    hence "R \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV)"
      by (meson arg_min_subset subsetD)
    then obtain r :: 'r where "R = {r}" and r_in_lim_set: "r \<in> limit_set (alts_\<E> E) UNIV"
      by auto
    have 
      "\<nexists>R'. R' \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV) \<and>
          closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E R'
            < closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E R"
      using min arg_min_set.simps is_arg_min_def CollectD
      by (metis (mono_tags, lifting))
    hence 
      "\<nexists>r'. r' \<in> limit_set (alts_\<E> E) UNIV \<and> 
          closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E {r'}
            < closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E {r}"
      using \<open>R = {r}\<close>
      by auto
    hence 
      "\<nexists>r'. r' \<in> limit_set (alts_\<E> E) UNIV \<and> score d C E r' < score d C E r"
      using score_is_closest_preimg_dist
      by metis
    hence "r \<in> arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV)"
      using r_in_lim_set arg_min_set.simps is_arg_min_def CollectI
      by metis
    thus "R \<in> set_to_set_set (arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV))"
      using \<open>R = {r}\<close>
      by simp
  next
    fix 
      R :: "'r set"
    assume "R \<in> set_to_set_set (arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV))"
    then obtain r :: 'r where 
      "R = {r}" and r_min_lim_set: "r \<in> arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV)"
      by auto
    hence 
      "\<nexists>r'. r' \<in> limit_set (alts_\<E> E) UNIV \<and> score d C E r' < score d C E r"
      by (metis CollectD arg_min_set.simps is_arg_min_def)
    hence 
      "\<nexists>r'. r' \<in> limit_set (alts_\<E> E) UNIV \<and> 
          closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E {r'}
            < closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E {r}"
      using score_is_closest_preimg_dist
      by metis
    moreover have 
      "\<forall>R' \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV). 
        \<exists>r' \<in> limit_set (alts_\<E> E) UNIV. R' = {r'}"
      by auto
    ultimately have "\<nexists>R'. R' \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV) \<and>
        closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E R'
          < closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E R"
      using \<open>R = {r}\<close> 
      by auto
    moreover have "R \<in> set_to_set_set (limit_set (alts_\<E> E) UNIV)"
      using r_min_lim_set \<open>R = {r}\<close> arg_min_subset 
      by fastforce
    ultimately show "R \<in> arg_min_set 
                  (closest_preimg_dist (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d E)
                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))"
      using arg_min_set.simps is_arg_min_def CollectI
      by (metis (mono_tags, lifting))
  qed
  also have "(arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV)) = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E"
    by simp
  finally have 
    "\<Union>?min = \<Union>(set_to_set_set (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E))"
    by presburger
  thus "fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E = \<Union>?min"
    using un_left_inv_set_to_set_set
    by auto
qed

subsubsection \<open>Invariance\<close>

theorem (in result) tot_invar_dist_imp_invar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    rel :: "('a, 'v) Election rel"
  assumes
    r_refl: "restr_refl_on (\<K>_els C) rel" and
    tot_invar_d: "totally_invariant_dist d rel" and
    invar_res: "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance rel)"
  shows "satisfies (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance rel)"
proof -
  let ?min = "(\<lambda>E. \<Union> \<circ> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d 
                                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))))"
  have "\<forall>E. satisfies (?min E) (Invariance rel)"
    using r_refl tot_invar_d invar_comp 
          minimizer_invar_under_refl_rel_and_tot_invar_dist[of 
            "\<K>_els C" rel d "elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)"]
    by blast
  moreover have "satisfies ?min (Invariance rel)"
    using invar_res
    by auto
  ultimately have 
    "satisfies (\<lambda>E. ?min E E) (Invariance rel)"
    using invar_param_fun[of ?min rel]
    by blast
  also have "(\<lambda>E. ?min E E) = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer comp_def
    by metis
  finally have invar_\<R>\<^sub>\<W>: "satisfies (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance rel)"
    by simp
  hence "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV - fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E) (Invariance rel)"
    using invar_res
    by fastforce
  thus "satisfies (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance rel)"
    using invar_\<R>\<^sub>\<W>
    by auto
qed

theorem (in result) invar_dist_cons_imp_invar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    G :: "'x monoid" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    B :: "('a, 'v) Election set" 
    \<comment> \<open>Base set of elections on which the DR rule is invariant, e.g. valid_elections.\<close>
  defines
    "rel \<equiv> rel_induced_by_action (carrier G) B \<phi>" and
    "restr_rel \<equiv> rel_induced_by_action (carrier G) (\<K>_els C) \<phi>"
  assumes        
    grp_act: "group_action G B \<phi>" and "\<K>_els C \<subseteq> B" and
    closed_domain: "rel \<inter> (\<K>_els C \<times> B) \<subseteq> restr_rel" and
    (* Could the closed_domain requirement be weakened? *)
    invar_res: "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance rel)" and
    invar_d: "invariant_dist d (carrier G) B \<phi>" and
    invar_C_winners: "satisfies (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (Invariance restr_rel)" 
  shows
    "satisfies (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance rel)"
proof -                    
  let ?min = "(\<lambda>E. \<Union> \<circ> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d 
                                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))))"
  have "\<forall>E. satisfies (?min E) (Invariance rel)"
    using grp_act closed_domain \<open>\<K>_els C \<subseteq> B\<close> invar_d invar_C_winners 
          grp_act_invar_dist_and_invar_f_imp_invar_minimizer rel_def 
          restr_rel_def invar_comp Sigma_cong 
    by (metis (no_types, lifting))
  moreover have "satisfies ?min (Invariance rel)"
    using invar_res
    by auto
  ultimately have 
    "satisfies (\<lambda>E. ?min E E) (Invariance rel)"
    using invar_param_fun[of ?min rel]
    by blast
  also have "(\<lambda>E. ?min E E) = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer comp_def
    by metis
  finally have invar_\<R>\<^sub>\<W>: "satisfies (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance rel)"
    by simp
  hence "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV - 
    fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E) (Invariance rel)"
    using invar_res
    by fastforce
  thus "satisfies (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance rel)"
    using invar_\<R>\<^sub>\<W>
    by auto
qed

subsubsection \<open>Equivariance\<close>

theorem (in result) invar_dist_equivar_cons_imp_equivar_dr_rule:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    G :: "'x monoid" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    \<psi> :: "('x, 'r) binary_fun" and
    B :: "('a, 'v) Election set" 
  defines
    "rel \<equiv> rel_induced_by_action (carrier G) B \<phi>" and
    "restr_rel \<equiv> rel_induced_by_action (carrier G) (\<K>_els C) \<phi>" and
    "equivar_prop \<equiv> 
      equivar_ind_by_act (carrier G) (\<K>_els C) \<phi> (set_action \<psi>)" and
    "equivar_prop_global_set_valued \<equiv> 
      equivar_ind_by_act (carrier G) B \<phi> (set_action \<psi>)" and
    "equivar_prop_global_result_valued \<equiv> 
      equivar_ind_by_act (carrier G) B \<phi> (result_action \<psi>)"
  assumes        
    grp_act: "group_action G B \<phi>" and grp_act_res: "group_action G UNIV \<psi>" and
    "\<K>_els C \<subseteq> B" and closed_domain: "rel \<inter> (\<K>_els C \<times> B) \<subseteq> restr_rel" and
    (* Could the closed_domain requirement be weakened? *)
    equivar_res: 
      "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) equivar_prop_global_set_valued" and
    invar_d: "invariant_dist d (carrier G) B \<phi>" and
    equivar_C_winners: "satisfies (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) equivar_prop"
  shows "satisfies (fun\<^sub>\<E> (distance_\<R> d C)) equivar_prop_global_result_valued"
proof -
  let ?min_E = "\<lambda>E. minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d 
                                (set_to_set_set (limit_set (alts_\<E> E) UNIV)) E"
  let ?min = "(\<lambda>E. \<Union> \<circ> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (\<K>_els C) d 
                                    (set_to_set_set (limit_set (alts_\<E> E) UNIV))))"
  let ?\<psi>' = "set_action (set_action \<psi>)" \<comment> \<open>Apply \<psi> to a set of sets.\<close>
  let ?equivar_prop_global_set_valued' = "equivar_ind_by_act (carrier G) B \<phi> ?\<psi>'"
  have "\<forall>E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
          set_to_set_set (limit_set (alts_\<E> (\<phi> g E)) UNIV) =
            {{r} | r. r \<in> limit_set (alts_\<E> (\<phi> g E)) UNIV}"
    by simp
  moreover have 
    "\<forall>E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
      limit_set (alts_\<E> (\<phi> g E)) UNIV = \<psi> g ` (limit_set (alts_\<E> E) UNIV)"
    using equivar_res grp_act group_action.element_image
    unfolding equivar_prop_global_set_valued_def equivar_ind_by_act_def
    by fastforce
  ultimately have 
    "\<forall>E g. g \<in> carrier G \<longrightarrow> E \<in> B \<longrightarrow>
      set_to_set_set (limit_set (alts_\<E> (\<phi> g E)) UNIV) = 
        {{r} | r. r \<in> \<psi> g ` (limit_set (alts_\<E> E) UNIV)}"
    by simp
  moreover have "\<forall>E g. {{r} | r. r \<in> \<psi> g ` (limit_set (alts_\<E> E) UNIV)}
                  = {\<psi> g ` {r} | r. r \<in> limit_set (alts_\<E> E) UNIV}"
    by blast
  moreover have "\<forall>E g. {\<psi> g ` {r} | r. r \<in> limit_set (alts_\<E> E) UNIV} =
                  ?\<psi>' g {{r} | r. r \<in> limit_set (alts_\<E> E) UNIV}"
    unfolding set_action.simps
    by blast
  ultimately have 
    "satisfies (\<lambda>E. set_to_set_set (limit_set (alts_\<E> E) UNIV))
              ?equivar_prop_global_set_valued'"
    using rewrite_equivar_ind_by_act[of 
            "\<lambda>E. set_to_set_set (limit_set (alts_\<E> E) UNIV)" "carrier G" B \<phi> ?\<psi>']
    by force
  moreover have "group_action G UNIV (set_action \<psi>)"
    using grp_act_induces_set_grp_act[of G UNIV \<psi>] grp_act_res 
    unfolding set_action.simps
    by auto
  ultimately have "satisfies ?min_E ?equivar_prop_global_set_valued'"
    using grp_act invar_d \<open>\<K>_els C \<subseteq> B\<close> closed_domain equivar_C_winners
          grp_act_invar_dist_and_equivar_f_imp_equivar_minimizer[of 
              G B \<phi> "set_action \<psi>" "\<K>_els C" 
              "\<lambda>E. set_to_set_set (limit_set (alts_\<E> E) UNIV)" 
              d "elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)"]
    unfolding restr_rel_def rel_def equivar_prop_def
    by blast
  moreover have 
    "satisfies \<Union> (equivar_ind_by_act (carrier G) UNIV ?\<psi>' (set_action \<psi>))"
    by (rule equivar_union_under_img_act[of "carrier G" \<psi>])
  ultimately have "satisfies (\<Union> \<circ> ?min_E) equivar_prop_global_set_valued"
    unfolding equivar_prop_global_set_valued_def
    using equivar_ind_by_act_comp[of ?min_E B UNIV "carrier G" ?\<psi>' \<phi> \<Union>]
    by blast
  moreover have "(\<lambda>E. ?min E E) = \<Union> \<circ> ?min_E"
    unfolding comp_def
    by blast
  ultimately have
    "satisfies (\<lambda>E. ?min E E) equivar_prop_global_set_valued"
    by simp
  moreover have "(\<lambda>E. ?min E E) = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)"
    using \<R>\<^sub>\<W>_is_minimizer comp_def
    by metis
  \<comment> \<open>As all components of the result are equivariant, the whole result is equivariant.\<close>
  ultimately have equivar_\<R>\<^sub>\<W>: 
    "satisfies (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) equivar_prop_global_set_valued"
    by simp
  moreover have "\<forall>g \<in> carrier G. bij (\<psi> g)"
    using grp_act_res
    by (simp add: bij_betw_def group_action.inj_prop group_action.surj_prop)
  ultimately have
    "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV - 
      fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E) equivar_prop_global_set_valued"
    using equivar_res 
          equivar_set_minus[of 
            "\<lambda>E. limit_set (alts_\<E> E) UNIV" "carrier G" 
            B \<phi> \<psi> "\<lambda>E. fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E"]
    unfolding equivar_prop_global_set_valued_def equivar_ind_by_act_def set_action.simps
    by blast
  thus "satisfies (fun\<^sub>\<E> (distance_\<R> d C)) equivar_prop_global_result_valued"
    using equivar_\<R>\<^sub>\<W>
    unfolding equivar_prop_global_result_valued_def equivar_prop_global_set_valued_def
    by (simp add: rewrite_equivar_ind_by_act)
qed

subsection \<open>Symmetry Property Inference Rules\<close>

lemma (in result) cons_domain_valid:
  fixes
    C :: "('a, 'v, 'r Result) Consensus_Class"
  shows
    "\<K>_els C \<subseteq> valid_elections"
proof
  fix 
    E :: "('a,'v) Election"
  assume 
    "E \<in> \<K>_els C"
  hence "fun\<^sub>\<E> profile E"
    unfolding \<K>\<^sub>\<E>.simps
    by force
  thus "E \<in> valid_elections"
    unfolding valid_elections_def
    by simp
qed

lemma (in result) cons_domain_finite:
  fixes
    C :: "('a, 'v, 'r Result) Consensus_Class"
  shows
    "\<K>_els C \<subseteq> finite_elections"
proof
  fix 
    E :: "('a,'v) Election"
  assume 
    "E \<in> \<K>_els C"
  hence "fun\<^sub>\<E> profile E \<and> finite (alts_\<E> E) \<and> finite (votrs_\<E> E)"
    unfolding \<K>\<^sub>\<E>.simps
    by force
  thus "E \<in> finite_elections"
    unfolding finite_elections_def
    by simp
qed

theorem (in result) anon_dist_and_cons_imp_anon_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class"
  assumes       
    anon_d: "distance_anonymity' valid_elections d" and
    anon_C: "consensus_rule_anonymity' C" and
    closed_C:
      "anonymity\<^sub>\<R> valid_elections \<inter> (\<K>_els C \<times> valid_elections) \<subseteq> anonymity\<^sub>\<R> (\<K>_els C)"
  shows "anonymity' valid_elections (distance_\<R> d C)"
  using cons_domain_valid[of C] assms anon_grp_act.group_action_axioms well_formed_res_anon
        invar_dist_cons_imp_invar_dr_rule[of anonymity\<^sub>\<G> valid_elections \<phi>_anon C d]
  unfolding distance_anonymity'.simps anonymity\<^sub>\<R>.simps anonymity'.simps
            consensus_rule_anonymity'.simps
  by blast

theorem (in result_properties) neutr_dist_and_cons_imp_neutr_dr:
  fixes
    d :: "('a, 'c) Election Distance" and
    C :: "('a, 'c, 'b Result) Consensus_Class"
  assumes
    neutr_d: "distance_neutrality valid_elections d" and
    neutr_C: "consensus_rule_neutrality (\<K>_els C) C" and
    closed_C:
      "neutrality\<^sub>\<R> valid_elections \<inter> (\<K>_els C \<times> valid_elections) \<subseteq> neutrality\<^sub>\<R> (\<K>_els C)"
  shows "neutrality valid_elections (distance_\<R> d C)" 
  using cons_domain_valid[of C] assms \<phi>_neutr_act.group_action_axioms
        well_formed_res_neutr act_neutr
        invar_dist_equivar_cons_imp_equivar_dr_rule[of 
          neutrality\<^sub>\<G> valid_elections \<phi>_neutr \<psi>_neutr C d]
  unfolding distance_neutrality.simps neutrality.simps
            consensus_rule_neutrality.simps neutrality\<^sub>\<R>.simps
  by blast 

theorem (in result) tot_hom_dist_imp_hom_dr:
  fixes
    d :: "('a, nat) Election Distance" and
    C :: "('a, nat, 'r Result) Consensus_Class"
  assumes       
    hom_d: "distance_homogeneity' d"
  shows "homogeneity' finite_elections (distance_\<R> d C)"
  using assms refl_homogeneity\<^sub>\<R> well_formed_res_homogeneity cons_domain_finite 
        tot_invar_dist_imp_invar_dr_rule [of C "homogeneity\<^sub>\<R> finite_elections" d]
  unfolding distance_homogeneity'_def homogeneity'.simps 
            restr_refl_on.simps refl_on_def
  by blast

end
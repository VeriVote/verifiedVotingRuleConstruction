section \<open>Function Symmetry Properties\<close>

theory Symmetry_Of_Functions
  imports Distance
          "HOL-Algebra.Bij"
          "HOL-Algebra.Group"
          "HOL-Algebra.Group_Action"
          "HOL.Fun"
begin

subsection \<open>Functions\<close>

type_synonym ('x, 'y) binary_fun = "'x \<Rightarrow> 'y \<Rightarrow> 'y"

abbreviation extensional_continuation :: "('x \<Rightarrow> 'x) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'x)" where
  "extensional_continuation f S \<equiv> (\<lambda>x. if (x \<in> S) then (f x) else undefined)"

text \<open>Relations\<close>

fun sym_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "sym_on A r = (\<forall>x \<in> A. \<forall>y \<in> A. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"

abbreviation sym :: "'a rel \<Rightarrow> bool" where "sym r \<equiv> sym_on UNIV r"

fun restr_refl_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "restr_refl_on A r = (\<forall> a \<in> A. (a,a) \<in> r)"

fun rel_induced_by_action :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x, 'y) binary_fun \<Rightarrow> 'y rel" where
  "rel_induced_by_action X Y \<phi> = {(y1, y2) \<in> Y \<times> Y. \<exists> x \<in> X. \<phi> x y1 = y2}"

fun product_rel :: "'x rel \<Rightarrow> ('x * 'x) rel" where
  "product_rel r = {(pair1, pair2). (fst pair1, fst pair2) \<in> r \<and> (snd pair1, snd pair2) \<in> r}"

fun equivariance_rel :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x,'y) binary_fun \<Rightarrow> ('y * 'y) rel" where
  "equivariance_rel X Y \<phi> = {((a,b), (c,d)). (a,b) \<in> Y \<times> Y \<and> (\<exists>x \<in> X. c = \<phi> x a \<and> d = \<phi> x b)}"

fun set_closed_under_rel :: "('a,'v) Election set \<Rightarrow> ('a, 'v) Election rel \<Rightarrow> bool" where
  "set_closed_under_rel X r = (\<forall> E E'. (E,E') \<in> r \<longrightarrow> E \<in> X \<longrightarrow> E' \<in> X)"

fun uncurried_dist :: "'x Distance \<Rightarrow> ('x * 'x \<Rightarrow> ereal)" where
  "uncurried_dist d = (\<lambda>pair. d (fst pair) (snd pair))"

fun set_to_set_set :: "'x set \<Rightarrow> 'x set set" where
  "set_to_set_set X = {{x} | x. x \<in> X}"

subsection \<open>Minimizer function\<close>

fun preimg :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'y \<Rightarrow> 'x set" where
  "preimg f X y = {x \<in> X. f x = y}"

fun inf_dist :: "'x Distance \<Rightarrow> 'x set \<Rightarrow> 'x \<Rightarrow> ereal" where
  "inf_dist d X a = Inf (d a ` X)"

fun closest_preimg_dist :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> ereal" where
  "closest_preimg_dist f domain\<^sub>f d x y = inf_dist d (preimg f domain\<^sub>f y) x"

fun minimizer :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> 'y set \<Rightarrow> 'x \<Rightarrow> 'y set" where
  "minimizer f domain\<^sub>f d Y x = arg_min_set (closest_preimg_dist f domain\<^sub>f d x) Y"

subsection \<open>Invariance and Equivariance\<close>

text \<open>
  Invariance and equivariance are symmetry properties of functions:
  Invariance means that related preimages have identical images and equivariance.
\<close>

datatype ('x,'y) property = 
  Invariance "'x rel" |
  Equivariance "'x set" "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"

fun has_prop :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x, 'y) property \<Rightarrow> bool" where
  "has_prop f (Invariance r) = (\<forall>a. \<forall>b. (a,b) \<in> r \<longrightarrow> f a = f b)" |
  "has_prop f (Equivariance X Act) = 
    (\<forall>(\<phi>, \<psi>) \<in> Act. \<forall>x \<in> X. \<phi> x \<in> X \<longrightarrow> f (\<phi> x) = \<psi> (f x))"

definition equivar_ind_by_act :: 
  "'z set \<Rightarrow> 'x set \<Rightarrow> ('z, 'x) binary_fun \<Rightarrow> ('z, 'y) binary_fun \<Rightarrow> ('x,'y) property" where
  "equivar_ind_by_act Param X \<phi> \<psi> = Equivariance X {(\<phi> g, \<psi> g) | g. g \<in> Param}"

subsection \<open>Invariance of Distances\<close>

fun totally_invariant_dist :: 
  "'x Distance \<Rightarrow> 'x rel \<Rightarrow> bool" where
  "totally_invariant_dist d rel = has_prop (uncurried_dist d) (Invariance (product_rel rel))"

fun invariant_dist :: 
  "'y Distance \<Rightarrow> 'x set \<Rightarrow> 'y set \<Rightarrow> ('x, 'y) binary_fun \<Rightarrow> bool" where
  "invariant_dist d X Y \<phi> = has_prop (uncurried_dist d) (Invariance (equivariance_rel X Y \<phi>))"

subsection \<open>Auxiliary Lemmas\<close>

subsubsection \<open>Rewrite Rules\<close>

theorem rewrite_invar_as_equivar:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    X :: "'x set" and
    G :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows
    "has_prop f (Invariance (rel_induced_by_action G X \<phi>)) =
      has_prop f (equivar_ind_by_act G X \<phi> (\<lambda>g. id))"
proof (unfold equivar_ind_by_act_def, simp, safe)
  fix
    x :: 'x and g :: 'z
  assume 
    "x \<in> X" and "g \<in> G" and "\<phi> g x \<in> X" and
    "\<forall>a b. a \<in> X \<and> b \<in> X \<and> (\<exists>x\<in>G. \<phi> x a = b) \<longrightarrow> f a = f b"
  thus "f (\<phi> g x) = id (f x)"
    by (metis id_def)
next
  fix
    x :: 'x and g :: 'z
  assume
    "x \<in> X" and "\<phi> g x \<in> X" and "g \<in> G" and
    equivar: "\<forall>a b. (\<exists>g. a = \<phi> g \<and> b = id \<and> g \<in> G) \<longrightarrow> 
                (\<forall>x\<in>X. a x \<in> X \<longrightarrow> f (a x) = b (f x))"
  hence "\<phi> g = \<phi> g \<and> id = id \<and> g \<in> G"
    by blast
  hence "\<forall>x\<in>X. \<phi> g x \<in> X \<longrightarrow> f (\<phi> g x) = id (f x)"
    using equivar
    by blast
  thus "f x = f (\<phi> g x)"
    using \<open>x \<in> X\<close> \<open>\<phi> g x \<in> X\<close> 
    by (metis id_def)
qed

lemma rewrite_invar_ind_by_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z set" and
    X :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows 
    "has_prop f (Invariance (rel_induced_by_action G X \<phi>)) = 
      (\<forall>a \<in> X. \<forall>g \<in> G. \<phi> g a \<in> X \<longrightarrow> f a = f (\<phi> g a))"
proof (safe)
  fix
    a :: 'x and g :: 'z
  assume
    invar: "has_prop f (Invariance (rel_induced_by_action G X \<phi>))" and
    "a \<in> X" and "g \<in> G" and "\<phi> g a \<in> X"
  hence "(a, \<phi> g a) \<in> rel_induced_by_action G X \<phi>"
    unfolding rel_induced_by_action.simps
    by blast
  thus "f a = f (\<phi> g a)"
    using invar
    by simp
next
  assume 
    invar: "\<forall>a\<in>X. \<forall>g\<in>G. \<phi> g a \<in> X \<longrightarrow> f a = f (\<phi> g a)"
  have "\<forall>(a,b) \<in> rel_induced_by_action G X \<phi>. a \<in> X \<and> b \<in> X \<and> (\<exists>g \<in> G. b = \<phi> g a)"
    by auto
  hence "\<forall>(a,b) \<in> rel_induced_by_action G X \<phi>. f a = f b"
    using invar
    by fastforce
  thus "has_prop f (Invariance (rel_induced_by_action G X \<phi>))"
    by simp
qed

lemma rewrite_equivar_ind_by_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z set" and
    X :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  shows
    "has_prop f (equivar_ind_by_act G X \<phi> \<psi>) = 
      (\<forall>g \<in> G. \<forall>x \<in> X. \<phi> g x \<in> X \<longrightarrow> f (\<phi> g x) = \<psi> g (f x))"
  unfolding equivar_ind_by_act_def
  by auto

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


lemma rewrite_sym_group:
  shows
    rewrite_carrier: "carrier (BijGroup UNIV) = {f. bij f}" and
    bij_car_el: "\<And>f. f \<in> carrier (BijGroup UNIV) \<Longrightarrow> bij f" and
    rewrite_mult: 
      "\<And> S x y. x \<in> carrier (BijGroup S) \<Longrightarrow> 
                  y \<in> carrier (BijGroup S) \<Longrightarrow> 
                  x \<otimes>\<^bsub>BijGroup S\<^esub> y = extensional_continuation (x \<circ> y) S" and
    rewrite_mult_univ:
      "\<And>x y. x \<in> carrier (BijGroup UNIV) \<Longrightarrow> 
              y \<in> carrier (BijGroup UNIV) \<Longrightarrow> 
              x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y = x \<circ> y"
proof -
  show rew: "carrier (BijGroup UNIV) = {f. bij f}"
    unfolding BijGroup_def Bij_def
    by simp
  fix 
    f :: "'b \<Rightarrow> 'b"
  assume 
    "f \<in> carrier (BijGroup UNIV)"
  thus "bij f"
    using rew
    by blast 
next
  fix
    S :: "'c set" and
    x :: "'c \<Rightarrow> 'c" and
    y :: "'c \<Rightarrow> 'c"
  assume
    "x \<in> carrier (BijGroup S)" and
    "y \<in> carrier (BijGroup S)"
  thus "x \<otimes>\<^bsub>BijGroup S\<^esub> y = extensional_continuation (x \<circ> y) S"
    unfolding BijGroup_def compose_def comp_def
    by (simp add: restrict_def)
next
  fix
    x :: "'d \<Rightarrow> 'd" and
    y :: "'d \<Rightarrow> 'd"
  assume
    "x \<in> carrier (BijGroup UNIV)" and
    "y \<in> carrier (BijGroup UNIV)"
  thus "x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y = x \<circ> y"
    unfolding BijGroup_def compose_def comp_def
    by (simp add: restrict_def)
qed

lemma rewrite_totally_invariant_dist:
  fixes
    d :: "'x Distance" and
    r :: "'x rel"
  shows "totally_invariant_dist d r = (\<forall> (x, y) \<in> r. \<forall> (a, b) \<in> r. d x a = d y b)"
proof (safe)
  fix 
    a :: 'x and b :: 'x and x :: 'x and y :: 'x
  assume 
    inv: "totally_invariant_dist d r" and
    "(a, b) \<in> r" and "(x, y) \<in> r"
  hence "((x,a), (y,b)) \<in> product_rel r"
    by simp
  thus "d x a = d y b" 
    using inv
    by simp
next
  show "\<forall>(x, y)\<in>r. \<forall>(a, b)\<in>r. d x a = d y b \<Longrightarrow> totally_invariant_dist d r"
  proof (unfold totally_invariant_dist.simps has_prop.simps product_rel.simps, safe)
    fix 
      a :: 'x  and b :: 'x and x :: 'x and y :: 'x
    assume 
      "\<forall>(x, y)\<in>r. \<forall>(a, b)\<in>r. d x a = d y b" and
      "(fst (x, a), fst (y, b)) \<in> r" and " (snd (x, a), snd (y, b)) \<in> r"
    thus "uncurried_dist d (x, a) = uncurried_dist d (y, b)"
      unfolding uncurried_dist.simps
      by blast
  qed
qed

lemma rewrite_invariant_dist:
  fixes
    d :: "'y Distance" and
    X :: "'x set" and
    Y :: "'y set" and
    \<phi> :: "('x,'y) binary_fun"
  shows "invariant_dist d X Y \<phi> = (\<forall> x \<in> X. \<forall> y \<in> Y. \<forall> z \<in> Y. d y z = d (\<phi> x y) (\<phi> x z))"
proof (safe)
  fix x :: 'x and y :: 'y and z :: 'y
  assume
    "x \<in> X" and "y \<in> Y" and "z \<in> Y" and
    "invariant_dist d X Y \<phi>"
  thus "d y z = d (\<phi> x y) (\<phi> x z)"
    by fastforce
next
  show "\<forall>x\<in>X. \<forall>y\<in>Y. \<forall>z\<in>Y. d y z = d (\<phi> x y) (\<phi> x z) \<Longrightarrow> invariant_dist d X Y \<phi>"
  proof (unfold invariant_dist.simps has_prop.simps equivariance_rel.simps, safe)
    fix x :: 'x and a :: 'y and b :: 'y
    assume 
      "\<forall>x\<in>X. \<forall>y\<in>Y. \<forall>z\<in>Y. d y z = d (\<phi> x y) (\<phi> x z)" and 
      "x \<in> X" and "a \<in> Y" and "b \<in> Y"
    hence "d a b = d (\<phi> x a) (\<phi> x b)" 
      by blast
    thus "uncurried_dist d (a, b) = uncurried_dist d (\<phi> x a, \<phi> x b)"
      by simp
  qed
qed

lemma extensional_univ:
  "extensional_continuation f UNIV = f"
  unfolding If_def
  by simp

subsubsection \<open>Invariance and Equivariance\<close>

lemma invar_under_subset_rel:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    rel' :: "'x rel"
  assumes
    subset: "rel' \<subseteq> rel" and
    invar: "has_prop f (Invariance rel)"
  shows
    "has_prop f (Invariance rel')"
  using assms has_prop.simps
  by auto

lemma invar_dist_image:
  fixes
    d :: "'y Distance" and
    G :: "'x monoid" and
    Y :: "'y set" and
    Y' :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun" and
    y :: 'y and
    g :: 'x
  assumes
    invar_d: "invariant_dist d (carrier G) Y \<phi>" and 
    "Y' \<subseteq> Y" and grp_act: "group_action G Y \<phi>" and
    "g \<in> carrier G" and "y \<in> Y"
  shows
    "d (\<phi> g y) ` (\<phi> g) ` Y' = d y ` Y'"
proof (safe)
  fix 
    y' :: 'y
  assume
    "y' \<in> Y'"
  hence "((y, y'), ((\<phi> g y), (\<phi> g y'))) \<in> equivariance_rel (carrier G) Y \<phi>"
    using \<open>Y' \<subseteq> Y\<close> \<open>y \<in> Y\<close> \<open>g \<in> carrier G\<close>
    unfolding equivariance_rel.simps
    by blast
  hence eq_dist: "uncurried_dist d ((\<phi> g y), (\<phi> g y')) = uncurried_dist d (y, y')"
    using invar_d
    unfolding invariant_dist.simps
    by fastforce
  thus "d (\<phi> g y) (\<phi> g y') \<in> d y ` Y'"
    using \<open>y' \<in> Y'\<close>
    by simp
  have "\<phi> g y' \<in> \<phi> g ` Y'"
    using \<open>y' \<in> Y'\<close>
    by simp
  thus "d y y' \<in> d (\<phi> g y) ` \<phi> g ` Y'"
    using eq_dist 
    unfolding uncurried_dist.simps
    by (simp add: rev_image_eqI)
qed

theorem equivar_preimg:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    X :: "'x set" and
    G :: "'z monoid" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun" and
    g :: 'z
  defines
    "rel \<equiv> rel_induced_by_action (carrier G) X \<phi>" and
    "restr_rel \<equiv> rel_induced_by_action (carrier G) domain\<^sub>f \<phi>" and
    "equivar_prop \<equiv> equivar_ind_by_act (carrier G) domain\<^sub>f \<phi> \<psi>"
  assumes        
    grp_act: "group_action G X \<phi>" and grp_act_res: "group_action G UNIV \<psi>" and
    "domain\<^sub>f \<subseteq> X" and closed_domain: "rel \<inter> (domain\<^sub>f \<times> X) \<subseteq> restr_rel" and
    (* Could the closed_domain requirement be weakened? *)
    equivar_f: "has_prop f equivar_prop" and
    grp_el: "g \<in> carrier G"
  shows "\<forall>y. preimg f domain\<^sub>f (\<psi> g y) = (\<phi> g) ` (preimg f domain\<^sub>f y)"
proof (safe)
  interpret grp_act: group_action G X \<phi> by (rule grp_act)
  interpret grp_act_results: group_action G UNIV \<psi> by (rule grp_act_res) 
  have grp_el_inv: "(inv\<^bsub>G\<^esub> g) \<in> carrier G"
    by (meson group.inv_closed group_hom.axioms(1) grp_act.group_hom grp_el)
  fix 
    y :: 'y and x :: 'x
  assume 
    preimg_el: "x \<in> preimg f domain\<^sub>f (\<psi> g y)"
  obtain x' where img: "x' = \<phi> (inv\<^bsub>G\<^esub> g) x"
    by simp
  have domain: "x \<in> domain\<^sub>f \<and> x \<in> X"
    using preimg_el \<open>domain\<^sub>f \<subseteq> X\<close>
    by auto
  hence "x' \<in> X"
    using \<open>domain\<^sub>f \<subseteq> X\<close> grp_act grp_el_inv preimg_el img grp_act.element_image 
    by auto
  hence "(x, x') \<in> rel \<inter> (domain\<^sub>f \<times> X)"
    unfolding rel_def
    using img preimg_el domain grp_el_inv
    by auto
  hence domain': "x' \<in> domain\<^sub>f"
    using closed_domain
    unfolding restr_rel_def rel_induced_by_action.simps
    by auto
  moreover have "(\<phi> (inv\<^bsub>G\<^esub> g), \<psi> (inv\<^bsub>G\<^esub> g)) \<in> {(\<phi> g, \<psi> g) | g. g \<in> carrier G}"
    using grp_el_inv
    by auto
  ultimately have "f x' = \<psi> (inv\<^bsub>G\<^esub> g) (f x)"
    using domain equivar_f img
    unfolding equivar_prop_def equivar_ind_by_act_def has_prop.simps
    by blast
  also have "f x = \<psi> g y"
    using preimg_el
    by simp
  also have "\<psi> (inv\<^bsub>G\<^esub> g) (\<psi> g y) = y"
    using grp_act_results.group_hom
    by (simp add: grp_act_results.orbit_sym_aux grp_el)
  finally have "f x' = y"
    by simp
  hence "x' \<in> preimg f domain\<^sub>f y"
    using domain'
    by simp
  moreover have "x = \<phi> g x'"
    using img domain domain' grp_el grp_el_inv
    by (metis group.inv_inv group_hom.axioms(1) grp_act.group_hom grp_act.orbit_sym_aux)
  ultimately show "x \<in> (\<phi> g) ` (preimg f domain\<^sub>f y)"
    by blast
next
  fix 
    y :: 'y and x :: 'x
  assume 
    preimg_el: "x \<in> preimg f domain\<^sub>f y"
  hence domain: "f x = y \<and> x \<in> domain\<^sub>f \<and> x \<in> X"
    using \<open>domain\<^sub>f \<subseteq> X\<close>
    by auto
  hence "\<phi> g x \<in> X"
    using grp_el
    by (meson group_action.element_image grp_act)
  hence "(x, \<phi> g x) \<in> rel \<inter> domain\<^sub>f \<times> X"
    unfolding rel_def
    using grp_el domain
    by auto
  hence "\<phi> g x \<in> domain\<^sub>f"
    using closed_domain
    unfolding restr_rel_def
    by auto
  moreover have "(\<phi> g, \<psi> g) \<in> {(\<phi> g, \<psi> g) |g. g \<in> carrier G}"
    using grp_el
    by blast
  ultimately show "\<phi> g x \<in> preimg f domain\<^sub>f (\<psi> g y)"
    using equivar_f domain
    unfolding equivar_prop_def equivar_ind_by_act_def
    by auto
qed

subsubsection \<open>Function Composition\<close>

lemma bij_app_to_set_of_sets:
  fixes
    f :: "'x \<Rightarrow> 'y"
  assumes
    "bij f"
  shows
    "bij (\<lambda>X. {f ` x | x. x \<in> X})"
proof (unfold bij_def inj_def surj_def, safe)
  fix
    X :: "'x set set" and Y :: "'x set set" and a :: "'x set"
  assume 
    "{f ` a | a. a \<in> X} = {f ` a | a. a \<in> Y}" and "a \<in> X"
  hence "f ` a \<in> {f ` a | a. a \<in> Y}"
    by blast
  then obtain a' :: "'x set" where el_Y': "a' \<in> Y" and "f ` a' = f ` a"
    by auto
  hence "the_inv f ` f ` a' = the_inv f ` f ` a"
    by simp 
  moreover have "\<forall>b. the_inv f ` f ` b = b"
    sorry
  ultimately have "a' = a"
    by simp
  thus "a \<in> Y"
    using el_Y'
    by simp
next
  fix
    X :: "'x set set" and Y :: "'x set set" and a :: "'x set"
  assume 
    "{f ` a | a. a \<in> X} = {f ` a | a. a \<in> Y}" and "a \<in> Y"
  show "a \<in> X"
    sorry (* same as first case by symmetry of = *)
next
  fix
    Y :: "'y set set"
  have "Y = {f ` (the_inv f) ` b | b. b \<in> Y}"
    sorry
  also have "{f ` (the_inv f) ` b | b. b \<in> Y} = 
              {f ` a | a. a \<in> {(the_inv f) ` b | b. b \<in> Y}}"
    by blast
  finally show "\<exists>X. Y = {f ` a | a. a \<in> X}"
    by blast
qed

lemma invar_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    rel :: "'x rel"
  assumes
    invar: "has_prop f (Invariance rel)"
  shows
    "has_prop (g \<circ> f) (Invariance rel)"
  using assms has_prop.simps
  by auto

lemma un_left_inv_set_to_set_set:
  "\<Union> \<circ> set_to_set_set = id"
proof
  fix
    X :: "'x set"
  have "(\<Union> \<circ> set_to_set_set) X = {x. \<exists>x' \<in> set_to_set_set X. x \<in> x'}"
    by auto
  also have "{x. \<exists>x' \<in> set_to_set_set X. x \<in> x'} = {x. {x} \<in> set_to_set_set X}"
    by auto
  also have "{x. {x} \<in> set_to_set_set X} = {x. {x} \<in> {{x} | x. x \<in> X}}"
    by simp
  also have "{x. {x} \<in> {{x} | x. x \<in> X}} = {x. x \<in> X}"
    by simp
  finally show "(\<Union> \<circ> set_to_set_set) X = id X"
    by simp
qed

lemma the_inv_comp:
  fixes
    f :: "'x \<Rightarrow> 'x" and
    g :: "'x \<Rightarrow> 'x"
  assumes
    "bij f" and
    "bij g"
  shows "the_inv (x \<circ> y) = (the_inv y) \<circ> (the_inv x)"
  sorry

lemma preimg_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'x \<Rightarrow> 'x" and
    X :: "'x set" and
    y :: 'y
  shows
    "preimg f (g ` X) y = g ` preimg (f \<circ> g) X y"
proof (safe)
  fix
    x :: 'x
  assume 
    "x \<in> preimg f (g ` X) y"
  hence "f x = y \<and> x \<in> g ` X"
    by simp
  then obtain x' :: 'x where "x' \<in> X" and "g x' = x" and "x' \<in> preimg (f \<circ> g) X y"
    unfolding comp_def
    by force
  thus "x \<in> g ` preimg (f \<circ> g) X y"
    by blast
next
   fix
    x :: 'x
  assume 
    "x \<in> preimg (f \<circ> g) X y"
  hence "f (g x) = y \<and> x \<in> X"
    by simp
  thus "g x \<in> preimg f (g ` X) y"
    by simp
qed
  
subsubsection \<open>Group Actions\<close>

lemma const_id_is_grp_act:
  fixes
    G :: "'x monoid"
  assumes
    "group G"
  shows
    "group_action G UNIV (\<lambda>g. id)"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, safe)
  show "group G"
    using assms
    by blast
next
  show "group (BijGroup UNIV)"
    by (rule group_BijGroup)
next
  show "id \<in> carrier (BijGroup UNIV)"
    unfolding BijGroup_def Bij_def
    by simp
  thus "id = id \<otimes>\<^bsub>BijGroup UNIV\<^esub> id"
    using rewrite_mult_univ
    by (metis comp_id)
qed

lemma invar_param_fun:
  fixes
    f :: "'x \<Rightarrow> ('x \<Rightarrow> 'y)" and
    rel :: "'x rel"
  assumes
    param_invar: "\<forall>x. has_prop (f x) (Invariance rel)" and
    invar: "has_prop f (Invariance rel)"
  shows
    "has_prop (\<lambda>x. f x x) (Invariance rel)"
  using invar param_invar 
  by auto

lemma rel_induced_by_monoid_action_refl:
  fixes
    X :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes
    hom: "\<phi> \<in> hom X (BijGroup Y)" and
    mon: "monoid X"
  shows "refl_on Y (rel_induced_by_action (carrier X) Y \<phi>)"
proof (unfold refl_on_def, clarsimp, safe)
  fix
    y :: 'y
  assume
    el: "y \<in> Y"
  interpret monoid: monoid X
    using assms
    by blast
  interpret group: group "(BijGroup Y)"
    by (simp add: group_BijGroup)
  have "\<one>\<^bsub>X\<^esub> \<in> carrier X"
    by simp
  moreover have "\<phi> \<one>\<^bsub>X\<^esub> = \<one>\<^bsub>BijGroup Y\<^esub>"
    using hom hom_in_carrier hom_mult 
    by fastforce
  ultimately show "\<exists>x \<in> carrier X. \<phi> x y = y"
    using el
    unfolding BijGroup_def
    by (metis monoid.select_convs(2) restrict_apply')
qed

subsection \<open>Equivariance\<close>

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
    "equivar_prop_global_set_valued \<equiv> equivar_ind_by_act (carrier G) X \<phi> (\<lambda>z. image (\<psi> z))"
  assumes        
    grp_act: "group_action G X \<phi>" and grp_act_res: "group_action G UNIV \<psi>" and
    "domain\<^sub>f \<subseteq> X" and closed_domain: "rel \<inter> (domain\<^sub>f \<times> X) \<subseteq> restr_rel" and
    (* Could the closed_domain requirement be weakened? *)
    equivar_img: "has_prop img equivar_prop_global_set_valued" and
    invar_d: "invariant_dist d (carrier G) X \<phi>" and
    equivar_f: "has_prop f equivar_prop"
  shows 
    "has_prop (\<lambda>x. minimizer f domain\<^sub>f d (img x) x) equivar_prop_global_set_valued"
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
    unfolding equivar_prop_global_set_valued_def
    by metis
  ultimately show
    "arg_min_set (closest_preimg_dist f domain\<^sub>f d (\<phi> g x)) (img (\<phi> g x)) =
       \<psi> g ` arg_min_set (closest_preimg_dist f domain\<^sub>f d x) (img x)"
    by presburger
qed

subsection \<open>Invariance\<close>

lemma closest_dist_invar_under_refl_rel_and_tot_invar_dist:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    d :: "'x Distance" and
    rel :: "'x rel"
  assumes
    r_refl: "restr_refl_on domain\<^sub>f rel" and
    tot_invar_d: "totally_invariant_dist d rel"
  shows "has_prop (closest_preimg_dist f domain\<^sub>f d) (Invariance rel)"
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
  shows "has_prop (minimizer f domain\<^sub>f d img) (Invariance rel)"
proof -
  have "has_prop (closest_preimg_dist f domain\<^sub>f d) (Invariance rel)"
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
    hom: "\<phi> \<in> hom G (BijGroup X)" and
    "monoid G" and "domain\<^sub>f \<subseteq> X" and
    tot_invar_d: "totally_invariant_dist d rel"
  shows "has_prop (minimizer f domain\<^sub>f d img) (Invariance rel)"
proof -
  have "refl_on X rel" 
    using \<open>monoid G\<close> hom rel_induced_by_monoid_action_refl 
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
    invar_f: "has_prop f (Invariance restr_rel)"
  shows "has_prop (minimizer f domain\<^sub>f d img) (Invariance rel)"
proof -
  let ?\<psi> = "\<lambda>g. id" and ?img = "\<lambda>x. img"
  have "has_prop f (equivar_ind_by_act (carrier G) domain\<^sub>f \<phi> ?\<psi>)"
    using invar_f rewrite_invar_as_equivar
    unfolding restr_rel_def 
    by blast
  moreover have "group_action G UNIV ?\<psi>"
    using const_id_is_grp_act grp_act
    unfolding group_action_def group_hom_def
    by blast
  moreover have 
    "has_prop ?img (equivar_ind_by_act (carrier G) X \<phi> (\<lambda>z. image (?\<psi> z)))"
    unfolding equivar_ind_by_act_def
    by fastforce
  ultimately have
    "has_prop (\<lambda>x. minimizer f domain\<^sub>f d (?img x) x)
              (equivar_ind_by_act (carrier G) X \<phi> (\<lambda>z. image (?\<psi> z)))"
    using assms 
          grp_act_invar_dist_and_equivar_f_imp_equivar_minimizer[of G X \<phi> ?\<psi> domain\<^sub>f ?img d f]
    by blast
  hence "has_prop (minimizer f domain\<^sub>f d img)
                  (equivar_ind_by_act (carrier G) X \<phi> (\<lambda>z. image id))"
    by blast
  thus ?thesis
    unfolding rel_def
    using rewrite_invar_as_equivar 
    by (metis image_id)
qed
  
end

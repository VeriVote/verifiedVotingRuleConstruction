section \<open>Function Symmetry Properties\<close>

theory Symmetry_Of_Functions
  imports Distance
          "HOL-Algebra.Bij"
          "HOL-Algebra.Group_Action"
          "HOL-Algebra.Generated_Groups"
begin

subsection \<open>Functions\<close>

type_synonym ('x, 'y) binary_fun = "'x \<Rightarrow> 'y \<Rightarrow> 'y"

fun extensional_continuation :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'y)" where
  "extensional_continuation f S = (\<lambda>x. if (x \<in> S) then (f x) else undefined)"

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

fun set_action :: "('x, 'r) binary_fun \<Rightarrow> ('x, 'r set) binary_fun" where
  "set_action \<psi> x = image (\<psi> x)"

subsection \<open>Minimizer function\<close>

fun preimg :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'y \<Rightarrow> 'x set" where
  "preimg f X y = {x \<in> X. f x = y}"

fun inf_dist :: "'x Distance \<Rightarrow> 'x set \<Rightarrow> 'x \<Rightarrow> ereal" where
  "inf_dist d X a = Inf (d a ` X)"

fun closest_preimg_dist :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> ereal" where
  "closest_preimg_dist f domain\<^sub>f d x y = inf_dist d (preimg f domain\<^sub>f y) x"

fun minimizer :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> 'y set \<Rightarrow> 'x \<Rightarrow> 'y set" where
  "minimizer f domain\<^sub>f d Y x = arg_min_set (closest_preimg_dist f domain\<^sub>f d x) Y"
(* arg_min instead of arg_min_set? *)

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

lemma rewrite_invar_ind_by_act [intro?]:
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

lemma rewrite_equivar_ind_by_act [intro?]:
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

lemma rewrite_grp_act_img:
  fixes
    G :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes
    grp_act: "group_action G Y \<phi>"
  shows 
    "\<forall>Z g h. Z \<subseteq> Y \<longrightarrow> g \<in> carrier G \<longrightarrow> h \<in> carrier G \<longrightarrow> 
              \<phi> (g \<otimes>\<^bsub>G\<^esub> h) ` Z = \<phi> g ` \<phi> h ` Z"
proof (safe)
  fix
    Z :: "'y set" and z :: 'y and
    g :: 'x and h :: 'x
  assume
    "g \<in> carrier G" and "h \<in> carrier G" and "z \<in> Z" and "Z \<subseteq> Y"
  hence eq: "\<phi> (g \<otimes>\<^bsub>G\<^esub> h) z = \<phi> g (\<phi> h z)"
    using grp_act group_action.composition_rule[of G Y \<phi> z g h] \<open>Z \<subseteq> Y\<close>
    by blast
  thus "\<phi> (g \<otimes>\<^bsub>G\<^esub> h) z \<in> \<phi> g ` \<phi> h ` Z"
    using \<open>z \<in> Z\<close>
    by blast
  show "\<phi> g (\<phi> h z) \<in> \<phi> (g \<otimes>\<^bsub>G\<^esub> h) ` Z"
    using \<open>z \<in> Z\<close> eq
    by force
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

text \<open>
  It suffices to show invariance under the group action of a generating set of a group
  to show invariance under the group action of the whole group.
  For example, it is enough to show invariance under transpositions to show invariance
  under a complete finite symmetric group.
\<close>

(* TODO Same for monoid actions? Equivariance? *)
  
theorem invar_generating_system_imp_invar:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z monoid" and
    H :: "'z set" and
    X :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun"
  assumes
    invar: "has_prop f (Invariance (rel_induced_by_action H X \<phi>))" and
    grp_act: "group_action G X \<phi>" and gen: "carrier G = generate G H"
  shows "has_prop f (Invariance (rel_induced_by_action (carrier G) X \<phi>))"
proof (unfold has_prop.simps rel_induced_by_action.simps, safe)
  fix
    x :: 'x and g :: 'z
  assume
    grp_el: "g \<in> carrier G" and "x \<in> X"
  interpret grp_act: group_action G X \<phi> using grp_act by blast
  have "g \<in> generate G H"
    using grp_el gen
    by blast
  hence "\<forall>x \<in> X. f x = f (\<phi> g x)"
  proof (induct g rule: generate.induct)
    case one
    hence "\<forall>x \<in> X. \<phi> \<one>\<^bsub>G\<^esub> x = x"
      using grp_act
      by (metis group_action.id_eq_one restrict_apply)
    thus ?case 
      by simp
  next
    case (incl g)
    hence "\<forall>x \<in> X. (x, \<phi> g x) \<in> rel_induced_by_action H X \<phi>"
      using gen grp_act generate.incl group_action.element_image 
      unfolding rel_induced_by_action.simps
      by fastforce
    thus ?case 
      using invar
      unfolding has_prop.simps
      by blast
  next
    case (inv g)
    hence "\<forall>x \<in> X. \<phi> (inv\<^bsub>G\<^esub> g) x \<in> X"
      using grp_act
      by (metis gen generate.inv group_action.element_image)
    hence "\<forall>x \<in> X. f (\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) x)) = f (\<phi> (inv\<^bsub>G\<^esub> g) x)"
      using gen generate.incl group_action.element_image grp_act 
            invar local.inv rewrite_invar_ind_by_act
      by metis
    moreover have "\<forall>x \<in> X. \<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) x) = x"
      using grp_act
      by (metis (full_types) gen generate.incl group.inv_closed group_action.orbit_sym_aux
                             group.inv_inv group_hom.axioms(1) grp_act.group_hom local.inv)
    ultimately show ?case 
      by simp
  next
    case (eng g1 g2)
    assume
      invar1: "\<forall>x\<in>X. f x = f (\<phi> g1 x)" and invar2: "\<forall>x\<in>X. f x = f (\<phi> g2 x)" and
      gen1: "g1 \<in> generate G H" and gen2: "g2 \<in> generate G H"
    hence "\<forall>x \<in> X. \<phi> g2 x \<in> X"
      using gen grp_act.element_image 
      by blast
    hence "\<forall>x \<in> X. f (\<phi> g1 (\<phi> g2 x)) = f (\<phi> g2 x)"
      by (auto simp add: invar1)
    moreover have "\<forall>x \<in> X. f (\<phi> g2 x) = f x"
      by (simp add: invar2)
    moreover have "\<forall>x \<in> X. f (\<phi> (g1 \<otimes>\<^bsub>G\<^esub> g2) x) = f (\<phi> g1 (\<phi> g2 x))"
      using grp_act gen grp_act.composition_rule gen1 gen2
      by simp
    ultimately show ?case
      by simp
  qed
  thus "f x = f (\<phi> g x)"
    using \<open>x \<in> X\<close>
    by blast
qed

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
    "bij (\<lambda>\<A>. {f ` A | A. A \<in> \<A>})"
proof (unfold bij_def inj_def surj_def, safe)
  {
    fix
      \<A> :: "'x set set" and \<B> :: "'x set set" and A :: "'x set"
    assume 
      "{f ` A | A. A \<in> \<A>} = {f ` B | B. B \<in> \<B>}" and "A \<in> \<A>"
    hence "f ` A \<in> {f ` B | B. B \<in> \<B>}"
      by blast
    then obtain B :: "'x set" where el_Y': "B \<in> \<B>" and "f ` B = f ` A"
      by auto
    hence "the_inv f ` f ` B = the_inv f ` f ` A"
      by simp
    hence "B = A"
      using image_inv_f_f assms \<open>f ` B = f ` A\<close> bij_betw_def
      by metis
    thus "A \<in> \<B>"
      using el_Y'
      by simp
  }
  note img_set_eq_imp_subs =
    \<open>\<And>\<A> \<B> A. {f ` A | A. A \<in> \<A>} = {f ` B | B. B \<in> \<B>} \<Longrightarrow> A \<in> \<A> \<Longrightarrow> A \<in> \<B>\<close>
  fix
    \<A> :: "'x set set" and \<B> :: "'x set set" and A :: "'x set"
  assume 
    "{f ` A | A. A \<in> \<A>} = {f ` B | B. B \<in> \<B>}" and "A \<in> \<B>"
  thus "A \<in> \<A>"
    using img_set_eq_imp_subs[of \<B> \<A> A] \<comment> \<open>Symmetry of "="\<close>
    by presburger
next
  fix
    \<A> :: "'y set set"
  have "\<forall>A. f ` (the_inv f) ` A = A"
    using image_f_inv_f[of f] assms
    by (metis bij_betw_def surj_imp_inv_eq the_inv_f_f)
  hence "{A | A. A \<in> \<A>} = {f ` (the_inv f) ` A | A. A \<in> \<A>}"
    by presburger
  hence "\<A> = {f ` (the_inv f) ` A | A. A \<in> \<A>}"  
    by simp
  also have "{f ` (the_inv f) ` A | A. A \<in> \<A>} = 
              {f ` A | A. A \<in> {(the_inv f) ` A | A. A \<in> \<A>}}"
    by blast
  finally show "\<exists>\<B>. \<A> = {f ` B | B. B \<in> \<B>}"
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

lemma equivar_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    X :: "'x set" and
    Y :: "'y set" and
    Act_f :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set" and
    Act_g :: "(('y \<Rightarrow> 'y) \<times> ('z \<Rightarrow> 'z)) set"
  defines 
    "transitive_acts \<equiv> 
      {(\<phi>, \<psi>). \<exists>\<psi>' :: 'y \<Rightarrow> 'y. (\<phi>, \<psi>') \<in> Act_f \<and> (\<psi>', \<psi>) \<in> Act_g \<and> \<psi>' ` f ` X \<subseteq> Y}"
  assumes
    "f ` X \<subseteq> Y" and
    "has_prop f (Equivariance X Act_f)" and
    "has_prop g (Equivariance Y Act_g)"
  shows 
    "has_prop (g \<circ> f) (Equivariance X transitive_acts)"
proof (unfold transitive_acts_def, simp, safe)
  fix
    \<phi> :: "'x \<Rightarrow> 'x" and \<psi>' :: "'y \<Rightarrow> 'y" and \<psi> :: "'z \<Rightarrow> 'z" and x :: 'x
  assume
    "x \<in> X" and "\<phi> x \<in> X" and "\<psi>' ` f ` X \<subseteq> Y" and
    act_f: "(\<phi>, \<psi>') \<in> Act_f" and act_g: "(\<psi>', \<psi>) \<in> Act_g"
  hence "f x \<in> Y \<and> \<psi>' (f x) \<in> Y"
    using assms
    by blast
  hence "\<psi> (g (f x)) = g (\<psi>' (f x))"
    using act_g assms
    by fastforce
  also have "g (f (\<phi> x)) = g (\<psi>' (f x))"
    using assms act_f \<open>x \<in> X\<close> \<open>\<phi> x \<in> X\<close>
    by fastforce
  finally show "g (f (\<phi> x)) = \<psi> (g (f x))"
    by simp
qed

lemma equivar_ind_by_act_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    G :: "'w set" and
    X :: "'x set" and
    Y :: "'y set" and
    \<phi> :: "('w, 'x) binary_fun" and
    \<psi>' :: "('w, 'y) binary_fun" and
    \<psi> :: "('w, 'z) binary_fun"
  assumes
    "f ` X \<subseteq> Y" and "\<forall>g \<in> G. \<psi>' g ` f ` X \<subseteq> Y" and
    "has_prop f (equivar_ind_by_act G X \<phi> \<psi>')" and
    "has_prop g (equivar_ind_by_act G Y \<psi>' \<psi>)"
  shows "has_prop (g \<circ> f) (equivar_ind_by_act G X \<phi> \<psi>)"
proof -
  let ?Act_f = "{(\<phi> g, \<psi>' g) | g. g \<in> G}" and
      ?Act_g = "{(\<psi>' g, \<psi> g) | g. g \<in> G}"
  have 
    "{(\<phi>, \<psi>). \<exists>\<psi>' :: 'y \<Rightarrow> 'y. (\<phi>, \<psi>') \<in> ?Act_f \<and> (\<psi>', \<psi>) \<in> ?Act_g \<and> \<psi>' ` f ` X \<subseteq> Y} =
      {(\<phi> g, \<psi> g) | g. g \<in> G}"
    sorry
  hence "has_prop (g \<circ> f) (Equivariance X {(\<phi> g, \<psi> g) | g. g \<in> G})"
    using assms equivar_comp[of f X Y ?Act_f g ?Act_g] 
    by (metis equivar_ind_by_act_def)
  thus ?thesis
    unfolding equivar_ind_by_act_def
    by blast
qed  

lemma equivar_set_minus:
  fixes
    f :: "'x \<Rightarrow> 'y set" and
    h :: "'x \<Rightarrow> 'y set" and
    G :: "'z set" and
    X :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  assumes
    "has_prop f (equivar_ind_by_act G X \<phi> (set_action \<psi>))" and 
    "has_prop h (equivar_ind_by_act G X \<phi> (set_action \<psi>))" and
    "\<forall>g \<in> G. bij (\<psi> g)"
  shows "has_prop (\<lambda>x. f x - h x) (equivar_ind_by_act G X \<phi> (set_action \<psi>))"
proof -
  have "\<forall>g \<in> G. \<forall>x \<in> X. \<phi> g x \<in> X \<longrightarrow> f (\<phi> g x) = \<psi> g ` (f x)"
    using assms
    by (simp add: rewrite_equivar_ind_by_act)
  moreover have "\<forall>g \<in> G. \<forall>x \<in> X. \<phi> g x \<in> X \<longrightarrow> h (\<phi> g x) = \<psi> g ` (h x)"
    using assms
    by (simp add: rewrite_equivar_ind_by_act)
  ultimately have 
    "\<forall>g \<in> G. \<forall>x \<in> X. \<phi> g x \<in> X \<longrightarrow> f (\<phi> g x) - h (\<phi> g x) = \<psi> g ` (f x) - \<psi> g ` (h x)"
    by blast
  moreover have "\<forall>g \<in> G. \<forall>A B. \<psi> g ` A - \<psi> g ` B = \<psi> g ` (A - B)"
    using assms
    by (simp add: bij_def image_set_diff)
  ultimately show ?thesis
    using rewrite_equivar_ind_by_act
    unfolding set_action.simps
    by fastforce
qed

lemma equivar_union_under_img_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows
    "has_prop \<Union> (equivar_ind_by_act G UNIV 
              (set_action (set_action \<phi>)) (set_action \<phi>))"
proof (unfold equivar_ind_by_act_def, clarsimp, safe)
  fix
    g :: 'z and \<X> :: "'x set set" and X :: "'x set" and x :: 'x
  assume
    "x \<in> X" and "X \<in> \<X>" and "g \<in> G"
  thus "\<phi> g x \<in> \<phi> g ` \<Union> \<X>"
    by blast
  have "\<phi> g ` X \<in> (`) (\<phi> g) ` \<X>"
    using \<open>X \<in> \<X>\<close>
    by simp
  thus "\<phi> g x \<in> \<Union> ((`) (\<phi> g) ` \<X>)"
    using \<open>x \<in> X\<close>
    by blast
qed

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
    f :: "'y \<Rightarrow> 'z" and
    g :: "'x \<Rightarrow> 'y" and
    X :: "'x set" and
    Y :: "'y set" and
    Z :: "'z set" and
    z :: 'z
  assumes
    "bij_betw f Y Z" and
    "bij_betw g X Y" and
    "z \<in> Z"
  shows "the_inv_into X (f \<circ> g) z = ((the_inv_into X g) \<circ> (the_inv_into Y f)) z"
proof (clarsimp)
  have el_Y: "the_inv_into Y f z \<in> Y"
    using assms
    by (meson bij_betw_apply bij_betw_the_inv_into)
  hence "g (the_inv_into X g (the_inv_into Y f z)) = the_inv_into Y f z"
    using assms
    by (simp add: f_the_inv_into_f_bij_betw)
  moreover have "f (the_inv_into Y f z) = z"
    using el_Y assms
    by (simp add: f_the_inv_into_f_bij_betw)
  ultimately have "(f \<circ> g) (the_inv_into X g (the_inv_into Y f z)) = z"
    by simp
  hence 
    "the_inv_into X (f \<circ> g) z = 
      the_inv_into X (f \<circ> g) ((f \<circ> g) (the_inv_into X g (the_inv_into Y f z)))"
    by presburger
  also have 
    "the_inv_into X (f \<circ> g) ((f \<circ> g) (the_inv_into X g (the_inv_into Y f z))) =
      the_inv_into X g (the_inv_into Y f z)"
    using assms
    by (meson bij_betw_apply bij_betw_imp_inj_on bij_betw_the_inv_into 
                bij_betw_trans the_inv_into_f_eq)
  finally show "the_inv_into X (f \<circ> g) z = the_inv_into X g (the_inv_into Y f z)"
    by blast
qed

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

definition map_monoid :: "'x set \<Rightarrow> ('x \<Rightarrow> 'x) monoid" where
  "map_monoid X = \<lparr>carrier = {f :: 'x \<Rightarrow> 'x. f ` X \<subseteq> X}, mult = comp, one = id\<rparr>"

lemma monoid_map_monoid: 
  fixes
    X :: "'x set"
  shows "monoid (map_monoid X)"
  unfolding monoid_def map_monoid_def
  by auto

lemma rel_induced_by_monoid_action_refl:
  fixes
    X :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes
    hom: "\<phi> \<in> hom X (map_monoid Y)" and
    one: "\<phi> \<one>\<^bsub>X\<^esub> = \<one>\<^bsub>map_monoid Y\<^esub>" and
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
  interpret monoid: monoid "map_monoid Y"
    by (rule monoid_map_monoid)
  have "\<one>\<^bsub>X\<^esub> \<in> carrier X"
    by simp
  thus "\<exists>x \<in> carrier X. \<phi> x y = y"
    using el one
    unfolding map_monoid_def
    by force
qed

lemma grp_act_is_monoid_act:
  fixes
    X :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes
    "group_action X Y \<phi>"
  shows
    hom: "\<phi> \<in> hom X (BijGroup Y)" and
    one: "\<phi> \<one>\<^bsub>X\<^esub> = \<one>\<^bsub>BijGroup Y\<^esub>"
proof -
  show "\<phi> \<in> hom X (BijGroup Y)"
    using assms
    unfolding group_action_def
    by simp
next
  show "\<phi> \<one>\<^bsub>X\<^esub> = \<one>\<^bsub>BijGroup Y\<^esub>"
    using assms group_action_def group_hom.hom_one 
    by blast
qed

theorem grp_act_induces_set_grp_act:
  fixes
    G :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  defines
    "\<phi>_img \<equiv> (\<lambda>g. extensional_continuation (image (\<phi> g)) (Pow Y))"
  assumes
    grp_act: "group_action G Y \<phi>"
  shows 
    "group_action G (Pow Y) \<phi>_img"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, safe)
  show "group G" 
    using assms
    unfolding group_action_def group_hom_def
    by simp
next
  show "group (BijGroup (Pow Y))"
    by (rule group_BijGroup)
next
  {
    fix
      g :: 'x
    assume "g \<in> carrier G"
    hence "bij_betw (\<phi> g) Y Y"
      using grp_act
      by (simp add: bij_betw_def group_action.inj_prop group_action.surj_prop)
    hence "bij_betw (image (\<phi> g)) (Pow Y) (Pow Y)"
      by (rule bij_betw_Pow)
    moreover have "\<forall>A \<in> Pow Y. \<phi>_img g A = image (\<phi> g) A"
      unfolding \<phi>_img_def
      by simp
    ultimately have "bij_betw (\<phi>_img g) (Pow Y) (Pow Y)"
      using bij_betw_cong 
      by fastforce
    moreover have "\<phi>_img g \<in> extensional (Pow Y)"
      unfolding \<phi>_img_def
      by (simp add: extensional_def)
    ultimately show "\<phi>_img g \<in> carrier (BijGroup (Pow Y))"
      unfolding BijGroup_def Bij_def
      by simp
  }
  note car_el =
    \<open>\<And>g. g \<in> carrier G \<Longrightarrow> \<phi>_img g \<in> carrier (BijGroup (Pow Y))\<close>
  fix
    g :: 'x and h :: 'x
  assume 
    car_g: "g \<in> carrier G" and car_h: "h \<in> carrier G"
  hence car_els: "\<phi>_img g \<in> carrier (BijGroup (Pow Y)) \<and> \<phi>_img h \<in> carrier (BijGroup (Pow Y))"
    using car_el
    by blast
  hence h_closed: "\<forall>A. A \<in> Pow Y \<longrightarrow> \<phi>_img h A \<in> Pow Y"
    unfolding BijGroup_def Bij_def
    using bij_betw_apply 
    by (metis Int_Collect partial_object.select_convs(1))
  from car_els have 
    "\<phi>_img g \<otimes>\<^bsub>BijGroup (Pow Y)\<^esub> \<phi>_img h = 
      extensional_continuation (\<phi>_img g \<circ> \<phi>_img h) (Pow Y)"
    using rewrite_mult
    by blast
  moreover have 
    "\<forall>A. A \<notin> Pow Y \<longrightarrow> extensional_continuation (\<phi>_img g \<circ> \<phi>_img h) (Pow Y) A = undefined"
    by simp
  moreover have "\<forall>A. A \<notin> Pow Y \<longrightarrow> \<phi>_img (g \<otimes>\<^bsub>G\<^esub> h) A = undefined"
    unfolding \<phi>_img_def
    by simp
  moreover have 
    "\<forall>A. A \<in> Pow Y \<longrightarrow> extensional_continuation (\<phi>_img g \<circ> \<phi>_img h) (Pow Y) A = \<phi> g ` \<phi> h ` A"
    using h_closed
    by (simp add: \<phi>_img_def)
  moreover have 
    "\<forall>A. A \<in> Pow Y \<longrightarrow> \<phi>_img (g \<otimes>\<^bsub>G\<^esub> h) A = \<phi> g ` \<phi> h ` A"
    unfolding \<phi>_img_def extensional_continuation.simps
    using rewrite_grp_act_img[of G Y \<phi>] car_g car_h grp_act
    by (metis PowD)
  ultimately have "\<forall>A. \<phi>_img (g \<otimes>\<^bsub>G\<^esub> h) A = (\<phi>_img g \<otimes>\<^bsub>BijGroup (Pow Y)\<^esub> \<phi>_img h) A"
    by metis
  thus "\<phi>_img (g \<otimes>\<^bsub>G\<^esub> h) = \<phi>_img g \<otimes>\<^bsub>BijGroup (Pow Y)\<^esub> \<phi>_img h"
    by blast
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
    "equivar_prop_global_set_valued \<equiv> equivar_ind_by_act (carrier G) X \<phi> (set_action \<psi>)"
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
    unfolding equivar_prop_global_set_valued_def set_action.simps
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
    hom: "\<phi> \<in> hom G (map_monoid X)" and
    one: "\<phi> \<one>\<^bsub>G\<^esub> = \<one>\<^bsub>map_monoid X\<^esub>" and
    "monoid G" and "domain\<^sub>f \<subseteq> X" and
    tot_invar_d: "totally_invariant_dist d rel"
  shows "has_prop (minimizer f domain\<^sub>f d img) (Invariance rel)"
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
    "has_prop ?img (equivar_ind_by_act (carrier G) X \<phi> (set_action ?\<psi>))"
    unfolding equivar_ind_by_act_def
    by fastforce
  ultimately have
    "has_prop (\<lambda>x. minimizer f domain\<^sub>f d (?img x) x)
              (equivar_ind_by_act (carrier G) X \<phi> (set_action ?\<psi>))"
    using assms 
          grp_act_invar_dist_and_equivar_f_imp_equivar_minimizer[of G X \<phi> ?\<psi> domain\<^sub>f ?img d f]
    by blast
  hence "has_prop (minimizer f domain\<^sub>f d img)
                  (equivar_ind_by_act (carrier G) X \<phi> (set_action ?\<psi>))"
    by blast
  thus ?thesis
    unfolding rel_def set_action.simps
    using rewrite_invar_as_equivar 
    by (metis image_id)
qed
  
end

(*  File:       Symmetry_Of_Functions.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Symmetry Properties of Functions\<close>

theory Symmetry_Of_Functions
  imports "HOL-Algebra.Group_Action"
          "HOL-Algebra.Generated_Groups"
begin

subsection \<open>Functions\<close>

type_synonym ('x, 'y) binary_fun = "'x \<Rightarrow> 'y \<Rightarrow> 'y"

fun extensional_continuation :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'y)" where
  "extensional_continuation f S = (\<lambda> x. if x \<in> S then f x else undefined)"

fun preimg :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'y \<Rightarrow> 'x set" where
  "preimg f S y = {x \<in> S. f x = y}"

subsection \<open>Relations for Symmetry Constructions\<close>

fun restricted_rel :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x set \<Rightarrow> 'x rel" where
  "restricted_rel r S S' = r \<inter> (S \<times> S')"

fun closed_restricted_rel :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "closed_restricted_rel r S T = ((restricted_rel r T S) `` T \<subseteq> T)"

fun action_induced_rel :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x, 'y) binary_fun \<Rightarrow> 'y rel" where
  "action_induced_rel S T \<phi> = {(y, y'). y \<in> T \<and> (\<exists> x \<in> S. \<phi> x y = y')}"

fun product :: "'x rel \<Rightarrow> ('x * 'x) rel" where
  "product r = {(p, p'). (fst p, fst p') \<in> r \<and> (snd p, snd p') \<in> r}"

fun equivariance :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x, 'y) binary_fun \<Rightarrow> ('y * 'y) rel" where
  "equivariance S T \<phi> =
      {((u, v), (x, y)). (u, v) \<in> T \<times> T \<and> (\<exists> z \<in> S. x = \<phi> z u \<and> y = \<phi> z v)}"

fun singleton_set_system :: "'x set \<Rightarrow> 'x set set" where
  "singleton_set_system S = {{x} | x. x \<in> S}"

fun set_action :: "('x, 'r) binary_fun \<Rightarrow> ('x, 'r set) binary_fun" where
  "set_action \<psi> x = image (\<psi> x)"

subsection \<open>Invariance and Equivariance\<close>

text \<open>
  Invariance and equivariance are symmetry properties of functions:
  Invariance means that related preimages have identical images and
  equivariance denotes consistent changes.
\<close>

datatype ('x, 'y) symmetry =
  Invariance "'x rel" |
  Equivariance "'x set" "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"

fun is_symmetry :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x, 'y) symmetry \<Rightarrow> bool" where
  "is_symmetry f (Invariance r) = (\<forall> x. \<forall> y. (x, y) \<in> r \<longrightarrow> f x = f y)" |
  "is_symmetry f (Equivariance s \<tau>) = (\<forall> (\<phi>, \<psi>) \<in> \<tau>. \<forall> x \<in> s. f (\<phi> x) = \<psi> (f x))"

definition action_induced_equivariance :: "'z set \<Rightarrow> 'x set \<Rightarrow> ('z, 'x) binary_fun \<Rightarrow>
        ('z, 'y) binary_fun \<Rightarrow> ('x, 'y) symmetry" where
  "action_induced_equivariance T S \<phi> \<psi> \<equiv> Equivariance S {(\<phi> z, \<psi> z) | z. z \<in> T}"

subsection \<open>Auxiliary Lemmas\<close>

lemma un_left_inv_singleton_set_system: "\<Union> \<circ> singleton_set_system = id"
proof
  fix s :: "'x set"
  have "(\<Union> \<circ> singleton_set_system) s = {x. {x} \<in> singleton_set_system s}"
    by force
  thus "(\<Union> \<circ> singleton_set_system) s = id s"
    by simp
qed

lemma preimg_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'x \<Rightarrow> 'x" and
    S :: "'x set" and
    x :: "'y"
  shows "preimg f (g ` S) x = g ` preimg (f \<circ> g) S x"
proof (safe)
  fix y :: "'x"
  assume "y \<in> preimg f (g ` S) x"
  then obtain z :: "'x" where
    "g z = y" and
    "z \<in> preimg (f \<circ> g) S x"
    unfolding comp_def
    by fastforce
  thus "y \<in> g ` preimg (f \<circ> g) S x"
    by blast
next
  fix y :: "'x"
  assume "y \<in> preimg (f \<circ> g) S x"
  thus "g y \<in> preimg f (g ` S) x"
    by simp
qed

subsection \<open>Rewrite Rules\<close>

theorem rewrite_invar_as_equivar:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    S :: "'x set" and
    T :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows "is_symmetry f (Invariance (action_induced_rel T S \<phi>)) =
            is_symmetry f (action_induced_equivariance T S \<phi> (\<lambda> g. id))"
proof (unfold action_induced_equivariance_def is_symmetry.simps, safe)
  fix
    x :: "'x" and
    g :: "'z"
  assume
    "x \<in> S" and
    "g \<in> T" and
    "\<forall> x y. (x, y) \<in> action_induced_rel T S \<phi> \<longrightarrow> f x = f y"
  moreover with this have "(x, \<phi> g x) \<in> action_induced_rel T S \<phi>"
    unfolding action_induced_rel.simps
    by blast
  ultimately show "f (\<phi> g x) = id (f x)"
    by simp
next
  fix x y :: "'x"
  assume
    equivar: 
      "\<forall> (\<phi>, \<psi>) \<in> {(\<phi> g, id) |g. g \<in> T}. \<forall> x \<in> S. f (\<phi> x) = \<psi> (f x)" and
    rel: "(x, y) \<in> action_induced_rel T S \<phi>"
  then obtain g :: "'z" where
    img: "\<phi> g x = y" and
    elt: "g \<in> T"
    unfolding action_induced_rel.simps
    by blast
  moreover have "x \<in> S"
    using rel 
    by simp
  ultimately have "f (\<phi> g x) = id (f x)"
    using equivar elt
    by blast
  thus "f x = f y"
    using img elt
    by simp
qed

lemma rewrite_invar_ind_by_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    S :: "'z set" and
    T :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows "is_symmetry f (Invariance (action_induced_rel S T \<phi>)) =
            (\<forall> x \<in> S. \<forall> y \<in> T. f y = f (\<phi> x y))"
proof (safe)
  fix
    y :: "'x" and
    x :: "'z"
  assume
    "is_symmetry f (Invariance (action_induced_rel S T \<phi>))" and
    "y \<in> T" and
    "x \<in> S"
  moreover from this have "(y, \<phi> x y) \<in> action_induced_rel S T \<phi>"
    unfolding action_induced_rel.simps
    by blast
  ultimately show "f y = f (\<phi> x y)"
    by simp
next
  assume "\<forall> x \<in> S. \<forall> y \<in> T. f y = f (\<phi> x y)"
  moreover have
    "\<forall> (x, y) \<in> action_induced_rel S T \<phi>. x \<in> T \<and> (\<exists> z \<in> S. y = \<phi> z x)"
    by auto
  ultimately show "is_symmetry f (Invariance (action_induced_rel S T \<phi>))"
    by auto
qed

lemma rewrite_equivariance:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    S :: "'z set" and
    T :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  shows "is_symmetry f (action_induced_equivariance S T \<phi> \<psi>) =
            (\<forall> x \<in> S. \<forall> y \<in> T. f (\<phi> x y) = \<psi> x (f y))"
  unfolding action_induced_equivariance_def
  by auto

lemma rewrite_group_action_img:
  fixes
    m :: "'x monoid" and
    S T :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun" and
    x y :: "'x"
  assumes
    "T \<subseteq> S" and
    "x \<in> carrier m" and
    "y \<in> carrier m" and
    "group_action m S \<phi>"
  shows "\<phi> (x \<otimes> \<^bsub>m\<^esub> y) ` T = \<phi> x ` \<phi> y ` T"
proof (safe)
  fix z :: "'y"
  assume z_in_t: "z \<in> T"
  hence "\<phi> (x \<otimes> \<^bsub>m\<^esub> y) z = \<phi> x (\<phi> y z)"
    using assms group_action.composition_rule[of m S]
    by blast
  thus
    "\<phi> (x \<otimes> \<^bsub>m\<^esub> y) z \<in> \<phi> x ` \<phi> y ` T" and
    "\<phi> x (\<phi> y z) \<in> \<phi> (x \<otimes>\<^bsub>m\<^esub> y) ` T"
    using z_in_t
    by (blast, force)
qed

lemma rewrite_carrier: "carrier (BijGroup UNIV) = {f. bij f}"
  unfolding BijGroup_def Bij_def
  by simp

lemma universal_set_carrier_imp_bij_group:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes "f \<in> carrier (BijGroup UNIV)"
  shows "bij f"
  using rewrite_carrier assms
  by blast

lemma rewrite_sym_group:
  fixes
    f g :: "'a \<Rightarrow> 'a" and
    S :: "'a set"
  assumes
    "f \<in> carrier (BijGroup S)" and
    "g \<in> carrier (BijGroup S)"
  shows
    rewrite_mult: "f \<otimes> \<^bsub>BijGroup S\<^esub> g = extensional_continuation (f \<circ> g) S" and
    rewrite_mult_univ: "S = UNIV \<longrightarrow> f \<otimes> \<^bsub>BijGroup S\<^esub> g = f \<circ> g"
  using assms
  unfolding BijGroup_def compose_def comp_def restrict_def
  by (simp, fastforce)

lemma simp_extensional_univ:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "extensional_continuation f UNIV = f"
  unfolding If_def
  by simp

lemma extensional_continuation_subset:
  fixes
    f :: "'a \<Rightarrow> 'b" and
    S T :: "'a set" and
    x :: "'a"
  assumes
    "T \<subseteq> S" and
    "x \<in> T"
  shows "extensional_continuation f S x = extensional_continuation f T x"
  using assms
  unfolding subset_iff
  by simp

lemma rel_ind_by_coinciding_action_on_subset_eq_restr:
  fixes
    \<phi> \<psi> :: "('a, 'b) binary_fun" and
    S :: "'a set" and
    T U :: "'b set"
  assumes
    "U \<subseteq> T" and
    "\<forall> x \<in> S. \<forall> y \<in> U. \<psi> x y = \<phi> x y"
  shows "action_induced_rel S U \<psi> = restricted_rel (action_induced_rel S T \<phi>) U UNIV"
proof (unfold action_induced_rel.simps restricted_rel.simps, safe)
  fix x :: "'b"
  assume "x \<in> U"
  thus "x \<in> T"
    using assms
    by blast
next
  fix 
    g :: "'a" and
    x :: "'b"
  assume 
    g_in_S: "g \<in> S" and
    x_in_U: "x \<in> U"
  hence "\<phi> g x = \<psi> g x"
    using assms
    by simp
  thus "\<exists> g' \<in> S. \<phi> g' x = \<psi> g x"
    using g_in_S
    by blast
next
  fix 
    g :: "'a" and
    x :: "'b"
  show "\<psi> g x \<in> UNIV"
    by blast
next
  fix 
    g :: "'a" and
    x :: "'b"
  assume  
    g_in_S: "g \<in> S" and
    x_in_U: "x \<in> U"
  hence "\<psi> g x = \<phi> g x"
    using assms
    by simp
  thus "\<exists> g' \<in> S. \<psi> g' x = \<phi> g x"
    using g_in_S
    by blast
qed

lemma coinciding_actions_ind_equal_rel:
  fixes
    S :: "'x set" and
    T :: "'y set" and
    \<phi> \<psi> :: "('x, 'y) binary_fun"
  assumes "\<forall> x \<in> S. \<forall> y \<in> T. \<phi> x y = \<psi> x y"
  shows "action_induced_rel S T \<phi> = action_induced_rel S T \<psi>"
  unfolding extensional_continuation.simps
  using assms
  by auto

subsection \<open>Group Actions\<close>

lemma const_id_is_group_action:
  fixes m :: "'x monoid"
  assumes "group m"
  shows "group_action m UNIV (\<lambda> x. id)"
  using assms
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, safe)
  show "group (BijGroup UNIV)"
    using group_BijGroup
    by metis
next
  show "id \<in> carrier (BijGroup UNIV)"
    unfolding BijGroup_def Bij_def
    by simp
  thus "id = id \<otimes> \<^bsub>BijGroup UNIV\<^esub> id"
    using rewrite_mult_univ comp_id
    by metis
qed

theorem group_act_induces_set_group_act:
  fixes
    m :: "'x monoid" and
    S :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  defines "\<phi>_img \<equiv> (\<lambda> x. extensional_continuation (image (\<phi> x)) (Pow S))"
  assumes "group_action m S \<phi>"
  shows "group_action m (Pow S) \<phi>_img"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, safe)
  show "group m"
    using assms
    unfolding group_action_def group_hom_def
    by simp
next
  show "group (BijGroup (Pow S))"
    using group_BijGroup
    by metis
next
  {
    fix x :: "'x"
    assume "x \<in> carrier m"
    hence "bij_betw (\<phi> x) S S"
      using assms group_action.surj_prop
      unfolding bij_betw_def
      by (simp add: group_action.inj_prop)
    hence "bij_betw (image (\<phi> x)) (Pow S) (Pow S)"
      using bij_betw_Pow
      by metis
    moreover have "\<forall> t \<in> Pow S. \<phi>_img x t = image (\<phi> x) t"
      unfolding \<phi>_img_def
      by simp
    ultimately have "bij_betw (\<phi>_img x) (Pow S) (Pow S)"
      using bij_betw_cong
      by fastforce
    moreover have "\<phi>_img x \<in> extensional (Pow S)"
      unfolding \<phi>_img_def extensional_def
      by simp
    ultimately show "\<phi>_img x \<in> carrier (BijGroup (Pow S))"
      unfolding BijGroup_def Bij_def
      by simp
  }
  fix x y :: "'x"
  note
    \<open>x \<in> carrier m \<Longrightarrow> \<phi>_img x \<in> carrier (BijGroup (Pow S))\<close> and
    \<open>y \<in> carrier m \<Longrightarrow> \<phi>_img y \<in> carrier (BijGroup (Pow S))\<close>
  moreover assume
    carrier_x: "x \<in> carrier m" and
    carrier_y: "y \<in> carrier m"
  ultimately have
    carrier_election_x: "\<phi>_img x \<in> carrier (BijGroup (Pow S))" and
    carrier_election_y: "\<phi>_img y \<in> carrier (BijGroup (Pow S))"
    by (presburger, presburger)
  hence h_closed: "\<forall> T \<in> Pow S. \<phi>_img y T \<in> Pow S"
    using bij_betw_apply Int_Collect
    unfolding BijGroup_def Bij_def partial_object.select_convs
    by (metis (no_types))
  from carrier_election_x carrier_election_y
  have "\<phi>_img x \<otimes> \<^bsub>BijGroup (Pow S)\<^esub> \<phi>_img y =
          extensional_continuation (\<phi>_img x \<circ> \<phi>_img y) (Pow S)"
    using rewrite_mult
    by blast
  moreover have
    "\<forall> T. T \<notin> Pow S
      \<longrightarrow> extensional_continuation (\<phi>_img x \<circ> \<phi>_img y) (Pow S) T = undefined"
    by simp
  moreover have
    "\<forall> T. T \<notin> Pow S \<longrightarrow> \<phi>_img (x \<otimes> \<^bsub>m\<^esub> y) T = undefined" and
    "\<forall> T \<in> Pow S.
        extensional_continuation (\<phi>_img x \<circ> \<phi>_img y) (Pow S) T = \<phi> x ` \<phi> y ` T"
    using h_closed
    unfolding \<phi>_img_def
    by (simp, simp)
  moreover have "\<forall> T \<in> Pow S. \<phi>_img (x \<otimes> \<^bsub>m\<^esub> y) T = \<phi> x ` \<phi> y ` T"
    unfolding \<phi>_img_def extensional_continuation.simps
    using rewrite_group_action_img carrier_x carrier_y assms PowD
    by metis
  ultimately have
    "\<forall> T. \<phi>_img (x \<otimes> \<^bsub>m\<^esub> y) T = (\<phi>_img x \<otimes> \<^bsub>BijGroup (Pow S)\<^esub> \<phi>_img y) T"
    by metis
  thus "\<phi>_img (x \<otimes> \<^bsub>m\<^esub> y) = \<phi>_img x \<otimes> \<^bsub>BijGroup (Pow S)\<^esub> \<phi>_img y"
    by blast
qed

subsection \<open>Invariance and Equivariance\<close>

text \<open>
  It suffices to show equivariance under the group action of a generating set of a group
  to show equivariance under the group action of the whole group.
  For example, it is enough to show invariance under transpositions to show invariance
  under a complete finite symmetric group.
\<close>

theorem equivar_generators_imp_equivar_group:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    m :: "'z monoid" and
    S :: "'z set" and
    T :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  assumes
    equivar: "is_symmetry f (action_induced_equivariance S T \<phi> \<psi>)" and
    action_\<phi>: "group_action m T \<phi>" and
    action_\<psi>: "group_action m (f ` T) \<psi>" and
    gen: "carrier m = generate m S"
  shows "is_symmetry f (action_induced_equivariance (carrier m) T \<phi> \<psi>)"
proof (unfold is_symmetry.simps action_induced_equivariance_def action_induced_rel.simps,
        safe)
  fix
    g :: "'z" and
    x :: "'x"
  assume
    group_elem: "g \<in> carrier m" and
    x_in_t: "x \<in> T"
  have "g \<in> generate m S"
    using group_elem gen
    by blast
  hence "\<forall> x \<in> T. f (\<phi> g x) = \<psi> g (f x)"
  proof (induct g rule: generate.induct)
    case one
    hence "\<forall> x \<in> T. \<phi> \<one> \<^bsub>m\<^esub> x = x"
      using action_\<phi> group_action.id_eq_one restrict_apply
      by metis
    moreover with one have "\<forall> y \<in> (f ` T). \<psi> \<one> \<^bsub>m\<^esub> y = y"
      using action_\<psi>  group_action.id_eq_one restrict_apply
      by metis
    ultimately show ?case
      by simp
  next
    case (incl g)
    hence "\<forall> x \<in> T. \<phi> g x \<in> T"
      using action_\<phi> gen generate.incl group_action.element_image
      by metis
    thus ?case
      using incl equivar rewrite_equivariance
      unfolding is_symmetry.simps
      by metis
  next
    case (inv g)
    hence in_t: "\<forall> x \<in> T. \<phi> (inv \<^bsub>m\<^esub> g) x \<in> T"
      using action_\<phi> gen generate.inv group_action.element_image
      by metis
    hence "\<forall> x \<in> T. f (\<phi> g (\<phi> (inv \<^bsub>m\<^esub> g) x)) = \<psi> g (f (\<phi> (inv \<^bsub>m\<^esub> g) x))"
      using gen action_\<phi> equivar local.inv rewrite_equivariance
      by metis
    moreover have "\<forall> x \<in> T. \<phi> g (\<phi> (inv \<^bsub>m\<^esub> g) x) = x"
      using action_\<phi> gen generate.incl group.inv_closed group_action.orbit_sym_aux
            group.inv_inv group_action.group_hom local.inv
      unfolding group_hom_def
      by (metis (full_types))
    ultimately have "\<forall> x \<in> T. \<psi> g (f (\<phi> (inv \<^bsub>m\<^esub> g) x)) = f x"
      by simp
    moreover have in_img_t: "\<forall> x \<in> T. f (\<phi> (inv \<^bsub>m\<^esub> g) x) \<in> f ` T"
      using in_t
      by blast
    ultimately have
      "\<forall> x \<in> T. \<psi> (inv \<^bsub>m\<^esub> g) (\<psi> g (f (\<phi> (inv \<^bsub>m\<^esub> g) x))) = \<psi> (inv \<^bsub>m\<^esub> g) (f x)"
      using action_\<psi> gen
      by metis
    moreover have
      "\<forall> x \<in> T. \<psi> (inv \<^bsub>m\<^esub> g) (\<psi> g (f (\<phi> (inv \<^bsub>m\<^esub> g) x))) = f (\<phi> (inv \<^bsub>m\<^esub> g) x)"
      using in_img_t action_\<psi> gen generate.incl group_action.orbit_sym_aux local.inv
      by metis
    ultimately show ?case
      by simp
  next
    case (eng g\<^sub>1 g\<^sub>2)
    assume
      equivar\<^sub>1: "\<forall> x \<in> T. f (\<phi> g\<^sub>1 x) = \<psi> g\<^sub>1 (f x)" and
      equivar\<^sub>2: "\<forall> x \<in> T. f (\<phi> g\<^sub>2 x) = \<psi> g\<^sub>2 (f x)" and
      gen\<^sub>1: "g\<^sub>1 \<in> generate m S" and
      gen\<^sub>2: "g\<^sub>2 \<in> generate m S"
    hence "\<forall> x \<in> T. \<phi> g\<^sub>2 x \<in> T"
      using gen action_\<phi> group_action.element_image
      by metis
    hence "\<forall> x \<in> T. f (\<phi> g\<^sub>1 (\<phi> g\<^sub>2 x)) = \<psi> g\<^sub>1 (f (\<phi> g\<^sub>2 x))"
      using equivar\<^sub>1
      by simp
    moreover have "\<forall> x \<in> T. f (\<phi> g\<^sub>2 x) = \<psi> g\<^sub>2 (f x)"
      using equivar\<^sub>2
      by simp
    ultimately show ?case
      using action_\<phi> action_\<psi> gen gen\<^sub>1 gen\<^sub>2 group_action.composition_rule imageI
      by (metis (no_types, lifting))
  qed
  thus "f (\<phi> g x) = \<psi> g (f x)"
    using x_in_t
    by simp
qed

lemma invar_parameterized_fun:
  fixes
    f :: "'x \<Rightarrow> ('x \<Rightarrow> 'y)" and
    r :: "'x rel"
  assumes
    "\<forall> x. is_symmetry (f x) (Invariance r)" and
    "is_symmetry f (Invariance r)"
  shows "is_symmetry (\<lambda> x. f x x) (Invariance r)"
  using assms
  by simp

lemma invar_under_subset_rel:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    r s :: "'x rel"
  assumes
    subset: "r \<subseteq> s" and
    invar: "is_symmetry f (Invariance s)"
  shows "is_symmetry f (Invariance r)"
  using assms
  by auto

lemma equivar_ind_by_act_coincide:
  fixes
    S :: "'x set" and
    T :: "'y set" and
    f :: "'y \<Rightarrow> 'z" and
    \<phi> \<phi>' :: "('x, 'y) binary_fun" and
    \<psi> :: "('x, 'z) binary_fun"
  assumes "\<forall> x \<in> S. \<forall> y \<in> T. \<phi> x y = \<phi>' x y"
  shows "is_symmetry f (action_induced_equivariance S T \<phi> \<psi>) =
            is_symmetry f (action_induced_equivariance S T \<phi>' \<psi>)"
  using assms
  unfolding rewrite_equivariance
  by simp

lemma equivar_under_subset:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    S T :: "'x set" and
    \<tau> :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"
  assumes
    "is_symmetry f (Equivariance S \<tau>)" and
    "T \<subseteq> S"
  shows "is_symmetry f (Equivariance T \<tau>)"
  using assms
  unfolding is_symmetry.simps
  by blast

lemma equivar_under_subset':
  fixes
    f :: "'x \<Rightarrow> 'y" and
    S :: "'x set" and
    \<tau> \<upsilon> :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"
  assumes
    "is_symmetry f (Equivariance S \<tau>)" and
    "\<upsilon> \<subseteq> \<tau>"
  shows "is_symmetry f (Equivariance S \<upsilon>)"
  using assms
  unfolding is_symmetry.simps
  by blast

theorem group_action_equivar_f_imp_equivar_preimg:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    \<D>\<^sub>f S :: "'x set" and
    m :: "'z monoid" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun" and
    x :: "'z"
  defines "equivar_prop \<equiv> action_induced_equivariance (carrier m) \<D>\<^sub>f \<phi> \<psi>"
  assumes
    action_\<phi>: "group_action m S \<phi>" and
    action_res: "group_action m UNIV \<psi>" and
    dom_in_s: "\<D>\<^sub>f \<subseteq> S" and
    closed_domain: (* Could the closed_domain requirement be weakened? *)
      "closed_restricted_rel (action_induced_rel (carrier m) S \<phi>) S \<D>\<^sub>f" and
    equivar_f: "is_symmetry f equivar_prop" and
    group_elem_x: "x \<in> carrier m"
  shows "\<forall> y. preimg f \<D>\<^sub>f (\<psi> x y) = (\<phi> x) ` (preimg f \<D>\<^sub>f y)"
proof (safe)
  interpret action_\<phi>: "group_action" "m" "S" "\<phi>"
    using action_\<phi>
    by simp
  interpret action_results: "group_action" "m" "UNIV" "\<psi>"
    using action_res
    by simp
  have group_elem_inv: "(inv \<^bsub>m\<^esub> x) \<in> carrier m"
    using group.inv_closed action_\<phi>.group_hom group_elem_x
    unfolding group_hom_def
    by metis
  fix
    y :: "'y" and
    z :: "'x"
  assume preimg_el: "z \<in> preimg f \<D>\<^sub>f (\<psi> x y)"
  obtain a :: "'x" where
    img: "a = \<phi> (inv \<^bsub>m\<^esub> x) z"
    by simp
  have domain: "z \<in> \<D>\<^sub>f \<and> z \<in> S"
    using preimg_el dom_in_s
    by auto
  hence "a \<in> S"
    using dom_in_s action_\<phi> group_elem_inv preimg_el img action_\<phi>.element_image
    by auto
  hence "(z, a) \<in> (action_induced_rel (carrier m) S \<phi>) \<inter> (\<D>\<^sub>f \<times> S)"
    using img preimg_el domain group_elem_inv
    by auto
  hence "a \<in> ((action_induced_rel (carrier m) S \<phi>) \<inter> (\<D>\<^sub>f \<times> S)) `` \<D>\<^sub>f"
    using img preimg_el domain group_elem_inv
    by auto
  hence a_in_domain: "a \<in> \<D>\<^sub>f"
    using closed_domain
    by auto
  moreover have "(\<phi> (inv \<^bsub>m\<^esub> x), \<psi> (inv \<^bsub>m\<^esub> x)) \<in> {(\<phi> g, \<psi> g) | g. g \<in> carrier m}"
    using group_elem_inv
    by auto
  ultimately have "f a = \<psi> (inv \<^bsub>m\<^esub> x) (f z)"
    using domain equivar_f img
    unfolding equivar_prop_def action_induced_equivariance_def
    by simp
  hence "f a = y"
    using preimg_el action_results.group_hom action_results.orbit_sym_aux
          group_elem_x
    by simp
  hence "a \<in> preimg f \<D>\<^sub>f y"
    using a_in_domain
    by simp
  moreover have "z = \<phi> x a"
    using action_\<phi>.group_hom action_\<phi>.orbit_sym_aux img domain
          a_in_domain group_elem_x group_elem_inv group.inv_inv
    unfolding group_hom_def
    by metis
  ultimately show "z \<in> (\<phi> x) ` (preimg f \<D>\<^sub>f y)"
    by simp
next
  fix
    y :: "'y" and
    z :: "'x"
  assume "z \<in> preimg f \<D>\<^sub>f y"
  hence domain: "f z = y \<and> z \<in> \<D>\<^sub>f \<and> z \<in> S"
    using dom_in_s
    by auto
  hence "\<phi> x z \<in> S"
    using group_elem_x group_action.element_image action_\<phi>
    by metis
  hence "(z, \<phi> x z) \<in> (action_induced_rel (carrier m) S \<phi>) \<inter> (\<D>\<^sub>f \<times> S) \<inter> \<D>\<^sub>f \<times> S"
    using group_elem_x domain
    by auto
  hence "\<phi> x z \<in> \<D>\<^sub>f"
    using closed_domain
    by auto
  moreover have "(\<phi> x, \<psi> x) \<in> {(\<phi> a, \<psi> a) | a. a \<in> carrier m}"
    using group_elem_x
    by blast
  ultimately show "\<phi> x z \<in> preimg f \<D>\<^sub>f (\<psi> x y)"
    using equivar_f domain
    unfolding equivar_prop_def action_induced_equivariance_def
    by simp
qed

subsection \<open>Function Composition\<close>

lemma invar_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    r :: "'x rel"
  assumes "is_symmetry f (Invariance r)"
  shows "is_symmetry (g \<circ> f) (Invariance r)"
  using assms
  by simp

lemma equivar_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    S :: "'x set" and
    T :: "'y set" and
    \<tau> :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set" and
    \<upsilon> :: "(('y \<Rightarrow> 'y) \<times> ('z \<Rightarrow> 'z)) set"
  defines
    "transitive_acts \<equiv>
      {(\<phi>, \<psi>). \<exists> \<chi> :: 'y \<Rightarrow> 'y. (\<phi>, \<chi>) \<in> \<tau> \<and> (\<chi>, \<psi>) \<in> \<upsilon> \<and> \<chi> ` f ` S \<subseteq> T}"
  assumes
    "f ` S \<subseteq> T" and
    "is_symmetry f (Equivariance S \<tau>)" and
    "is_symmetry g (Equivariance T \<upsilon>)"
  shows "is_symmetry (g \<circ> f) (Equivariance S transitive_acts)"
proof (unfold transitive_acts_def is_symmetry.simps comp_def, safe)
  fix
    \<phi> :: "'x \<Rightarrow> 'x" and
    \<chi> :: "'y \<Rightarrow> 'y" and
    \<psi> :: "'z \<Rightarrow> 'z" and
    x :: "'x"
  assume
    x_in_X: "x \<in> S" and
    \<chi>_img\<^sub>f_img\<^sub>s_in_t: "\<chi> ` f ` S \<subseteq> T" and
    act_f: "(\<phi>, \<chi>) \<in> \<tau>" and
    act_g: "(\<chi>, \<psi>) \<in> \<upsilon>"
  hence "f x \<in> T \<and> \<chi> (f x) \<in> T"
    using assms
    by blast
  hence "\<psi> (g (f x)) = g (\<chi> (f x))"
    using act_g assms
    by fastforce
  also have "g (f (\<phi> x)) = g (\<chi> (f x))"
    using assms act_f x_in_X
    by fastforce
  finally show "g (f (\<phi> x)) = \<psi> (g (f x))"
    by simp
qed

lemma equivar_ind_by_action_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    S :: "'w set" and
    T :: "'x set" and
    U :: "'y set" and
    \<phi> :: "('w, 'x) binary_fun" and
    \<chi> :: "('w, 'y) binary_fun" and
    \<psi> :: "('w, 'z) binary_fun"
  assumes
    "f ` T \<subseteq> U" and
    "\<forall> x \<in> S. \<chi> x ` f ` T \<subseteq> U" and
    "is_symmetry f (action_induced_equivariance S T \<phi> \<chi>)" and
    "is_symmetry g (action_induced_equivariance S U \<chi> \<psi>)"
  shows "is_symmetry (g \<circ> f) (action_induced_equivariance S T \<phi> \<psi>)"
proof -
  let ?a\<^sub>\<phi> = "{(\<phi> a, \<chi> a) | a. a \<in> S}" and
      ?a\<^sub>\<psi> = "{(\<chi> a, \<psi> a) | a. a \<in> S}"
  have "\<forall> a \<in> S. (\<phi> a, \<chi> a) \<in> {(\<phi> a, \<chi> a) | b. b \<in> S}
            \<and> (\<chi> a, \<psi> a) \<in> {(\<chi> b, \<psi> b) | b. b \<in> S} \<and> \<chi> a ` f ` T \<subseteq> U"
    using assms
    by blast
  hence "{(\<phi> a, \<psi> a) | a. a \<in> S}
      \<subseteq> {(\<phi>, \<psi>). \<exists> \<upsilon>. (\<phi>, \<upsilon>) \<in> ?a\<^sub>\<phi> \<and> (\<upsilon>, \<psi>) \<in> ?a\<^sub>\<psi> \<and> \<upsilon> ` f ` T \<subseteq> U}"
    by blast
  hence "is_symmetry (g \<circ> f) (Equivariance T {(\<phi> a, \<psi> a) | a. a \<in> S})"
    using assms equivar_comp[of _ _ _ ?a\<^sub>\<phi> _ ?a\<^sub>\<psi>] equivar_under_subset'
    unfolding action_induced_equivariance_def
    by (metis (no_types, lifting))
  thus ?thesis
    unfolding action_induced_equivariance_def
    by blast
qed

lemma equivar_set_minus:
  fixes
    f g :: "'x \<Rightarrow> 'y set" and
    S :: "'z set" and
    T :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  assumes
    f_equivar: "is_symmetry f (action_induced_equivariance S T \<phi> (set_action \<psi>))" and
    g_equivar: "is_symmetry g (action_induced_equivariance S T \<phi> (set_action \<psi>))" and
    bij_a: "\<forall> a \<in> S. bij (\<psi> a)"
  shows
    "is_symmetry (\<lambda> b. f b - g b) (action_induced_equivariance S T \<phi> (set_action \<psi>))"
proof -
  have
    "\<forall> a \<in> S. \<forall> x \<in> T. f (\<phi> a x) = \<psi> a ` (f x)" and
    "\<forall> a \<in> S. \<forall> x \<in> T. g (\<phi> a x) = \<psi> a ` (g x)"
    using f_equivar g_equivar
    unfolding rewrite_equivariance
    by (simp, simp)
  hence "\<forall> a \<in> S. \<forall> b \<in> T. f (\<phi> a b) - g (\<phi> a b) = \<psi> a ` (f b) - \<psi> a ` (g b)"
    by blast
  moreover have "\<forall> a \<in> S. \<forall> u v. \<psi> a ` u - \<psi> a ` v = \<psi> a ` (u - v)"
    using bij_a image_set_diff
    unfolding bij_def
    by blast
  ultimately show ?thesis
    unfolding set_action.simps
    using rewrite_equivariance
    by fastforce
qed

lemma equivar_union_under_image_action:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    S :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows "is_symmetry \<Union> (action_induced_equivariance S UNIV
              (set_action (set_action \<phi>)) (set_action \<phi>))"
  unfolding action_induced_equivariance_def is_symmetry.simps set_action.simps
  by blast

end
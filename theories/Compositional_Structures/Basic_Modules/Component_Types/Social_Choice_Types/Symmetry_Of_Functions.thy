(*  File:       Symmetry_Of_Functions.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Function Symmetry Properties\<close>

theory Symmetry_Of_Functions
  imports "HOL-Algebra.Group_Action"
          "HOL-Algebra.Generated_Groups"
begin

subsection \<open>Functions\<close>

type_synonym ('x, 'y) binary_fun = "'x \<Rightarrow> 'y \<Rightarrow> 'y"

fun extensional_continuation :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'y)" where
  "extensional_continuation f s = (\<lambda> x. if (x \<in> s) then (f x) else undefined)"

fun preimg :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'y \<Rightarrow> 'x set" where
  "preimg f s x = {x' \<in> s. f x' = x}"

text \<open>Relations\<close>

fun restr_rel :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x set \<Rightarrow> 'x rel" where
  "restr_rel r s s' = r \<inter> s \<times> s'"

fun closed_under_restr_rel :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "closed_under_restr_rel r s t = ((restr_rel r t s) `` t \<subseteq> t)"

fun rel_induced_by_action :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x, 'y) binary_fun \<Rightarrow> 'y rel" where
  "rel_induced_by_action s t \<phi> = {(y, y') \<in> t \<times> t. \<exists> x \<in> s. \<phi> x y = y'}"

fun product_rel :: "'x rel \<Rightarrow> ('x * 'x) rel" where
  "product_rel r = {(p, p'). (fst p, fst p') \<in> r \<and> (snd p, snd p') \<in> r}"

fun equivariance_rel :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x,'y) binary_fun \<Rightarrow> ('y * 'y) rel" where
  "equivariance_rel s t \<phi> = {((u, v), (x, y)). (u, v) \<in> t \<times> t \<and> (\<exists> z \<in> s. x = \<phi> z u \<and> y = \<phi> z v)}"

fun set_closed_under_rel :: "'x set \<Rightarrow> 'x rel \<Rightarrow> bool" where
  "set_closed_under_rel s r = (\<forall> x y. (x, y) \<in> r \<longrightarrow> x \<in> s \<longrightarrow> y \<in> s)"

fun singleton_set_system :: "'x set \<Rightarrow> 'x set set" where
  "singleton_set_system s = {{x} | x. x \<in> s}"

fun set_action :: "('x, 'r) binary_fun \<Rightarrow> ('x, 'r set) binary_fun" where
  "set_action \<psi> x = image (\<psi> x)"

subsection \<open>Invariance and Equivariance\<close>

text \<open>
  Invariance and equivariance are symmetry properties of functions:
  Invariance means that related preimages have identical images and
  equivariance denotes consistent changes.
\<close>

datatype ('x, 'y) property =
  Invariance "'x rel" |
  Equivariance "'x set" "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"

fun satisfies :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x, 'y) property \<Rightarrow> bool" where
  "satisfies f (Invariance r) = (\<forall> x. \<forall> y. (x, y) \<in> r \<longrightarrow> f x = f y)" |
  "satisfies f (Equivariance s \<tau>) = (\<forall> (\<phi>, \<psi>) \<in> \<tau>. \<forall> x \<in> s. \<phi> x \<in> s \<longrightarrow> f (\<phi> x) = \<psi> (f x))"

definition equivar_ind_by_act :: "'z set \<Rightarrow> 'x set \<Rightarrow> ('z, 'x) binary_fun
      \<Rightarrow> ('z, 'y) binary_fun \<Rightarrow> ('x,'y) property" where
  "equivar_ind_by_act s t \<phi> \<psi> = Equivariance t {(\<phi> x, \<psi> x) | x. x \<in> s}"

subsection \<open>Auxiliary Lemmas\<close>

lemma inj_imp_inj_on_set_system:
  fixes f :: "'x \<Rightarrow> 'y"
  assumes "inj f"
  shows "inj (\<lambda> s. {f ` x | x. x \<in> s})"
proof (unfold inj_def, safe)
  fix
    s :: "'x set set" and
    t :: "'x set set" and
    x :: "'x set"
  assume f_elem_s_eq_f_elem_t: "{f ` x' | x'. x' \<in> s} = {f ` x' | x'. x' \<in> t}"
  then obtain y :: "'x set" where
    "f ` y = f ` x"
    by metis
  hence y_eq_x: "y = x"
    using image_inv_f_f assms
    by metis
  moreover have
    "x \<in> t \<longrightarrow> f ` x \<in> {f ` x' | x'. x' \<in> s}" and
    "x \<in> s \<longrightarrow> f ` x \<in> {f ` x' | x'. x' \<in> t}"
    using f_elem_s_eq_f_elem_t
    by auto
  ultimately have "x \<in> t \<longrightarrow> y \<in> s" and "x \<in> s \<longrightarrow> y \<in> t"
    using assms
    by (simp add: inj_image_eq_iff, simp add: inj_image_eq_iff)
  thus "x \<in> t \<Longrightarrow> x \<in> s" and "x \<in> s \<Longrightarrow> x \<in> t"
    using y_eq_x
    by (simp, simp)
qed

lemma inj_and_surj_imp_surj_on_set_system:
  fixes f :: "'x \<Rightarrow> 'y"
  assumes
    "inj f" and
    "surj f"
  shows "surj (\<lambda> s. {f ` x | x. x \<in> s})"
proof (unfold surj_def, safe)
  fix s :: "'y set set"
  have "\<forall> x. f ` (the_inv f) ` x = x"
    using image_f_inv_f assms surj_imp_inv_eq the_inv_f_f
    by (metis (no_types, opaque_lifting))
  hence "s = {f ` (the_inv f) ` x | x. x \<in> s}"
    by simp
  also have "{f ` (the_inv f) ` x | x. x \<in> s} =
              {f ` x | x. x \<in> {(the_inv f) ` x | x. x \<in> s}}"
    by blast
  finally show "\<exists> t. s = {f ` x | x. x \<in> t}"
    by blast
qed

lemma bij_imp_bij_on_set_system:
  fixes f :: "'x \<Rightarrow> 'y"
  assumes "bij f"
  shows "bij (\<lambda> s. {f ` x | x. x \<in> s})"
proof (unfold bij_def)
  have "range f = UNIV"
    using assms
    unfolding bij_betw_def
    by safe
  moreover have "inj f"
    using assms
    unfolding bij_betw_def
    by safe
  ultimately show "inj (\<lambda> s. {f ` x | x. x \<in> s}) \<and> surj (\<lambda> s. {f ` x | x. x \<in> s})"
    using inj_imp_inj_on_set_system
    by (simp add: inj_and_surj_imp_surj_on_set_system)
qed

lemma un_left_inv_singleton_set_system: "\<Union> \<circ> singleton_set_system = id"
proof
  fix s :: "'x set"
  have "(\<Union> \<circ> singleton_set_system) s = {x. \<exists> s' \<in> singleton_set_system s. x \<in> s'}"
    by auto
  also have "{x. \<exists> s' \<in> singleton_set_system s. x \<in> s'} = {x. {x} \<in> singleton_set_system s}"
    by auto
  also have "{x. {x} \<in> singleton_set_system s} = {x. {x} \<in> {{x} | x. x \<in> s}}"
    by simp
  finally show "(\<Union> \<circ> singleton_set_system) s = id s"
    by simp
qed

lemma the_inv_comp:
  fixes
    f :: "'y \<Rightarrow> 'z" and
    g :: "'x \<Rightarrow> 'y" and
    s :: "'x set" and
    t :: "'y set" and
    u :: "'z set" and
    x :: "'z"
  assumes
    "bij_betw f t u" and
    "bij_betw g s t" and
    "x \<in> u"
  shows "the_inv_into s (f \<circ> g) x = ((the_inv_into s g) \<circ> (the_inv_into t f)) x"
proof (clarsimp)
  have el_Y: "the_inv_into t f x \<in> t"
    using assms bij_betw_apply bij_betw_the_inv_into
    by metis
  hence "g (the_inv_into s g (the_inv_into t f x)) = the_inv_into t f x"
    using assms f_the_inv_into_f_bij_betw
    by metis
  moreover have "f (the_inv_into t f x) = x"
    using el_Y assms f_the_inv_into_f_bij_betw
    by metis
  ultimately have "(f \<circ> g) (the_inv_into s g (the_inv_into t f x)) = x"
    by simp
  hence "the_inv_into s (f \<circ> g) x =
      the_inv_into s (f \<circ> g) ((f \<circ> g) (the_inv_into s g (the_inv_into t f x)))"
    by presburger
  also have
    "the_inv_into s (f \<circ> g) ((f \<circ> g) (the_inv_into s g (the_inv_into t f x))) =
      the_inv_into s g (the_inv_into t f x)"
    using assms bij_betw_apply bij_betw_imp_inj_on bij_betw_the_inv_into bij_betw_trans
          the_inv_into_f_eq
    by (metis (no_types, lifting))
  finally show "the_inv_into s (f \<circ> g) x = the_inv_into s g (the_inv_into t f x)"
    by blast
qed

lemma preimg_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'x \<Rightarrow> 'x" and
    s :: "'x set" and
    x :: "'y"
  shows "preimg f (g ` s) x = g ` preimg (f \<circ> g) s x"
proof (safe)
  fix y :: "'x"
  assume "y \<in> preimg f (g ` s) x"
  then obtain z :: "'x" where
    "g z = y" and
    "z \<in> preimg (f \<circ> g) s x"
    unfolding comp_def
    by fastforce
  thus "y \<in> g ` preimg (f \<circ> g) s x"
    by blast
next
  fix y :: "'x"
  assume "y \<in> preimg (f \<circ> g) s x"
  thus "g y \<in> preimg f (g ` s) x"
    by simp
qed

subsection \<open>Rewrite Rules\<close>

theorem rewrite_invar_as_equivar:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    s :: "'x set" and
    t :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows "satisfies f (Invariance (rel_induced_by_action t s \<phi>)) =
            satisfies f (equivar_ind_by_act t s \<phi> (\<lambda> g. id))"
proof (unfold equivar_ind_by_act_def, simp, safe)
  fix
    x :: "'x" and
    y :: "'z"
  assume
    "x \<in> s" and
    "y \<in> t" and
    "\<phi> y x \<in> s"
  thus
    "(\<forall> x' y'. x' \<in> s \<and> y' \<in> s \<and> (\<exists> z \<in> t. \<phi> z x' = y') \<longrightarrow> f x' = f y')
        \<Longrightarrow> (f (\<phi> y x) = id (f x))" and
    "(\<forall> x' y'. (\<exists> z. x' = \<phi> z \<and> y' = id \<and> z \<in> t) \<longrightarrow>
        (\<forall> z \<in> s. x' z \<in> s \<longrightarrow> f (x' z) = y' (f z)))
        \<Longrightarrow> (f x = f (\<phi> y x))"
    unfolding id_def
    by (metis, metis)
qed

lemma rewrite_invar_ind_by_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    s :: "'z set" and
    t :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows "satisfies f (Invariance (rel_induced_by_action s t \<phi>)) =
          (\<forall> x \<in> s. \<forall> y \<in> t. \<phi> x y \<in> t \<longrightarrow> f y = f (\<phi> x y))"
proof (safe)
  fix
    y :: "'x" and
    x :: "'z"
  assume
    "satisfies f (Invariance (rel_induced_by_action s t \<phi>))" and
    "y \<in> t" and
    "x \<in> s" and
    "\<phi> x y \<in> t"
  moreover from this have "(y, \<phi> x y) \<in> rel_induced_by_action s t \<phi>"
    unfolding rel_induced_by_action.simps
    by blast
  ultimately show "f y = f (\<phi> x y)"
    by simp
next
  assume "\<forall> x \<in> s. \<forall> y \<in> t. \<phi> x y \<in> t \<longrightarrow> f y = f (\<phi> x y)"
  moreover have
    "\<forall> (x, y) \<in> rel_induced_by_action s t \<phi>. x \<in> t \<and> y \<in> t \<and> (\<exists> z \<in> s. y = \<phi> z x)"
    by auto
  ultimately show "satisfies f (Invariance (rel_induced_by_action s t \<phi>))"
    by auto
qed

lemma rewrite_equivar_ind_by_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    s :: "'z set" and
    t :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  shows "satisfies f (equivar_ind_by_act s t \<phi> \<psi>) =
          (\<forall> x \<in> s. \<forall> y \<in> t. \<phi> x y \<in> t \<longrightarrow> f (\<phi> x y) = \<psi> x (f y))"
  unfolding equivar_ind_by_act_def
  by auto

lemma rewrite_group_act_img:
  fixes
    m :: "'x monoid" and
    s :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun" and
    t :: "'y set" and
    x :: "'x" and
    y :: "'x"
  assumes
    "t \<subseteq> s" and
    "x \<in> carrier m" and
    "y \<in> carrier m" and
    "group_action m s \<phi>"
  shows "\<phi> (x \<otimes> \<^bsub>m\<^esub> y) ` t = \<phi> x ` \<phi> y ` t"
proof (safe)
  fix z :: "'y"
  assume z_in_t: "z \<in> t"
  hence "\<phi> (x \<otimes> \<^bsub>m\<^esub> y) z = \<phi> x (\<phi> y z)"
    using assms group_action.composition_rule[of m s]
    by blast
  thus
    "\<phi> (x \<otimes> \<^bsub>m\<^esub> y) z \<in> \<phi> x ` \<phi> y ` t" and
    "\<phi> x (\<phi> y z) \<in> \<phi> (x \<otimes>\<^bsub>m\<^esub> y) ` t"
    using z_in_t
    by (blast, force)
qed

lemma rewrite_carrier: "carrier (BijGroup UNIV) = {f'. bij f'}"
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
    f :: "'a \<Rightarrow> 'a" and
    g :: "'a \<Rightarrow> 'a" and
    s :: "'a set"
  assumes
    f_carrier: "f \<in> carrier (BijGroup s)" and
    g_carrier: "g \<in> carrier (BijGroup s)"
  shows
    rewrite_mult: "f \<otimes> \<^bsub>BijGroup s\<^esub> g = extensional_continuation (f \<circ> g) s" and
    rewrite_mult_univ: "s = UNIV \<longrightarrow> f \<otimes> \<^bsub>BijGroup s\<^esub> g = f \<circ> g"
proof -
  show "f \<otimes> \<^bsub>BijGroup s\<^esub> g = extensional_continuation (f \<circ> g) s"
    using f_carrier g_carrier
    unfolding BijGroup_def compose_def comp_def restrict_def
    by simp
next
  show "s = UNIV \<longrightarrow> f \<otimes> \<^bsub>BijGroup s\<^esub> g = f \<circ> g"
    using f_carrier g_carrier
    unfolding BijGroup_def compose_def comp_def restrict_def
    by fastforce
qed

lemma simp_extensional_univ:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "extensional_continuation f UNIV = f"
  unfolding If_def
  by simp

lemma extensional_continuation_subset:
  fixes
    f :: "'a \<Rightarrow> 'b" and
    s :: "'a set" and
    t :: "'a set" and
    x :: "'a"
  assumes
    "t \<subseteq> s" and
    "x \<in> t"
  shows "extensional_continuation f s x = extensional_continuation f t x"
  using assms
  unfolding subset_iff
  by simp

lemma rel_ind_by_coinciding_action_on_subset_eq_restr:
  fixes
    \<phi> :: "('a, 'b) binary_fun" and
    \<psi> :: "('a, 'b) binary_fun" and
    s :: "'a set" and
    t :: "'b set" and
    u :: "'b set"
  assumes
    "u \<subseteq> t" and
    "\<forall> x \<in> s. \<forall> y \<in> u. \<psi> x y = \<phi> x y"
  shows "rel_induced_by_action s u \<psi> = Restr (rel_induced_by_action s t \<phi>) u"
proof (unfold rel_induced_by_action.simps)
  have "{(x, y). (x, y) \<in> u \<times> u \<and> (\<exists> z \<in> s. \<psi> z x = y)}
          = {(x, y). (x, y) \<in> u \<times> u \<and> (\<exists> z \<in> s. \<phi> z x = y)}"
    using assms
    by auto
  also have "... = Restr {(x, y). (x, y) \<in> t \<times> t \<and> (\<exists> z \<in> s. \<phi> z x = y)} u"
    using assms
    by blast
  finally show "{(x, y). (x, y) \<in> u \<times> u \<and> (\<exists> z \<in> s. \<psi> z x = y)} =
                  Restr {(x, y). (x, y) \<in> t \<times> t \<and> (\<exists> z \<in> s. \<phi> z x = y)} u"
    by simp
qed

lemma coinciding_actions_ind_equal_rel:
  fixes
    s :: "'x set" and
    t :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun" and
    \<psi> :: "('x, 'y) binary_fun"
  assumes "\<forall> x \<in> s. \<forall> y \<in> t. \<phi> x y = \<psi> x y"
  shows "rel_induced_by_action s t \<phi> = rel_induced_by_action s t \<psi>"
  unfolding extensional_continuation.simps
  using assms
  by auto

subsection \<open>Group Actions\<close>

lemma const_id_is_group_act:
  fixes m :: "'x monoid"
  assumes "group m"
  shows "group_action m UNIV (\<lambda> x. id)"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, safe)
  show "group m"
    using assms
    by blast
next
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
    s :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  defines "\<phi>_img \<equiv> (\<lambda> x. extensional_continuation (image (\<phi> x)) (Pow s))"
  assumes "group_action m s \<phi>"
  shows "group_action m (Pow s) \<phi>_img"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, safe)
  show "group m"
    using assms
    unfolding group_action_def group_hom_def
    by simp
next
  show "group (BijGroup (Pow s))"
    using group_BijGroup
    by metis
next
  {
    fix x :: "'x"
    assume car_x: "x \<in> carrier m"
    hence "bij_betw (\<phi> x) s s"
      using assms group_action.surj_prop
      unfolding bij_betw_def
      by (simp add: group_action.inj_prop)
    hence "bij_betw (image (\<phi> x)) (Pow s) (Pow s)"
      using bij_betw_Pow
      by metis
    moreover have "\<forall> t \<in> Pow s. \<phi>_img x t = image (\<phi> x) t"
      unfolding \<phi>_img_def
      by simp
    ultimately have "bij_betw (\<phi>_img x) (Pow s) (Pow s)"
      using bij_betw_cong
      by fastforce
    moreover have "\<phi>_img x \<in> extensional (Pow s)"
      unfolding \<phi>_img_def extensional_def
      by simp
    ultimately show "\<phi>_img x \<in> carrier (BijGroup (Pow s))"
      unfolding BijGroup_def Bij_def
      by simp
  }
  fix
    x :: "'x" and
    y :: "'x"
  note
    car_x_el = \<open>x \<in> carrier m \<Longrightarrow> \<phi>_img x \<in> carrier (BijGroup (Pow s))\<close> and
    car_y_el = \<open>y \<in> carrier m \<Longrightarrow> \<phi>_img y \<in> carrier (BijGroup (Pow s))\<close>
  assume
    car_x: "x \<in> carrier m" and
    car_y: "y \<in> carrier m"
  hence car_els: "\<phi>_img x \<in> carrier (BijGroup (Pow s)) \<and> \<phi>_img y \<in> carrier (BijGroup (Pow s))"
    using car_x_el car_y_el car_y
    by blast
  hence h_closed: "\<forall> t. t \<in> Pow s \<longrightarrow> \<phi>_img y t \<in> Pow s"
    using bij_betw_apply Int_Collect partial_object.select_convs(1)
    unfolding BijGroup_def Bij_def
    by metis
  from car_els
  have "\<phi>_img x \<otimes> \<^bsub>BijGroup (Pow s)\<^esub> \<phi>_img y =
          extensional_continuation (\<phi>_img x \<circ> \<phi>_img y) (Pow s)"
    using rewrite_mult
    by blast
  moreover have
    "\<forall> t. t \<notin> Pow s \<longrightarrow> extensional_continuation (\<phi>_img x \<circ> \<phi>_img y) (Pow s) t = undefined"
    by simp
  moreover have "\<forall> t. t \<notin> Pow s \<longrightarrow> \<phi>_img (x \<otimes> \<^bsub>m\<^esub> y) t = undefined"
    unfolding \<phi>_img_def
    by simp
  moreover have
    "\<forall> t. t \<in> Pow s \<longrightarrow> extensional_continuation (\<phi>_img x \<circ> \<phi>_img y) (Pow s) t = \<phi> x ` \<phi> y ` t"
    using h_closed
    unfolding \<phi>_img_def
    by simp
  moreover have "\<forall> t. t \<in> Pow s \<longrightarrow> \<phi>_img (x \<otimes> \<^bsub>m\<^esub> y) t = \<phi> x ` \<phi> y ` t"
    unfolding \<phi>_img_def extensional_continuation.simps
    using rewrite_group_act_img car_x car_y assms PowD
    by metis
  ultimately have "\<forall> t. \<phi>_img (x \<otimes> \<^bsub>m\<^esub> y) t = (\<phi>_img x \<otimes> \<^bsub>BijGroup (Pow s)\<^esub> \<phi>_img y) t"
    by metis
  thus "\<phi>_img (x \<otimes> \<^bsub>m\<^esub> y) = \<phi>_img x \<otimes> \<^bsub>BijGroup (Pow s)\<^esub> \<phi>_img y"
    by blast
qed

subsection \<open>Invariance and Equivariance\<close>

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
    m :: "'z monoid" and
    s :: "'z set" and
    t :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun"
  assumes
    invar: "satisfies f (Invariance (rel_induced_by_action s t \<phi>))" and
    action_\<phi>: "group_action m t \<phi>" and
    gen: "carrier m = generate m s"
  shows "satisfies f (Invariance (rel_induced_by_action (carrier m) t \<phi>))"
proof (unfold satisfies.simps rel_induced_by_action.simps, safe)
  fix
    g :: "'z" and
    x :: "'x"
  assume
    group_elem: "g \<in> carrier m" and
    x_in_t: "x \<in> t"
  interpret interpr_action_\<phi>: "group_action" "m" "t" "\<phi>"
    using action_\<phi>
    by blast
  have "g \<in> generate m s"
    using group_elem gen
    by blast
  hence "\<forall> x \<in> t. f x = f (\<phi> g x)"
  proof (induct g rule: generate.induct)
    case one
    hence "\<forall> x \<in> t. \<phi> \<one> \<^bsub>m\<^esub> x = x"
      using action_\<phi> group_action.id_eq_one restrict_apply
      by metis
    thus ?case
      by simp
  next
    case (incl g)
    hence "\<forall> x \<in> t. (x, \<phi> g x) \<in> rel_induced_by_action s t \<phi>"
      using gen action_\<phi> generate.incl group_action.element_image
      unfolding rel_induced_by_action.simps
      by fastforce
    thus ?case
      using invar
      unfolding satisfies.simps
      by blast
  next
    case (inv g)
    hence "\<forall> x \<in> t. \<phi> (inv \<^bsub>m\<^esub> g) x \<in> t"
      using action_\<phi> gen generate.inv group_action.element_image
      by metis
    hence "\<forall> x \<in> t. f (\<phi> g (\<phi> (inv \<^bsub>m\<^esub> g) x)) = f (\<phi> (inv \<^bsub>m\<^esub> g) x)"
      using gen generate.incl group_action.element_image action_\<phi>
            invar local.inv rewrite_invar_ind_by_act
      by metis
    moreover have "\<forall> x \<in> t. \<phi> g (\<phi> (inv \<^bsub>m\<^esub> g) x) = x"
      using action_\<phi> gen generate.incl group.inv_closed group_action.orbit_sym_aux
            group.inv_inv group_hom.axioms(1) interpr_action_\<phi>.group_hom local.inv
      by (metis (full_types))
    ultimately show ?case
      by simp
  next
    case (eng g\<^sub>1 g\<^sub>2)
    assume
      invar\<^sub>1: "\<forall> x \<in> t. f x = f (\<phi> g\<^sub>1 x)" and
      invar\<^sub>2: "\<forall> x \<in> t. f x = f (\<phi> g\<^sub>2 x)" and
      gen\<^sub>1: "g\<^sub>1 \<in> generate m s" and
      gen\<^sub>2: "g\<^sub>2 \<in> generate m s"
    hence "\<forall> x \<in> t. \<phi> g\<^sub>2 x \<in> t"
      using gen interpr_action_\<phi>.element_image
      by blast
    hence "\<forall> x \<in> t. f (\<phi> g\<^sub>1 (\<phi> g\<^sub>2 x)) = f (\<phi> g\<^sub>2 x)"
      using invar\<^sub>1
      by simp
    moreover have "\<forall> x \<in> t. f (\<phi> g\<^sub>2 x) = f x"
      using invar\<^sub>2
      by simp
    moreover have "\<forall> x \<in> t. f (\<phi> (g\<^sub>1 \<otimes> \<^bsub>m\<^esub> g\<^sub>2) x) = f (\<phi> g\<^sub>1 (\<phi> g\<^sub>2 x))"
      using action_\<phi> gen interpr_action_\<phi>.composition_rule gen\<^sub>1 gen\<^sub>2
      by simp
    ultimately show ?case
      by simp
  qed
  thus "f x = f (\<phi> g x)"
    using x_in_t
    by simp
qed

lemma invar_parameterized_fun:
  fixes
    f :: "'x \<Rightarrow> ('x \<Rightarrow> 'y)" and
    r :: "'x rel"
  assumes
    param_invar: "\<forall> x. satisfies (f x) (Invariance r)" and
    invar: "satisfies f (Invariance r)"
  shows "satisfies (\<lambda> x. f x x) (Invariance r)"
  using invar param_invar 
  by auto

lemma invar_under_subset_rel:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    r :: "'x rel"
  assumes
    subset: "r \<subseteq> rel" and
    invar: "satisfies f (Invariance rel)"
  shows "satisfies f (Invariance r)"
  using assms
  by auto

lemma equivar_ind_by_act_coincide:
  fixes
    s :: "'x set" and
    t :: "'y set" and
    f :: "'y \<Rightarrow> 'z" and
    \<phi> :: "('x, 'y) binary_fun" and
    \<phi>' :: "('x, 'y) binary_fun" and
    \<psi> :: "('x, 'z) binary_fun"
  assumes "\<forall> x \<in> s. \<forall> y \<in> t. \<phi> x y = \<phi>' x y"
  shows "satisfies f (equivar_ind_by_act s t \<phi> \<psi>) = satisfies f (equivar_ind_by_act s t \<phi>' \<psi>)"
  using assms
  unfolding rewrite_equivar_ind_by_act
  by simp

lemma equivar_under_subset:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    s :: "'x set" and
    t :: "'x set" and
    \<tau> :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"
  assumes
    "satisfies f (Equivariance s \<tau>)" and
    "t \<subseteq> s"
  shows "satisfies f (Equivariance t \<tau>)"
  using assms
  unfolding satisfies.simps
  by blast

lemma equivar_under_subset':
  fixes
    f :: "'x \<Rightarrow> 'y" and
    s :: "'x set" and
    \<tau> :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set" and
    \<upsilon> :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"
  assumes
    "satisfies f (Equivariance s \<tau>)" and
    "\<upsilon> \<subseteq> \<tau>"
  shows "satisfies f (Equivariance s \<upsilon>)"
  using assms
  unfolding satisfies.simps
  by blast

theorem group_act_equivar_f_imp_equivar_preimg:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    \<D>\<^sub>f :: "'x set" and
    s :: "'x set" and
    m :: "'z monoid" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun" and
    x :: "'z"
  defines "equivar_prop \<equiv> equivar_ind_by_act (carrier m) \<D>\<^sub>f \<phi> \<psi>"
  assumes
    action_\<phi>: "group_action m s \<phi>" and
    action_res: "group_action m UNIV \<psi>" and
    dom_in_s: "\<D>\<^sub>f \<subseteq> s" and
    closed_domain: (* Could the closed_domain requirement be weakened? *)
      "closed_under_restr_rel (rel_induced_by_action (carrier m) s \<phi>) s \<D>\<^sub>f" and
    equivar_f: "satisfies f equivar_prop" and
    group_elem_x: "x \<in> carrier m"
  shows "\<forall> y. preimg f \<D>\<^sub>f (\<psi> x y) = (\<phi> x) ` (preimg f \<D>\<^sub>f y)"
proof (safe)
  interpret action_\<phi>: "group_action" "m" "s" "\<phi>"
    using action_\<phi>
    by simp
  interpret action_results: "group_action" "m" "UNIV" "\<psi>"
    using action_res
    by simp 
  have group_elem_inv: "(inv \<^bsub>m\<^esub> x) \<in> carrier m"
    using group.inv_closed group_hom.axioms(1) action_\<phi>.group_hom group_elem_x
    by metis
  fix
    y :: "'y" and
    z :: "'x"
  assume preimg_el: "z \<in> preimg f \<D>\<^sub>f (\<psi> x y)"
  obtain a :: "'x" where
    img: "a = \<phi> (inv \<^bsub>m\<^esub> x) z"
    by simp
  have domain: "z \<in> \<D>\<^sub>f \<and> z \<in> s"
    using preimg_el dom_in_s
    by auto
  hence "a \<in> s"
    using dom_in_s action_\<phi> group_elem_inv preimg_el img action_\<phi>.element_image
    by auto
  hence "(z, a) \<in> (rel_induced_by_action (carrier m) s \<phi>) \<inter> (\<D>\<^sub>f \<times> s)"
    using img preimg_el domain group_elem_inv
    by auto
  hence "a \<in> ((rel_induced_by_action (carrier m) s \<phi>) \<inter> (\<D>\<^sub>f \<times> s)) `` \<D>\<^sub>f"
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
    unfolding equivar_prop_def equivar_ind_by_act_def
    by simp
  also have "f z = \<psi> x y"
    using preimg_el
    by simp
  also have "\<psi> (inv \<^bsub>m\<^esub> x) (\<psi> x y) = y"
    using action_results.group_hom action_results.orbit_sym_aux group_elem_x
    by simp
  finally have "f a = y"
    by simp
  hence "a \<in> preimg f \<D>\<^sub>f y"
    using a_in_domain
    by simp
  moreover have "z = \<phi> x a"
    using group_hom.axioms(1) action_\<phi>.group_hom action_\<phi>.orbit_sym_aux
          img domain a_in_domain group_elem_x group_elem_inv group.inv_inv
    by metis
  ultimately show "z \<in> (\<phi> x) ` (preimg f \<D>\<^sub>f y)"
    by simp
next
  fix
    y :: "'y" and
    z :: "'x"
  assume preimg_el: "z \<in> preimg f \<D>\<^sub>f y"
  hence domain: "f z = y \<and> z \<in> \<D>\<^sub>f \<and> z \<in> s"
    using dom_in_s
    by auto
  hence "\<phi> x z \<in> s"
    using group_elem_x group_action.element_image action_\<phi>
    by metis
  hence "(z, \<phi> x z) \<in> (rel_induced_by_action (carrier m) s \<phi>) \<inter> (\<D>\<^sub>f \<times> s) \<inter> \<D>\<^sub>f \<times> s"
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
    unfolding equivar_prop_def equivar_ind_by_act_def
    by simp
qed

subsubsection \<open>Invariance and Equivariance Function Composition\<close>

lemma invar_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    r :: "'x rel"
  assumes "satisfies f (Invariance r)"
  shows "satisfies (g \<circ> f) (Invariance r)"
  using assms
  by simp

lemma equivar_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    s :: "'x set" and
    t :: "'y set" and
    \<tau> :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set" and
    \<upsilon> :: "(('y \<Rightarrow> 'y) \<times> ('z \<Rightarrow> 'z)) set"
  defines
    "transitive_acts \<equiv>
      {(\<phi>, \<psi>). \<exists> \<chi> :: 'y \<Rightarrow> 'y. (\<phi>, \<chi>) \<in> \<tau> \<and> (\<chi>, \<psi>) \<in> \<upsilon> \<and> \<chi> ` f ` s \<subseteq> t}"
  assumes
    "f ` s \<subseteq> t" and
    "satisfies f (Equivariance s \<tau>)" and
    "satisfies g (Equivariance t \<upsilon>)"
  shows "satisfies (g \<circ> f) (Equivariance s transitive_acts)"
proof (unfold transitive_acts_def, simp, safe)
  fix
    \<phi> :: "'x \<Rightarrow> 'x" and
    \<chi> :: "'y \<Rightarrow> 'y" and
    \<psi> :: "'z \<Rightarrow> 'z" and
    x :: "'x"
  assume
    x_in_X: "x \<in> s" and
    \<phi>_x_in_X: "\<phi> x \<in> s" and
    \<chi>_img\<^sub>f_img\<^sub>s_in_t: "\<chi> ` f ` s \<subseteq> t" and
    act_f: "(\<phi>, \<chi>) \<in> \<tau>" and
    act_g: "(\<chi>, \<psi>) \<in> \<upsilon>"
  hence "f x \<in> t \<and> \<chi> (f x) \<in> t"
    using assms
    by blast
  hence "\<psi> (g (f x)) = g (\<chi> (f x))"
    using act_g assms
    by fastforce
  also have "g (f (\<phi> x)) = g (\<chi> (f x))"
    using assms act_f x_in_X \<phi>_x_in_X
    by fastforce
  finally show "g (f (\<phi> x)) = \<psi> (g (f x))"
    by simp
qed

lemma equivar_ind_by_act_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    s :: "'w set" and
    t :: "'x set" and
    u :: "'y set" and
    \<phi> :: "('w, 'x) binary_fun" and
    \<chi> :: "('w, 'y) binary_fun" and
    \<psi> :: "('w, 'z) binary_fun"
  assumes
    "f ` t \<subseteq> u" and
    "\<forall> x \<in> s. \<chi> x ` f ` t \<subseteq> u" and
    "satisfies f (equivar_ind_by_act s t \<phi> \<chi>)" and
    "satisfies g (equivar_ind_by_act s u \<chi> \<psi>)"
  shows "satisfies (g \<circ> f) (equivar_ind_by_act s t \<phi> \<psi>)"
proof -
  let ?a\<^sub>\<phi> = "{(\<phi> a, \<chi> a) | a. a \<in> s}" and
      ?a\<^sub>\<psi> = "{(\<chi> a, \<psi> a) | a. a \<in> s}"
  have "\<forall> a \<in> s. (\<phi> a, \<chi> a) \<in> {(\<phi> a, \<chi> a) | b. b \<in> s} \<and>
                  (\<chi> a, \<psi> a) \<in> {(\<chi> b, \<psi> b) | b. b \<in> s} \<and> \<chi> a ` f ` t \<subseteq> u"
    using assms
    by blast
  hence "{(\<phi> a, \<psi> a) | a. a \<in> s} \<subseteq>
          {(\<phi>, \<psi>). \<exists> \<upsilon>. (\<phi>, \<upsilon>) \<in> ?a\<^sub>\<phi> \<and> (\<upsilon>, \<psi>) \<in> ?a\<^sub>\<psi> \<and> \<upsilon> ` f ` t \<subseteq> u}"
    by blast
  hence "satisfies (g \<circ> f) (Equivariance t {(\<phi> a, \<psi> a) | a. a \<in> s})"
    using assms equivar_comp[of f t u ?a\<^sub>\<phi> g ?a\<^sub>\<psi>] equivar_under_subset'
    unfolding equivar_ind_by_act_def
    by (metis (no_types, lifting))
  thus ?thesis
    unfolding equivar_ind_by_act_def
    by blast
qed

lemma equivar_set_minus:
  fixes
    f :: "'x \<Rightarrow> 'y set" and
    g :: "'x \<Rightarrow> 'y set" and
    s :: "'z set" and
    t :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  assumes
    f_equivar: "satisfies f (equivar_ind_by_act s t \<phi> (set_action \<psi>))" and
    g_equivar: "satisfies g (equivar_ind_by_act s t \<phi> (set_action \<psi>))" and
    bij_a: "\<forall> a \<in> s. bij (\<psi> a)"
  shows "satisfies (\<lambda> b. f b - g b) (equivar_ind_by_act s t \<phi> (set_action \<psi>))"
proof -
  have "\<forall> a \<in> s. \<forall> x \<in> t. \<phi> a x \<in> t \<longrightarrow> f (\<phi> a x) = \<psi> a ` (f x)"
    using f_equivar
    unfolding rewrite_equivar_ind_by_act
    by simp
  moreover have "\<forall> a \<in> s. \<forall> x \<in> t. \<phi> a x \<in> t \<longrightarrow> g (\<phi> a x) = \<psi> a ` (g x)"
    using g_equivar
    unfolding rewrite_equivar_ind_by_act
    by simp
  ultimately have
    "\<forall> a \<in> s. \<forall> b \<in> t. \<phi> a b \<in> t \<longrightarrow> f (\<phi> a b) - g (\<phi> a b) = \<psi> a ` (f b) - \<psi> a ` (g b)"
    by blast
  moreover have "\<forall> a \<in> s. \<forall> u v. \<psi> a ` u - \<psi> a ` v = \<psi> a ` (u - v)"
    using bij_a image_set_diff
    unfolding bij_def
    by blast
  ultimately show ?thesis
    unfolding set_action.simps
    using rewrite_equivar_ind_by_act
    by fastforce
qed

lemma equivar_union_under_img_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    s :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows "satisfies \<Union> (equivar_ind_by_act s UNIV
              (set_action (set_action \<phi>)) (set_action \<phi>))"
proof (unfold equivar_ind_by_act_def, clarsimp, safe)
  fix
    x :: "'z" and
    ts :: "'x set set" and
    t :: "'x set" and
    y :: "'x"
  assume
    "y \<in> t" and
    "t \<in> ts"
  thus
    "\<phi> x y \<in> \<phi> x ` \<Union> ts" and
    "\<phi> x y \<in> \<Union> ((`) (\<phi> x) ` ts)"
    by (blast, blast)
qed

end
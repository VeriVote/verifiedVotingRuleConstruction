(*  File:       Relation_Quotients.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Quotient Rules\<close>

section \<open>Quotients of Equivalence Relations\<close>

theory Relation_Quotients
  imports "../Social_Choice_Types/Symmetry_Of_Functions"
begin

subsection \<open>Definitions\<close>

fun singleton_set :: "'x set \<Rightarrow> 'x" where
  "singleton_set s = (if (card s = 1) then (the_inv (\<lambda> x. {x}) s) else undefined)"
\<comment> \<open>This is undefined if \<open>card s \<noteq> 1\<close>.
    Note that "\<open>undefined = undefined\<close>" is the only provable equality for \<open>undefined\<close>.\<close>

text \<open>
  For a given function, we define a function on sets that maps each set to the
  unique image under f of its elements, if one exists.
  Otherwise, the result is undefined.
\<close>
fun \<pi>\<^sub>\<Q> :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x set \<Rightarrow> 'y)" where
  "\<pi>\<^sub>\<Q> f s = singleton_set (f ` s)"

text \<open>
  For a given function f on sets and a mapping from elements to sets,
  we define a function on the set element type that maps each element to the
  image of its corresponding set under f.
  A natural mapping is from elements to their classes under a relation.
\<close>
fun inv_\<pi>\<^sub>\<Q> :: "('x \<Rightarrow> 'x set) \<Rightarrow> ('x set \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> 'y)" where
  "inv_\<pi>\<^sub>\<Q> cls f x = f (cls x)"

fun relation_class :: "'x rel \<Rightarrow> 'x \<Rightarrow> 'x set" where
  "relation_class r x = r `` {x}"

subsection \<open>Well-Definedness\<close>

lemma singleton_set_undef_if_card_neq_one:
  fixes s :: "'x set"
  assumes "card s \<noteq> 1"
  shows "singleton_set s = undefined"
  using assms
  by simp

lemma singleton_set_def_if_card_one:
  fixes s :: "'x set"
  assumes "card s = 1"
  shows "\<exists>! x. x = singleton_set s \<and> {x} = s"
  using assms card_1_singletonE inj_def singleton_inject the_inv_f_f
  unfolding singleton_set.simps
  by (metis (mono_tags, lifting))

text \<open>
  If the given function is invariant under an equivalence relation, the induced
  function on sets is well-defined for all equivalence classes of that relation.
\<close>
theorem pass_to_quotient:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    r :: "'x rel" and
    s :: "'x set"
  assumes
    "f respects r" and
    "equiv s r"
  shows "\<forall> t \<in> s // r. \<forall> x \<in> t. \<pi>\<^sub>\<Q> f t = f x"
proof (safe)
  fix
    t :: "'x set" and
    x :: "'x"
  have "\<forall> y \<in> r``{x}. (x, y) \<in> r"
    unfolding Image_def
    by simp
  hence func_eq_x:
    "{f y | y. y \<in> r``{x}} = {f x | y. y \<in> r``{x}}"
    using assms
    unfolding congruent_def
    by fastforce
  assume
    "t \<in> s // r" and
    x_in_t: "x \<in> t"
  moreover from this have "r `` {x} \<in> s // r"
    using assms quotient_eq_iff equiv_class_eq_iff quotientI
    by metis
  ultimately have r_img_elem_x_eq_t: "r `` {x} = t"
    using assms quotient_eq_iff Image_singleton_iff
    by metis
  hence "{f x | y. y \<in> r``{x}} = {f x}"
    using x_in_t
    by blast
  hence "f ` t = {f x}"
    using Setcompr_eq_image r_img_elem_x_eq_t func_eq_x
    by metis
  thus "\<pi>\<^sub>\<Q> f t = f x"
    using singleton_set_def_if_card_one is_singletonI
          is_singleton_altdef the_elem_eq
    unfolding \<pi>\<^sub>\<Q>.simps
    by metis
qed

text \<open>
  A function on sets induces a function on the element type that is invariant
  under a given equivalence relation.
\<close>
theorem pass_to_quotient_inv:
  fixes
    f :: "'x set \<Rightarrow> 'x" and
    r :: "'x rel" and
    s :: "'x set"
  assumes "equiv s r"
  defines "induced_fun \<equiv> (inv_\<pi>\<^sub>\<Q> (relation_class r) f)"
  shows
    "induced_fun respects r" and
    "\<forall> A \<in> s // r. \<pi>\<^sub>\<Q> induced_fun A = f A"
proof (safe)
  have "\<forall> (a, b) \<in> r. relation_class r a = relation_class r b"
    using assms equiv_class_eq
    unfolding relation_class.simps
    by fastforce
  hence "\<forall> (a, b) \<in> r. induced_fun a = induced_fun b"
    unfolding induced_fun_def inv_\<pi>\<^sub>\<Q>.simps
    by auto
  thus "induced_fun respects r"
    unfolding congruent_def
    by metis
  moreover fix A :: "'x set"
  assume "A \<in> s // r"
  moreover with assms
  obtain a :: "'x" where
    "a \<in> A" and
    A_eq_rel_class_r_a: "A = relation_class r a"
    using equiv_Eps_in proj_Eps
    unfolding proj_def relation_class.simps
    by metis
  ultimately have "\<pi>\<^sub>\<Q> induced_fun A = induced_fun a"
    using pass_to_quotient assms
    by blast
  thus "\<pi>\<^sub>\<Q> induced_fun A = f A"
    using A_eq_rel_class_r_a
    unfolding induced_fun_def
    by simp
qed

subsection \<open>Equivalence Relations\<close>

lemma restr_equals_restricted_rel:
  fixes
    s t :: "'a set" and
    r :: "'a rel"
  assumes
    "closed_restricted_rel r s t" and
    "t \<subseteq> s"
  shows "restricted_rel r t s = Restr r t"
proof(simp, safe)
  fix a b :: "'a"
  assume
    "(a, b) \<in> r" and
    "a \<in> t" and
    "b \<in> s"
  thus "b \<in> t" 
    using assms
    unfolding closed_restricted_rel.simps restricted_rel.simps
    by blast
next
  fix a b :: "'a"
  assume "b \<in> t"
  thus "b \<in> s"
    using assms
    by blast
qed

lemma equiv_rel_restr:
  fixes
    s t :: "'x set" and
    r :: "'x rel"
  assumes
    "equiv s r" and
    "t \<subseteq> s"
  shows "equiv t (Restr r t)"
proof (unfold equiv_def refl_on_def, safe)
  fix x :: "'x"
  assume "x \<in> t"
  thus "(x, x) \<in> r"
    using assms
    unfolding equiv_def refl_on_def
    by blast
next
  show "sym (Restr r t)"
    using assms
    unfolding equiv_def sym_def
    by blast
next
  show "Relation.trans (Restr r t)"
    using assms
    unfolding equiv_def Relation.trans_def
    by blast
qed

lemma rel_ind_by_group_act_equiv:
  fixes
    m :: "'x monoid" and
    s :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes "group_action m s \<phi>"
  shows "equiv s (action_induced_rel (carrier m) s \<phi>)"
proof (unfold equiv_def refl_on_def sym_def Relation.trans_def
              action_induced_rel.simps, safe)
  fix y :: "'y"
  assume "y \<in> s"
  hence "\<phi> \<one> \<^bsub>m\<^esub> y = y"
    using assms group_action.id_eq_one restrict_apply'
    by metis
  thus "\<exists> g \<in> carrier m. \<phi> g y = y"
    using assms group.is_monoid group_hom.axioms
    unfolding group_action_def
    by blast
next
  fix
    y :: "'y" and
    g :: "'x"
  assume
    y_in_s: "y \<in> s" and
    carrier_g: "g \<in> carrier m"
  hence "y = \<phi> (inv \<^bsub>m\<^esub> g) (\<phi> g y)"
    using assms
    by (simp add: group_action.orbit_sym_aux)
  thus "\<exists> h \<in> carrier m. \<phi> h (\<phi> g y) = y"
    using assms carrier_g group.inv_closed
          group_action.group_hom group_hom.axioms(1)
    by metis
next
  fix
    y :: "'y" and
    g h :: "'x"
  assume
    y_in_s: "y \<in> s" and
    carrier_g: "g \<in> carrier m" and
    carrier_h: "h \<in> carrier m"
  hence "\<phi> (h \<otimes> \<^bsub>m\<^esub> g) y = \<phi> h (\<phi> g y)"
    using assms
    by (simp add: group_action.composition_rule)
  thus "\<exists> f \<in> carrier m. \<phi> f y = \<phi> h (\<phi> g y)"
    using assms carrier_g carrier_h group_action.group_hom
          group_hom.axioms(1) monoid.m_closed
    unfolding group_def
    by metis
next
  fix
    y :: "'y" and
    g :: "'x"
  assume
    y_in_s: "y \<in> s" and
    carrier_g: "g \<in> carrier m"
  thus "\<phi> g y \<in> s"
    using assms group_action.element_image
    by metis
next
  fix
    y :: "'y" and
    g :: "'x"
  assume
    y_in_s: "y \<in> s" and
    carrier_g: "g \<in> carrier m"
  thus "\<phi> g y \<in> s"
    using assms group_action.element_image
    by metis
qed

end
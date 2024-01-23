chapter \<open>Quotient Rules\<close>

section \<open>Quotients of Equivalence Relations\<close>

theory Relation_Quotients
  imports HOL.Equiv_Relations
          "../Social_Choice_Types/Symmetry_Of_Functions"
          Main
begin

subsection \<open>Definitions\<close>

fun singleton_set :: "'x set \<Rightarrow> 'x" where
  "singleton_set X = (if (card X = 1) then (the_inv (\<lambda> x. {x}) X) else undefined)"
\<comment> \<open>This is undefined if card X != 1.
    Note that "undefined = undefined" is the only provable equality for undefined.\<close>

(* export_code singleton_set in Haskell *)

text \<open>
  For a given function, we define a function on sets that maps each set to the
  unique image under f of its elements, if one exists.
  Otherwise, the result is undefined.
\<close>
fun \<pi>\<^sub>\<Q> :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x set \<Rightarrow> 'y)" where
  "\<pi>\<^sub>\<Q> f X = singleton_set (f ` X)"

text \<open>
  For a given function f on sets and a mapping from elements to sets,
  we define a function on the set element type that maps each element to the
  image of its corresponding set under f.
  A natural mapping is from elements to their classes under a relation (rel cls).
\<close>
fun inv_\<pi>\<^sub>\<Q> :: "('x \<Rightarrow> 'x set) \<Rightarrow> ('x set \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> 'y)" where
  "inv_\<pi>\<^sub>\<Q> cls f x = f (cls x)"

fun rel_cls :: "'x rel \<Rightarrow> 'x \<Rightarrow> 'x set" where
  "rel_cls r x = r `` {x}"

subsection \<open>Well-Definedness\<close>

lemma singleton_set_undef_if_card_neq_one:
  fixes X :: "'x set"
  assumes "card X \<noteq> 1"
  shows "singleton_set X = undefined"
  using assms
  by simp

lemma singleton_set_def_if_card_one:
  fixes X :: "'x set"
  assumes "card X = 1"
  shows "\<exists>! x. x = singleton_set X \<and> {x} = X"
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
    X :: "'x set"
  assumes
    "f respects r" and
    "equiv X r"
  shows "\<forall> A \<in> X // r. \<forall> x \<in> A. \<pi>\<^sub>\<Q> f A = f x"
proof (safe)
  fix
    A :: "'x set" and
    x :: 'x
  assume
    "A \<in> X // r" and
    x_in_A: "x \<in> A"
  hence r_img_elem_x_eq_A: "r `` {x} = A"
    using assms ImageI equiv_class_eq_iff quotientI quotient_eq_iff singleton_iff
    by meson
  have "\<forall> y \<in> r``{x}. (x, y) \<in> r"
    unfolding Image_def
    by simp
  hence "\<forall> y \<in> r``{x}. f y = f x"
    using assms
    unfolding congruent_def
    by fastforce
  hence "{f y | y. y \<in> r``{x}} = {f x | y. y \<in> r``{x}}"
    using assms
    unfolding congruent_def
    by metis
  also have "{f x | y. y \<in> r``{x}} = {f x}"
    using assms x_in_A r_img_elem_x_eq_A
    unfolding refl_on_def
    by blast
  finally have "f ` A = {f x}"
    using r_img_elem_x_eq_A
    by auto
  thus "\<pi>\<^sub>\<Q> f A = f x"
    using singleton_set_def_if_card_one is_singletonI is_singleton_altdef the_elem_eq
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
    X :: "'x set"
  assumes "equiv X r"
  defines "induced_fun \<equiv> (inv_\<pi>\<^sub>\<Q> (rel_cls r) f)"
  shows
    invar: "induced_fun respects r" and
    inv: "\<forall> A \<in> X // r. \<pi>\<^sub>\<Q> induced_fun A = f A"
proof (safe)
  have "\<forall> (a, b) \<in> r. rel_cls r a = rel_cls r b"
    using assms equiv_class_eq
    unfolding rel_cls.simps
    by fastforce
  hence "\<forall> (a, b) \<in> r. induced_fun a = induced_fun b"
    unfolding induced_fun_def inv_\<pi>\<^sub>\<Q>.simps
    by auto
  thus invar: "induced_fun respects r"
    unfolding congruent_def
    by blast
  \<comment> \<open>We want to reuse this fact, so no "next".\<close>
  fix A :: "'x set"
  assume A_in_quot_X_r: "A \<in> X // r"
  then obtain a :: 'x where
    a_in_A: "a \<in> A" and
    A_eq_rel_class_r_a: "A = rel_cls r a"
    using assms equiv_Eps_in proj_Eps
    unfolding proj_def rel_cls.simps
    by metis
  with invar A_in_quot_X_r pass_to_quotient
  have "\<pi>\<^sub>\<Q> induced_fun A = induced_fun a"
    using assms
    by blast
  also have "induced_fun a = f A"
    using A_eq_rel_class_r_a
    unfolding induced_fun_def
    by simp
  finally show "\<pi>\<^sub>\<Q> induced_fun A = f A"
    by simp
qed

subsection \<open>Equivalence Relations\<close>

lemma equiv_rel_restr:
  fixes
    X :: "'x set" and
    Y :: "'x set" and
    r :: "'x rel"
  assumes
    "equiv X r" and
    "Y \<subseteq> X" 
  shows "equiv Y (Restr r Y)"
proof (unfold equiv_def refl_on_def, safe)
  fix x :: 'x
  assume "x \<in> Y"
  hence "x \<in> X"
    using assms
    by blast
  thus "(x, x) \<in> r"
    using assms
    unfolding equiv_def refl_on_def
    by simp
next
  show "sym (Restr r Y)"
    using assms
    unfolding equiv_def sym_def
    by blast
next
  show "Relation.trans (Restr r Y)"
    using assms
    unfolding equiv_def Relation.trans_def
    by blast
qed

lemma rel_ind_by_grp_act_equiv:
  fixes
    G :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes "group_action G Y \<phi>"
  shows "equiv Y (rel_induced_by_action (carrier G) Y \<phi>)"
proof (unfold equiv_def refl_on_def sym_def Relation.trans_def rel_induced_by_action.simps, 
        clarsimp, safe)
  fix y :: 'y
  assume "y \<in> Y"
  hence "\<phi> \<one> \<^bsub>G\<^esub> y = y"
    using assms group_action.id_eq_one restrict_apply'
    by metis
  thus "\<exists> g \<in> carrier G. \<phi> g y = y"
    using assms group.is_monoid group_hom.axioms
    unfolding group_action_def
    by blast
next
  fix
    y :: "'y" and
    g :: "'x"
  assume
    "y \<in> Y" and
    "\<phi> g y \<in> Y" and
    carrier_g: "g \<in> carrier G"
  hence "y = \<phi> (inv \<^bsub>G\<^esub> g) (\<phi> g y)"
    using assms
    by (simp add: group_action.orbit_sym_aux)
  thus "\<exists> h \<in> carrier G. \<phi> h (\<phi> g y) = y"
    using carrier_g assms group.inv_closed group_action.group_hom group_hom.axioms(1)
    by metis
next
  fix
    y :: "'y" and
    g :: "'x" and
    h :: "'x"
  assume
    "y \<in> Y" and
    "\<phi> g y \<in> Y" and
    "\<phi> h (\<phi> g y) \<in> Y" and
    carrier_g: "g \<in> carrier G" and
    carrier_h: "h \<in> carrier G"
  hence "\<phi> (h \<otimes> \<^bsub>G\<^esub> g) y = \<phi> h (\<phi> g y)"
    using assms
    by (simp add: group_action.composition_rule)
  thus "\<exists> f \<in> carrier G. \<phi> f y = \<phi> h (\<phi> g y)"
    using Group.group_def carrier_g carrier_h assms group_action.group_hom
          group_hom.axioms(1) monoid.m_closed
    by metis
qed

end
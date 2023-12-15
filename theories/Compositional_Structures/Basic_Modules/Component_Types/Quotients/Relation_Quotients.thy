theory Relation_Quotients
  imports HOL.Equiv_Relations
          Main
begin

fun singleton_set :: "'x set \<Rightarrow> 'x" where
  "singleton_set X = (if (card X = 1) then (the_inv (\<lambda>x. {x}) X) else undefined)"

fun \<pi>\<^sub>\<Q> :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x set \<Rightarrow> 'y)" where
  "\<pi>\<^sub>\<Q> f X = singleton_set (f ` X)"

lemma singleton_set_undef_if_card_neq_one:
  fixes
    X :: "'x set"
  assumes
    "card X \<noteq> 1"
  shows
    "singleton_set X = undefined"
  using assms 
  by auto

lemma singleton_set_def_if_card_one:
  fixes
    X :: "'x set"
  assumes
    "card X = 1"
  shows
    "\<exists>!x. x = singleton_set X \<and> {x} = X"
  using assms
  unfolding singleton_set.simps
  by (metis (mono_tags, lifting) card_1_singletonE inj_def singleton_inject the_inv_f_f)

theorem pass_to_quotient:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    r :: "'x rel" and
    X :: "'x set"
  assumes
    "f respects r" and
    "equiv X r"
  shows
    "\<forall>A \<in> X // r. \<forall>x \<in> A. \<pi>\<^sub>\<Q> f A = f x"
proof (safe)
  fix
    A :: "'x set" and
    x :: 'x
  assume
    "A \<in> X // r" and "x \<in> A"
  hence "r `` {x} = A"
    using assms
    by (meson ImageI equiv_class_eq_iff quotientI quotient_eq_iff singleton_iff)
  have "\<forall>y \<in> r``{x}. (x, y) \<in> r"
    unfolding Image_def
    by blast
  hence "\<forall>y \<in> r``{x}. f y = f x"
    using assms
    unfolding congruent_def   
    by auto
  hence "{f y | y. y \<in> r``{x}} = {f x | y. y \<in> r``{x}}"
    using assms
    unfolding congruent_def     
    by blast
  also have "{f x | y. y \<in> r``{x}} = {f x}"
    using assms \<open>x \<in> A\<close> \<open>r `` {x} = A\<close>
    unfolding refl_on_def
    by blast
  finally have "f ` A = {f x}"
    using \<open>r `` {x} = A\<close>
    by auto
  thus "\<pi>\<^sub>\<Q> f A = f x"
    using singleton_set_def_if_card_one
    unfolding \<pi>\<^sub>\<Q>.simps
    by (metis is_singletonI is_singleton_altdef the_elem_eq)
qed

end
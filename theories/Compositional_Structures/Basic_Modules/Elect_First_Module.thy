(*  File:       Elect_First_Module.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elect First Module\<close>

theory Elect_First_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  The elect first module elects the alternative that is most preferred on the first ballot and
  rejects all other alternatives.
\<close>

subsection \<open>Definition\<close>

fun least :: "'v::wellorder set \<Rightarrow> 'v" where
  "least V = (Least (\<lambda> v. v \<in> V))"

fun elect_first_module :: "('a, 'v::wellorder, 'a Result) Electoral_Module" where
  "elect_first_module V A p =
    ({a \<in> A. above (p (least V)) a = {a}},
    {a \<in> A. above (p (least V)) a \<noteq> {a}},
    {})"

subsection \<open>Soundness\<close>

theorem elect_first_mod_sound: "\<S>\<C>\<F>_result.electoral_module elect_first_module"
proof (intro \<S>\<C>\<F>_result.electoral_modI)
  fix
    A :: "'a set" and
    V :: "'v::wellorder set" and
    p :: "('a, 'v) Profile"
  have "{a \<in> A. above (p (least V)) a = {a}} \<union> {a \<in> A. above (p (least V)) a \<noteq> {a}} = A"
    by blast
  hence "set_equals_partition A (elect_first_module V A p)"
    by simp
  moreover have
    "\<forall> a \<in> A. (a \<notin> {a' \<in> A.  above (p (least V)) a' = {a'}} \<or> 
                a \<notin> {a' \<in> A. above (p (least V)) a' \<noteq> {a'}})"
    by simp
  hence "{a \<in> A. above (p (least V)) a = {a}} \<inter> {a \<in> A. above (p (least V)) a \<noteq> {a}} = {}"
    by blast
  hence "disjoint3 (elect_first_module V A p)"
    by simp
  ultimately show "well_formed_\<S>\<C>\<F> A (elect_first_module V A p)"
    by simp
qed

end
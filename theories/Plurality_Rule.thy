(*  File:       Plurality_Rule.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Voting Rules\<close>

section \<open>Plurality Rule\<close>

theory Plurality_Rule
  imports "Compositional_Structures/Basic_Modules/Plurality_Module"
          "Compositional_Structures/Revision_Composition"
          "Compositional_Structures/Elect_Composition"
begin

text \<open>
  This is a definition of the plurality voting rule as elimination module as well as directly.
  In the former one, the max operator of the set of the scores of all alternatives is evaluated
  and is used as the threshold value.
\<close>

subsection \<open>Definition\<close>

fun plurality_rule :: "'a Electoral_Module" where
  "plurality_rule A p = elector plurality A p"

fun plurality_rule' :: "'a Electoral_Module" where
  "plurality_rule' A p =
    ({a \<in> A. \<forall> x \<in> A. win_count p x \<le> win_count p a},
     {a \<in> A. \<exists> x \<in> A. win_count p x > win_count p a},
     {})"

lemma plurality_revision_equiv:
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  shows "plurality' A p = (plurality_rule'\<down>) A p"
proof (unfold plurality_rule'.simps plurality'.simps revision_composition.simps,
        standard, clarsimp, standard, safe)
  fix
    a :: "'a" and
    b :: "'a"
  assume
    "b \<in> A" and
    "card {i. i < length p \<and> above (p!i) a = {a}} <
      card {i. i < length p \<and> above (p!i) b = {b}}" and
    "\<forall> a' \<in> A. card {i. i < length p \<and> above (p!i) a' = {a'}} \<le>
      card {i. i < length p \<and> above (p!i) a = {a}}"
  thus "False"
    using leD
    by blast
next
  fix
    a :: "'a" and
    b :: "'a"
  assume
    "b \<in> A" and
    "\<not> card {i. i < length p \<and> above (p!i) b = {b}} \<le>
      card {i. i < length p \<and> above (p!i) a = {a}}"
  thus "\<exists> x \<in> A.
          card {i. i < length p \<and> above (p!i) a = {a}}
          < card {i. i < length p \<and> above (p!i) x = {x}}"
    using linorder_not_less
    by blast
qed

lemma plurality_elim_equiv:
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    "A \<noteq> {}" and
    "finite_profile A p"
  shows "plurality A p = (plurality_rule'\<down>) A p"
  using assms plurality_mod_elim_equiv plurality_revision_equiv
  by (metis (full_types))

subsection \<open>Soundness\<close>

theorem plurality_rule_sound[simp]: "electoral_module plurality_rule"
  unfolding plurality_rule.simps
  using elector_sound plurality_sound
  by metis

theorem plurality_rule'_sound[simp]: "electoral_module plurality_rule'"
proof (unfold electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  have "disjoint3 (
      {a \<in> A. \<forall> a' \<in> A. win_count p a' \<le> win_count p a},
      {a \<in> A. \<exists> a' \<in> A. win_count p a < win_count p a'},
      {})"
    by auto
  moreover have
    "{a \<in> A. \<forall> x \<in> A. win_count p x \<le> win_count p a} \<union>
      {a \<in> A. \<exists> x \<in> A. win_count p a < win_count p x} = A"
    using not_le_imp_less
    by auto
  ultimately show "well_formed A (plurality_rule' A p)"
    by simp
qed

subsection \<open>Electing\<close>

lemma plurality_rule_elect_non_empty:
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  assumes
    A_non_empty: "A \<noteq> {}" and
    fin_prof_A: "finite_profile A p"
  shows "elect plurality_rule A p \<noteq> {}"
proof
  assume plurality_elect_none: "elect plurality_rule A p = {}"
  obtain max where
    max: "max = Max (win_count p ` A)"
    by simp
  then obtain a where
    max_a: "win_count p a = max \<and> a \<in> A"
    using Max_in A_non_empty fin_prof_A empty_is_image finite_imageI imageE
    by (metis (no_types, lifting))
  hence "\<forall> a' \<in> A. win_count p a' \<le> win_count p a"
    using fin_prof_A max
    by simp
  moreover have "a \<in> A"
    using max_a
    by simp
  ultimately have "a \<in> {a' \<in> A. \<forall> c \<in> A. win_count p c \<le> win_count p a'}"
    by blast
  hence "a \<in> elect plurality_rule A p"
    by auto
  thus False
    using plurality_elect_none all_not_in_conv
    by metis
qed

text \<open>
  The plurality module is electing.
\<close>

theorem plurality_rule_electing[simp]: "electing plurality_rule"
proof (unfold electing_def, safe)
  show "electoral_module plurality_rule"
    using plurality_rule_sound
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    elect_none: "elect plurality_rule A p = {}" and
    a_in_A: "a \<in> A"
  have "\<forall> A p. A \<noteq> {} \<and> finite_profile A p \<longrightarrow> elect plurality_rule A p \<noteq> {}"
    using plurality_rule_elect_non_empty
    by (metis (no_types))
  hence empty_A: "A = {}"
    using fin_A prof_p elect_none
    by (metis (no_types))
  thus "a \<in> {}"
    using a_in_A
    by simp
qed

subsection \<open>Property\<close>

lemma plurality_rule_inv_mono_eq:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assumes
    elect_a: "a \<in> elect plurality_rule A p" and
    lift_a: "lifted A p q a"
  shows "elect plurality_rule A q = elect plurality_rule A p \<or>
          elect plurality_rule A q = {a}"
proof -
  have "a \<in> elect (elector plurality) A p"
    using elect_a
    by simp
  moreover have eq_p: "elect (elector plurality) A p = defer plurality A p"
    by simp
  ultimately have "a \<in> defer plurality A p"
    by blast
  hence "defer plurality A q = defer plurality A p \<or> defer plurality A q = {a}"
    using lift_a plurality_def_inv_mono_alts
    by metis
  moreover have "elect (elector plurality) A q = defer plurality A q"
    by simp
  ultimately show
    "elect plurality_rule A q = elect plurality_rule A p \<or>
      elect plurality_rule A q = {a}"
    using eq_p
    by simp
qed

text \<open>
  The plurality rule is invariant-monotone.
\<close>

theorem plurality_rule_inv_mono[simp]: "invariant_monotonicity plurality_rule"
proof (unfold invariant_monotonicity_def, intro conjI impI allI)
  show "electoral_module plurality_rule"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume "a \<in> elect plurality_rule A p \<and> Profile.lifted A p q a"
  thus "elect plurality_rule A q = elect plurality_rule A p \<or>
          elect plurality_rule A q = {a}"
    using plurality_rule_inv_mono_eq
    by metis
qed

end
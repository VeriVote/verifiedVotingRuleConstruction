(*  File:       Interpretation_Code.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Result + Property Locale Code Generation\<close>

theory Interpretation_Code
  imports Electoral_Module
          Distance_Rationalization
begin
setup Locale_Code.open_block

text \<open>
  Lemmas stating the explicit instantiations of interpreted abstract functions from locales.
\<close>

lemma electoral_module_\<S>\<C>\<F>_code_lemma:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  shows "\<S>\<C>\<F>_result.electoral_module m = (\<forall> A V p. profile V A p \<longrightarrow> well_formed_\<S>\<C>\<F> A (m V A p))"
  unfolding \<S>\<C>\<F>_result.electoral_module_def
  by simp

lemma \<R>\<^sub>\<W>_\<S>\<C>\<F>_code_lemma:
  fixes
    d :: "('a, 'v) Election Distance" and
    K :: "('a, 'v, 'a Result) Consensus_Class" and
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  shows "\<S>\<C>\<F>_result.\<R>\<^sub>\<W> d K V A p = arg_min_set (score d K (A, V, p)) (limit_set_\<S>\<C>\<F> A UNIV)"
  unfolding \<S>\<C>\<F>_result.\<R>\<^sub>\<W>.simps
  by safe

lemma distance_\<R>_\<S>\<C>\<F>_code_lemma:
  fixes
    d :: "('a, 'v) Election Distance" and
    K :: "('a, 'v, 'a Result) Consensus_Class" and
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  shows "\<S>\<C>\<F>_result.distance_\<R> d K V A p =
      (\<S>\<C>\<F>_result.\<R>\<^sub>\<W> d K V A p, (limit_set_\<S>\<C>\<F> A UNIV) - \<S>\<C>\<F>_result.\<R>\<^sub>\<W> d K V A p, {})"
  unfolding \<S>\<C>\<F>_result.distance_\<R>.simps
  by safe

lemma \<R>\<^sub>\<W>_std_\<S>\<C>\<F>_code_lemma:
  fixes
    d :: "('a, 'v) Election Distance" and
    K :: "('a, 'v, 'a Result) Consensus_Class" and
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  shows "\<S>\<C>\<F>_result.\<R>\<^sub>\<W>_std d K V A p =
      arg_min_set (score_std d K (A, V, p)) (limit_set_\<S>\<C>\<F> A UNIV)"
  unfolding \<S>\<C>\<F>_result.\<R>\<^sub>\<W>_std.simps
  by safe

lemma distance_\<R>_std_\<S>\<C>\<F>_code_lemma:
  fixes
    d :: "('a, 'v) Election Distance" and
    K :: "('a, 'v, 'a Result) Consensus_Class" and
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile"
  shows "\<S>\<C>\<F>_result.distance_\<R>_std d K V A p =
      (\<S>\<C>\<F>_result.\<R>\<^sub>\<W>_std d K V A p, (limit_set_\<S>\<C>\<F> A UNIV) - \<S>\<C>\<F>_result.\<R>\<^sub>\<W>_std d K V A p, {})"
  unfolding \<S>\<C>\<F>_result.distance_\<R>_std.simps
  by safe

lemma anonymity_\<S>\<C>\<F>_code_lemma:
  shows "\<S>\<C>\<F>_result.anonymity =
    (\<lambda> m::(('a, 'v, 'a Result) Electoral_Module).
      \<S>\<C>\<F>_result.electoral_module m \<and>
          (\<forall> A V p \<pi>::('v \<Rightarrow> 'v).
                bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> m V A p = m V' A' q)))"
  unfolding \<S>\<C>\<F>_result.anonymity_def
  by simp


text \<open>
  Declarations for replacing interpreted abstract functions from locales
  by their explicit instantiations for code generation.
\<close>

declare [[lc_add "\<S>\<C>\<F>_result.electoral_module" electoral_module_\<S>\<C>\<F>_code_lemma]]
declare [[lc_add "\<S>\<C>\<F>_result.\<R>\<^sub>\<W>" \<R>\<^sub>\<W>_\<S>\<C>\<F>_code_lemma]]
declare [[lc_add "\<S>\<C>\<F>_result.\<R>\<^sub>\<W>_std" \<R>\<^sub>\<W>_std_\<S>\<C>\<F>_code_lemma]]
declare [[lc_add "\<S>\<C>\<F>_result.distance_\<R>" distance_\<R>_\<S>\<C>\<F>_code_lemma]]
declare [[lc_add "\<S>\<C>\<F>_result.distance_\<R>_std" distance_\<R>_std_\<S>\<C>\<F>_code_lemma]]
declare [[lc_add "\<S>\<C>\<F>_result.anonymity" anonymity_\<S>\<C>\<F>_code_lemma]]


text \<open>
  Constant aliases to use when exporting code instead of the interpreted functions
\<close>

definition "\<R>\<^sub>\<W>_\<S>\<C>\<F>_code = \<S>\<C>\<F>_result.\<R>\<^sub>\<W>"
definition "\<R>\<^sub>\<W>_std_\<S>\<C>\<F>_code = \<S>\<C>\<F>_result.\<R>\<^sub>\<W>_std"
definition "distance_\<R>_\<S>\<C>\<F>_code = \<S>\<C>\<F>_result.distance_\<R>"
definition "distance_\<R>_std_\<S>\<C>\<F>_code = \<S>\<C>\<F>_result.distance_\<R>_std"
definition "electoral_module_\<S>\<C>\<F>_code = \<S>\<C>\<F>_result.electoral_module"
definition "anonymity_\<S>\<C>\<F>_code = \<S>\<C>\<F>_result.anonymity"

setup Locale_Code.close_block

end
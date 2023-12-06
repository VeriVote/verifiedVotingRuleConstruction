theory Interpretation_Code
  imports Electoral_Module
          Distance_Rationalization
begin
setup Locale_Code.open_block

text \<open>
  Lemmas stating the explicit instantiations of interpreted abstract functions from locales.
\<close>

lemma electoral_module_soc_choice_code_lemma: 
  "social_choice_result.electoral_module m
    \<equiv> \<forall> A V p. profile V A p \<longrightarrow> well_formed_soc_choice A (m V A p)"
  by (rule social_choice_result.electoral_module_def)

lemma \<R>\<^sub>\<W>_soc_choice_code_lemma: 
  "social_choice_result.\<R>\<^sub>\<W> d K V A p 
    = arg_min_set (score d K (A, V, p)) (limit_set_soc_choice A UNIV)"
  by (rule social_choice_result.\<R>\<^sub>\<W>.simps)

lemma distance_\<R>_soc_choice_code_lemma:
  "social_choice_result.distance_\<R> d K V A p = 
    (social_choice_result.\<R>\<^sub>\<W> d K V A p, 
      (limit_set_soc_choice A UNIV) - social_choice_result.\<R>\<^sub>\<W> d K V A p, {})"
  by (rule social_choice_result.distance_\<R>.simps)

lemma \<R>\<^sub>\<W>_std_soc_choice_code_lemma: 
  "social_choice_result.\<R>\<^sub>\<W>_std d K V A p = 
    arg_min_set (score_std d K (A, V, p)) (limit_set_soc_choice A UNIV)"
  by (rule social_choice_result.\<R>\<^sub>\<W>_std.simps)

lemma distance_\<R>_std_soc_choice_code_lemma:
  "social_choice_result.distance_\<R>_std d K V A p = 
    (social_choice_result.\<R>\<^sub>\<W>_std d K V A p, 
    (limit_set_soc_choice A UNIV) - social_choice_result.\<R>\<^sub>\<W>_std d K V A p, {})"
  by (rule social_choice_result.distance_\<R>_std.simps)


text \<open>
  Declarations for replacing interpreted abstract functions from locales 
  by their explicit instantiations for code generation.
\<close>

declare [[lc_add "social_choice_result.electoral_module" electoral_module_soc_choice_code_lemma]]
declare [[lc_add "social_choice_result.\<R>\<^sub>\<W>" \<R>\<^sub>\<W>_soc_choice_code_lemma]]
declare [[lc_add "social_choice_result.\<R>\<^sub>\<W>_std" \<R>\<^sub>\<W>_std_soc_choice_code_lemma]]
declare [[lc_add "social_choice_result.distance_\<R>" distance_\<R>_soc_choice_code_lemma]]
declare [[lc_add "social_choice_result.distance_\<R>_std" distance_\<R>_std_soc_choice_code_lemma]]


text \<open>
  Constant aliases to use when exporting code instead of the interpreted functions
\<close>

definition "\<R>\<^sub>\<W>_soc_choice_code = social_choice_result.\<R>\<^sub>\<W>"
definition "\<R>\<^sub>\<W>_std_soc_choice_code = social_choice_result.\<R>\<^sub>\<W>_std"
definition "distance_\<R>_soc_choice_code = social_choice_result.distance_\<R>"
definition "distance_\<R>_std_soc_choice_code = social_choice_result.distance_\<R>_std"
definition "electoral_module_soc_choice_code = social_choice_result.electoral_module" 

setup Locale_Code.close_block
end
(*  File:       Elimination_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elimination Module\<close>

theory Elimination_Module
  imports Evaluation_Function
          Electoral_Module
begin

text \<open>
  This is the elimination module. It rejects a set of alternatives only if
  these are not all alternatives. The alternatives potentially to be rejected
  are put in a so-called elimination set. These are all alternatives that score
  below a preset threshold value that depends on the specific voting rule.
\<close>

subsection \<open>General Definitions\<close>

type_synonym Threshold_Value = enat

type_synonym Threshold_Relation = "enat \<Rightarrow> enat \<Rightarrow> bool"

type_synonym ('a, 'v) Electoral_Set = "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a set"

fun elimination_set :: "('a, 'v) Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> ('a, 'v) Electoral_Set" where
 "elimination_set e t r V A p = {a \<in> A . r (e V a A p) t }"

fun average :: "('a, 'v) Evaluation_Function \<Rightarrow> 'v set \<Rightarrow>
  'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> Threshold_Value" where
  "average e V A p = (let sum = (\<Sum> x \<in> A. e V x A p) in 
                      (if (sum = infinity) then (infinity) 
                       else ((the_enat sum) div (card A))))"
(* export_code average in Haskell *)

subsection \<open>General Auxiliary Lemmas\<close>

lemma score_bounded:
  fixes
    e :: "'a \<Rightarrow> nat" and
    A :: "'a set" and
    a :: "'a"
  assumes
    a_in_A: "a \<in> A" and
    fin_A: "finite A"
  shows "e a \<le> Max {e x | x. x \<in> A}"
proof -
  have "e a \<in> {e x |x. x \<in> A}"
    using a_in_A
    by blast
  thus ?thesis
    using fin_A Max_ge
    by simp
qed

lemma max_score_contained:
  fixes
    e :: "'a \<Rightarrow> nat" and
    A :: "'a set" and
    a :: "'a"
  assumes
    A_not_empty: "A \<noteq> {}" and
    fin_A: "finite A"
  shows "\<exists> b \<in> A. e b = Max {e x | x. x \<in> A}"
proof -
  have "finite {e x | x. x \<in> A}"
    using fin_A
    by simp
  hence "Max {e x | x. x \<in> A} \<in> {e x | x. x \<in> A}"
    using A_not_empty Max_in
    by blast
  thus ?thesis
    by auto
qed

lemma elimset_in_alts:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "elimination_set e t r V A p \<subseteq> A"
  unfolding elimination_set.simps
  by safe

subsection \<open>General Inference Rules\<close>

lemma cr_eval_imp_dcc_max_elim_helper:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    e :: "('a, 'v) Evaluation_Function" and
    a :: "'a"
  assumes
    "finite_profile V A p" and
    "condorcet_rating e" and
    "condorcet_winner V A p a"
  shows "elimination_set e (Max {e V b A p | b. b \<in> A}) (<) V A p = A - {a}"
proof (safe, simp_all, safe)
  assume "e V a A p < Max {e V b A p | b. b \<in> A}"
  thus False
    using cond_winner_imp_max_eval_val assms
    by fastforce
next
  fix a' :: "'a"
  assume
    "a' \<in> A" and
    "\<not> e V a' A p < Max {e V b A p | b. b \<in> A}"
  thus "a' = a"
    using non_cond_winner_not_max_eval assms
    by (metis (mono_tags, lifting))
qed

(* Social Choice Specific Results *)

subsection \<open>Social Choice Definitions\<close>

fun elimination_module :: "('a, 'v) Evaluation_Function \<Rightarrow> 
  Threshold_Value \<Rightarrow> Threshold_Relation \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "elimination_module e t r V A p =
      (if (elimination_set e t r V A p) \<noteq> A
        then ({}, (elimination_set e t r V A p), A - (elimination_set e t r V A p))
        else ({}, {}, A))"

subsection \<open>Common Social Choice Eliminators\<close>

fun less_eliminator :: "('a, 'v) Evaluation_Function \<Rightarrow> 
  Threshold_Value \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "less_eliminator e t V A p = elimination_module e t (<) V A p"

fun max_eliminator :: 
  "('a, 'v) Evaluation_Function \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "max_eliminator e V A p =
    less_eliminator e (Max {e V x A p | x. x \<in> A}) V A p"
find_theorems "max_eliminator"

fun leq_eliminator :: 
  "('a, 'v) Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
    ('a, 'v, 'a Result) Electoral_Module" where
  "leq_eliminator e t V A p = elimination_module e t (\<le>) V A p"

fun min_eliminator :: 
  "('a, 'v) Evaluation_Function \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "min_eliminator e V A p =
    leq_eliminator e (Min {e V x A p | x. x \<in> A}) V A p"

fun less_average_eliminator :: 
  "('a, 'v) Evaluation_Function \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "less_average_eliminator e V A p = less_eliminator e (average e V A p) V A p"

fun leq_average_eliminator :: 
  "('a, 'v) Evaluation_Function \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "leq_average_eliminator e V A p = leq_eliminator e (average e V A p) V A p"

subsection \<open>Soundness\<close>

lemma elim_mod_sound[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "social_choice_result.electoral_module (elimination_module e t r)"
  unfolding social_choice_result.electoral_module_def
  by auto

lemma less_elim_sound[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "social_choice_result.electoral_module (less_eliminator e t)"
  unfolding social_choice_result.electoral_module_def
  by auto

lemma leq_elim_sound[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "social_choice_result.electoral_module (leq_eliminator e t)"
  unfolding social_choice_result.electoral_module_def
  by auto

lemma max_elim_sound[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "social_choice_result.electoral_module (max_eliminator e)"
  unfolding social_choice_result.electoral_module_def
  by auto

lemma min_elim_sound[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "social_choice_result.electoral_module (min_eliminator e)"
  unfolding social_choice_result.electoral_module_def
  by auto

lemma less_avg_elim_sound[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "social_choice_result.electoral_module (less_average_eliminator e)"
  unfolding social_choice_result.electoral_module_def
  by auto

lemma leq_avg_elim_sound[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "social_choice_result.electoral_module (leq_average_eliminator e)"
  unfolding social_choice_result.electoral_module_def
  by auto

subsection \<open>Non-Blocking\<close>

lemma elim_mod_non_blocking:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "non_blocking (elimination_module e t r)"
  unfolding non_blocking_def
  by auto

lemma less_elim_non_blocking:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_blocking (less_eliminator e t)"
  unfolding less_eliminator.simps
  using elim_mod_non_blocking
  by auto

lemma leq_elim_non_blocking:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_blocking (leq_eliminator e t)"
  unfolding leq_eliminator.simps
  using elim_mod_non_blocking
  by auto

lemma max_elim_non_blocking:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_blocking (max_eliminator e)"
  unfolding non_blocking_def
  using social_choice_result.electoral_module_def
  by auto

lemma min_elim_non_blocking:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_blocking (min_eliminator e)"
  unfolding non_blocking_def
  using social_choice_result.electoral_module_def
  by auto

lemma less_avg_elim_non_blocking:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_blocking (less_average_eliminator e)"
  unfolding non_blocking_def
  using social_choice_result.electoral_module_def
  by auto

lemma leq_avg_elim_non_blocking:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_blocking (leq_average_eliminator e)"
  unfolding non_blocking_def
  using social_choice_result.electoral_module_def
  by auto

subsection \<open>Non-Electing\<close>

lemma elim_mod_non_electing:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "non_electing (elimination_module e t r)"
  unfolding non_electing_def
  by simp

lemma less_elim_non_electing:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_electing (less_eliminator e t)"
  using elim_mod_non_electing less_elim_sound
  unfolding non_electing_def
  by simp

lemma leq_elim_non_electing:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_electing (leq_eliminator e t)"
  unfolding non_electing_def
  by simp

lemma max_elim_non_electing:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_electing (max_eliminator e)"
  unfolding non_electing_def
  by simp

lemma min_elim_non_electing:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_electing (min_eliminator e)"
  unfolding non_electing_def
  by simp

lemma less_avg_elim_non_electing:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_electing (less_average_eliminator e)"
  unfolding non_electing_def
  by auto

lemma leq_avg_elim_non_electing:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_electing (leq_average_eliminator e)"
  unfolding non_electing_def
  by simp

subsection \<open>Inference Rules\<close>

text \<open>
  If the used evaluation function is Condorcet rating,
    max-eliminator is Condorcet compatible.
\<close>

theorem cr_eval_imp_ccomp_max_elim[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  assumes "condorcet_rating e"
  shows "condorcet_compatibility (max_eliminator e)"
proof (unfold condorcet_compatibility_def, safe)
  show "social_choice_result.electoral_module (max_eliminator e)"
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    c_win: "condorcet_winner V A p a" and
    rej_a: "a \<in> reject V (max_eliminator e) A p"
  have "e V a A p = Max {e V b A p | b. b \<in> A}"
    using c_win cond_winner_imp_max_eval_val assms
    by fastforce
  hence "a \<notin> reject V (max_eliminator e) A p"
    by simp
  thus "False"
    using rej_a
    by linarith
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume "a \<in> elect V (max_eliminator e) A p"
  moreover have "a \<notin> elect V (max_eliminator e) A p"
    by simp
  ultimately show False
    by linarith
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    a' :: "'a"
  assume
    "condorcet_winner V A p a" and
    "a \<in> elect V (max_eliminator e) A p"
  thus "a' \<in> reject V (max_eliminator e) A p"
    using condorcet_winner.elims(2) empty_iff max_elim_non_electing
    unfolding non_electing_def
    by metis
qed

text \<open>
  If the used evaluation function is Condorcet rating, max-eliminator
  is defer-Condorcet-consistent.
\<close>

theorem cr_eval_imp_dcc_max_elim[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  assumes "condorcet_rating e"
  shows "defer_condorcet_consistency (max_eliminator e)"
proof (unfold defer_condorcet_consistency_def, safe, simp)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    winner: "condorcet_winner V A p a" and
    finite_C: "finite A" and
    finite_V: "finite V"
  hence profile: "finite_profile V A p"
    by simp
  let ?trsh = "Max {e V b A p | b. b \<in> A}"
  show
    "max_eliminator e V A p =
      ({},
        A - defer V (max_eliminator e) A p,
        {b \<in> A. condorcet_winner V A p b})"
  proof (cases "elimination_set e (?trsh) (<) V A p \<noteq> A")
    have elim_set: "(elimination_set e ?trsh (<) V A p) = A - {a}"
      using profile assms winner cr_eval_imp_dcc_max_elim_helper
      by (metis (mono_tags, lifting))
    case True
    hence
      "max_eliminator e V A p =
        ({},
          (elimination_set e ?trsh (<) V A p),
          A - (elimination_set e ?trsh (<) V A p))"
      by simp
    also have "... = ({}, A - {a}, {a})"
      using elim_set winner
      by auto
    also have "... = ({},A - defer V (max_eliminator e) A p, {a})"
      using calculation
      by simp
    also have
      "... = ({},
              A - defer V (max_eliminator e) A p,
              {b \<in> A. condorcet_winner V A p b})"
      using cond_winner_unique_3 winner Collect_cong
      by (metis (no_types, lifting))
    finally show ?thesis
      using winner
      by metis
  next
    case False
    moreover have "?trsh = e V a A p"
      using assms winner cond_winner_imp_max_eval_val
      by fastforce
    ultimately show ?thesis
      using winner
      by auto
  qed
qed

end

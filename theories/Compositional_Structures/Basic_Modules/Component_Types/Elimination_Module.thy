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

subsection \<open>Definition\<close>

type_synonym Threshold_Value = nat

type_synonym Threshold_Relation = "nat \<Rightarrow> nat \<Rightarrow> bool"

type_synonym 'a Electoral_Set = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set"

fun elimination_set :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> 'a Electoral_Set" where
 "elimination_set e t r A p = {a \<in> A . r (e a A p) t }"

fun elimination_module :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> 'a Electoral_Module" where
  "elimination_module e t r A p =
      (if (elimination_set e t r A p) \<noteq> A
        then ({}, (elimination_set e t r A p), A - (elimination_set e t r A p))
        else ({},{},A))"

subsection \<open>Common Eliminators\<close>

fun less_eliminator :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module" where
  "less_eliminator e t A p = elimination_module e t (<) A p"

fun max_eliminator :: "'a Evaluation_Function \<Rightarrow> 'a Electoral_Module" where
  "max_eliminator e A p =
    less_eliminator e (Max {e x A p | x. x \<in> A}) A p"

fun leq_eliminator :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module" where
  "leq_eliminator e t A p = elimination_module e t (\<le>) A p"

fun min_eliminator :: "'a Evaluation_Function \<Rightarrow> 'a Electoral_Module" where
  "min_eliminator e A p =
    leq_eliminator e (Min {e x A p | x. x \<in> A}) A p"

fun average :: "'a Evaluation_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                    Threshold_Value" where
  "average e A p = (\<Sum> x \<in> A. e x A p) div (card A)"

fun less_average_eliminator :: "'a Evaluation_Function \<Rightarrow>
                                'a Electoral_Module" where
  "less_average_eliminator e A p = less_eliminator e (average e A p) A p"

fun leq_average_eliminator :: "'a Evaluation_Function \<Rightarrow>
                                'a Electoral_Module" where
  "leq_average_eliminator e A p = leq_eliminator e (average e A p) A p"

subsection \<open>Auxiliary Lemmas\<close>

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
  shows "\<exists> a' \<in> A. e a' = Max {e x |x. x \<in> A}"
proof -
  have "finite {e x |x. x \<in> A}"
    using fin_A
    by simp
  hence "Max {e x |x. x \<in> A} \<in> {e x |x. x \<in> A}"
    using A_not_empty Max_in
    by blast
  thus ?thesis
    by auto
qed

subsection \<open>Soundness\<close>

lemma elim_mod_sound[simp]:
  fixes
    e :: "'a Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "electoral_module (elimination_module e t r)"
proof (unfold electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  have "set_equals_partition A (elimination_module e t r A p)"
    by auto
  thus "well_formed A (elimination_module e t r A p)"
    by simp
qed

lemma less_elim_sound[simp]:
  fixes
    e :: "'a Evaluation_Function" and
    t :: "Threshold_Value"
  shows "electoral_module (less_eliminator e t)"
proof (unfold electoral_module_def, safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  show
    "{a \<in> A. e a A p < t} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p < t} \<union> A = A"
    by safe
qed

lemma leq_elim_sound[simp]:
  fixes
    e :: "'a Evaluation_Function" and
    t :: "Threshold_Value"
  shows "electoral_module (leq_eliminator e t)"
proof (unfold electoral_module_def, safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  show
    "{a \<in> A. e a A p \<le> t} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p \<le> t} \<union> A = A"
    by safe
qed

lemma max_elim_sound[simp]:
  fixes e :: "'a Evaluation_Function"
  shows "electoral_module (max_eliminator e)"
proof (unfold electoral_module_def, safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  show
    "{a \<in> A. e a A p < Max {e x A p |x. x \<in> A}} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p < Max {e x A p |x. x \<in> A}} \<union> A = A"
    by safe
qed

lemma min_elim_sound[simp]:
  fixes e :: "'a Evaluation_Function"
  shows "electoral_module (min_eliminator e)"
proof (unfold electoral_module_def, safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  show
    "{a \<in> A. e a A p \<le> Min {e x A p | x. x \<in> A}} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p \<le> Min {e x A p | x. x \<in> A}} \<union> A = A"
    by safe
qed

lemma less_avg_elim_sound[simp]:
  fixes e :: "'a Evaluation_Function"
  shows "electoral_module (less_average_eliminator e)"
proof (unfold electoral_module_def, safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  show
    "{a \<in> A. e a A p < (\<Sum> x \<in> A. e x A p) div card A} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p < (\<Sum> x \<in> A. e x A p) div card A} \<union> A = A"
    by safe
qed

lemma leq_avg_elim_sound[simp]:
  fixes e :: "'a Evaluation_Function"
  shows "electoral_module (leq_average_eliminator e)"
proof (unfold electoral_module_def, safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  show
    "{a \<in> A. e a A p \<le> (\<Sum> x \<in> A. e x A p) div card A} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p \<le> (\<Sum> x \<in> A. e x A p) div card A} \<union> A = A"
    by safe
qed

subsection \<open>Non-Electing\<close>

lemma elim_mod_non_electing:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  assumes profile: "finite_profile A p"
  shows "non_electing (elimination_module e t r)"
  unfolding non_electing_def
  by simp

lemma less_elim_non_electing:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function" and
    t :: "Threshold_Value"
  assumes profile: "finite_profile A p"
  shows "non_electing (less_eliminator e t)"
  using elim_mod_non_electing profile less_elim_sound
  unfolding non_electing_def
  by simp

lemma leq_elim_non_electing:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function" and
    t :: "Threshold_Value"
  assumes profile: "finite_profile A p"
  shows "non_electing (leq_eliminator e t)"
  unfolding non_electing_def
  by simp

lemma max_elim_non_electing:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function"
  assumes profile: "finite_profile A p"
  shows "non_electing (max_eliminator e)"
  unfolding non_electing_def
  by simp

lemma min_elim_non_electing:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function"
  assumes profile: "finite_profile A p"
  shows "non_electing (min_eliminator e)"
  unfolding non_electing_def
  by simp

lemma less_avg_elim_non_electing:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function"
  assumes profile: "finite_profile A p"
  shows "non_electing (less_average_eliminator e)"
proof (unfold non_electing_def, safe)
  show "electoral_module (less_average_eliminator e)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    elect_a: "a \<in> elect (less_average_eliminator e) A p"
  hence fin_prof: "finite_profile A p"
    by metis
  have "non_electing (less_average_eliminator e)"
    unfolding non_electing_def
    by simp
  hence "{} = elect (less_average_eliminator e) A p"
    using fin_prof
    unfolding non_electing_def
    by metis
  thus "a \<in> {}"
    using elect_a
    by metis
qed

lemma leq_avg_elim_non_electing:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function"
  assumes profile: "finite_profile A p"
  shows "non_electing (leq_average_eliminator e)"
proof (unfold non_electing_def, safe)
  show "electoral_module (leq_average_eliminator e)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    fin_A: "finite A" and
    prof_p: "profile A p" and
    elect_a: "a \<in> elect (leq_average_eliminator e) A p"
  have "non_electing (leq_average_eliminator e)"
    unfolding non_electing_def
    by simp
  hence "{} = elect (leq_average_eliminator e) A p"
    using fin_A prof_p
    unfolding non_electing_def
    by metis
  thus "a \<in> {}"
    using elect_a
    by metis
qed

subsection \<open>Inference Rules\<close>

text \<open>
  If the used evaluation function is Condorcet rating,
    max-eliminator is Condorcet compatible.
\<close>

theorem cr_eval_imp_ccomp_max_elim[simp]:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function"
  assumes
    profile: "finite_profile A p" and
    rating: "condorcet_rating e"
  shows "condorcet_compatibility (max_eliminator e)"
proof (unfold condorcet_compatibility_def, safe)
  show "electoral_module (max_eliminator e)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    c_win: "condorcet_winner A p a" and
    rej_a: "a \<in> reject (max_eliminator e) A p"
  have "e a A p = Max {e b A p | b. b \<in> A}"
    using c_win cond_winner_imp_max_eval_val rating
    by fastforce
  hence "a \<notin> reject (max_eliminator e) A p"
    by simp
  thus "False"
    using rej_a
    by linarith
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume elect_a: "a \<in> elect (max_eliminator e) A p"
  have "a \<notin> elect (max_eliminator e) A p"
    by simp
  thus False
    using elect_a
    by linarith
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a" and
    a' :: "'a"
  assume
    "condorcet_winner A p a" and
    "a \<in> elect (max_eliminator e) A p"
  thus "a' \<in> reject (max_eliminator e) A p"
    using profile rating condorcet_winner.elims(2)
          empty_iff max_elim_non_electing
    unfolding non_electing_def
    by metis
qed

lemma cr_eval_imp_dcc_max_elim_helper:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    e :: "'a Evaluation_Function" and
    a :: "'a"
  assumes
    f_prof: "finite_profile A p" and
    rating: "condorcet_rating e" and
    winner: "condorcet_winner A p a"
  shows "elimination_set e (Max {e b A p | b. b \<in> A}) (<) A p = A - {a}"
proof (safe, simp_all, safe)
  assume "e a A p < Max {e b A p | b. b \<in> A}"
  thus False
    using cond_winner_imp_max_eval_val
          rating winner f_prof
    by fastforce
next
  fix a' :: "'a"
  assume
    "a' \<in> A" and
    "\<not> e a' A p < Max {e b A p | b. b \<in> A}"
  thus "a' = a"
    using non_cond_winner_not_max_eval rating winner f_prof
    by (metis (mono_tags, lifting))
qed

text \<open>
  If the used evaluation function is Condorcet rating, max-eliminator
  is defer-Condorcet-consistent.
\<close>

theorem cr_eval_imp_dcc_max_elim[simp]:
  fixes e :: "'a Evaluation_Function"
  assumes rating: "condorcet_rating e"
  shows "defer_condorcet_consistency (max_eliminator e)"
proof (unfold defer_condorcet_consistency_def, safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    winner: "condorcet_winner A p a" and
    finite: "finite A"
  hence profile: "finite_profile A p"
    by simp
  let ?trsh = "Max {e b A p | b. b \<in> A}"
  show
    "max_eliminator e A p =
      ({},
        A - defer (max_eliminator e) A p,
        {b \<in> A. condorcet_winner A p b})"
  proof (cases "elimination_set e (?trsh) (<) A p \<noteq> A")
    case True
    from profile rating winner
    have 0: "(elimination_set e ?trsh (<) A p) = A - {a}"
      using cr_eval_imp_dcc_max_elim_helper
      by (metis (mono_tags, lifting))
    have
      "max_eliminator e A p =
        ({},
          (elimination_set e ?trsh (<) A p),
          A - (elimination_set e ?trsh (<) A p))"
      using True
      by simp
    also have "... = ({}, A - {a}, {a})"
      using 0 winner
      by auto
    also have "... = ({},A - defer (max_eliminator e) A p, {a})"
      using calculation
      by simp
    also have
      "... =
        ({},
          A - defer (max_eliminator e) A p,
          {b \<in> A. condorcet_winner A p b})"
      using cond_winner_unique_3 winner Collect_cong
      by (metis (no_types, lifting))
    finally show ?thesis
      using finite winner
      by metis
  next
    case False
    have "?trsh = e a A p"
      using rating winner
      by (simp add: cond_winner_imp_max_eval_val)
    thus ?thesis
      using winner False
      by auto
  qed
qed

end

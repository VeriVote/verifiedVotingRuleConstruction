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

type_synonym Threshold_Value = "enat"

type_synonym Threshold_Relation = "enat \<Rightarrow> enat \<Rightarrow> bool"

type_synonym ('a, 'v) Electoral_Set = "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a set"

fun elimination_set :: "('a, 'v) Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
        Threshold_Relation \<Rightarrow> ('a, 'v) Electoral_Set" where
 "elimination_set e t r V A p = {a \<in> A . r (e V a A p) t}"

fun average :: "('a, 'v) Evaluation_Function \<Rightarrow> 'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow>
        Threshold_Value" where
  "average e V A p = (let sum = (\<Sum> x \<in> A. e V x A p) in
                      (if (sum = infinity) then (infinity)
                       else ((the_enat sum) div (card A))))"

subsection \<open>Social-Choice Definitions\<close>

fun elimination_module :: "('a, 'v) Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
        Threshold_Relation \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module" where
  "elimination_module e t r V A p =
      (if (elimination_set e t r V A p) \<noteq> A
        then ({}, (elimination_set e t r V A p), A - (elimination_set e t r V A p))
        else ({}, {}, A))"

subsection \<open>Social-Choice Eliminators\<close>

fun less_eliminator :: "('a, 'v) Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" where
  "less_eliminator e t V A p = elimination_module e t (<) V A p"

fun max_eliminator :: "('a, 'v) Evaluation_Function \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" where
  "max_eliminator e V A p =
    less_eliminator e (Max {e V x A p | x. x \<in> A}) V A p"

fun leq_eliminator :: "('a, 'v) Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" where
  "leq_eliminator e t V A p = elimination_module e t (\<le>) V A p"

fun min_eliminator :: "('a, 'v) Evaluation_Function \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" where
  "min_eliminator e V A p =
    leq_eliminator e (Min {e V x A p | x. x \<in> A}) V A p"

fun less_average_eliminator :: "('a, 'v) Evaluation_Function \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" where
  "less_average_eliminator e V A p = less_eliminator e (average e V A p) V A p"

fun leq_average_eliminator :: "('a, 'v) Evaluation_Function \<Rightarrow>
        ('a, 'v, 'a Result) Electoral_Module" where
  "leq_average_eliminator e V A p = leq_eliminator e (average e V A p) V A p"

subsection \<open>Soundness\<close>

lemma elim_mod_sound[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "\<S>\<C>\<F>_result.electoral_module (elimination_module e t r)"
  unfolding \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma less_elim_sound[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "\<S>\<C>\<F>_result.electoral_module (less_eliminator e t)"
  unfolding \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma leq_elim_sound[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "\<S>\<C>\<F>_result.electoral_module (leq_eliminator e t)"
  unfolding \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma max_elim_sound[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "\<S>\<C>\<F>_result.electoral_module (max_eliminator e)"
  unfolding \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma min_elim_sound[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "\<S>\<C>\<F>_result.electoral_module (min_eliminator e)"
  unfolding \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma less_avg_elim_sound[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "\<S>\<C>\<F>_result.electoral_module (less_average_eliminator e)"
  unfolding \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma leq_avg_elim_sound[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "\<S>\<C>\<F>_result.electoral_module (leq_average_eliminator e)"
  unfolding \<S>\<C>\<F>_result.electoral_module.simps
  by auto

subsection \<open>Independence of Non-Voters\<close>

lemma voters_determine_elim_mod[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (elimination_module e t r)"
proof (unfold voters_determine_election.simps elimination_module.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assume "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> a \<in> A. (e V a A p) = (e V a A p')"
    using assms
    unfolding voters_determine_election.simps
    by simp
  hence "{a \<in> A. r (e V a A p) t} = {a \<in> A. r (e V a A p') t}"
    by metis
  hence "elimination_set e t r V A p = elimination_set e t r V A p'"
    unfolding elimination_set.simps
    by presburger
  thus "(if elimination_set e t r V A p \<noteq> A
        then ({}, elimination_set e t r V A p, A - elimination_set e t r V A p)
        else ({}, {}, A)) =
     (if elimination_set e t r V A p' \<noteq> A
        then ({}, elimination_set e t r V A p', A - elimination_set e t r V A p')
        else ({}, {}, A))"
    by presburger
qed

lemma voters_determine_less_elim[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (less_eliminator e t)"
  using assms voters_determine_elim_mod
  unfolding less_eliminator.simps voters_determine_election.simps
  by (metis (full_types))

lemma voters_determine_leq_elim[simp]:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (leq_eliminator e t)"
  using assms voters_determine_elim_mod
  unfolding leq_eliminator.simps voters_determine_election.simps
  by (metis (full_types))

lemma voters_determine_max_elim[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (max_eliminator e)"
proof (unfold max_eliminator.simps voters_determine_election.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assume coinciding: "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> x \<in> A. e V x A p = e V x A p'"
    using assms
    unfolding voters_determine_evaluation.simps
    by simp
  hence "Max {e V x A p | x. x \<in> A} = Max {e V x A p' | x. x \<in> A}"
    by metis
  thus "less_eliminator e (Max {e V x A p | x. x \<in> A}) V A p =
       less_eliminator e (Max {e V x A p' | x. x \<in> A}) V A p'"
    using coinciding assms voters_determine_less_elim
    unfolding voters_determine_election.simps
    by (metis (no_types, lifting))
qed

lemma voters_determine_min_elim[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (min_eliminator e)"
proof (unfold min_eliminator.simps voters_determine_election.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assume coinciding: "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> x \<in> A. e V x A p = e V x A p'"
    using assms
    unfolding voters_determine_election.simps
    by simp
  hence "Min {e V x A p | x. x \<in> A} = Min {e V x A p' | x. x \<in> A}"
    by metis
  thus "leq_eliminator e (Min {e V x A p | x. x \<in> A}) V A p =
       leq_eliminator e (Min {e V x A p' | x. x \<in> A}) V A p'"
    using coinciding assms voters_determine_leq_elim
    unfolding voters_determine_election.simps
    by (metis (no_types, lifting))
qed

lemma voters_determine_less_avg_elim[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (less_average_eliminator e)"
proof (unfold less_average_eliminator.simps voters_determine_election.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assume coinciding: "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> x \<in> A. e V x A p = e V x A p'"
    using assms
    unfolding voters_determine_election.simps
    by simp
  hence "average e V A p = average e V A p'"
    unfolding average.simps
    by auto
  thus "less_eliminator e (average e V A p) V A p =
       less_eliminator e (average e V A p') V A p'"
    using coinciding assms voters_determine_less_elim
    unfolding voters_determine_election.simps
    by (metis (no_types, lifting))
qed

lemma voters_determine_leq_avg_elim[simp]:
  fixes e :: "('a, 'v) Evaluation_Function"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (leq_average_eliminator e)"
proof (unfold leq_average_eliminator.simps voters_determine_election.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assume coinciding: "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> x \<in> A. e V x A p = e V x A p'"
    using assms
    unfolding voters_determine_election.simps
    by simp
  hence "average e V A p = average e V A p'"
    unfolding average.simps
    by auto
  thus "leq_eliminator e (average e V A p) V A p =
       leq_eliminator e (average e V A p') V A p'"
    using coinciding assms voters_determine_leq_elim
    unfolding voters_determine_election.simps
    by (metis (no_types, lifting))
qed

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
  using \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma min_elim_non_blocking:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_blocking (min_eliminator e)"
  unfolding non_blocking_def
  using \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma less_avg_elim_non_blocking:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_blocking (less_average_eliminator e)"
  unfolding non_blocking_def
  using \<S>\<C>\<F>_result.electoral_module.simps
  by auto

lemma leq_avg_elim_non_blocking:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_blocking (leq_average_eliminator e)"
  unfolding non_blocking_def
  using \<S>\<C>\<F>_result.electoral_module.simps
  by auto

subsection \<open>Non-Electing\<close>

lemma elim_mod_non_electing:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "non_electing (elimination_module e t r)"
  unfolding non_electing_def
  by force

lemma less_elim_non_electing:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_electing (less_eliminator e t)"
  using elim_mod_non_electing less_elim_sound
  unfolding non_electing_def
  by force

lemma leq_elim_non_electing:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_electing (leq_eliminator e t)"
  unfolding non_electing_def
  by force

lemma max_elim_non_electing:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_electing (max_eliminator e)"
  unfolding non_electing_def
  by force

lemma min_elim_non_electing:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_electing (min_eliminator e)"
  unfolding non_electing_def
  by force

lemma less_avg_elim_non_electing:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_electing (less_average_eliminator e)"
  unfolding non_electing_def
  by auto

lemma leq_avg_elim_non_electing:
  fixes e :: "('a, 'v) Evaluation_Function"
  shows "non_electing (leq_average_eliminator e)"
  unfolding non_electing_def
  by force

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
  show "\<S>\<C>\<F>_result.electoral_module (max_eliminator e)"
    by force
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    c_win: "condorcet_winner V A p a" and
    rej_a: "a \<in> reject (max_eliminator e) V A p"
  have "e V a A p = Max {e V b A p | b. b \<in> A}"
    using c_win cond_winner_imp_max_eval_val assms
    by fastforce
  hence "a \<notin> reject (max_eliminator e) V A p"
    by simp
  thus False
    using rej_a
    by linarith
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume "a \<in> elect (max_eliminator e) V A p"
  moreover have "a \<notin> elect (max_eliminator e) V A p"
    by simp
  ultimately show False
    by linarith
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a a' :: "'a"
  assume
    "condorcet_winner V A p a" and
    "a \<in> elect (max_eliminator e) V A p"
  thus "a' \<in> reject (max_eliminator e) V A p"
    using empty_iff max_elim_non_electing
    unfolding condorcet_winner.simps non_electing_def
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
proof (unfold defer_condorcet_consistency_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (max_eliminator e)"
    using max_elim_sound
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume winner: "condorcet_winner V A p a"
  hence f_prof: "finite_profile V A p"
    by simp
  let ?trsh = "Max {e V b A p | b. b \<in> A}"
  show
    "max_eliminator e V A p =
      ({},
        A - defer (max_eliminator e) V A p,
        {b \<in> A. condorcet_winner V A p b})"
  proof (cases "elimination_set e (?trsh) (<) V A p \<noteq> A")
    have "e V a A p = Max {e V x A p | x. x \<in> A}"
      using winner assms cond_winner_imp_max_eval_val
      by fastforce
    hence "\<forall> b \<in> A. b \<noteq> a
        \<longleftrightarrow> b \<in> {c \<in> A. e V c A p < Max {e V b A p | b. b \<in> A}}"
      using winner assms mem_Collect_eq linorder_neq_iff
      unfolding condorcet_rating_def
      by (metis (mono_tags, lifting))
    hence elim_set: "(elimination_set e ?trsh (<) V A p) = A - {a}"
      unfolding elimination_set.simps
      by blast
    case True
    hence
      "max_eliminator e V A p =
        ({},
          (elimination_set e ?trsh (<) V A p),
          A - (elimination_set e ?trsh (<) V A p))"
      by simp
    also have "\<dots> = ({},A - defer (max_eliminator e) V A p, {a})"
      using elim_set winner
      by auto
    also have
      "\<dots> = ({},
              A - defer (max_eliminator e) V A p,
              {b \<in> A. condorcet_winner V A p b})"
      using cond_winner_unique winner Collect_cong
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
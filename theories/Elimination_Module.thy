(*  File:       Elimination_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elimination Module\<close>

theory Elimination_Module
  imports Evaluation_Function
begin

text
\<open>This is the elimination module. It rejects a set of alternatives only if these
are not all alternatives. The alternatives potentially to be rejected are put
in a so-called elimination set. These are all alternatives that score below
a preset threshold value that depends on the specific voting rule.\<close>

subsection \<open>Definition\<close>

type_synonym Threshold_Value = nat

fun elimination_set :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            (nat \<Rightarrow> Threshold_Value \<Rightarrow> bool) \<Rightarrow>
                              'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
 "elimination_set e t r A p = {a \<in> A . r (e a A p) t }"

fun elimination_module :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
        (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a Electoral_Module" where
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
  "average e A p = (\<Sum>x \<in> A. e x A p) div (card A)"

fun less_average_eliminator :: "'a Evaluation_Function \<Rightarrow>
                                'a Electoral_Module" where
  "less_average_eliminator e A p = less_eliminator e (average e A p) A p"

fun leq_average_eliminator :: "'a Evaluation_Function \<Rightarrow>
                                'a Electoral_Module" where
  "leq_average_eliminator e A p = leq_eliminator e (average e A p) A p"

subsection \<open>Soundness\<close>

lemma elim_mod_sound[simp]: "electoral_module (elimination_module e t r)"
proof (unfold electoral_module_def)
  show
    "\<forall>A p. finite_profile A p \<longrightarrow>
        partition A (elimination_module e t r A p)"
  proof (unfold partition.simps)
    show
      "\<forall>A p. finite_profile A p \<longrightarrow>
          disjoint3 (elimination_module e t r A p) \<and>
          set_equals_partition A (elimination_module e t r A p)"
      by auto
  qed
qed

lemma less_elim_sound[simp]: "electoral_module (less_eliminator e t)"
  using elim_mod_sound less_eliminator.simps electoral_module_def
  by (metis (no_types))

lemma leq_elim_sound[simp]: "electoral_module (leq_eliminator e t)"
  using elim_mod_sound leq_eliminator.simps electoral_module_def
  by (metis (no_types))

lemma max_elim_sound[simp]: "electoral_module (max_eliminator e)"
proof -
  obtain
    AA :: "('a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow>
              'a set" and
    rrs :: "('a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow>
              ('a \<times> 'a) set list" where
    "\<forall>f.
      (electoral_module f \<or> 
        \<not> Electoral_Module.partition (AA f) (f (AA f) (rrs f)) \<and>
            profile (AA f) (rrs f) \<and> finite (AA f)) \<and> 
      (electoral_module f \<longrightarrow> 
        (\<forall>A rs. profile A rs \<and> finite A \<longrightarrow> Electoral_Module.partition A (f A rs)))"
    using electoral_module_def
    by metis
  thus ?thesis
    using electoral_module_def
    by force
qed

lemma min_elim_sound[simp]: "electoral_module (min_eliminator e)"
proof -
  obtain
    AA :: "('a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow>
              'a set" and
    rrs :: "('a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow>
              ('a \<times> 'a) set list" where
    "\<forall>f.
      (electoral_module f \<or> 
        \<not> Electoral_Module.partition (AA f) (f (AA f) (rrs f)) \<and>
            profile (AA f) (rrs f) \<and> finite (AA f)) \<and> 
      (electoral_module f \<longrightarrow> 
        (\<forall>A rs. profile A rs \<and> finite A \<longrightarrow> Electoral_Module.partition A (f A rs)))"
    using electoral_module_def
    by metis
  thus ?thesis
    using leq_elim_sound min_eliminator.simps
    by (metis (no_types, lifting))
qed

lemma less_avg_elim_sound[simp]: "electoral_module (less_average_eliminator e)"
  using less_average_eliminator.simps electoral_module_def less_elim_sound
  by metis

lemma leq_avg_elim_sound[simp]: "electoral_module (leq_average_eliminator e)"
  using leq_average_eliminator.simps electoral_module_def leq_elim_sound
  by metis

subsection \<open>Non-Electing\<close>

lemma elim_mod_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (elimination_module e t r )"
  by (simp add: non_electing_def)

lemma less_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (less_eliminator e t)"
  using elim_mod_non_electing profile less_elim_sound
  by (simp add: non_electing_def)

lemma leq_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (leq_eliminator e t)"
  using elim_mod_non_electing profile
        leq_eliminator.simps leq_elim_sound
  by (simp add: non_electing_def)

lemma max_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (max_eliminator e)"
  using profile electoral_module_def
        non_electing_def max_eliminator.simps less_elim_non_electing
  by (metis (mono_tags, lifting))

lemma min_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (min_eliminator e)"
  using profile electoral_module_def non_electing_def
        leq_elim_non_electing min_eliminator.simps
  by (metis (mono_tags, lifting))

lemma less_avg_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (less_average_eliminator e)"
  using profile electoral_module_def non_electing_def
        less_elim_non_electing less_average_eliminator.simps
  by (metis (mono_tags, lifting))

lemma leq_avg_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (leq_average_eliminator e)"
  using profile electoral_module_def non_electing_def
        leq_elim_non_electing leq_average_eliminator.simps
  by (metis (mono_tags, lifting))

subsection \<open>Properties\<close>

(*** If the used evaluation function is Condorcet rating,
     max-eliminator is Condorcet compatible. ***)
theorem cr_eval_imp_ccomp_max_elim[simp]:
  assumes
    profile: "finite_profile A p" and
    rating: "condorcet_rating e"
  shows
    "condorcet_compatibility (max_eliminator e)"
proof (unfold condorcet_compatibility_def)
  show
    "electoral_module (max_eliminator e) \<and>
       (\<forall>A p w. condorcet_winner A p w \<and> finite A \<longrightarrow>
           w \<notin> reject (max_eliminator e) A p \<and>
           (\<forall>l. \<not> condorcet_winner A p l \<longrightarrow>
               l \<notin> elect (max_eliminator e) A p) \<and>
           (w \<in> elect (max_eliminator e) A p \<longrightarrow>
               (\<forall>l. \<not> condorcet_winner A p l \<longrightarrow>
                   l \<in> reject (max_eliminator e) A p)))"
  proof (auto)
    have f1:
      "\<And>A p w x. condorcet_winner A p w \<Longrightarrow>
          finite A \<Longrightarrow> w \<in> A \<Longrightarrow> e w A p < Max {e x A p |x. x \<in> A} \<Longrightarrow>
          x \<in> A \<Longrightarrow> e x A p < Max {e x A p |x. x \<in> A}"
      using cond_winner_imp_max_eval_val rating
      by (simp add: cond_winner_imp_max_eval_val)
    thus
      "\<And>A p w x.
          profile A p \<Longrightarrow> w \<in> A \<Longrightarrow>
            \<forall>x\<in>A - {w}.
              card {i. i < length p \<and> (w, x) \<in> (p!i)} <
                card {i. i < length p \<and> (x, w) \<in> (p!i)} \<Longrightarrow>
                  finite A \<Longrightarrow> e w A p < Max {e x A p | x. x \<in> A} \<Longrightarrow>
                    x \<in> A \<Longrightarrow> e x A p < Max {e x A p | x. x \<in> A}"
      by simp
  qed
qed

lemma cr_eval_imp_dcc_max_elim_helper1:
  assumes
    f_prof: "finite_profile A p" and
    rating: "condorcet_rating e" and
    winner: "condorcet_winner A p w"
  shows "elimination_set e (Max {e x A p | x. x \<in> A}) (<) A p = A - {w}"
proof (auto)
  show "w \<in> A \<Longrightarrow> e w A p < Max {e x A p |x. x \<in> A} \<Longrightarrow> False"
    using cond_winner_imp_max_eval_val f_prof rating winner
          Collect_cong nat_neq_iff less_not_refl
    by (simp add: cond_winner_imp_max_eval_val)
next
  show "\<And>x. x \<in> A \<Longrightarrow> x \<noteq> w \<Longrightarrow> e x A p < Max {e x A p |x. x \<in> A}"
    using non_cond_winner_not_max_eval f_prof rating winner
    by (metis (mono_tags, lifting))
qed

(*
  If the used evaluation function is Condorcet rating, max-eliminator
  is defer-Condorcet-consistent.
*)
theorem cr_eval_imp_dcc_max_elim[simp]:
  assumes rating: "condorcet_rating e"
  shows "defer_condorcet_consistency (max_eliminator e)"
proof (unfold defer_condorcet_consistency_def, intro allI conjI impI)
  have "electoral_module (max_eliminator e)"
    using max_elim_sound max_eliminator.simps
    by simp
  thus "electoral_module (max_eliminator e)"
    using elimination_module.simps
    by auto
  next
    show
      "\<And>A p w. condorcet_winner A p w \<and> finite A \<Longrightarrow>
          max_eliminator e A p =
            ({},
              A - defer (max_eliminator e) A p,
              {d \<in> A. condorcet_winner A p d})"
    proof -
      fix
        A :: "'a set" and
        p :: "('a \<times> 'a) set list" and
        w :: "'a"
      assume assm:
        "condorcet_winner A p w \<and> finite A"
      have winner:
        "condorcet_winner A p w"
        using assm
        by simp
      also have finite:
        "finite A"
        using assm
        by simp
      thus
        "max_eliminator e A p =
          ({},
            A - defer (max_eliminator e) A p,
            {a \<in> A. condorcet_winner A p a})"
      proof (cases "elimination_set e (Max {e y A p | y. y \<in> A}) (<) A p \<noteq> A")
        let ?trsh = "(Max {e y A p | y. y \<in> A})"
        case True
        have profile: "finite_profile A p"
          using condorcet_winner.simps winner
          by metis
        with rating winner have 0:
          "(elimination_set e ?trsh (<) A p) = A - {w}"
          using cr_eval_imp_dcc_max_elim_helper1
                assm cr_eval_imp_dcc_max_elim_helper1
          by (metis (mono_tags, lifting))
        have
          "max_eliminator e A p =
            ({},
              (elimination_set e ?trsh (<) A p),
              A - (elimination_set e ?trsh (<) A p))"
          using True
          by simp
        also have "... = ({}, A - {w}, A - (A - {w}))"
          using "0"
          by presburger
        also have "... = ({}, A - {w}, {w})"
          using condorcet_winner.simps winner double_diff
                subsetI empty_subsetI insert_subset
          by metis
        also have "... = ({},A - defer (max_eliminator e) A p, {w})"
          using calculation
          by auto
        also have
          "... =
            ({},
            A - defer (max_eliminator e) A p,
            {d \<in> A. condorcet_winner A p d})"
          using cond_winner_unique3 winner Collect_cong
          by (metis (no_types, lifting))
        finally show ?thesis
          using finite winner
          by metis
      next
        case False
        thus ?thesis
        proof -
          have f1:
            "finite A \<and> profile A p \<and> w \<in> A \<and> (\<forall>a. a \<notin> A - {w} \<or> wins w p a)"
            using condorcet_winner.simps winner
            by metis
          hence
            "Max {e a A p |a. a \<in> A} = e w A p"
            using rating winner
            by (simp add: cond_winner_imp_max_eval_val)
          hence False
            using f1 False
            by auto
          thus ?thesis
            by simp
        qed
      qed
    qed
qed


end

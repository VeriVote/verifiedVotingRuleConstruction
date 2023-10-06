(*  File:       Result.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Result\<close>

theory Result
  imports Main
          Profile
begin

text \<open>
  An electoral result is the principal result type of the composable modules
  voting framework, as it is a generalization of the set of winning
  alternatives from social choice functions. Electoral results are selections
  of the received (possibly empty) set of alternatives into the three disjoint
  groups of elected, rejected and deferred alternatives.
  Any of those sets, e.g., the set of winning (elected) alternatives, may also
  be left empty, as long as they collectively still hold all the received
  alternatives.
\<close>

subsection \<open>Definition\<close>

text \<open>
  A result generally is related to the alternative set A (of type 'a).
  A result should be well-formed on the alternatives.
  Also it should be possible to limit a well-formed result to a subset of the alternatives.

  Specific result types like social choice results (sets of alternatives) can be realized
  via sublocales of the result locale.
\<close>

type_synonym 'r Result = "'r set * 'r set * 'r set"

fun disjoint3 :: "'r Result \<Rightarrow> bool" where
  "disjoint3 (e, r, d) =
    ((e \<inter> r = {}) \<and>
      (e \<inter> d = {}) \<and>
      (r \<inter> d = {}))"

fun set_equals_partition :: "'r set \<Rightarrow>'r Result \<Rightarrow> bool" where
  "set_equals_partition X (r1, r2, r3) = (r1 \<union> r2 \<union> r3 = X)"

locale result =
  fixes well_formed :: "'a set \<Rightarrow> ('r Result) \<Rightarrow> bool" 
    and limit_set :: "'a set \<Rightarrow> 'r set \<Rightarrow> 'r set"
  assumes "\<And> A r. (set_equals_partition (limit_set A UNIV) r \<and> disjoint3 r) 
            \<Longrightarrow> well_formed A r"
      and "\<And> A B r1 r2 r3. A \<subseteq> B \<Longrightarrow> well_formed B (r1, r2, r3) 
            \<Longrightarrow> well_formed A ((limit_set A r1), (limit_set A r2), (limit_set A r3))"

text \<open>
  These three functions return the elect, reject, or defer set of a result.
\<close>

fun (in result) limit_res :: "'a set \<Rightarrow> 'r Result \<Rightarrow> 'r Result" where
  "limit_res A (e, r, d) = (limit_set A e, limit_set A r, limit_set A d)"

abbreviation elect_r :: "'r Result \<Rightarrow> 'r set" where
  "elect_r r \<equiv> fst r"

abbreviation reject_r :: "'r Result \<Rightarrow> 'r set" where
  "reject_r r \<equiv> fst (snd r)"

abbreviation defer_r :: "'r Result \<Rightarrow> 'r set" where
  "defer_r r \<equiv> snd (snd r)"

subsection \<open>Social Choice Results\<close>

text \<open>
  A social choice result contains three sets of alternatives:
  elected, rejected, and deferred alternatives.
\<close>

subsection \<open>Auxiliary Functions\<close>

text \<open>
  A partition of a set A are pairwise disjoint sets that "set equals
  partition" A. For this specific predicate, we have three disjoint sets
  in a three-tuple.
\<close>

fun well_formed :: "'a set \<Rightarrow> 'a Result \<Rightarrow> bool" where
  "well_formed A res = (disjoint3 res \<and> set_equals_partition A res)"

fun limit_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "limit_set A r = A \<inter> r"

subsection \<open>Auxiliary Lemmas\<close>

lemma result_imp_rej:
  fixes
    A :: "'a set" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assumes "well_formed A (e, r, d)"
  shows "A - (e \<union> d) = r"
proof (safe)
  fix a :: "'a"
  assume
    "a \<in> A" and
    "a \<notin> r" and
    "a \<notin> d"
  moreover have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    using assms
    by simp
  ultimately show "a \<in> e"
    by auto
next
  fix a :: "'a"
  assume "a \<in> r"
  moreover have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    using assms
    by simp
  ultimately show "a \<in> A"
    by auto
next
  fix a :: "'a"
  assume
    "a \<in> r" and
    "a \<in> e"
  moreover have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    using assms
    by simp
  ultimately show False
    by auto
next
  fix a :: "'a"
  assume
    "a \<in> r" and
    "a \<in> d"
  moreover have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = A)"
    using assms
    by simp
  ultimately show False
    by auto
qed

lemma result_count:
  fixes
    A :: "'a set" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assumes
    wf_result: "well_formed A (e, r, d)" and
    fin_A: "finite A"
  shows "card A = card e + card r + card d"
proof -
  have "e \<union> r \<union> d = A"
    using wf_result
    by simp
  moreover have "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {})"
    using wf_result
    by simp
  ultimately show ?thesis
    using fin_A Int_Un_distrib2 finite_Un card_Un_disjoint sup_bot.right_neutral
    by metis
qed

lemma defer_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed A r"
  shows "defer_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> defer_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have
    "\<forall> p. \<exists> E R D. set_equals_partition A p \<longrightarrow> (E, R, D) = p \<and> E \<union> R \<union> D = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI snd_conv
    by metis
qed

lemma elect_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed A r"
  shows "elect_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> elect_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have
    "\<forall> p. \<exists> E R D. set_equals_partition A p \<longrightarrow> (E, R, D) = p \<and> E \<union> R \<union> D = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI assms fst_conv
    by metis
qed

lemma reject_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed A r"
  shows "reject_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> reject_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have
    "\<forall> p. \<exists> E R D. set_equals_partition A p \<longrightarrow> (E, R, D) = p \<and> E \<union> R \<union> D = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI assms fst_conv snd_conv disjoint3.cases
    by metis
qed

subsection \<open>Social Welfare Results\<close>

text \<open>
  A social welfare result contains three sets of relations:
  elected, rejected, and deferred
  A well-formed social welfare result consists only of linear 
  orders on the alternatives.
\<close>

fun well_formed_welfare :: "'a set \<Rightarrow> ('a Preference_Relation) Result \<Rightarrow> bool" where
  "well_formed_welfare A res = (disjoint3 res \<and> 
                                  set_equals_partition {r. linear_order_on A r} res)"

fun limit_set_welfare :: 
  "'a set \<Rightarrow> ('a Preference_Relation) set \<Rightarrow> ('a Preference_Relation) set" where 
  "limit_set_welfare A res = {limit A r | r. r \<in> res \<and> linear_order_on A (limit A r)}"
(* TODO first result assumption does not hold like that *)

subsection \<open>Result Interpretations\<close>

(* print_locale! result *)

interpretation social_choice_result:
  result "well_formed" "limit_set" 
proof (unfold_locales, simp, auto) qed

interpretation social_welfare_result:
  result "well_formed_welfare" "limit_set_welfare"
proof (unfold_locales, safe)
  fix 
    A :: "'a set" and
    r1 :: "('a Preference_Relation) set" and
    r2 :: "('a Preference_Relation) set" and
    r3 :: "('a Preference_Relation) set"
  assume
    partition: "set_equals_partition (limit_set_welfare A UNIV) (r1, r2, r3)" and
    disj: "disjoint3 (r1, r2, r3)"
  have "limit_set_welfare A UNIV = 
          {limit A r | r. r \<in> UNIV \<and> linear_order_on A (limit A r)}"
    by simp
  also have "... = {limit A r | r. r \<in> UNIV} \<inter> 
                    {limit A r | r. linear_order_on A (limit A r)}"
    by auto
  also have "... = {limit A r | r. linear_order_on A (limit A r)}"
    by auto
  also have "... = {r. linear_order_on A r}"
  proof (safe)
    fix 
      r :: "'a Preference_Relation"
    assume 
      lin_ord: "linear_order_on A r"
    hence "\<forall> a b. (a, b) \<in> r \<longrightarrow> (a, b) \<in> limit A r"
      unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by auto
    hence "r \<subseteq> limit A r" by auto
    moreover have "limit A r \<subseteq> r" by auto
    ultimately have "r = limit A r" by simp
    thus "\<exists>x. r = limit A x \<and> linear_order_on A (limit A x)"
      using lin_ord
      by metis
  qed
  thus "well_formed_welfare A (r1, r2, r3)"
    using partition disj
    by simp
next
  fix 
    A :: "'a set" and
    B :: "'a set" and
    r1 :: "('a Preference_Relation) set" and
    r2 :: "('a Preference_Relation) set" and
    r3 :: "('a Preference_Relation) set"
  assume 
    subset: "A \<subseteq> B" and
    wf_B: "well_formed_welfare B (r1, r2, r3)"
  hence "\<forall> r \<in> r1 \<union> r2 \<union> r3. linear_order_on B r" 
    by simp
  moreover have "\<forall> r. (linear_order_on B r) \<longrightarrow> linear_order_on A (limit A r)"
    using subset limit_presv_lin_ord
    by blast
  ultimately have "\<forall> r \<in> r1 \<union> r2 \<union> r3. linear_order_on A (limit A r)"
    by blast
(* TODO this doesn't hold with the current limit_set definition... *)
  thus "well_formed_welfare A
        (limit_set_welfare A r1, limit_set_welfare A r2, limit_set_welfare A r3)"  sorry
qed
    

end

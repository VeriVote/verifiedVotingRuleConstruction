(*  File:       Evaluation_Function.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Evaluation Function\<close>

theory Evaluation_Function
  imports "Social_Choice_Types/Profile"
begin

text \<open>
  This is the evaluation function. From a set of currently eligible
  alternatives, the evaluation function computes a numerical value that is then
  to be used for further (s)election, e.g., by the elimination module.
\<close>

subsection \<open>Definition\<close>

type_synonym ('a, 'v) Evaluation_Function =
  "'v set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> enat"

subsection \<open>Property\<close>

text \<open>
  An Evaluation function is a Condorcet-rating iff the following holds:
  If a Condorcet Winner w exists, w and only w has the highest value.
\<close>

definition condorcet_rating :: "('a, 'v) Evaluation_Function \<Rightarrow> bool" where
  "condorcet_rating f \<equiv>
    \<forall> A V p w . condorcet_winner V A p w \<longrightarrow>
      (\<forall> l \<in> A . l \<noteq> w \<longrightarrow> f V l A p < f V w A p)"

text \<open>
  An Evaluation function is dependent only on the participating voters iff
  it is invariant under profile changes that only impact non-voters.
\<close>

fun voters_determine_evaluation :: "('a, 'v) Evaluation_Function \<Rightarrow> bool" where
  "voters_determine_evaluation f =
    (\<forall> A V p p'. (\<forall> v \<in> V. p v = p' v) \<longrightarrow> (\<forall> a \<in> A. f V a A p = f V a A p'))"

subsection \<open>Theorems\<close>

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet winner w exists, w has the maximum evaluation value.
\<close>

theorem cond_winner_imp_max_eval_val:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    rating: "condorcet_rating e" and
    f_prof: "finite_profile V A p" and
    winner: "condorcet_winner V A p a"
  shows "e V a A p = Max {e V b A p | b. b \<in> A}"
proof -
  let ?set = "{e V b A p | b. b \<in> A}" and
      ?eMax = "Max {e V b A p | b. b \<in> A}" and
      ?eW = "e V a A p"
  have "?eW \<in> ?set"
    using CollectI winner
    unfolding condorcet_winner.simps
    by (metis (mono_tags, lifting))
  moreover have "\<forall> e \<in> ?set. e \<le> ?eW"
  proof (safe)
    fix b :: "'a"
    assume "b \<in> A"
    thus "e V b A p \<le> e V a A p"
      using less_imp_le rating winner order_refl
      unfolding condorcet_rating_def
      by metis
  qed
  moreover have "finite ?set"
    using f_prof
    by simp
  moreover have "?set \<noteq> {}"
    using winner
    unfolding condorcet_winner.simps
    by fastforce
  ultimately show ?thesis
    using Max_eq_iff
    by (metis (no_types, lifting))
qed

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet Winner w exists, a non-Condorcet
  winner has a value lower than the maximum
  evaluation value.
\<close>

theorem non_cond_winner_not_max_eval:
  fixes
    e :: "('a, 'v) Evaluation_Function" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    rating: "condorcet_rating e" and
    f_prof: "finite_profile V A p" and
    winner: "condorcet_winner V A p a" and
    lin_A: "b \<in> A" and
    loser: "a \<noteq> b"
  shows "e V b A p < Max {e V c A p | c. c \<in> A}"
proof -
  have "e V b A p < e V a A p"
    using lin_A loser rating winner
    unfolding condorcet_rating_def
    by metis
  also have "\<dots> = Max {e V c A p | c. c \<in> A}"
    using cond_winner_imp_max_eval_val f_prof rating winner
    by fastforce
  finally show ?thesis
    by simp
qed

end
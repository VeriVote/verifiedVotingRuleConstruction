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

type_synonym 'a Evaluation_Function = "'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> nat"

subsection \<open>Property\<close>

text \<open>
  An Evaluation function is Condorcet-rating iff the following holds:
  If a Condorcet Winner w exists, w and only w has the highest value.
\<close>

definition condorcet_rating :: "'a Evaluation_Function \<Rightarrow> bool" where
  "condorcet_rating f \<equiv>
    \<forall> A p w . condorcet_winner A p w \<longrightarrow>
      (\<forall> l \<in> A . l \<noteq> w \<longrightarrow> f l A p < f w A p)"

subsection \<open>Theorems\<close>

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet winner w exists, w has the maximum evaluation value.
\<close>

theorem cond_winner_imp_max_eval_val:
  fixes
    e :: "'a Evaluation_Function" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes
    rating: "condorcet_rating e" and
    f_prof: "finite_profile A p" and
    winner: "condorcet_winner A p a"
  shows "e a A p = Max {e b A p | b. b \<in> A}"
proof -
  let ?set = "{e b A p | b. b \<in> A}" and
      ?eMax = "Max {e b A p | b. b \<in> A}" and
      ?eW = "e a A p"
  have "?eW \<in> ?set"
    using CollectI condorcet_winner.simps winner
    by (metis (mono_tags, lifting))
  moreover have "\<forall> e \<in> ?set. e \<le> ?eW"
  proof (safe)
    fix b :: "'a"
    assume "b \<in> A"
    moreover have "\<forall> n n'. (n::nat) = n' \<longrightarrow> n \<le> n'"
      by simp
    ultimately show "e b A p \<le> e a A p"
      using less_imp_le rating winner
      unfolding condorcet_rating_def
      by (metis (no_types))
  qed
  ultimately have "?eW \<in> ?set \<and> (\<forall> e \<in> ?set. e \<le> ?eW)"
    by blast
  moreover have "finite ?set"
    using f_prof
    by simp
  moreover have "?set \<noteq> {}"
    using condorcet_winner.simps winner
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
    e :: "'a Evaluation_Function" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    rating: "condorcet_rating e" and
    f_prof: "finite_profile A p" and
    winner: "condorcet_winner A p a" and
    lin_A: "b \<in> A" and
    loser: "a \<noteq> b"
  shows "e b A p < Max {e c A p | c. c \<in> A}"
proof -
  have "e b A p < e a A p"
    using lin_A loser rating winner
    unfolding condorcet_rating_def
    by metis
  also have "e a A p = Max {e c A p | c. c \<in> A}"
    using cond_winner_imp_max_eval_val f_prof rating winner
    by fastforce
  finally show ?thesis
    by simp
qed

end

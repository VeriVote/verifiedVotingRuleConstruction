(*  File:       Quotient_Type_Election.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Alternative Election Type\<close>

theory Quotient_Type_Election
  imports Profile
begin

lemma election_equality_equiv:
  "election_equality E E" and
  "election_equality E E' \<longrightarrow> election_equality E' E" and
  "election_equality E E' \<longrightarrow> election_equality E' F
      \<longrightarrow> election_equality E F"
proof (safe)
  have "election_equality
    (fst E, fst (snd E), snd (snd E)) (fst E, fst (snd E), snd (snd E))"
    unfolding election_equality.simps
    by safe
  thus "election_equality E E"
    by clarsimp
next
  assume "election_equality E E'"
  hence "election_equality
    (fst E, fst (snd E), snd (snd E)) (fst E', fst (snd E'), snd (snd E'))"
    by simp
  hence "election_equality
    (fst E', fst (snd E'), snd (snd E')) (fst E, fst (snd E), snd (snd E))"
    unfolding election_equality.simps
    by (metis (mono_tags, lifting))
  thus "election_equality E' E"
    by clarsimp
next
  assume
    "election_equality E E'" and
    "election_equality E' F"
  hence
    "election_equality
      (fst E, fst (snd E), snd (snd E)) (fst E', fst (snd E'), snd (snd E'))" and
    "election_equality
      (fst E', fst (snd E'), snd (snd E')) (fst F, fst (snd F), snd (snd F))"
    by (simp, simp)
  hence "election_equality
    (fst E, fst (snd E), snd (snd E)) (fst F, fst (snd F), snd (snd F))"
    unfolding election_equality.simps
    by (metis (no_types, lifting))
  thus "election_equality E F"
    by clarsimp
qed

quotient_type ('a, 'v) Election\<^sub>\<Q> =
  "'a set \<times> 'v set \<times> ('a, 'v) Profile" / "election_equality"
  unfolding equivp_reflp_symp_transp reflp_def symp_def transp_def
  using election_equality_equiv
  by simp

fun fst\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> 'a set" where
  "fst\<^sub>\<Q> E = fst (rep_Election\<^sub>\<Q> E)"

fun snd\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> 'v set \<times> ('a, 'v) Profile" where
  "snd\<^sub>\<Q> E = snd (rep_Election\<^sub>\<Q> E)"

abbreviation alternatives_\<E>\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> 'a set" where
  "alternatives_\<E>\<^sub>\<Q> E \<equiv> fst\<^sub>\<Q> E"

abbreviation voters_\<E>\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> 'v set" where
  "voters_\<E>\<^sub>\<Q> E \<equiv> fst (snd\<^sub>\<Q> E)"

abbreviation profile_\<E>\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> ('a, 'v) Profile" where
  "profile_\<E>\<^sub>\<Q> E \<equiv> snd (snd\<^sub>\<Q> E)"

end
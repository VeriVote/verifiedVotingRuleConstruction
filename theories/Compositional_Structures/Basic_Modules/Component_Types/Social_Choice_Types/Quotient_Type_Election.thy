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
  have "\<forall> E. E = (fst E, fst (snd E), snd (snd E))"
    by simp
  thus
    "election_equality E E" and
    "election_equality E E' \<Longrightarrow> election_equality E' E" and
    "election_equality E E' \<Longrightarrow> election_equality E' F
        \<Longrightarrow> election_equality E F"
    using election_equality.simps[of
            "fst E" "fst (snd E)" "snd (snd E)"]
          election_equality.simps[of
            "fst E'" "fst (snd E')" "snd (snd E')"
            "fst E" "fst (snd E)" "snd (snd E)"]
          election_equality.simps[of
            "fst E'" "fst (snd E')" "snd (snd E')"
            "fst F" "fst (snd F)" "snd (snd F)"]
    by (metis, metis, metis)
qed

quotient_type ('a, 'v) Election\<^sub>\<Q> =
  "'a set \<times> 'v set \<times> ('a, 'v) Profile" / "election_equality"
  unfolding equivp_reflp_symp_transp reflp_def symp_def transp_def
  using election_equality_equiv
  by simp

fun fst\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> 'a set" where
  "fst\<^sub>\<Q> E = Product_Type.fst (rep_Election\<^sub>\<Q> E)"

fun snd\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> 'v set \<times> ('a, 'v) Profile" where
  "snd\<^sub>\<Q> E = Product_Type.snd (rep_Election\<^sub>\<Q> E)"

abbreviation alternatives_\<E>\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> 'a set" where
  "alternatives_\<E>\<^sub>\<Q> E \<equiv> fst\<^sub>\<Q> E"

abbreviation voters_\<E>\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> 'v set" where
  "voters_\<E>\<^sub>\<Q> E \<equiv> Product_Type.fst (snd\<^sub>\<Q> E)"

abbreviation profile_\<E>\<^sub>\<Q> :: "('a, 'v) Election\<^sub>\<Q> \<Rightarrow> ('a, 'v) Profile" where
  "profile_\<E>\<^sub>\<Q> E \<equiv> Product_Type.snd (snd\<^sub>\<Q> E)"

end
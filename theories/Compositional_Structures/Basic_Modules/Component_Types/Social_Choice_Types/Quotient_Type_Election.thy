section \<open>Alternative Election Type\<close>

theory Quotient_Type_Election
  imports Profile
begin

lemma election_equality_equiv:
  "election_equality E E" and
  "election_equality E E' \<Longrightarrow> election_equality E' E" and
  "election_equality E E' \<Longrightarrow> election_equality E' F \<Longrightarrow> election_equality E F"
proof -
  have simp_tuple: "\<forall>E. E = (fst E, fst (snd E), snd (snd E))"
    by simp
  thus "election_equality E E"
    using election_equality.simps[of 
            "fst E" "fst (snd E)" "snd (snd E)" "fst E" "fst (snd E)" "snd (snd E)"]
    by auto
  show "election_equality E E' \<Longrightarrow> election_equality E' E"
    using simp_tuple 
          election_equality.simps[of
            "fst E" "fst (snd E)" "snd (snd E)" "fst E'" "fst (snd E')" "snd (snd E')"]
          election_equality.simps[of
            "fst E'" "fst (snd E')" "snd (snd E')" "fst E" "fst (snd E)" "snd (snd E)"]
    by metis
  show "election_equality E E' \<Longrightarrow> election_equality E' F \<Longrightarrow> election_equality E F"
    using simp_tuple 
          election_equality.simps[of
            "fst E" "fst (snd E)" "snd (snd E)" "fst E'" "fst (snd E')" "snd (snd E')"]
          election_equality.simps[of
            "fst E'" "fst (snd E')" "snd (snd E')" "fst F" "fst (snd F)" "snd (snd F)"]
          election_equality.simps[of
            "fst E" "fst (snd E)" "snd (snd E)" "fst F" "fst (snd F)" "snd (snd F)"]
    by metis
qed
    
quotient_type ('a, 'v) Election_Alt = 
  "'a set \<times> 'v set \<times> ('a, 'v) Profile" / election_equality
  unfolding equivp_reflp_symp_transp reflp_def symp_def transp_def
  using election_equality_equiv
  by simp

fun fst_alt :: "('a, 'v) Election_Alt \<Rightarrow> 'a set" where
  "fst_alt E = Product_Type.fst (rep_Election_Alt E)"

fun snd_alt :: "('a, 'v) Election_Alt \<Rightarrow> 'v set \<times> ('a, 'v) Profile" where
  "snd_alt E = Product_Type.snd (rep_Election_Alt E)"

abbreviation alts_\<E>_alt :: "('a, 'v) Election_Alt \<Rightarrow> 'a set" where 
  "alts_\<E>_alt E \<equiv> fst_alt E"

abbreviation votrs_\<E>_alt :: "('a, 'v) Election_Alt \<Rightarrow> 'v set" where 
  "votrs_\<E>_alt E \<equiv> Product_Type.fst (snd_alt E)"

abbreviation prof_\<E>_alt :: "('a, 'v) Election_Alt \<Rightarrow> ('a, 'v) Profile" where 
  "prof_\<E>_alt E \<equiv> Product_Type.snd (snd_alt E)"

end
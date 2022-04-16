(*  File:       List_Permutation.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Preliminaries\<close>

section \<open>List Permutation\<close>

theory List_Permutation
  imports Main
          "HOL-Library.Permutations"
begin

text \<open>
  TODO.
\<close>

definition is_perm :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "is_perm pi \<equiv> \<forall>n. (pi n) permutes {..<n}"

fun build_perm :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "build_perm pi xs = permute_list (pi (length xs)) xs"

fun inv_perm :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "inv_perm pi n = inv (pi n)"

end
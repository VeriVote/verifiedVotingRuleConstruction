(*  File:       Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance Rationalization\<close>

theory Distance_Rationalization
  imports "HOL-Combinatorics.Multiset_Permutations"
          "Social_Choice_Types/Refined_Types/Preference_List"
          "Consensus_Class"
          "Distance"
begin

text \<open>
  A distance rationalization of a voting rule is its interpretation as a
  procedure that elects an uncontroversial winner if there is one, and
  otherwise elects the alternatives that are as close to becoming an
  uncontroversial winner as possible. Within general distance rationalization,
  a voting rule is characterized by a distance on profiles and a consensus
  class.
\<close>

subsection \<open>Definitions\<close>

fun \<K>\<^sub>\<E> :: "'a Consensus_Class \<Rightarrow> 'a \<Rightarrow> 'a Election set" where
  "\<K>\<^sub>\<E> K a =
    {(A, p) | A p. (consensus_\<K> K) (A, p) \<and> finite_profile A p \<and> elect (rule_\<K> K) A p = {a}}"

fun score :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a Election \<Rightarrow> 'a \<Rightarrow> ereal" where
  "score d K E a = Inf (d E ` (\<K>\<^sub>\<E> K a))"

fun arg_min_set :: "('b \<Rightarrow> 'a :: ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "arg_min_set f A = Collect (is_arg_min f (\<lambda> a. a \<in> A))"

(* fun arg_min_set' :: "('b \<Rightarrow> 'a::ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
   "arg_min_set_' f A = Set.filter (is_arg_min f (\<lambda> a. a \<in> A)) A" *)

fun \<R>\<^sub>\<W> :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "\<R>\<^sub>\<W> d K A p = arg_min_set (score d K (A, p)) A"

fun distance_\<R> :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a Electoral_Module" where
  "distance_\<R> d K A p = (\<R>\<^sub>\<W> d K A p, A - \<R>\<^sub>\<W> d K A p, {})"

subsection \<open>Standard Definitions\<close>

definition standard :: "'a Election Distance \<Rightarrow> bool" where
 "standard d \<equiv> \<forall> A A' p p'. (length p \<noteq> length p' \<or> A \<noteq> A') \<longrightarrow> d (A, p) (A', p') = \<infinity>"

(*
  We want "profiles n A = {}" for infinite A.
  We have "permutations_of_set A = {} \<longleftrightarrow> \<not>finite A"
    (Multiset_Permutations.permutations_of_set_empty_iff).
    "listset (replicate 0 (list_to_rel ` {})" is "{[]}", not "{}".
  This is why we make the case where "permutations_of_set A = {}" explicit.
  Open question: Would "finite A" instead of "permutations_of_set A = {}"
                 also work for code generation?
*)
fun profiles :: "nat \<Rightarrow> 'a set \<Rightarrow> ('a Profile) set" where
  "profiles n A = (if permutations_of_set A = {} then {}
                   else listset (replicate n (pl_\<alpha> ` permutations_of_set A)))"

fun \<K>\<^sub>\<E>_std :: "'a Consensus_Class \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a Election set" where
  "\<K>\<^sub>\<E>_std K a A n =
    (\<lambda> p. (A, p)) ` (Set.filter (\<lambda> p. (consensus_\<K> K) (A, p) \<and> elect (rule_\<K> K) A p = {a})
                                (profiles n A))"

fun score_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a Election \<Rightarrow> 'a \<Rightarrow> ereal" where
  "score_std d K E a =
    (if \<K>\<^sub>\<E>_std K a (alts_\<E> E) (length (prof_\<E> E)) = {}
      then \<infinity> else Min (d E ` (\<K>\<^sub>\<E>_std K a (alts_\<E> E) (length (prof_\<E> E)))))"

fun \<R>\<^sub>\<W>_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a set
                          \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "\<R>\<^sub>\<W>_std d K A p = arg_min_set (score_std d K (A, p)) A"

fun distance_\<R>_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Class \<Rightarrow> 'a Electoral_Module" where
  "distance_\<R>_std d K A p = (\<R>\<^sub>\<W>_std d K A p, A - \<R>\<^sub>\<W>_std d K A p, {})"

subsection \<open>Auxiliary Lemmas\<close>

lemma list_cons_presv_finiteness:
  fixes
    A :: "'a set" and
    B :: "'a list set"
  assumes
    fin_A: "finite A" and
    fin_B: "finite B"
  shows "finite {a#b | a b. a \<in> A \<and> b \<in> B}"
proof -
  let ?P = "\<lambda> A. finite {a#b | a b. a \<in> A \<and> b \<in> B}"
  have "\<And> a A'. finite A' \<Longrightarrow> a \<notin> A' \<Longrightarrow> ?P A' \<Longrightarrow> ?P (insert a A')"
  proof -
    fix
      a :: "'a" and
      A' :: "'a set"
    assume
      fin: "finite A'" and
      not_in: "a \<notin> A'" and
      fin_set: "finite {a#b | a b. a \<in> A' \<and> b \<in> B}"
    have "{a'#b | a' b. a' \<in> insert a A' \<and> b \<in> B}
            = {a#b | a b. a \<in> A' \<and> b \<in> B} \<union> {a#b | b. b \<in> B}"
      by auto
    moreover have "finite {a#b | b. b \<in> B}"
      using fin_B
      by simp
    ultimately have "finite {a'#b | a' b. a' \<in> insert a A' \<and> b \<in> B}"
      using fin_set
      by simp
    thus "?P (insert a A')"
      by simp
  qed
  moreover have "?P {}"
    by simp
  ultimately show "?P A"
    using finite_induct[of A ?P] fin_A
    by simp
qed

lemma listset_finiteness:
  fixes l :: "'a set list"
  assumes "\<forall> i::nat. i < length l \<longrightarrow> finite (l!i)"
  shows "finite (listset l)"
  using assms
proof (induct l, simp)
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list"
  assume
    elems_fin_then_set_fin: "\<forall> i::nat < length l. finite (l!i) \<Longrightarrow> finite (listset l)" and
    fin_all_elems: "\<forall> i::nat < length (a#l). finite ((a#l)!i)"
  hence "finite a"
    by auto
  moreover from fin_all_elems
  have "\<forall> i < length l. finite (l!i)"
    by auto
  with elems_fin_then_set_fin
  have "finite (listset l)"
    by simp
  ultimately have "finite {a'#l' | a' l'. a' \<in> a \<and> l' \<in> (listset l)}"
    using list_cons_presv_finiteness
    by auto
  thus "finite (listset (a#l))"
    by (simp add: set_Cons_def)
qed

lemma ls_entries_empty_imp_ls_set_empty:
  fixes l :: "'a set list"
  assumes
    "0 < length l" and
    "\<forall> i ::nat. i < length l \<longrightarrow> l!i = {}"
  shows "listset l = {}"
  using assms
proof (induct l, simp)
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list"
  assume all_elems_empty: "\<forall> i::nat < length (a#l). (a#l)!i = {}"
  hence "a = {}"
    by auto
  moreover from all_elems_empty
  have "\<forall> i < length l. l!i = {}"
    by auto
  ultimately have "{a'#l' | a' l'. a' \<in> a \<and> l' \<in> (listset l)} = {}"
    by simp
  thus "listset (a#l) = {}"
    by (simp add: set_Cons_def)
qed

lemma all_ls_elems_same_len:
  fixes l :: "'a set list"
  shows "\<forall> m::('a list). m \<in> listset l \<longrightarrow> length m = length l"
proof (induct l, simp)
  case (Cons a l)
  assume "\<forall> l'::('a list). l' \<in> listset l \<longrightarrow> length l' = length l"
  hence "\<forall> m \<in> {x#l' | x l'. x \<in> a \<and> l' \<in> listset l}. length m = 1 + length l"
    by auto
  hence "\<forall> m \<in> {x#l' | x l'. x \<in> a \<and> l' \<in> listset l}. length m = length (a#l)"
    by simp
  thus ?case
    by (simp add: set_Cons_def)
qed

lemma all_ls_elems_in_ls_set:
  fixes l :: "'a set list"
  shows "\<forall> l'::('a list). \<forall> i::nat. l' \<in> listset l \<and> i < length l' \<longrightarrow> l'!i \<in> l!i"
proof (induct l, simp, safe)
  case (Cons a l)
  fix
    a :: "'a set" and
    l :: "'a set list" and
    l' :: "'a list" and
    i :: nat
  assume elems_in_set_then_elems_pos:
    "\<forall> l'::('a list). \<forall> i::nat. l' \<in> listset l \<and> i < length l' \<longrightarrow> l'!i \<in> l!i" and
    l_prime_in_set_a_l: "l' \<in> listset (a#l)" and
    i_lt_len_l_prime: "i < length l'"
  have "l' \<in> set_Cons a (listset l)"
    using l_prime_in_set_a_l
    by simp
  hence "l' \<in> {ys. \<exists> b m. ys = b#m \<and> b \<in> a \<and> m \<in> (listset l)}"
    unfolding set_Cons_def
    by simp
  hence "\<exists> b m. l' = b#m \<and> b \<in> a \<and> m \<in> (listset l)"
    by simp
  thus "l'!i \<in> (a#l)!i"
    using elems_in_set_then_elems_pos i_lt_len_l_prime nth_Cons_Suc
          Suc_less_eq gr0_conv_Suc length_Cons nth_non_equal_first_eq
    by metis
qed

subsection \<open>Soundness\<close>

lemma \<R>_sound:
  fixes
    K :: "'a Consensus_Class" and
    d :: "'a Election Distance"
  shows "electoral_module (distance_\<R> d K)"
  unfolding electoral_module_def
  by (auto simp add: is_arg_min_def)

subsection \<open>Inference Rules\<close>

lemma is_arg_min_equal:
  fixes
    f :: "'a \<Rightarrow> 'b::ord" and
    g :: "'a \<Rightarrow> 'b" and
    S :: "'a set" and
    x :: 'a
  assumes "\<forall> x \<in> S. f x = g x"
  shows "is_arg_min f (\<lambda> s. s \<in> S) x = is_arg_min g (\<lambda> s. s \<in> S) x"
proof (unfold is_arg_min_def, cases "x \<in> S")
  case False
  thus "(x \<in> S \<and> (\<nexists> y. y \<in> S \<and> f y < f x)) = (x \<in> S \<and> (\<nexists> y. y \<in> S \<and> g y < g x))"
    by simp
next
  case x_in_S: True
  thus "(x \<in> S \<and> (\<nexists> y. y \<in> S \<and> f y < f x)) = (x \<in> S \<and> (\<nexists> y. y \<in> S \<and> g y < g x))"
  proof (cases "\<exists> y. (\<lambda> s. s \<in> S) y \<and> f y < f x")
    case y: True
    then obtain y :: 'a where
      "(\<lambda> s. s \<in> S) y \<and> f y < f x"
      by metis
    hence "(\<lambda> s. s \<in> S) y \<and> g y < g x"
      using x_in_S assms
      by metis
    thus ?thesis
      using y
      by metis
  next
    case not_y: False
    have "\<not> (\<exists> y. (\<lambda> s. s \<in> S) y \<and> g y < g x)"
    proof (safe)
      fix  y :: "'a"
      assume
        y_in_S: "y \<in> S" and
        g_y_lt_g_x: "g y < g x"
      have f_eq_g_for_elems_in_S: "\<forall> a. a \<in> S \<longrightarrow> f a = g a"
        using assms
        by simp
      hence "g x = f x"
        using x_in_S
        by presburger
      thus "False"
        using f_eq_g_for_elems_in_S g_y_lt_g_x not_y y_in_S
        by (metis (no_types))
    qed
    with x_in_S not_y
    show ?thesis
      by simp
  qed
qed

lemma standard_distance_imp_equal_score:
  fixes
    d :: "'a Election Distance" and
    K :: "'a Consensus_Class" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes std: "standard d"
  shows "score d K (A, p) a = score_std d K (A, p) a"
proof -
  have profile_set:
    "profiles (length p) A = {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
  proof (cases "\<not> finite A", simp)
    case fin_A: False
    show ?thesis
    proof (cases "0 < length p")
      case True
      show ?thesis
      proof (safe)
        fix x :: "'a Profile"
        assume xprof: "x \<in> profiles (length p) A"
        from fin_A
        show "finite A"
          by simp
        from xprof
        have "profiles (length p) A \<noteq> {}"
          by blast
        hence ne: "pl_\<alpha> ` permutations_of_set A \<noteq> {}"
          by auto
        have "length (replicate (length p) (pl_\<alpha> ` permutations_of_set A)) = length p"
          by simp
        hence "\<forall> xs \<in> listset (replicate (length p) (pl_\<alpha> ` permutations_of_set A)).
                length xs = length p"
          using all_ls_elems_same_len
          by metis
        thus len_eq: "length x = length p"
          using xprof ne
          by simp
        show "profile A x"
        proof (unfold profile_def, safe)
          fix i :: nat
          assume lt_len_x: "i < length x"
          with len_eq
          have i_lt_len_p: "i < length p"
            by simp
          hence "x!i \<in> replicate (length p) (pl_\<alpha> ` permutations_of_set A)!i"
            using xprof ne all_ls_elems_in_ls_set lt_len_x profiles.simps image_is_empty
            by metis
          hence "x!i \<in> pl_\<alpha> ` permutations_of_set A"
            using i_lt_len_p
            by simp
          hence relation_of:
            "x!i \<in> {relation_of (\<lambda> y z. rank_l l z \<le> rank_l l y) (set l) |
                l. l \<in> permutations_of_set A}"
          proof (safe)
            fix l :: "'a Preference_List"
            assume
              i_th_rel: "x!i = pl_\<alpha> l" and
              perm_l: "l \<in> permutations_of_set A"
            have rel_of_set_l_eq_l_list: "relation_of (\<lambda> y z. y \<lesssim>\<^sub>l z) (set l) = pl_\<alpha> l"
              using rel_of_pref_pred_for_set_eq_list_to_rel
              by blast
            have "relation_of (\<lambda> y z. rank_l l z \<le> rank_l l y) (set l) = pl_\<alpha> l"
            proof (unfold relation_of_def rank_l.simps, safe)
              fix
                a :: "'a" and
                b :: "'a"
              assume
                idx_b_lte_idx_a: "(if b \<in> set l then index l b + 1 else 0) \<le>
                                    (if a \<in> set l then index l a + 1 else 0)" and
                a_in_l: "a \<in> set l" and
                b_in_l : "b \<in> set l"
              have l_set_eq_l_list: "{(a, b). (a, b) \<in> set l \<times> set l \<and> a \<lesssim>\<^sub>l b} = pl_\<alpha> l"
                using rel_of_set_l_eq_l_list
                by (simp add: relation_of_def)
              have "a \<in> set l"
                unfolding member_def
                using a_in_l
                by simp
              thus "(a, b) \<in> pl_\<alpha> l"
                using l_set_eq_l_list idx_b_lte_idx_a b_in_l member_def
                by fastforce
            next
              fix
                a :: "'a" and
                b :: "'a"
              assume "(a, b) \<in> pl_\<alpha> l"
              thus "a \<in> set l"
                using Collect_mem_eq case_prod_eta in_rel_Collect_case_prod_eq
                      is_less_preferred_than_l.elims(2)
                unfolding pl_\<alpha>_def
                by (metis (no_types))
            next
              fix
                a :: "'a" and
                b :: "'a"
              assume a_b_in_rel_of_l: "(a, b) \<in> pl_\<alpha> l"
              have l_set_eq_l_list: "{(a, b). (a, b) \<in> set l \<times> set l \<and> a \<lesssim>\<^sub>l b} = pl_\<alpha> l"
                using rel_of_set_l_eq_l_list
                by (simp add: relation_of_def)
              thus "b \<in> set l"
                using a_b_in_rel_of_l is_less_preferred_than_l.elims(2)
                by blast
            next
              fix
                a :: "'a" and
                b :: "'a"
                assume a_b_in_rel_of_l: "(a, b) \<in> pl_\<alpha> l"
                have l_set_eq_l_list: "{(a, b). (a, b) \<in> set l \<times> set l \<and> a \<lesssim>\<^sub>l b} = pl_\<alpha> l"
                  using rel_of_set_l_eq_l_list
                  by (simp add: relation_of_def)
                hence "a \<lesssim>\<^sub>l b"
                  using a_b_in_rel_of_l case_prodE mem_Collect_eq prod.inject
                  by blast
                thus "(if b \<in> set l then index l b + 1 else 0) \<le>
                        (if a \<in> set l then index l a + 1 else 0)"
                  by force
              qed
            show "\<exists> l'. x!i = relation_of (\<lambda> y z. rank_l l' z \<le> rank_l l' y) (set l') \<and>
                  l' \<in> permutations_of_set A"
            proof
              have "relation_of (\<lambda> y z. rank_l l z \<le> rank_l l y) (set l) = pl_\<alpha> l"
              proof (unfold relation_of_def rank_l.simps, safe)
                fix
                  a :: "'a" and
                  b :: "'a"
                assume
                  idx_b_lte_idx_a: "(if b \<in> set l then index l b + 1 else 0) \<le>
                          (if a \<in> set l then index l a + 1 else 0)" and
                  a_in_l: "a \<in> set l" and
                  b_in_l : "b \<in> set l"
                have l_set_eq_l_list: "{(a, b). (a, b) \<in> set l \<times> set l \<and> a \<lesssim>\<^sub>l b} = pl_\<alpha> l"
                  using rel_of_set_l_eq_l_list
                  by (simp add: relation_of_def)
                have  "a \<in> set l"
                  unfolding member_def
                  using a_in_l
                  by simp
                thus "(a, b) \<in> pl_\<alpha> l"
                  using l_set_eq_l_list idx_b_lte_idx_a b_in_l member_def
                  by fastforce
              next
                fix
                  a :: "'a" and
                  b :: "'a"
                assume "(a, b) \<in> pl_\<alpha> l"
                thus "a \<in> set l"
                  using Collect_mem_eq case_prod_eta in_rel_Collect_case_prod_eq
                        is_less_preferred_than_l.elims(2)
                  unfolding pl_\<alpha>_def
                  by (metis (no_types))
              next
                fix
                  a :: "'a" and
                  b :: "'a"
                assume a_b_in_rel_of_l: "(a, b) \<in> pl_\<alpha> l"
                have l_set_eq_l_list: "{(a, b). (a, b) \<in> set l \<times> set l \<and> a \<lesssim>\<^sub>l b} = pl_\<alpha> l"
                  using rel_of_set_l_eq_l_list
                  by (simp add: relation_of_def)
                thus "b \<in> set l"
                  using a_b_in_rel_of_l is_less_preferred_than_l.elims(2)
                  by blast
              next
                fix
                  a :: "'a" and
                  b :: "'a"
                assume a_b_in_rel_of_l: "(a, b) \<in> pl_\<alpha> l"
                have l_set_eq_l_list: "{(a, b). (a, b) \<in> set l \<times> set l \<and> a \<lesssim>\<^sub>l b} = pl_\<alpha> l"
                  using rel_of_set_l_eq_l_list
                  by (simp add: relation_of_def)
                hence "a \<lesssim>\<^sub>l b"
                  using a_b_in_rel_of_l case_prodE mem_Collect_eq prod.inject
                  by blast
                thus "(if b \<in> set l then index l b + 1 else 0) \<le>
                        (if a \<in> set l then index l a + 1 else 0)"
                  by force
              qed
              thus "x!i = relation_of (\<lambda> y z. rank_l l z \<le> rank_l l y) (set l) \<and>
                      l \<in> permutations_of_set A"
                using perm_l i_th_rel
                by presburger
            qed
          qed
          let ?P = "\<lambda> xs y z. rank_l xs z \<le> rank_l xs y"
          have "\<And> xs a. a \<in> (set xs) \<Longrightarrow> ?P xs a a"
            by simp
          moreover have
            "\<And> xs a b c. \<lbrakk> a \<in> (set xs); b \<in> (set xs); c \<in> (set xs) \<rbrakk>
              \<Longrightarrow> ?P xs a b \<Longrightarrow> ?P xs b c \<Longrightarrow> ?P xs a c"
            by simp
          moreover have
            "\<And> xs a b. \<lbrakk> a \<in> (set xs); b \<in> (set xs) \<rbrakk> \<Longrightarrow> ?P xs a b \<Longrightarrow> ?P xs b a \<Longrightarrow> a = b"
            using pos_in_list_yields_pos le_antisym
            by metis
          ultimately have "\<And> xs. partial_order_on (set xs) (relation_of (?P xs) (set xs))"
            using partial_order_on_relation_ofI
            by (smt (verit, ccfv_SIG))
          moreover have set: "\<And> xs. xs \<in> permutations_of_set A \<Longrightarrow> set xs = A"
            by (simp add: permutations_of_setD)
          ultimately have "partial_order_on A (x!i)"
            using relation_of
            by fastforce
          moreover have "\<And> xs. total_on (set xs) (relation_of (?P xs) (set xs))"
            using relation_of
            unfolding total_on_def relation_of_def
            by auto
          hence "total_on A (x!i)"
            using relation_of set
            by fastforce
          ultimately show "linear_order_on A (x!i)"
            unfolding linear_order_on_def
            by simp
        qed
      next
        fix x :: "'a Profile"
        assume
          len_eq: "length x = length p" and
          fin_A: "finite A" and
          prof_A_x: "profile A x"
        show "x \<in> profiles (length p) A"
          using fin_A
        proof (unfold profiles.simps, clarsimp)
          assume fin_A: "finite A"
          (* Intermediate step: Show that all linear orders over A 
             are in "pl_\<alpha> ' (permutations_of_set A)".
             Then, use the argument that "listset (replicate l S))" for a set S is the set of lists
             of length l where each item is in S. *)
          have "x \<in> listset
                (replicate (length p)
                  ((\<lambda> x. {(a, b). a \<in> A \<and> b \<in> A \<and> index x b \<le> index x a}) `
                    {l. set l = A \<and> well_formed_l l}))"
            sorry
          thus "x \<in> listset (replicate (length p) (pl_\<alpha> ` permutations_of_set A))"
            unfolding pl_\<alpha>_def permutations_of_set_def is_less_preferred_than_l.simps
            by clarsimp
        qed
      qed
    next
      case not_zero_lt_len_p: False
      have "finite_profile A []"
        using fin_A
        unfolding profile_def
        by simp
      moreover have "length [] = length p"
        using not_zero_lt_len_p
        by simp
      moreover have "{x. finite_profile A x \<and> length x = length p} \<subseteq> {[]}"
        using not_zero_lt_len_p
        by auto
      moreover have "profiles (length p) A = {[]}"
        using fin_A not_zero_lt_len_p
        by simp
      ultimately show ?thesis
        by (simp add: subset_antisym)
    qed
  qed
  hence "\<K>\<^sub>\<E>_std K a A (length p) =
           \<K>\<^sub>\<E> K a \<inter> Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
    by force
  moreover have "Inf (d (A, p) ` (\<K>\<^sub>\<E> K a)) =
                   Inf (d (A, p) ` (\<K>\<^sub>\<E> K a \<inter>
                    Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}))"
    using std
    (* Since d in standard, d (A,p) (A,p') is \<infinity> for all p' not in the set. *)
    sorry
  ultimately have inf_eq_inf_for_std_cons:
    "Inf (d (A, p) ` (\<K>\<^sub>\<E> K a)) =
      Inf (d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p)))"
    by simp
  also have inf_eq_min_for_std_cons:
    "\<dots> = Min (d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p)))"
  proof (cases "\<K>\<^sub>\<E>_std K a A (length p) = {}")
    case True
    thus ?thesis
    (* Find out what "Min {}" does. If it is not \<infinity>, redefine score_std:
    "score_std d K E a = 
      (if consensus_elections_std K a (alts_\<E> E) (length (prof_\<E> E)) = {}
      then \<infinity>
      else Min (d E ` (consensus_elections_std K a (alts_\<E> E) (length (prof_\<E> E)))))"
    This is consistent with the convention that the distance from empty consensus sets is \<infinity>
    mentioned by Hadjibeyli and Wilson after remark 3.5 *)
      sorry
  next
    case False
    hence "d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p)) \<noteq> {}"
      by simp
    moreover have "finite (\<K>\<^sub>\<E>_std K a A (length p))"
    proof -
      have "\<forall> l A. finite A \<longrightarrow> finite (permutations_of_set A)"
        by simp
      hence "finite (pl_\<alpha> ` permutations_of_set A)"
        by simp
      moreover have fin_A_imp_fin_all: "\<forall> n A. finite A \<longrightarrow> finite (profiles n A)"
        using listset_finiteness
        by force
      hence "finite (profiles (length p) A)"
      proof (cases "finite A")
        case True
        thus ?thesis
          using fin_A_imp_fin_all
          by metis
      next
        case False
        hence "permutations_of_set A = {}"
          using permutations_of_set_infinite
          by simp
        hence list_perm_A_empty: "pl_\<alpha> ` permutations_of_set A = {}"
          by simp
        let ?xs = "replicate (length p) (pl_\<alpha> ` permutations_of_set A)"
        from list_perm_A_empty
        have "\<forall> i < length ?xs. ?xs!i = {}"
          by simp
        hence "finite (listset (replicate (length p) (pl_\<alpha> ` permutations_of_set A)))"
          by (simp add: listset_finiteness)
        thus ?thesis
          by simp
      qed
      hence "finite (Set.filter (\<lambda> p. (consensus_\<K> K) (A, p) \<and> elect (rule_\<K> K) A p = {a})
                (profiles (length p) A))"
        using finite_filter
        by blast
      thus ?thesis
        by simp
    qed
    hence "finite (d (A, p) ` (\<K>\<^sub>\<E>_std K a A (length p)))"
      by simp
    ultimately show ?thesis
      by (simp add: Lattices_Big.complete_linorder_class.Min_Inf)
  qed
  finally show "score d K (A, p) a = score_std d K (A, p) a"
    using inf_eq_inf_for_std_cons inf_eq_min_for_std_cons top_ereal_def
    by simp
qed

lemma anonymous_distance_and_consensus_imp_rule_anonymity:
  fixes
    d :: "'a Election Distance" and
    K :: "'a Consensus_Class"
  assumes
    d_anon: "distance_anonymity d" and
    K_anon: "consensus_rule_anonymity K"
  shows "anonymity (distance_\<R> d K)"
proof (unfold anonymity_def, safe)
  show "electoral_module (distance_\<R> d K)"
    by (simp add: \<R>_sound)
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume
    fin: "finite A" and
    profile_p: "profile A p" and
    profile_q: "profile A q" and
    p_q_perm: "p <~~> q"
  from p_q_perm
  obtain pi where
    pi_perm: "pi permutes {..< length p}" and
    pq: "permute_list pi p = q"
    using mset_eq_permutation
    by metis
  let ?listpi = "permute_list pi"
  let ?pi' = "\<lambda> n. (if n = length p then pi else id)"
  have perm: "\<forall> n. (?pi' n) permutes {..< n}"
    using pi_perm
    by simp
  let ?listpi' = "\<lambda> xs. permute_list (?pi' (length xs)) xs"
  let ?m = "distance_\<R> d K"
  let ?P = "\<lambda> a A' p'. (A', p') \<in> \<K>\<^sub>\<E> K a"
  have "\<forall> a. {(A', p') | A' p'. ?P a A' p'} = {(A', ?listpi' p') | A' p'. ?P a A' p'}"
  proof (clarify)
    fix a :: "'a"
    have apply_perm: "\<And> S x y. x <~~> y \<Longrightarrow> ?P a S x \<Longrightarrow> ?P a S y"
    proof -
      fix
        S :: "'a set" and
        x :: "'a Profile" and
        y :: "'a Profile"
      assume
        perm: "x <~~> y"  and
        fav_cons: "(S, x) \<in> \<K>\<^sub>\<E> K a"
      hence fin_S_x: "finite_profile S x"
        by simp
      from perm
      have fin_S_y: "finite_profile S y"
        unfolding profile_def
        using fin_S_x nth_mem perm_set_eq profile_set
        by metis
      moreover from perm fav_cons
      have fst_x_and_elect_snd_x_a: "(consensus_\<K> K) (S, x) \<and> elect (rule_\<K> K) S x = {a}"
        by simp
      with K_anon perm fin_S_x fin_S_y
      have "(consensus_\<K> K) (S, y) \<and> elect (rule_\<K> K) S y = {a}"
        unfolding consensus_rule_anonymity_def anonymity_def
        using fin_S_x fst_x_and_elect_snd_x_a calculation perm
        by (metis (no_types))
      ultimately show "(S, y) \<in> \<K>\<^sub>\<E> K a"
        by simp
    qed
    show "{(A', p') | A' p'. ?P a A' p'} = {(A', ?listpi' p') | A' p'. ?P a A' p'}" (is "?X = ?Y")
    proof
      show "?X \<subseteq> ?Y"
      proof
        fix E :: "'a Election"
        let
          ?A = "alts_\<E> E" and
          ?p = "prof_\<E> E"
        assume consensus_election_E: "E \<in> {(A', p') | A' p'. ?P a A' p'}"
        hence consens_elect_E_inst: "?P a ?A ?p"
          by simp
        show "E \<in> {(A', ?listpi' p') | A' p'. ?P a A' p'}"
        proof (cases "length ?p = length p")
          case True
          hence "permute_list (inv pi) ?p <~~> ?p"
            using pi_perm
            by (simp add: permutes_inv)
          with apply_perm consens_elect_E_inst
          have "?P a ?A (permute_list (inv pi) ?p)"
            by presburger
          moreover have "length (permute_list (inv pi) ?p) = length p"
            using True
            by simp
          ultimately have perm_elem:
            "(?A, ?listpi (permute_list (inv pi) ?p)) \<in>
                {(A', ?listpi p') | A' p'. length p' = length p \<and> ?P a A' p'}"
            by auto
          have "permute_list pi (permute_list (inv pi) ?p) = ?p"
            using permute_list_compose True pi_perm permute_list_id permutes_inv_o(2) pi_perm(1)
            by metis
          thus ?thesis
            using perm_elem
            by auto
        next
          case False
          with consensus_election_E
          show ?thesis
            by fastforce (* because ?listpi ?p = ?p *)
        qed
      qed
    next
      show "?Y \<subseteq> ?X"
      proof
        fix E :: "'a Election"
        let
          ?A = "alts_\<E> E" and
          ?r = "prof_\<E> E"
        assume consensus_elect_permut_E: "E \<in> {(A', ?listpi' p') | A' p'. ?P a A' p'}"
        hence "\<exists> p'. ?r = ?listpi' p' \<and> ?P a ?A p'"
          by auto
        then obtain p' where
          rp': "?r = ?listpi' p'" and
          consens_elect_inst: "?P a ?A p'"
          by metis
        show "E \<in> {(A', p') | A' p'. ?P a A' p'}"
        proof (cases "length p' = length p")
          case True
          have "?r <~~> p'"
            using pi_perm rp'
            by simp
          with consens_elect_inst apply_perm rp'
          have "?P a ?A ?r"
            by presburger
          moreover have "length ?r = length p"
            using rp' True
            by simp
          ultimately show "E \<in> {(A', p') | A' p'. ?P a A' p'}"
            by simp
        next
          case False
          thus ?thesis
            using consensus_elect_permut_E rp'
            by fastforce (* because ?listpi ?p = ?p *)
        qed
      qed
    qed
  qed
  hence "\<forall> a \<in> A. d (A, q) ` {(A', p') | A' p'. ?P a A' p'}
             = d (A, q) ` {(A', ?listpi' p') | A' p'. ?P a A' p'}"
    by (metis (no_types, lifting))
  hence "\<forall> a \<in> A. {d (A, q) (A', p') | A' p'. ?P a A' p'}
             = {d (A, q) (A', ?listpi' p') | A' p'. ?P a A' p'}"
    by blast
  moreover from d_anon
  have "\<forall> a \<in> A. {d (A, p) (A', p') | A' p'. ?P a A' p'} =
          {d (A, ?listpi' p) (A', ?listpi' p') | A' p'. ?P a A' p'}"
  proof (clarify)
    fix a :: "'a"
    have "?listpi' = (\<lambda> p. permute_list (?pi' (length p)) p)"
      by simp
    from d_anon
    have anon:
      "\<And> A' p' A p pi. (\<forall> n. (pi n) permutes {..< n})
          \<longrightarrow> d (A, p) (A', p')
                = d (A, permute_list (pi (length p)) p) (A', permute_list (pi (length p')) p')"
      unfolding distance_anonymity_def
      by blast
    show "{d (A, p) (A', p') | A' p'. ?P a A' p'} =
            {d (A, ?listpi' p) (A', ?listpi' p') | A' p'. ?P a A' p'}"
      using perm anon[of ?pi' A p]
      unfolding distance_anonymity_def
      by simp
  qed
  hence "\<forall> a \<in> A. {d (A, p) (A', p') | A' p'. ?P a A' p'} =
          {d (A, q) (A', ?listpi' p') | A' p'. ?P a A' p'}"
    using pq
    by simp
  ultimately have
    "\<forall> a \<in> A. {d (A, q) (A', p') | A' p'. (A', p') \<in> \<K>\<^sub>\<E> K a} =
                {d (A, p) (A', p') | A' p'. (A', p') \<in> \<K>\<^sub>\<E> K a}"
    by simp
  hence "\<forall> a \<in> A. d (A, q) ` \<K>\<^sub>\<E> K a = d (A, p) ` \<K>\<^sub>\<E> K a"
    by fast
  hence "\<forall> a \<in> A. score d K (A, p) a = score d K (A, q) a"
    by simp
  thus "distance_\<R> d K A p = distance_\<R> d K A q"
    using is_arg_min_equal[of A "score d K (A, p)" "score d K (A, q)"]
    by auto
qed

end

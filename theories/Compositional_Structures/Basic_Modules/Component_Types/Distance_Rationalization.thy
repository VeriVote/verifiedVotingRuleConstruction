(*  File:       Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance Rationalization\<close>

theory Distance_Rationalization
  imports "Distance"
          "Consensus_Rule"
          "HOL-Combinatorics.Multiset_Permutations"
          "Votewise_Distance"
begin

text \<open>
  A distance rationalizing of a voting rule is its interpretation as a
  procedure that elects an uncontroversial winner if there is one, and
  otherwise elects the alternatives that are as close to becoming an
  uncontroversial winner as possible. Within general distance rationalization,
  a voting rule is characterized by a distance on profiles and a consensus
  class.
\<close>

subsection \<open>Definition\<close>

fun favoring_consensus_elections :: "'a Consensus_Rule \<Rightarrow> 'a  \<Rightarrow> 'a Election set" where
  "favoring_consensus_elections K a =
    {(A, p) | A p. (fst K) (A, p) \<and> finite_profile A p \<and> elect_r ((snd K) A p) = {a}}"

fun score :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Election \<Rightarrow> 'a \<Rightarrow> ereal" where
  "score d K E a = Inf (d E ` (favoring_consensus_elections K a))"

fun arg_min_set :: "('b \<Rightarrow> 'a :: ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "arg_min_set f A = Collect (is_arg_min f (\<lambda> a. a \<in> A))"

(* fun arg_min_set_2 :: "('b \<Rightarrow> 'a::ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
   "arg_min_set_2 f A = Set.filter (is_arg_min f (\<lambda> a. a \<in> A)) A" *)

fun dr_winners :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a set \<Rightarrow>
                   'a Profile \<Rightarrow> 'a set" where
  "dr_winners d K A p = arg_min_set (score d K (A, p)) A"

fun dr_rule :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Electoral_Module" where
  "dr_rule d K A p = (dr_winners d K A p, A - dr_winners d K A p, {})"

subsection \<open>Code Equations\<close>

fun list_to_rel :: "'a list \<Rightarrow> 'a rel" where
  "list_to_rel [] = {}" |
  "list_to_rel [x] = {(x, x)}" |
  "list_to_rel xs = set (map (\<lambda> x. (x, hd xs)) xs) \<union> list_to_rel (tl xs)"

fun pos_in_list_acc :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "pos_in_list_acc acc [] y = acc + 1" |
  "pos_in_list_acc acc (x#xs) y = (if x = y then acc else pos_in_list_acc (acc + 1) xs y)"

(* Index of the first occurrence of y in xs *)
fun pos_in_list :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "pos_in_list xs y = pos_in_list_acc 0 xs y"

lemma a:
  fixes
    xs :: "'a list" and
    x :: "'a"
  shows "\<And> acc. pos_in_list_acc (acc + 1) xs x = pos_in_list_acc acc xs x + 1"
proof (induct xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons b ys)
  thus ?case
  proof (cases "b = x")
    case True
    thus ?thesis
      by simp
  next
    case False
    hence "pos_in_list_acc (acc + 1) (b#ys) x = pos_in_list_acc (acc + 2) ys x"
      by simp
    also from False
    have "\<dots> = pos_in_list_acc (acc + 1) ys x + 1"
      using Suc_eq_plus1 add_2_eq_Suc' Cons
      by presburger
    also from False
    have "\<dots> = pos_in_list_acc acc (b#ys) x + 1"
      by simp
    finally show ?thesis
      by simp
  qed
qed

lemma p:
  fixes
    xs :: "'a list" and
    x :: "'a" and
    i :: "nat"
  assumes
    "i < length xs" and
    "\<forall> j < i. xs!j \<noteq> x" and
    "xs!i = x"
  shows "pos_in_list xs x = i"
  using assms
proof (induction xs arbitrary: i)
case Nil
  thus ?case
    by simp
next
  case (Cons a xs)
  thus ?case
  proof (cases i)
    case 0
    with Cons.prems(3)
    show ?thesis
      by simp
  next
    case (Suc nat)
    with Cons.prems(2)
    have "a \<noteq> x"
      by auto
    hence "pos_in_list (a#xs) x = pos_in_list_acc 1 xs x"
      by simp
    also have "\<dots> = pos_in_list_acc 0 xs x + 1"
      using a
      by simp
    also have "\<dots> = pos_in_list xs x + 1"
      by simp
    also have "\<dots> = i"
    proof -
      from Cons.prems(1)
      have "nat < length xs"
        using Suc
        by simp
      moreover from Cons.prems(2)
      have "\<forall> j < nat. xs!j \<noteq> x"
        using Suc
        by auto
      moreover from Cons.prems(3)
      have "xs!nat = x"
        using Suc
        by simp
      ultimately have "pos_in_list xs x = nat"
        using Cons.IH
        by simp
      thus ?thesis
        using Suc
        by simp
    qed
    finally show ?thesis
      by simp
  qed
qed

(* Possibly a useful addition: 
  x \<in> set xs \<Longrightarrow> (\<And> i. i < length xs \<Longrightarrow> i < (pos_in_list xs x) \<Longrightarrow> xs!i \<noteq> x *)
lemma pos_in_list_altdef:
  fixes
    xs :: "'a list" and
    x :: "'a"
  assumes "x \<in> set xs"
  shows "xs!(pos_in_list xs x) = x"
  using assms
proof (induction xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons a xs)
  thus ?case
  proof (cases "x = a")
    case True
    thus ?thesis
      by simp
  next
    case False
    with Cons
    have "x \<in> set xs"
      by simp
    with Cons
    have "xs!(pos_in_list xs x) = x"
      by simp
    moreover have "pos_in_list (a#xs) x = pos_in_list xs x + 1"
    proof -
      have acc_pos_list: "\<And> acc. pos_in_list_acc (acc + 1) xs x = pos_in_list_acc acc xs x + 1"
      proof (induct xs)
        case Nil
        thus ?case
          by simp
      next
        case (Cons b xs)
        thus ?case
        proof (cases "b = x")
          case True
          thus ?thesis
            by simp
        next
          case False
          hence "pos_in_list_acc (acc + 1) (b#xs) x = pos_in_list_acc (acc + 2) xs x"
            by simp
          also from Cons
          have "\<dots> = pos_in_list_acc (acc + 1) xs x + 1"
            by simp
          also from False
          have "\<dots> = pos_in_list_acc acc (b#xs) x + 1"
            by simp
          finally show ?thesis
            by simp
        qed
      qed
      have "pos_in_list (a#xs) x = pos_in_list_acc 0 (a#xs) x"
        by simp
      also have "\<dots> = (if a = x then 0 else pos_in_list_acc 1 xs x)"
        by simp
      also have "\<dots> = pos_in_list_acc 1 xs x"
        using False
        by simp
      also have "\<dots> = pos_in_list_acc 0 xs x + 1"
        using acc_pos_list
        by simp
      also have "\<dots> = pos_in_list xs x + 1"
        by simp
      finally show ?thesis
        by simp
    qed
    ultimately show "(a#xs)!(pos_in_list (a#xs) x) = x"
      by simp
  qed
qed

(* Alternative expression of list_to_rel using relation_of. 
  This is used in the proof that list_to_rel produces linear orders. *)
lemma list_to_rel_altdef:
  fixes xs
  assumes "distinct xs"
  shows "relation_of (\<lambda> y z. pos_in_list xs y \<ge> pos_in_list xs z) (set xs) = list_to_rel xs"
  using assms
proof (unfold relation_of_def, safe)
  fix
    xs :: "'a list" and
    a :: "'a" and
    b :: "'a"
  assume
    dist_xs: "distinct xs" and
    b_above_a: "pos_in_list xs b \<le> pos_in_list xs a" and
    a_in_xs: "a \<in> set xs" and
    b_in_xs: "b \<in> set xs"
  show "(a, b) \<in> list_to_rel xs"
    (* During the execution of "list_to_rel xs",
      (a, b) is added by the recursive call of list_to_rel on a list where b is the head *)
    sorry
next
  fix
    xs :: "'a list" and
    a :: "'a" and
    b :: "'a"
  assume
    dist_xs: "distinct xs" and
    ab_in_xs: "(a, b) \<in> list_to_rel xs"
  (* For the proofs of the following statements, look at the two ways (a, b) can be added to 
    "list_to_rel xs": by the second or third pattern matching case of the definition of list_to_rel.
  *)
  show "a \<in> set xs"
    sorry
  show "b \<in> set xs"
    sorry
  show "pos_in_list xs b \<le> pos_in_list xs a"
    sorry
qed


(*
  We want "all_profiles l A = {}" for infinite A.
  We have "permutations_of_set A = {} \<longleftrightarrow> \<not>finite A"
    (Multiset_Permutations.permutations_of_set_empty_iff).
    "listset (replicate 0 (list_to_rel ` {})" is "{[]}", not "{}".
  This is why we make the case where "permutations_of_set A = {}" explicit.
  Open question: Would "finite A" instead of "permutations_of_set A = {}"
                 also work for code generation?
*)
fun all_profiles :: "nat \<Rightarrow> 'a set \<Rightarrow> ('a Profile) set" where
  "all_profiles l A = (if permutations_of_set A = {} then {}
                       else listset (replicate l (list_to_rel ` permutations_of_set A)))"

fun favoring_consensus_elections_std :: "'a Consensus_Rule \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> nat
                                          \<Rightarrow> 'a Election set" where
  "favoring_consensus_elections_std K a A l =
    (\<lambda> p. (A, p)) ` (Set.filter (\<lambda> p. (fst K) (A, p) \<and> elect_r ((snd K) A p) = {a})
                                (all_profiles l A))"

fun score_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Election \<Rightarrow> 'a \<Rightarrow> ereal" where
  "score_std d K E a = Min (d E ` (favoring_consensus_elections_std K a (fst E) (length (snd E))))"

fun dr_winners_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a set
                          \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "dr_winners_std d K A p = arg_min_set (score_std d K (A, p)) A"

fun dr_rule_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Electoral_Module" where
  "dr_rule_std d K A p = (dr_winners_std d K A p, A - dr_winners_std d K A p, {})"

lemma 1:
  fixes
    A :: "'a set" and
    B :: "'a list set"
  assumes
    finA: "finite A" and
    finB: "finite B"
  shows "finite {a#b | a b. a \<in> A \<and> b \<in> B}"
proof -
  let ?P = "\<lambda> A. finite {a#b |a b. a \<in> A \<and> b \<in> B}"
  have "\<And> a A'. finite A' \<Longrightarrow> a \<notin> A' \<Longrightarrow> ?P A' \<Longrightarrow> ?P (insert a A')"
  proof -
    fix
      a :: "'a" and
      A' :: "'a set"
    assume
      fin: "finite A'" and
      notin: "a \<notin> A'" and
      finset: "finite {a#b | a b. a \<in> A' \<and> b \<in> B}"
    have "{a'#b | a' b. a' \<in> insert a A' \<and> b \<in> B}
            = {a#b | a b. a \<in> A' \<and> b \<in> B} \<union> {a#b | b. b \<in> B}"
      by auto
    moreover have "finite {a#b | b. b \<in> B}"
      using finB
      by simp
    ultimately have "finite {a'#b | a' b. a' \<in> insert a A' \<and> b \<in> B}"
      using finset
      by simp
    thus "?P (insert a A')"
      by simp
  qed
  moreover have "?P {}"
    by simp
  ultimately show "?P A"
    using finite_induct[of A ?P] finA
    by simp
qed

lemma 2: "\<forall> xs. (\<forall> i < length xs. finite (xs!i)) \<longrightarrow> finite (listset xs)"
proof
  fix xs :: "'b set list"
  show "(\<forall> i < length xs. finite (xs!i)) \<longrightarrow> finite (listset xs)"
  proof (induct xs)
    case Nil
    thus ?case
      by simp
  next
    case (Cons a ys)
    fix
      a :: "'b set" and
      ys :: "'b set list"
    assume assm1: "(\<forall> i < length ys. finite (ys!i)) \<longrightarrow> finite (listset ys)"
    show "(\<forall> i < length (a#ys). finite ((a#ys)!i)) \<longrightarrow> finite (listset (a#ys))"
    proof (clarify)
      assume assm2: "\<forall> i < length (a#ys). finite ((a#ys)!i)"
      hence "finite a"
        by auto
      moreover from assm2
      have "\<forall> i < length ys. finite (ys!i)"
        by auto
      with assm1
      have "finite (listset ys)"
        by simp
      ultimately have "finite {x#xs' | x xs'. x \<in> a \<and> xs' \<in> (listset ys)}"
        using 1
        by auto
      thus "finite (listset (a#ys))"
        by (simp add: set_Cons_def)
    qed
  qed
qed

lemma 3: "\<forall> xs. length xs > 0 \<and> (\<forall> i < length xs. xs!i = {}) \<longrightarrow> listset xs = {}"
proof
  fix xs :: "'b set list"
  show "length xs > 0 \<and> (\<forall> i < length xs. xs!i = {}) \<longrightarrow> listset xs = {}"
  proof (induct xs)
    case Nil
    thus ?case
      by simp
  next
    case (Cons a xs)
      fix
        a :: "'b set" and
        xs :: "'b set list"
    assume assm1: "0 < length xs \<and> (\<forall> i < length xs. xs!i = {}) \<longrightarrow> listset xs = {}"
    show "0 < length (a#xs) \<and> (\<forall> i < length (a#xs). (a#xs)!i = {}) \<longrightarrow> listset (a#xs) = {}"
    proof (clarify)
      assume assm2: "\<forall> i < length (a#xs). (a#xs)!i = {}"
      hence "a = {}"
        by auto
      moreover from assm2
      have "\<forall> i < length xs. xs!i = {}"
        by auto
      ultimately have "{x#xs' | x xs'. x \<in> a \<and> xs' \<in> (listset xs)} = {}"
        by simp
      thus "listset (a#xs) = {}"
        by (simp add: set_Cons_def)
    qed
  qed
qed

lemma 5: "\<forall> ys \<in> listset xs. length ys = length xs"
proof (induct xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons a xs)
  assume IH: "\<forall> ys \<in> listset xs. length ys = length xs"
  have "\<forall> ys \<in> {x#xs' | x xs'. x \<in> a \<and> xs' \<in> (listset xs)}. length ys = 1 + length xs"
    using IH
    by auto
  hence "\<forall> ys \<in> {x#xs' | x xs'. x \<in> a \<and> xs' \<in> (listset xs)}. length ys = length (a#xs)"
    by simp
  thus ?case
    by (simp add: set_Cons_def)
qed

lemma 6: "\<forall> ys \<in> listset xs. (\<forall> i < length ys. ys!i \<in> xs!i)"
proof (induct xs)
case Nil
  thus ?case
    by simp
next
  case (Cons a xs)
  assume IH: "\<forall> ys \<in> listset xs. \<forall> i < length ys. ys!i \<in> xs!i"
  show "\<forall> ys \<in> listset (a#xs). \<forall> i < length ys. ys!i \<in> (a#xs)!i"
  proof (safe)
    fix
      ys :: "'a list" and
      i :: nat
    assume
      1: "ys \<in> listset (a#xs)" and
      2: "i < length ys"
    have "ys \<in> set_Cons a (listset xs)"
      using 1
      by simp
    hence "ys \<in> {ys. \<exists> b bs. ys = b#bs \<and> b \<in> a \<and> bs \<in> (listset xs)}"
      unfolding set_Cons_def
      by simp
    hence ex: "\<exists> b bs. ys = b#bs \<and> b \<in> a \<and> bs \<in> (listset xs)"
      by simp
    show "ys!i \<in> (a#xs)!i"
    proof (cases "i > 0")
      case False
      from ex
      have "ys!0 \<in> a"
        by auto
      thus ?thesis
        using False
        by simp
    next
      case True
      with ex IH
      show ?thesis
        using 2 nth_Cons_Suc 
        by fastforce
    qed
  qed
qed

lemma standard_implies_equal_score:
  fixes
    d :: "'a Election Distance" and
    K :: "'a Consensus_Rule" and
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assumes std: "standard d"
  shows "score d K (A, p) a = score_std d K (A, p) a"
proof -
  have all_profiles_set:
    "all_profiles (length p) A = {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
  proof (cases "finite A")
    case False
    hence "all_profiles (length p) A = {}"
      by simp
    moreover have "{x. finite_profile A x \<and> length x = (length p)} = {}"
      using False
      by simp
    ultimately show ?thesis
      by simp
  next
    case t1: True
    show ?thesis
    proof (cases "length p > 0")
      case t2: True
      show ?thesis
      proof (safe)
        fix x :: "'a Profile"
        assume xprof: "x \<in> all_profiles (length p) A"
        from t1
        show "finite A"
          by simp
        from xprof
        have "all_profiles (length p) A \<noteq> {}"
          by blast
        hence ne: "list_to_rel ` permutations_of_set A \<noteq> {}"
          by auto
        have "length (replicate (length p) (list_to_rel ` permutations_of_set A)) = length p"
          by simp
        hence "\<forall> xs \<in> listset (replicate (length p) (list_to_rel ` permutations_of_set A)).
                length xs = length p"
          using 5
          by metis
        thus l: "length x = length p"
          using xprof ne
          by simp
        show "profile A x"
        proof (unfold profile_def, safe)
          fix i :: nat
          assume lt_len_x: "i < length x"
          with l
          have "i < length p"
            by simp
          hence "x!i \<in> replicate (length p) (list_to_rel ` permutations_of_set A)!i"
            using xprof ne 6 lt_len_x all_profiles.simps image_is_empty
            by metis
          hence "x!i \<in> list_to_rel ` permutations_of_set A"
            using \<open>i < length p\<close>
            by simp
          hence relation_of:
            "x!i \<in> {relation_of (\<lambda> y z. pos_in_list xs y \<ge> pos_in_list xs z) (set xs)
                      | xs. xs \<in> permutations_of_set A}"
            using list_to_rel_altdef permutations_of_setD
            by blast
          let ?P = "\<lambda> xs y z. pos_in_list xs y \<ge> pos_in_list xs z"
          have refl: "\<And> xs a. a \<in> (set xs) \<Longrightarrow> ?P xs a a"
            by simp
          moreover have trans:
            "\<And> xs a b c. \<lbrakk> a \<in> (set xs); b \<in> (set xs); c \<in> (set xs) \<rbrakk>
              \<Longrightarrow> ?P xs a b \<Longrightarrow> ?P xs b c \<Longrightarrow> ?P xs a c"
            by simp
          moreover have antisym:
            "\<And> xs a b. \<lbrakk> a \<in> (set xs); b \<in> (set xs) \<rbrakk> \<Longrightarrow> ?P xs a b \<Longrightarrow> ?P xs b a \<Longrightarrow> a = b"
            using pos_in_list_altdef le_antisym
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
          leneq: "length x = length p" and
          fin_A: "finite A" and
          prof_A_x: "profile A x"
        show "x \<in> all_profiles (length p) A"
          (* Intermediate step: Show that all linear orders over A 
          are in "list_to_rel ' (permutations_of_set A)".  
          Then, use the argument that "listset (replicate l S))" for a set S is the set of lists 
          of length l where each item is in S. *)
          sorry
      qed
    next
      case f2: False
      have "finite_profile A []"
        using t1
        unfolding profile_def
        by simp
      moreover have "length [] = length p"
        using f2
        by simp
      moreover have "{x. finite_profile A x \<and> length x = length p} \<subseteq> {[]}"
        using f2
        by auto
      moreover have "all_profiles (length p) A = {[]}"
        using t1 f2
        by simp
      ultimately show ?thesis
        by (simp add: subset_antisym)
    qed
  qed
  hence "favoring_consensus_elections_std K a A (length p) =
           favoring_consensus_elections K a
            \<inter> Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
    by auto
  moreover have "Inf (d (A,p) ` (favoring_consensus_elections K a)) = 
                   Inf (d (A,p) ` (favoring_consensus_elections K a
                    \<inter> Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}))"
    using \<open>standard d\<close>
    (* Since d in standard, d (A,p) (A,p') is \<infinity> for all p' not in the set. *)
    sorry
  ultimately have "Inf (d (A,p) ` (favoring_consensus_elections K a)) = 
                    Inf (d (A,p) ` (favoring_consensus_elections_std K a A (length p)))"
    by simp
  also have "\<dots> = Min (d (A,p) ` (favoring_consensus_elections_std K a A (length p)))"
  proof (cases "favoring_consensus_elections_std K a A (length p) = {}")
    case True
    thus ?thesis
    (* Find out what "Min {}" does. If it is not \<infinity>, redefine score_std:
    "score_std d K E a = 
      (if favoring_consensus_elections_std K a (fst E) (length (snd E)) = {}
      then \<infinity>
      else Min (d E ` (favoring_consensus_elections_std K a (fst E) (length (snd E)))))" 
    This is consistent with the convention that the distance from empty consensus sets is \<infinity>
    mentioned by Hadjibeyli and Wilson after remark 3.5 *)
      sorry
  next
    case False
    hence "d (A,p) ` (favoring_consensus_elections_std K a A (length p)) \<noteq> {}"
      by simp
    moreover have "finite (favoring_consensus_elections_std K a A (length p))"
    proof -
      have "\<forall> l A. finite A \<longrightarrow> finite (permutations_of_set A)"
        by simp
      hence "finite (list_to_rel ` permutations_of_set A)"
        by simp
      moreover have fin_A_imp_fin_all: "\<forall> l A. finite A \<longrightarrow> finite (all_profiles l A)"
        using 2
        by force
      hence "finite (all_profiles (length p) A)"
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
        hence list_perm_A_empty: "list_to_rel ` permutations_of_set A = {}"
          by simp
        let ?xs = "replicate (length p) (list_to_rel ` permutations_of_set A)"
        from list_perm_A_empty
        have "\<forall> i < length ?xs. ?xs!i = {}"
          by simp
        hence "finite (listset (replicate (length p) (list_to_rel ` permutations_of_set A)))"
          by (simp add: 2)
        thus ?thesis
          by simp
      qed
      hence "finite (Set.filter (\<lambda> p. (fst K) (A, p) \<and> elect_r ((snd K) A p)
              = {a}) (all_profiles (length p) A))"
        using finite_filter
        by blast
      thus ?thesis
        by simp
    qed
    hence "finite (d (A,p) ` (favoring_consensus_elections_std K a A (length p)))"
      by simp
    ultimately show ?thesis
      by (simp add: Lattices_Big.complete_linorder_class.Min_Inf)
  qed
  finally show "score d K (A,p) a = score_std d K (A,p) a"
    by simp
qed

lemma swap_standard: "standard (votewise_distance swap l_one)"
proof (unfold standard_def, clarify)
  fix
    C :: "'a set" and
    B :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile"
  assume assm: "length p \<noteq> length q \<or> C \<noteq> B"
  thus "votewise_distance swap l_one (C, p) (B, q) = \<infinity>"
  proof (cases "length p = length q")
    case False
    thus ?thesis
      by simp
  next
    case len_p_eq_len_q: True
    with assm
    have C_Neq_B: "C \<noteq> B"
      by simp
    thus ?thesis
    proof (cases "length p > 0")
      case False
      with C_Neq_B
      show ?thesis
        by simp
    next
      case True
      with len_p_eq_len_q
      have map_fst_eq_swap: "(map2 (\<lambda> x y. swap (C, x) (B, y)) p q)!0 = swap (C, (p!0)) (B, (q!0))"
        by simp
      also have map_fst_is_infty: "\<dots> = \<infinity>"
        using C_Neq_B
        by simp
      finally have first_el_is_infty: "(map2 (\<lambda> x y. swap (C, x) (B, y)) p q)!0 = \<infinity>"
        by simp
      moreover from True len_p_eq_len_q
      have len_gt_zero: "length (map2 (\<lambda> x y. swap (C, x) (B, y)) p q) > 0"
        by simp
      ultimately have l_one_is_infty: "l_one (map2 (\<lambda> x y. swap (C, x) (B, y)) p q) = \<infinity>"
        (* Should not be very hard *)
        sorry
      with True len_p_eq_len_q
      show ?thesis
        by simp
    qed
  qed
qed

lemma equal_score_swap: "score (votewise_distance swap l_one)
                          = score_std (votewise_distance swap l_one)"
  using standard_implies_equal_score swap_standard
  by fast

definition "drswap = dr_rule (votewise_distance swap l_one)"

lemma [code]: "drswap = dr_rule_std (votewise_distance swap l_one)"
proof -
  from equal_score_swap
  have "\<forall> K E a. score (votewise_distance swap l_one) K E a
        = score_std (votewise_distance swap l_one) K E a"
    by metis
  hence "\<forall> K A p. dr_winners (votewise_distance swap l_one) K A p
          = dr_winners_std (votewise_distance swap l_one) K A p"
    by (simp add: equal_score_swap)
  hence "\<forall> K A p. dr_rule (votewise_distance swap l_one) K A p
          = dr_rule_std (votewise_distance swap l_one) K A p"
    by fastforce
  thus ?thesis
    unfolding drswap_def
    by blast
qed

subsection \<open>Soundness\<close>

lemma dr_is_em:
  fixes
    K :: "'a Consensus_Rule" and
    d :: "'a Election Distance"
  shows "electoral_module (dr_rule d K)"
proof (unfold electoral_module_def, rule dr_rule.induct, safe)
  fix
    d :: "'a Election Distance" and
    k :: "'a Consensus_Rule" and
    A :: "'a set" and
    p :: "'a Profile"
  show "well_formed A (dr_rule d k A p)"
    by (auto simp add: is_arg_min_def)
qed

subsection \<open>TODO\<close>

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
      proof (rule ccontr)
        assume "\<not> \<not> (\<exists> y. (\<lambda> s. s \<in> S) y \<and> g y < g x)"
        then obtain y :: 'a where
          "(\<lambda> s. s \<in> S) y \<and> g y < g x"
          by metis
        hence "(\<lambda> s. s \<in> S) y \<and> f y < f x"
          using x_in_S assms
          by metis
        with not_y
        show False
          by metis
      qed
      with x_in_S not_y
      show ?thesis
        by simp
  qed
qed

lemma rule_anon_if_el_dist_and_cons_class_anon:
  fixes
    d :: "'a Election Distance" and
    K :: "'a Consensus_Rule"
  assumes
    d_anon: "el_distance_anonymity d" and
    K_anon: "consensus_rule_anonymity K"
  shows "anonymity (dr_rule d K)"
proof (unfold anonymity_def, clarify)
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
  let ?m = "dr_rule d K"
  let ?P = "\<lambda> a A' p'. (A', p') \<in> favoring_consensus_elections K a"
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
        favcons: "(S, x) \<in> favoring_consensus_elections K a"
      hence fin_S_x: "finite_profile S x"
        by simp
      from perm
      have fin_S_y: "finite_profile S y"
        unfolding profile_def
        using fin_S_x nth_mem perm_set_eq profile_set
        by metis
      moreover from perm favcons
      have fst_x_and_elect_snd_x_a: "(fst K) (S, x) \<and> elect_r ((snd K) S x) = {a}"
        by simp
      with K_anon perm fin_S_x fin_S_y
      have "(fst K) (S, y) \<and> elect_r ((snd K) S y) = {a}"
        unfolding consensus_rule_anonymity_def anonymity_def
        using fin_S_x fst_x_and_elect_snd_x_a calculation perm
        by (metis (no_types))
      ultimately show "(S, y) \<in> favoring_consensus_elections K a"
        by simp
    qed
    show "{(A', p') | A' p'. ?P a A' p'} = {(A', ?listpi' p') | A' p'. ?P a A' p'}" (is "?X = ?Y")
    proof
      show "?X \<subseteq> ?Y"
      proof
        fix E :: "'a Election"
        let
          ?A = "fst E" and
          ?p = "snd E"
        assume assm: "E \<in> {(A', p') | A' p'. ?P a A' p'}"
        hence 2: "?P a ?A ?p"
          by simp
        show "E \<in> {(A', ?listpi' p') | A' p'. ?P a A' p'}"
        proof (cases "length ?p = length p")
          case True
          hence "permute_list (inv pi) ?p <~~> ?p"
            using pi_perm
            by (simp add: permutes_inv)
          with apply_perm 2
          have "?P a ?A (permute_list (inv pi) ?p)"
            by presburger
          moreover have "length (permute_list (inv pi) ?p) = length p"
            using True
            by simp
          ultimately have "(?A, ?listpi (permute_list (inv pi) ?p)) \<in> {(A', ?listpi p')
                            | A' p'. length p' = length p \<and> ?P a A' p'}"
            by auto
          moreover have "?listpi (permute_list (inv pi) ?p) = permute_list (inv pi \<circ> pi) ?p"
            using permute_list_compose True pi_perm
            by metis
          hence "?listpi (permute_list (inv pi) ?p) = ?p"
            using permute_list_id permutes_inv_o(2) pi_perm(1)
            by metis
          ultimately have "E \<in> {(A', ?listpi p') | A' p'. length p' = length p \<and> ?P a A' p'}"
            by simp
          thus ?thesis
            by auto
        next
          case False
          with assm
          show ?thesis
            by fastforce (* because ?listpi ?p = ?p *)
        qed
      qed
    next
      show "?Y \<subseteq> ?X"
      proof
        fix E :: "'a Election"
        let
          ?A = "fst E" and
          ?r = "snd E"
        assume assm: "E \<in> {(A', ?listpi' p') | A' p'. ?P a A' p'}"
        hence "\<exists> p'. ?r = ?listpi' p' \<and> ?P a ?A p'"
          by auto
        then obtain p' where
          rp': "?r = ?listpi' p'" and
          2: "?P a ?A p'"
          by metis
        show "E \<in> {(A', p') | A' p'. ?P a A' p'}"
        proof (cases "length p' = length p")
          case True
          have "?r <~~> p'"
            using pi_perm rp'
            by simp
          with 2 apply_perm rp'
          have "?P a ?A ?r"
            by presburger
          moreover have "length ?r = length p"
            using rp' True
            by simp
          ultimately show "E \<in> {(A', p') | A' p'. ?P a A' p'}"
            by simp
        next
          case False
          with assm
          show ?thesis
            using rp'
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
    have anon: "\<And> A' p' A p pi. (\<forall> n. (pi n) permutes {..< n})
          \<longrightarrow> d (A, p) (A', p')
                = d (A, permute_list (pi (length p)) p) (A', permute_list (pi (length p')) p')"
      unfolding el_distance_anonymity_def
      by blast
    show "{d (A, p) (A', p') | A' p'. ?P a A' p'} =
            {d (A, ?listpi' p) (A', ?listpi' p') | A' p'. ?P a A' p'}"
      using perm anon[of ?pi' A p]
      unfolding el_distance_anonymity_def
      by simp
  qed
  hence "\<forall> a \<in> A. {d (A, p) (A', p') | A' p'. ?P a A' p'} =
          {d (A, q) (A', ?listpi' p') | A' p'. ?P a A' p'}"
    using pq
    by simp
  ultimately have
    "\<forall> a \<in> A. {d (A, q) (A', p') | A' p'. (A', p') \<in> favoring_consensus_elections K a}
            = {d (A, p) (A', p') | A' p'. (A', p') \<in> favoring_consensus_elections K a}"
    by simp
  hence "\<forall> a \<in> A. d (A, q) ` favoring_consensus_elections K a =
               d (A, p) ` favoring_consensus_elections K a"
    by fast
  hence "\<forall> a \<in> A. score d K (A, p) a = score d K (A, q) a"
    by simp
  thus "dr_rule d K A p = dr_rule d K A q"
    using is_arg_min_equal[of A "score d K (A, p)" "score d K (A, q)"]
    by auto
qed

end

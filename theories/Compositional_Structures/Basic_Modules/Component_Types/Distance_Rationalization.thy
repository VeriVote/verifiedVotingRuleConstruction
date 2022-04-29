(*  File:       Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance Rationalization\<close>

theory Distance_Rationalization
  imports "Distance"
          "Consensus_Rule"
          "HOL-Library.Multiset_Permutations"
          "Votewise_Distance"
begin

text \<open>
  A distance rationalizing of a voting rule is its interpretation  as a
  procedure that electa an uncontroversial winner if there is one, and
  otherwise elect the alternatives that are as close to becoming an
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

fun arg_min_set :: "('b \<Rightarrow> 'a::ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "arg_min_set f A = Collect (is_arg_min f (\<lambda> a. a \<in> A))"

(*fun arg_min_set_2 :: "('b \<Rightarrow> 'a::ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "arg_min_set_2 f A = Set.filter (is_arg_min f (\<lambda> a. a \<in> A)) A"*)

fun dr_winners :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a set \<Rightarrow>
                   'a Profile \<Rightarrow> 'a set" where
  "dr_winners d K A p = arg_min_set (score d K (A, p)) A"

fun dr_rule :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Electoral_Module" where
  "dr_rule d K A p = (dr_winners d K A p, A - dr_winners d K A p, {})"

subsection \<open>Code Equations\<close>

fun list_to_rel :: "'a list \<Rightarrow> 'a rel" where
  "list_to_rel [] = {}" |
  "list_to_rel [x] = {(x,x)}" |
  "list_to_rel xs = set (map (\<lambda> x. (x, hd xs)) xs) \<union> list_to_rel (tl xs)"

fun pos_in_list_acc :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "pos_in_list_acc acc [] y = acc + 1" |
  "pos_in_list_acc acc (x#xs) y = (if x = y then acc else pos_in_list_acc (acc + 1) xs y)"

fun pos_in_list :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "pos_in_list xs y = pos_in_list_acc 0 xs y"

lemma list_to_rel_altdef: "distinct xs \<longrightarrow> relation_of (\<lambda>y z. pos_in_list xs y \<ge> pos_in_list xs z) (set xs) = list_to_rel xs"
  sorry

fun all_profiles :: "nat \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set list set" where
  "all_profiles l A = (let s = list_to_rel ` permutations_of_set A in
                      (if s = {} then {} else 
                      listset (replicate l (list_to_rel ` permutations_of_set A))))"

value "listset ([]::int set list)"

value "permutations_of_set {1,2,3::int}"

fun favoring_consensus_elections_std :: "'a Consensus_Rule \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a Election set" where
  "favoring_consensus_elections_std K a A l =
    (\<lambda> p. (A, p)) ` (Set.filter (\<lambda> p. (fst K) (A, p) \<and> elect_r ((snd K) A p) = {a}) (all_profiles l A))"
                            
fun score_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Election \<Rightarrow> 'a \<Rightarrow> ereal" where
  "score_std d K E a = Min (d E ` (favoring_consensus_elections_std K a (fst E) (length (snd E))))"

fun dr_winners_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a set \<Rightarrow>
                   'a Profile \<Rightarrow> 'a set" where
  "dr_winners_std d K A p = arg_min_set (score_std d K (A, p)) A"

fun dr_rule_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Electoral_Module" where
  "dr_rule_std d K A p = (dr_winners_std d K A p, A - dr_winners_std d K A p, {})"

lemma 1: "\<And> A B. finite A \<and> finite B \<longrightarrow> finite {a # b |a b. a \<in> A \<and> b \<in> B}"
proof safe
  fix A :: "'a set" and B :: "'a list set"
  assume "finite A" and "finite B"
  let ?P = "\<lambda> A. finite {a # b |a b. a \<in> A \<and> b \<in> B}"
  have "\<And>a A'. finite A' \<Longrightarrow> a \<notin> A' \<Longrightarrow> ?P A' \<Longrightarrow> ?P (insert a A')"
  proof-
    fix a and A'
    assume 
      fin: "finite A'" and
      notin: "a \<notin> A'" and
      finset: "finite {a # b |a b. a \<in> A' \<and> b \<in> B}"
    have "{aa # b |aa b. aa \<in> insert a A' \<and> b \<in> B} = {a # b |a b. a \<in> A' \<and> b \<in> B} \<union> {a # b |b. b \<in> B}"
      by auto
    moreover have "finite {a # b |b. b \<in> B}"
      using \<open>finite B\<close>
      by simp
    ultimately have "finite {aa # b |aa b. aa \<in> insert a A' \<and> b \<in> B}"
      using finset
      by simp
    then show "?P (insert a A')"
      by simp
  qed
  moreover have "?P {}"
    by simp
  ultimately show "?P A"
    using finite_induct[of A ?P] \<open>finite A\<close> 
    by auto
qed
  
lemma 2: "\<forall> xs. (\<forall> i < length xs. finite (xs ! i)) \<longrightarrow> finite (listset xs)"
proof
  fix xs :: "'b set list"
  show "(\<forall>i<length xs. finite (xs ! i)) \<longrightarrow> finite (listset xs)"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    fix a :: "'b set" and xs :: "'b set list"
    assume assm1: "(\<forall>i<length xs. finite (xs ! i)) \<longrightarrow> finite (listset xs)"
    (*have "listset (a # xs) = set_Cons a (listset xs)"
      by simp
    also have "\<dots> = {x # xs'|x xs'. x \<in> a \<and> xs' \<in> (listset xs)}"
      unfolding set_Cons_def
      by simp*)
    show "(\<forall>i<length (a # xs). finite ((a # xs) ! i)) \<longrightarrow> finite (listset (a # xs))"
    proof clarify
      assume assm2: "\<forall>i<length (a # xs). finite ((a # xs) ! i)"
      hence "finite a"
        by auto
      moreover from assm2 have "(\<forall> i < length xs. finite (xs ! i))"
        by auto
      with assm1 have "finite (listset xs)"
        by simp
      ultimately have "finite {x # xs'|x xs'. x \<in> a \<and> xs' \<in> (listset xs)}"
        using 1
        by auto
      then show "finite (listset (a # xs))"
        unfolding set_Cons_def
        by (simp add: set_Cons_def)
    qed
  qed
qed

value "listset ([{},{}]::int set list)"

lemma 3: "\<forall> xs. length xs > 0 \<and> (\<forall> i < length xs. xs ! i = {}) \<longrightarrow> listset xs = {}"
proof
  fix xs :: "'b set list"
  show "length xs > 0 \<and> (\<forall> i < length xs. xs ! i = {}) \<longrightarrow> listset xs = {}"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    fix a :: "'b set" and xs :: "'b set list"
    assume assm1: "0 < length xs \<and> (\<forall>i<length xs. xs ! i = {}) \<longrightarrow> listset xs = {}"
    (*have "listset (a # xs) = set_Cons a (listset xs)"
      by simp
    also have "\<dots> = {x # xs'|x xs'. x \<in> a \<and> xs' \<in> (listset xs)}"
      unfolding set_Cons_def
      by simp*)
    show "0 < length (a # xs) \<and> (\<forall>i<length (a # xs). (a # xs) ! i = {}) \<longrightarrow> listset (a # xs) = {}"
    proof clarify
      assume assm2: "\<forall>i<length (a # xs). (a # xs) ! i = {}"
      hence "a = {}"
        by auto
      moreover from assm2 have "(\<forall> i < length xs. xs ! i = {})"
        by auto
      ultimately have "{x # xs'|x xs'. x \<in> a \<and> xs' \<in> (listset xs)} = {}"
        by auto
      then show "listset (a # xs) = {}"
        unfolding set_Cons_def
        by (simp add: set_Cons_def)
    qed
  qed
qed

(*lemma 4:
  fixes A and l
  assumes infinite: "infinite A"
  shows "all_profiles l A = {}"
proof-
  from infinite have "permutations_of_set A = {}"
    using permutations_of_set_infinite
    by simp
  hence e: "list_to_rel ` permutations_of_set A = {}"
    by simp
  let ?xs = "replicate l (list_to_rel ` permutations_of_set A)"
  from e have "\<forall>i < length ?xs. ?xs ! i = {}"
    by simp
  hence "listset (replicate l (list_to_rel ` permutations_of_set A)) = {}"
    by (simp add: "2")
  then show ?thesis
    by simp
*)

lemma 5: "\<forall> ys \<in> listset xs. length ys = length xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume IH: "\<forall>ys\<in>listset xs. length ys = length xs"
  have "\<forall>ys\<in>{x # xs'|x xs'. x \<in> a \<and> xs' \<in> (listset xs)}. length ys = 1 + length xs"
    using IH
    by auto
  hence "\<forall>ys\<in>{x # xs'|x xs'. x \<in> a \<and> xs' \<in> (listset xs)}. length ys = length (a#xs)"
    by simp
  then show ?case
    by (simp add: set_Cons_def)
qed

lemma 6: "\<forall> ys \<in> listset xs. (\<forall> i < length ys. ys ! i \<in> xs ! i)"
proof (induct xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume IH: "\<forall>ys\<in>listset xs. \<forall>i<length ys. ys ! i \<in> xs ! i"
  show "\<forall>ys\<in>listset (a # xs). \<forall>i<length ys. ys ! i \<in> (a # xs) ! i"
  proof(safe)
    fix ys and i
    assume 1: "ys \<in> listset (a # xs)" and 2: "i < length ys"
    have "ys \<in> set_Cons a (listset xs)"
        using 1
        by simp
      hence "ys \<in> {ys. \<exists>b bs. ys = b # bs \<and> b \<in> a \<and> bs \<in> (listset xs)}"
        unfolding set_Cons_def
        by simp
      hence ex: "\<exists> b bs. ys = b # bs \<and> b \<in> a \<and> bs \<in> (listset xs)"
        by simp
    show "ys ! i \<in> (a # xs) ! i"
    proof (cases "i > 0")
      case False
      from ex have "ys ! 0 \<in> a"
        by auto
      then show ?thesis 
        using False
        by simp
    next
      case True
      with ex IH show ?thesis
        using 2 nth_Cons_Suc 
        by fastforce
    qed
  qed
qed

lemma standard_implies_equal_score:
  fixes d::"'a Election Distance" and K::"'a Consensus_Rule" and A::"'a set" and p::"'a Profile" and a::"'a"
  assumes std: "standard d" (*and fin: "finite A"*)
  shows "score d K (A,p) a = score_std d K (A,p) a"
proof-
  have "all_profiles (length p) A = {x. finite_profile A x \<and> length x = (length p)}"
  proof (cases "finite A")
    case f1: False
    have "all_profiles (length p) A = {}"
    proof-
      have "permutations_of_set A = {}"
        using permutations_of_set_infinite f1
        by simp
      hence "list_to_rel ` permutations_of_set A = {}"
        by simp
      then show ?thesis
        by simp
    qed
    moreover have "{x. finite_profile A x \<and> length x = (length p)} = {}"
      using f1
      by simp
    ultimately show ?thesis
      by simp
  next
    case t1: True
    show ?thesis     
    proof (cases "(length p) > 0")
      case t2: True
      show ?thesis
      proof safe
        fix x
        assume xprof: "x \<in> all_profiles (length p) A"
        from t1 show "finite A"
          by simp
        from xprof have "all_profiles (length p) A \<noteq> {}"
            by blast
        hence ne: "list_to_rel ` permutations_of_set A \<noteq> {}"
          by auto
        have "length (replicate (length p) (list_to_rel ` permutations_of_set A)) = length p"
          by simp
        hence "\<forall>xs \<in> listset (replicate (length p) (list_to_rel ` permutations_of_set A)). length xs = length p"
          using 5
          by metis
        then show l: "length x = length p"
          using xprof ne
          by simp
        show "profile A x"
        proof (unfold profile_def, safe)
          fix i
          assume "i < length x"
          with l have "i < length p"
            by simp
          hence "x ! i \<in> replicate (length p) (list_to_rel ` permutations_of_set A) ! i"
            using xprof ne
            by (metis "6" \<open>i < length x\<close> all_profiles.elims)
          hence "x ! i \<in> list_to_rel ` permutations_of_set A"
            using \<open>i < length p\<close> by force
          hence "x ! i \<in> {relation_of (\<lambda>y z. pos_in_list xs y \<ge> pos_in_list xs z) (set xs)| xs. xs \<in> permutations_of_set A}"
            using list_to_rel_altdef permutations_of_setD
            by blast
          then show "linear_order_on A (x ! i)"
            (*using partial_order_on_relation_ofI*)
            sorry
        qed
      next
        show "\<And>x. length x = length p \<Longrightarrow> finite A \<Longrightarrow> profile A x \<Longrightarrow> x \<in> all_profiles (length p) A"
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
        by auto
    qed
  qed

  hence "favoring_consensus_elections_std K a A (length p) = 
         favoring_consensus_elections K a \<inter> Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
  proof (cases "finite A")
    case False
    then show ?thesis
      by auto
  next
    case True
    then show ?thesis sorry
  qed

  moreover have "Inf (d (A,p) ` (favoring_consensus_elections K a)) = 
                 Inf (d (A,p) ` (favoring_consensus_elections K a \<inter> Pair A ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}))"
    using \<open>standard d\<close>
    sorry

  ultimately have "Inf (d (A,p) ` (favoring_consensus_elections K a)) = 
                   Inf (d (A,p) ` (favoring_consensus_elections_std K a A (length p)))"
    by simp

  also have "\<dots> = Min (d (A,p) ` (favoring_consensus_elections_std K a A (length p)))"
  proof (cases "favoring_consensus_elections_std K a A (length p) = {}")
    case True
    then show ?thesis sorry
  next
    case False
    hence "d (A,p) ` (favoring_consensus_elections_std K a A (length p)) \<noteq> {}"
      by simp
    moreover have "finite (favoring_consensus_elections_std K a A (length p))"
    proof-
      have "\<forall> l A. finite A \<longrightarrow> finite (permutations_of_set A)"
        by simp
      hence "finite (list_to_rel ` permutations_of_set A)"
        by simp
      moreover have f: "\<forall> l A. finite A \<longrightarrow> finite (all_profiles l A)"
        using 2
        by force
      hence "finite (all_profiles (length p) A)"
      proof (cases "finite A")
        case True
        then show ?thesis using f by blast
      next
        case False
        hence "permutations_of_set A = {}"
          using permutations_of_set_infinite
          by simp
        hence e: "list_to_rel ` permutations_of_set A = {}"
          by simp
        let ?xs = "replicate (length p) (list_to_rel ` permutations_of_set A)"
        from e have "\<forall>i < length ?xs. ?xs ! i = {}"
          by simp
        hence "finite (listset (replicate (length p) (list_to_rel ` permutations_of_set A)))"
          by (simp add: "2")
        then show ?thesis
          by simp
      qed
      hence "finite (Set.filter (\<lambda> p. (fst K) (A, p) \<and> elect_r ((snd K) A p) = {a}) (all_profiles (length p) A))"
        using finite_filter 
        by blast
      then show ?thesis
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

(*lemma standard_implies_equal_score: "standard d \<longrightarrow> score d = score_std d"
proof
  fix d :: "'a Election Distance"
  assume "standard d"
  have "\<And> K A p a. score d K (A,p) a = score_std d K (A,p) a"
  proof safe
    fix 
      K :: "'a Consensus_Rule" and
      A :: "'a set" and
      p :: "'a Profile" and
      a :: "'a"
    have "\<forall> l A. all_profiles l A = {p :: 'a Profile. finite_profile A p \<and> length p = l}"
    proof clarify
      fix l and A
      show "all_profiles l A = {p. finite_profile A p \<and> length p = l} "
   proof (cases "l > 0")
     case True
     show ?thesis
     proof safe
       fix x
       assume "x \<in> all_profiles l A"
       show "finite A"
       proof (rule ccontr)
         assume "\<not> finite A"
         hence "all_profiles l A = {}"
           using permutations_of_set_infinite True
           sorry
         then show "False"
           sorry
       qed
       show "profile A x"
         sorry
       show "length x = l"
         sorry
       assume "l = length x" and "finite A" and "profile A x"
     next
       show "\<And>x. l = length x \<Longrightarrow> finite A \<Longrightarrow> profile A x \<Longrightarrow> x \<in> all_profiles (length x) A"
         sorry
     qed
   next
     case False
     have "finite_profile A []"
       try
       sorry
     moreover have "{p. finite_profile A p \<and> length p = l} \<subseteq> {[]}"
       using False
       by auto
     moreover have "all_profiles l A = {[]}"
       using False
       by simp
     then show ?thesis
       sorry
   qed

  hence "favoring_consensus_elections_std K a A (length p) = 
         favoring_consensus_elections K a \<inter> (\<lambda> p. (A, p)) ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}"
    sorry
  moreover have "Inf (d (A,p) ` (favoring_consensus_elections K a)) = 
                 Inf (d (A,p) ` (favoring_consensus_elections K a \<inter> (\<lambda> p. (A, p)) ` {p' :: 'a Profile. finite_profile A p' \<and> length p' = length p}))"
    using \<open>standard d\<close>
    sorry
  ultimately have "Inf (d (A,p) ` (favoring_consensus_elections K a)) = 
                   Inf (d (A,p) ` (favoring_consensus_elections_std K a A (length p)))"
    by simp
  also have "\<dots> = Min (d (A,p) ` (favoring_consensus_elections_std K a A (length p)))"
  proof (cases "favoring_consensus_elections_std K a A (length p) = {}")
    case True
    then show ?thesis sorry
  next
    case False
    hence "d (A,p) ` (favoring_consensus_elections_std K a A (length p)) \<noteq> {}"
      by simp
    moreover have "finite (favoring_consensus_elections_std K a A (length p))"
    proof-
      have "\<forall> l A. finite A \<longrightarrow> finite (permutations_of_set A)"
        by simp
      hence "finite (list_to_rel ` permutations_of_set A)"
        by simp
      moreover have f: "\<forall> l A. finite A \<longrightarrow> finite (all_profiles l A)"
        using 2
        by force
      hence "finite (all_profiles (length p) A)"
      proof (cases "finite A")
        case True
        then show ?thesis using f by auto
      next
        case False
        hence "permutations_of_set A = {}"
          using permutations_of_set_infinite
          by simp
        hence e: "list_to_rel ` permutations_of_set A = {}"
          by simp
        let ?xs = "replicate (length p) (list_to_rel ` permutations_of_set A)"
        from e have "\<forall>i < length ?xs. ?xs ! i = {}"
          by simp
        hence "finite (listset (replicate (length p) (list_to_rel ` permutations_of_set A)))"
          by (simp add: "2")
        then show ?thesis
          by simp
      qed
      hence "finite (Set.filter (\<lambda> p. (fst K) (A, p) \<and> elect_r ((snd K) A p) = {a}) (all_profiles (length p) A))"
        using finite_filter 
        by blast
      then show ?thesis
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
  then show "score d = score_std d"
    by fast
qed
*)

lemma swap_standard: "standard (votewise_distance swap l_one)"
  unfolding standard_def
  sorry (*conterexample found!*)

lemma equal_score_swap: "score (votewise_distance swap l_one) = score_std (votewise_distance swap l_one)"
  using standard_implies_equal_score swap_standard
  by auto

definition "drswap = dr_rule (votewise_distance swap l_one)"

lemma [code]: "drswap = dr_rule_std (votewise_distance swap l_one)"
proof-
  from equal_score_swap have "\<forall> K E a. score (votewise_distance swap l_one) K E a = score_std (votewise_distance swap l_one) K E a"
    by metis
  hence "\<forall> K A p. dr_winners (votewise_distance swap l_one) K A p = dr_winners_std (votewise_distance swap l_one) K A p"
    by (simp add: equal_score_swap)
  hence "\<forall> K A p. dr_rule (votewise_distance swap l_one) K A p = dr_rule_std (votewise_distance swap l_one) K A p"
    by fastforce
  then show ?thesis
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
  thus "(x \<in> S \<and> (\<nexists>y. y \<in> S \<and> f y < f x)) = (x \<in> S \<and> (\<nexists>y. y \<in> S \<and> g y < g x))"
    by simp
next
  case x_in_S: True
  thus "(x \<in> S \<and> (\<nexists>y. y \<in> S \<and> f y < f x)) = (x \<in> S \<and> (\<nexists>y. y \<in> S \<and> g y < g x))"
  proof (cases "\<exists> y. (\<lambda> s. s \<in> S) y \<and> f y < f x")
    case y: True
    then obtain y::'a where
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
        then obtain y::'a where
          "(\<lambda> s. s \<in> S) y \<and> g y < g x"
          by metis
        hence "(\<lambda> s. s \<in> S) y \<and> f y < f x"
          using x_in_S assms
          by metis
        with not_y show False
          by metis
      qed
      with x_in_S not_y show ?thesis
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
    pi :: "'a Profile \<Rightarrow> 'a Profile" and
    A :: "'a set" and
    p :: "'a Profile"
  assume
    perm: "newnameforpermut pi" and
    fin: "finite A" and
    profile: "profile A p"
  let ?m = "dr_rule d K"
  let ?P = "\<lambda> a A' p'. (A', p') \<in> favoring_consensus_elections K a"
  have "\<forall> a \<in> A. {(A', p') | A' p'. ?P a A' p'} = {(A', pi p') | A' p'. ?P a A' p'}"
  proof (clarify)
    fix
      a :: "'a"
    have apply_perm:
      "\<And> pi A' p'. newnameforpermut pi \<Longrightarrow>
        (A', p') \<in> {(A', p') | A' p'. ?P a A' p'} \<Longrightarrow>
        (A', pi p') \<in> {(A', p') | A' p'. ?P a A' p'}"
    proof (clarify)
      fix
        pi :: "'a Profile \<Rightarrow> 'a Profile" and
        A' :: "'a set" and
        p' :: "'a Profile"
      assume
        perm: "newnameforpermut pi"  and
        favcons: "(A', p') \<in> favoring_consensus_elections K a"
      from favcons
      have finprof: "finite_profile A' p'"
        by simp
      with perm perm_preserves_finite_profile[of A' p' pi]
      have "finite_profile A' (pi p')"
        unfolding newnameforpermut_def
        by simp
      moreover from favcons
      have "(fst K) (A', p') \<and> elect_r ((snd K) A' p') = {a}"
        by simp
      with K_anon perm finprof
      have "(fst K) (A', (pi p')) \<and> elect_r ((snd K) A' (pi p')) = {a}"
        unfolding consensus_rule_anonymity_def anonymity_def
        by auto
      ultimately have "(A', pi p') \<in> favoring_consensus_elections K a"
        by simp
      thus "\<exists> A'' p''. (A', pi p') = (A'', p'')
            \<and> (A'', p'') \<in> favoring_consensus_elections K a"
        by simp
    qed
    show "{(A', p') | A' p'. ?P a A' p'} = {(A', pi p') | A' p'. ?P a A' p'}" (is "?X = ?Y")
    proof
      show "?X \<subseteq> ?Y"
      proof
        fix E :: "'a Election"
        assume assm: "E \<in> {(A', p') | A' p'. ?P a A' p'}"
        let
          ?A = "fst E" and
          ?p = "snd E"
        let ?pi_inv = "inverse_perm pi"
        have "newnameforpermut ?pi_inv"
          using perm inverse_perm_preserves_perm
          by auto
        with assm apply_perm[of ?pi_inv]
        have "(?A, ?pi_inv ?p) \<in> {(A', p') | A' p'. ?P a A' p'}"
          by auto
        moreover have "?p = pi (?pi_inv ?p)"
          using perm pi_inverse_perm_pi_is_id[of pi]
          by auto
        ultimately show "E \<in> {(A', pi p') | A' p'. ?P a A' p'}"
          by force
      qed
    next
      show "?Y \<subseteq> ?X"
      proof
        fix E :: "'a Election"
        let
          ?A = "fst E" and
          ?r = "snd E"
        assume assm: "E \<in> {(A', pi p') | A' p'. ?P a A' p'}"
        hence "\<exists> p'. ?r = pi p' \<and> ?P a ?A p'"
          by auto
        then obtain p' where
          perm_p': "?r = pi p'" and
          "?P a ?A p'"
          by blast
        hence "(?A, p') \<in> {(A', p') | A' p'. ?P a A' p'}"
          by simp
        with perm apply_perm
        have "(?A, ?r) \<in> {(A', p') | A' p'. ?P a A' p'}"
          using perm_p'
          by simp
        thus "E \<in> {(A', p') | A' p'. ?P a A' p'}"
          by simp
      qed
    qed
  qed
  hence "\<forall> a \<in> A. d (A, pi p) ` {(A', p') | A' p'. ?P a A' p'}
             = d (A, pi p) ` {(A', pi p') | A' p'. ?P a A' p'}"
    by (metis (no_types, lifting))
  hence "\<forall> a \<in> A. {d (A, pi p) (A', p') | A' p'. ?P a A' p'}
             = {d (A, pi p) (A', pi p') | A' p'. ?P a A' p'}"
    by blast
  moreover from d_anon
  have "\<forall> a \<in> A. {d (A, p) (A', p') | A' p'. ?P a A' p'} =
          {d (A, pi p) (A', pi p') | A' p'. ?P a A' p'}"
  proof (clarify)
    fix a :: "'a"
    from d_anon
    have "\<And> A' p'. newnameforpermut pi \<longrightarrow> d (A, p) (A', p') = d (A, pi p) (A', pi p')"
      unfolding el_distance_anonymity_def perm
      by blast
    thus "{d (A, p) (A', p') | A' p'. ?P a A' p'} =
            {d (A, pi p) (A', pi p') | A' p'. ?P a A' p'}"
      using perm
      unfolding el_distance_anonymity_def
      by simp
  qed
  ultimately
  have "\<forall> a \<in> A. {d (A, pi p) (A', p') | A' p'. (A', p') \<in> favoring_consensus_elections K a}
            = {d (A, p) (A', p') | A' p'. (A', p') \<in> favoring_consensus_elections K a}"
    by auto
  hence "\<forall> a \<in> A. d (A, pi p) ` favoring_consensus_elections K a =
               d (A, p) ` favoring_consensus_elections K a"
    by fast
  hence "\<forall> a \<in> A. score d K (A, p) a = score d K (A, pi p) a"
    by simp
  thus "dr_rule d K A p = dr_rule d K A (pi p)"
    using is_arg_min_equal[of A "score d K (A, p)" "score d K (A, pi p)"]
    by auto
qed

end

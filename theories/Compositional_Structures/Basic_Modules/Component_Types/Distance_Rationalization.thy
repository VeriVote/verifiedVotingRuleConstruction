(*  File:       Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance Rationalization\<close>

theory Distance_Rationalization
  imports "Distance"
          "Consensus_Rule"
          "HOL-Library.Multiset_Permutations"
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

fun arg_min_set_2 :: "('b \<Rightarrow> 'a::ord) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "arg_min_set_2 f A = Set.filter (is_arg_min f (\<lambda> a. a \<in> A)) A"

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

fun all_profiles :: "nat \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set list set" where
  "all_profiles l A = listset (replicate l (list_to_rel ` permutations_of_set A))"

fun favoring_consensus_elections_std :: "'a Consensus_Rule \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a Election set" where
  "favoring_consensus_elections_std K a A l =
    (\<lambda> p. (A, p)) ` (Set.filter (\<lambda> p. (fst K) (A, p) \<and> elect_r ((snd K) A p) = {a}) (all_profiles l A))"

fun score_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Election \<Rightarrow> 'a \<Rightarrow> ereal" where
  "score_std d K E a = Min (d E ` (favoring_consensus_elections_std K a (fst E) (length (snd E))))"

fun dr_winners_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a set \<Rightarrow>
                   'a Profile \<Rightarrow> 'a set" where
  "dr_winners_std d K A p = arg_min_set_2 (score_std d K (A, p)) A"

fun dr_rule_std :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Electoral_Module" where
  "dr_rule_std d K A p = (dr_winners_std d K A p, A - dr_winners_std d K A p, {})"

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

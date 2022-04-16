(*  File:       Distance_Rationalization.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Distance Rationalization\<close>

theory Distance_Rationalization
  imports "Distance"
          "Consensus_Rule"
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

fun dr_winners :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a set \<Rightarrow>
                   'a Profile \<Rightarrow> 'a set" where
  "dr_winners d K A p = arg_min_set (score d K (A, p)) A"

fun dr_rule :: "'a Election Distance \<Rightarrow> 'a Consensus_Rule \<Rightarrow> 'a Electoral_Module" where
  "dr_rule d K A p = (dr_winners d K A p, A - dr_winners d K A p, {})"

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
    pi :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
    A :: "'a set" and
    p :: "'a Profile"
  assume
    perm: "is_perm pi" and
    fin: "finite A" and
    profile: "profile A p"
  let ?m = "dr_rule d K"
  let ?P = "\<lambda> a A' p'. (A', p') \<in> favoring_consensus_elections K a"
  have "\<forall> a \<in> A. {(A', p') | A' p'. ?P a A' p'} = {(A', build_perm pi p') | A' p'. ?P a A' p'}"
  proof (clarify)
    fix
      a :: "'a"
    have apply_perm:
      "\<And> pi A' p'. is_perm pi \<Longrightarrow>
        (A', p') \<in> {(A', p') | A' p'. ?P a A' p'} \<Longrightarrow>
        (A', build_perm pi p') \<in> {(A', p') | A' p'. ?P a A' p'}"
    proof (clarify)
      fix
        pi :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
        A' :: "'a set" and
        p' :: "'a Profile"
      assume
        perm: "is_perm pi"  and
        favcons: "(A', p') \<in> favoring_consensus_elections K a"
      from favcons
      have finprof: "finite_profile A' p'"
        by simp
      with perm
      have "finite_profile A' (build_perm pi p')"
        unfolding profile_def
        by (metis perm finprof build_perm.elims is_perm_def length_permute_list nth_mem profile_set set_permute_list)
      moreover from favcons
      have "(fst K) (A', p') \<and> elect_r ((snd K) A' p') = {a}"
        by simp
      with K_anon perm finprof
      have "(fst K) (A', (build_perm pi p')) \<and> elect_r ((snd K) A' (build_perm pi p')) = {a}"
        unfolding consensus_rule_anonymity_def anonymity_def
        by auto
      ultimately have "(A', build_perm pi p') \<in> favoring_consensus_elections K a"
        by simp
      thus "\<exists> A'' p''. (A', build_perm pi p') = (A'', p'')
            \<and> (A'', p'') \<in> favoring_consensus_elections K a"
        by simp
    qed
    show "{(A', p') | A' p'. ?P a A' p'} = {(A', build_perm pi p') | A' p'. ?P a A' p'}" (is "?X = ?Y")
    proof
      show "?X \<subseteq> ?Y"
      proof
        fix E :: "'a Election"
        assume assm: "E \<in> {(A', p') | A' p'. ?P a A' p'}"
        let
          ?A = "fst E" and
          ?p = "snd E"
        have "is_perm (inv_perm pi)"
          using perm permutes_inv
          unfolding is_perm_def
          by (metis inv_perm.simps)
        with assm apply_perm[of \<open>inv_perm pi\<close>]
        have "(?A, build_perm (inv_perm pi) ?p) \<in> {(A', p') | A' p'. ?P a A' p'}"
          by auto
        moreover have "?p = build_perm pi (build_perm (inv_perm pi) ?p)"
        proof-
          let ?n = "length ?p"
          have "build_perm pi (build_perm (inv_perm pi) ?p) =
                build_perm pi (permute_list (inv_perm pi ?n) ?p)"
            by simp
          also have "\<dots> = build_perm pi (permute_list (inv (pi ?n)) ?p)"
            by simp
          also have "\<dots> = permute_list (pi ?n) (permute_list (inv (pi ?n)) ?p)"
            by simp
          also have "\<dots> = permute_list (pi ?n \<circ> (inv (pi ?n))) ?p"
            using permute_list_compose
            by (metis (no_types, lifting) is_perm_def perm permutes_inv_o(1) permutes_inv_o(2))
          also have "\<dots> = permute_list id ?p"
          proof-
            have "pi ?n \<circ> (inv (pi ?n)) = id"
              using perm permutes_inv_o
              unfolding is_perm_def
              by auto
            then show ?thesis
              by simp
          qed
          finally show ?thesis
            by simp
        qed
        ultimately show "E \<in> {(A', build_perm pi p') | A' p'. ?P a A' p'}"
          by force
      qed
    next
      show "?Y \<subseteq> ?X"
      proof
        fix E :: "'a Election"
        let
          ?A = "fst E" and
          ?r = "snd E"
        assume assm: "E \<in> {(A', build_perm pi p') | A' p'. ?P a A' p'}"
        hence "\<exists> p'. ?r = build_perm pi p' \<and> ?P a ?A p'"
          by auto
        then obtain p' where
          perm_p': "?r = build_perm pi p'" and
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
  hence "\<forall> a \<in> A. d (A, build_perm pi p) ` {(A', p') | A' p'. ?P a A' p'}
             = d (A, build_perm pi p) ` {(A', build_perm pi p') | A' p'. ?P a A' p'}"
    by (metis (no_types, lifting))
  hence "\<forall> a \<in> A. {d (A, build_perm pi p) (A', p') | A' p'. ?P a A' p'}
             = {d (A, build_perm pi p) (A', build_perm pi p') | A' p'. ?P a A' p'}"
    by blast
  moreover from d_anon
  have "\<forall> a \<in> A. {d (A, p) (A', p') | A' p'. ?P a A' p'} =
          {d (A, build_perm pi p) (A', build_perm pi p') | A' p'. ?P a A' p'}"
  proof (clarify)
    fix a :: "'a"
    from d_anon
    have "\<And> A' p'. is_perm pi \<longrightarrow> d (A, p) (A', p') = d (A, build_perm pi p) (A', build_perm pi p')"
      unfolding el_distance_anonymity_def perm
      by blast
    thus "{d (A, p) (A', p') | A' p'. ?P a A' p'} =
            {d (A, build_perm pi p) (A', build_perm pi p') | A' p'. ?P a A' p'}"
      using perm
      unfolding el_distance_anonymity_def
      by simp
  qed
  ultimately
  have "\<forall> a \<in> A. {d (A, build_perm pi p) (A', p') | A' p'. (A', p') \<in> favoring_consensus_elections K a}
            = {d (A, p) (A', p') | A' p'. (A', p') \<in> favoring_consensus_elections K a}"
    by auto
  hence "\<forall> a \<in> A. d (A, build_perm pi p) ` favoring_consensus_elections K a =
               d (A, p) ` favoring_consensus_elections K a"
    by fast
  hence "\<forall> a \<in> A. score d K (A, p) a = score d K (A, build_perm pi p) a"
    by simp
  thus "dr_rule d K A p = dr_rule d K A (build_perm pi p)"
    using is_arg_min_equal[of A "score d K (A, p)" "score d K (A, build_perm pi p)"]
    by auto
qed

end

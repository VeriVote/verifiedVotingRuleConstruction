(*  File:       Profile.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Preference Profile\<close>

theory Profile
  imports Preference_Relation
          "HOL.Finite_Set"
          "HOL-Library.Extended_Nat"
          "HOL-Combinatorics.List_Permutation"
begin

text \<open>
  Preference profiles denote the decisions made by the individual voters on
  the eligible alternatives. They are represented in the form of one preference
  relation (e.g., selected on a ballot) per voter, collectively captured in a
  mapping of voters onto their respective preference relations.
  If there are finitely many voters, they can be enumerated and the mapping can
  be interpreted as a list of preference relations.
  Unlike the common preference profiles in the social-choice sense, the
  profiles described here consider only the (sub-)set of alternatives that are
  received.
\<close>

subsection \<open>Definition\<close>

text \<open>
  A profile contains one ballot for each voter.
  An election consists of a set of participating voters,
  a set of eligible alternatives and a corresponding profile.
\<close>

type_synonym ('a, 'v) Profile = "'v \<Rightarrow> ('a Preference_Relation)"

type_synonym ('a, 'v) Election = "'a set \<times> 'v set \<times> ('a, 'v) Profile"

fun election_equality :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election \<Rightarrow> bool" where
  "election_equality (A, V, p) (A', V', p') = (A = A' \<and> V = V' \<and> (\<forall> v \<in> V. p v = p' v))"

abbreviation alts_\<E> :: "('a, 'v) Election \<Rightarrow> 'a set" where "alts_\<E> E \<equiv> fst E"

abbreviation votrs_\<E> :: "('a, 'v) Election \<Rightarrow> 'v set" where "votrs_\<E> E \<equiv> fst (snd E)"

abbreviation prof_\<E> :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Profile" where "prof_\<E> E \<equiv> snd (snd E)"

text \<open>
  A profile on a set of alternatives A and a voter set V consists of ballots
  that are linear orders on A for all voters in V.
  A finite profile is one with finitely many alternatives and voters.
\<close>

definition profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> bool" where
  "profile V A p \<equiv> \<forall> v \<in> V. linear_order_on A (p v)"

abbreviation finite_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> bool" where
  "finite_profile V A p \<equiv> finite A \<and> finite V \<and> profile V A p"

abbreviation finite_election :: "('a,'v) Election \<Rightarrow> bool" where
  "finite_election E \<equiv> finite_profile (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E)"

definition finite_voter_elections :: "('a, 'v) Election set" where
  "finite_voter_elections =
    {el :: ('a, 'v) Election. finite (votrs_\<E> el)}"

definition finite_elections :: "('a, 'v) Election set" where
  "finite_elections =
    {el :: ('a, 'v) Election. finite_profile (votrs_\<E> el) (alts_\<E> el) (prof_\<E> el)}"

definition valid_elections :: "('a,'v) Election set" where
  "valid_elections = {E. profile (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E)}"

\<comment> \<open>Elections with fixed alternatives,
    finite voters and a default value for the profile value on non-voters.\<close>
fun fixed_alt_elections :: "'a set \<Rightarrow> ('a, 'v) Election set" where
  "fixed_alt_elections A = valid_elections \<inter>
    {E. alts_\<E> E = A \<and> finite (votrs_\<E> E) \<and> (\<forall> v. v \<notin> votrs_\<E> E \<longrightarrow> prof_\<E> E v = {})}"

\<comment> \<open>Counts the occurrences of a ballot in an election,
    i.e. how many voters chose that exact ballot.\<close>
fun vote_count :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election \<Rightarrow> nat" where
  "vote_count p E = card {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p}"

subsection \<open>Vote Count\<close>

lemma sum_comp:
  fixes
    f :: "'x \<Rightarrow> 'z::comm_monoid_add" and
    g :: "'y \<Rightarrow> 'x" and
    X :: "'x set" and
    Y :: "'y set"
  assumes "bij_betw g Y X"
  shows "sum f X = sum (f \<circ> g) Y"
  using assms
proof (induction "card X" arbitrary: X Y f g)
  case 0
  assume "bij_betw g Y X"
  hence "card Y = 0"
    using bij_betw_same_card "0.hyps"
    unfolding "0.hyps"
    by simp
  hence "sum f X = 0 \<and> sum (f \<circ> g) Y = 0"
    using assms 0 card_0_eq sum.empty sum.infinite
    by metis
  thus ?case
    by simp
next
  case (Suc n)
  assume
    card_X: "Suc n = card X" and
    bij: "bij_betw g Y X" and
    hyp: "\<And> X Y f g. n = card X \<Longrightarrow> bij_betw g Y X \<Longrightarrow> sum f X = sum (f \<circ> g) Y"
  then obtain x :: "'x"
    where x_in_X: "x \<in> X"
    by fastforce
  with bij have "bij_betw g (Y - {the_inv_into Y g x}) (X - {x})"
    using bij_betw_DiffI bij_betw_apply bij_betw_singletonI bij_betw_the_inv_into
          empty_subsetI f_the_inv_into_f_bij_betw insert_subsetI
    by (metis (mono_tags, lifting))
  moreover have "n = card (X - {x})"
    using card_X x_in_X
    by fastforce
  ultimately have "sum f (X - {x}) = sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using hyp Suc
    by blast
  moreover have
    "sum (f \<circ> g) Y = f (g (the_inv_into Y g x)) + sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using Suc.hyps(2) x_in_X bij bij_betw_def calculation card.infinite
          f_the_inv_into_f_bij_betw nat.discI sum.reindex sum.remove
    by metis
  moreover have "f (g (the_inv_into Y g x)) + sum (f \<circ> g) (Y - {the_inv_into Y g x}) =
    f x + sum (f \<circ> g) (Y - {the_inv_into Y g x})"
    using x_in_X bij f_the_inv_into_f_bij_betw
    by metis
  moreover have "sum f X = f x + sum f (X - {x})"
    using Suc.hyps(2) Zero_neq_Suc x_in_X card.infinite sum.remove
    by metis
  ultimately show ?case
    by simp
qed

lemma vote_count_sum:
  fixes E :: "('a, 'v) Election"
  assumes
    "finite (votrs_\<E> E)" and
    "finite (UNIV::('a \<times> 'a) set)"
  shows "sum (\<lambda> p. vote_count p E) UNIV = card (votrs_\<E> E)"
proof (simp)
  have "\<forall> p. finite {v \<in> votrs_\<E> E. prof_\<E> E v = p}"
    using assms
    by force
  moreover have
    "disjoint {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}"
    unfolding disjoint_def
    by blast
  moreover have partition:
    "votrs_\<E> E = \<Union> {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}"
    using Union_eq[of "{{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}"]
    by blast
  ultimately have card_eq_sum':
    "card (votrs_\<E> E) = sum card {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}"
    using card_Union_disjoint[of "{{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}"]
    by auto
  have "finite {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}"
    using partition assms
    by (simp add: finite_UnionD)
  moreover have
    "{{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV} =
        {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
              p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}} \<union>
        {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
              p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}}"
    by blast
  moreover have
    "{} = {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
              p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}} \<inter>
          {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
              p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}}"
    by blast
  ultimately have "sum card {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV} =
    sum card {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
                p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}} +
    sum card {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
                p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}}"
    using sum.union_disjoint[of
            "{{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
              p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
            "{{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
                p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}}"]
    by simp
  moreover have
    "\<forall> X \<in> {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
            p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}}. card X = 0"
    using card_eq_0_iff
    by fastforce
  ultimately have card_eq_sum:
    "card (votrs_\<E> E) = sum card {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
                          p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
    using card_eq_sum'
    by simp
  have "inj_on (\<lambda> p. {v \<in> votrs_\<E> E. prof_\<E> E v = p})
                {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
    unfolding inj_on_def
    by blast
  moreover have
    "(\<lambda> p. {v \<in> votrs_\<E> E. prof_\<E> E v = p}) ` {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}} \<subseteq>
         {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
                          p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
    by blast
  moreover have
    "(\<lambda> p. {v \<in> votrs_\<E> E. prof_\<E> E v = p}) ` {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}} \<supseteq>
      {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
        p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
    by blast
  ultimately have "bij_betw (\<lambda> p. {v \<in> votrs_\<E> E. prof_\<E> E v = p})
    {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}
    {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
      p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
    unfolding bij_betw_def
    by simp
  hence sum_rewrite:
    "(\<Sum> x \<in> {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}.
            card {v \<in> votrs_\<E> E. prof_\<E> E v = x}) =
      sum card {{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
        p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
    using sum_comp[of
        "\<lambda> p. {v \<in> votrs_\<E> E. prof_\<E> E v = p}"
        "{p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
        "{{v \<in> votrs_\<E> E. prof_\<E> E v = p} | p.
          p \<in> UNIV \<and> {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"
        "card"]
    unfolding comp_def
    by simp
  have "{p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}} \<inter>
    {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}} = {}"
    by blast
  moreover have "{p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}} \<union>
    {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}} = UNIV"
    by blast
  ultimately have "(\<Sum> p \<in> UNIV. card {v \<in> votrs_\<E> E. prof_\<E> E v = p}) =
    (\<Sum> x \<in> {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}. card {v \<in> votrs_\<E> E. prof_\<E> E v = x}) +
    (\<Sum> x \<in> {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}}. card {v \<in> votrs_\<E> E. prof_\<E> E v = x})"
    using assms sum.union_disjoint[of
      "{p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}}"
      "{p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<noteq> {}}"]
    using Finite_Set.finite_set add.commute finite_Un
    by (metis (mono_tags, lifting))
  moreover have
    "\<forall> x \<in> {p. {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {}}.
        card {v \<in> votrs_\<E> E. prof_\<E> E v = x} = 0"
    using card_eq_0_iff
    by fastforce
  ultimately show "(\<Sum> p \<in> UNIV. card {v \<in> votrs_\<E> E. prof_\<E> E v = p}) = card (votrs_\<E> E)"
    using card_eq_sum sum_rewrite
    by simp
qed

subsection \<open>Voter Permutations\<close>

text \<open>
  A common action of interest on elections is renaming the voters, 
  e.g. when talking about anonymity.
\<close>

fun rename :: "('v \<Rightarrow> 'v) \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "rename \<pi> (A, V, p) = (A, \<pi> ` V, p \<circ> (the_inv \<pi>))"

lemma rename_sound:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    prof: "profile V A p" and
    renamed: "(A, V', q) = rename \<pi> (A, V, p)" and
    bij: "bij \<pi>"
  shows "profile V' A q"
proof (unfold profile_def, safe)
  fix v' :: "'v"
  assume v'_in_V': "v' \<in> V'"
  let ?q_img = "((the_inv) \<pi>) v'"
  have "V' = \<pi> ` V"
    using renamed
    by simp
  hence "?q_img \<in> V"
    using UNIV_I v'_in_V' bij bij_is_inj bij_is_surj
          f_the_inv_into_f inj_image_mem_iff
    by metis
  hence "linear_order_on A (p ?q_img)"
    using prof
    unfolding profile_def
    by simp
  moreover have "q v' = p ?q_img"
    using renamed bij
    by simp
  ultimately show "linear_order_on A (q v')"
    by simp
qed

lemma rename_finite:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    prof: "finite_profile V A p" and
    renamed: "(A, V', q) = rename \<pi> (A, V, p)" and
    bij: "bij \<pi>"
  shows "finite_profile V' A q"
proof (safe)
  show "finite A"
    using prof
    by simp
  show "finite V'"
    using bij renamed prof
    by simp
  show "profile V' A q"
    using assms rename_sound
    by metis
qed

lemma rename_inv:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes "bij \<pi>"
  shows "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) = (A, V, p)"
proof -
  have "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) =
    (A, \<pi> ` (the_inv \<pi>) ` V, p \<circ> (the_inv (the_inv \<pi>)) \<circ> (the_inv \<pi>))"
    by simp
  moreover have "\<pi> ` (the_inv \<pi>) ` V = V"
    using assms
    by (simp add: f_the_inv_into_f_bij_betw image_comp)
  moreover have "(the_inv (the_inv \<pi>)) = \<pi>"
    using assms bij_betw_def inj_on_the_inv_into surj_def surj_imp_inv_eq the_inv_f_f
    by (metis (mono_tags, opaque_lifting))
  moreover have "\<pi> \<circ> (the_inv \<pi>) = id"
    using assms f_the_inv_into_f_bij_betw
    by fastforce
  ultimately show "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) = (A, V, p)"
    by (simp add: rewriteR_comp_comp)
qed
    
lemma rename_inj:
  fixes \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows "inj (rename \<pi>)"
proof (unfold inj_def, clarsimp)
  fix
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  assume
    eq_V: "\<pi> ` V = \<pi> ` V'" and
    "p \<circ> the_inv \<pi> = p' \<circ> the_inv \<pi>"
  hence "p \<circ> the_inv \<pi> \<circ> \<pi> = p' \<circ> the_inv \<pi> \<circ> \<pi>"
    by simp
  hence "p = p'"
    using assms bij_betw_the_inv_into bij_is_surj surj_fun_eq
    by metis
  moreover have "V = V'"
    using assms eq_V
    by (simp add: bij_betw_imp_inj_on inj_image_eq_iff)
  ultimately show "V = V' \<and> p = p'"
    by blast
qed

lemma rename_surj:
  fixes \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows
    on_valid_els: "rename \<pi> ` valid_elections = valid_elections" and
    on_finite_els: "rename \<pi> ` finite_elections = finite_elections"
proof (safe)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  assume valid: "(A, V, p) \<in> valid_elections"
  have "bij (the_inv \<pi>)"
    using assms bij_betw_the_inv_into
    by blast
  hence "rename (the_inv \<pi>) (A, V, p) \<in> valid_elections"
    using rename_sound valid
    unfolding valid_elections_def
    by fastforce
  thus "(A, V, p) \<in> rename \<pi> ` valid_elections"
    using assms image_eqI rename_inv[of \<pi>]
    by metis
  assume "(A', V', p') = rename \<pi> (A, V, p)"
  thus "(A', V', p') \<in> valid_elections"
    using rename_sound valid assms
    unfolding valid_elections_def
    by fastforce
next
  fix
    A :: "'b set" and
    A' :: "'b set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('b, 'v) Profile" and
    p' :: "('b, 'v) Profile"
  assume finite: "(A, V, p) \<in> finite_elections"
  have "bij (the_inv \<pi>)"
    using assms bij_betw_the_inv_into
    by blast
  hence "rename (the_inv \<pi>) (A, V, p) \<in> finite_elections"
    using rename_finite finite
    unfolding finite_elections_def
    by fastforce
  thus "(A, V, p) \<in> rename \<pi> ` finite_elections"
    using assms image_eqI rename_inv[of \<pi>]
    by metis
  assume "(A', V', p') = rename \<pi> (A, V, p)"
  thus "(A', V', p') \<in> finite_elections"
    using rename_sound finite assms
    unfolding finite_elections_def
    by fastforce
qed

subsection \<open>List Representation for Ordered Voter Types\<close>

text \<open>
  A profile on a voter set that has a natural order can be viewed as a list of ballots.
\<close>

fun to_list :: "'v::linorder set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a Preference_Relation) list" where
  "to_list V p = (if (finite V)
                    then (map p (sorted_list_of_set V))
                    else [])"

lemma map2_helper:
  fixes
    f :: "'x \<Rightarrow> 'y \<Rightarrow> 'z" and
    g :: "'x \<Rightarrow> 'x" and
    h :: "'y \<Rightarrow> 'y" and
    l1 :: "'x list" and
    l2 :: "'y list"
  shows "map2 f (map g l1) (map h l2) = map2 (\<lambda> x y. f (g x) (h y)) l1 l2"
proof -
  have "map2 f (map g l1) (map h l2) = map (\<lambda> (x, y). f x y) (zip (map g l1) (map h l2))"
    by simp
  moreover have "map (\<lambda> (x, y). f x y) (zip (map g l1) (map h l2)) =
    map (\<lambda> (x, y). f x y) (map (\<lambda> (x, y). (g x, h y)) (zip l1 l2))"
    using zip_map_map
    by metis
  moreover have "map (\<lambda> (x, y). f x y) (map (\<lambda> (x, y). (g x, h y)) (zip l1 l2)) =
    map ((\<lambda> (x, y). f x y) \<circ> (\<lambda> (x, y). (g x, h y))) (zip l1 l2)"
    by simp
  moreover have "map ((\<lambda> (x, y). f x y) \<circ> (\<lambda> (x, y). (g x, h y))) (zip l1 l2) =
    map (\<lambda> (x, y). f (g x) (h y)) (zip l1 l2)"
    by auto
  moreover have "map (\<lambda> (x, y). f (g x) (h y)) (zip l1 l2) = map2 (\<lambda> x y. f (g x) (h y)) l1 l2"
    by simp
  ultimately show
    "map2 f (map g l1) (map h l2) = map2 (\<lambda> x y. f (g x) (h y)) l1 l2"
    by simp
qed

lemma to_list_simp:
  fixes
    i :: "nat" and
    V :: "'v::linorder set" and
    p :: "('a, 'v) Profile"
  assumes
    "i < card V"
  shows "(to_list V p)!i = p ((sorted_list_of_set V)!i)"
proof -
  have "(to_list V p)!i = (map p (sorted_list_of_set V))!i"
    by simp
  also have "... = p ((sorted_list_of_set V)!i)"
    using assms
    by simp
  finally show ?thesis
    by simp
qed

lemma to_list_comp:
  fixes
    V :: "'v::linorder set" and
    p :: "('a, 'v) Profile" and
    f :: "'a rel \<Rightarrow> 'a rel"
  shows "to_list V (f \<circ> p) = map f (to_list V p)"
proof -
  have "\<forall> i < card V. (to_list V (f \<circ> p))!i = (f \<circ> p) ((sorted_list_of_set V)!i)"
    using to_list_simp
    by blast
  moreover have
    "\<forall> i < card V. (f \<circ> p) ((sorted_list_of_set V)!i) = (map (f \<circ> p) (sorted_list_of_set V))!i"
    unfolding map_def
    by simp
  moreover have 
    "\<forall> i < card V. (map (f \<circ> p) (sorted_list_of_set V))!i =
      (map f (map p (sorted_list_of_set V)))!i"
    by simp
  moreover have "map p (sorted_list_of_set V) = to_list V p"
    using to_list_simp list_eq_iff_nth_eq
    by simp
  ultimately have "\<forall> i < card V. (to_list V (f \<circ> p))!i = (map f (to_list V p))!i"
    by presburger
  moreover have "length (map f (to_list V p)) = card V"
    by simp
  moreover have "length (to_list V (f \<circ> p)) = card V" 
    by simp
  ultimately show ?thesis
    using nth_equalityI
    by simp
qed

lemma set_card_upper_bound:
  fixes
    i :: "nat" and
    V :: "nat set"
  assumes
    fin_V: "finite V" and
    bound_v: "\<forall> v \<in> V. i > v"
  shows "i \<ge> card V"
proof (cases "V = {}")
  case True
  thus ?thesis
    by simp
next
  case False
  hence "Max V \<in> V"
    using fin_V
    by simp
  moreover have "Max V \<ge> (card V) - 1"
    using False Max_ge_iff fin_V calculation card_Diff1_less finite_le_enumerate
          card_Diff_singleton finite_enumerate_in_set
    by metis
  ultimately show ?thesis
    using fin_V bound_v
    by fastforce
qed

lemma sorted_list_of_set_nth_equals_card:
  fixes
    V :: "'v::linorder set" and
    x :: "'v"
  assumes
    fin_V: "finite V" and
    x_V: "x \<in> V"
  shows "sorted_list_of_set V!(card {v \<in> V. v < x}) = x"
proof -
  let ?c = "card {v \<in> V. v < x}" and
      ?set = "{v \<in> V. v < x}"
  have ex_index: "\<forall> v \<in> V. \<exists> n. n < card V \<and> (sorted_list_of_set V!n) = v"
    using sorted_list_of_set.distinct_sorted_key_list_of_set
          sorted_list_of_set.length_sorted_key_list_of_set
          sorted_list_of_set.set_sorted_key_list_of_set
          distinct_Ex1 fin_V
    by metis
  then obtain \<phi> where
    index_\<phi>: "\<forall> v \<in> V. \<phi> v < card V \<and> (sorted_list_of_set V!(\<phi> v)) = v"
    by metis
  (* \<phi> x = ?c, i.e. \<phi> x \<ge> ?c and \<phi> x \<le> ?c *)
  let ?i = "\<phi> x"
  have inj_\<phi>: "inj_on \<phi> V"
    using inj_onI index_\<phi>
    by metis
  have mono_\<phi>: "\<forall> v v'. v \<in> V \<and> v' \<in> V \<and> v < v' \<longrightarrow> \<phi> v < \<phi> v'"
    using sorted_list_of_set.idem_if_sorted_distinct dual_order.strict_trans2 fin_V index_\<phi>
          finite_sorted_distinct_unique linorder_neqE_nat sorted_wrt_iff_nth_less
          sorted_list_of_set.length_sorted_key_list_of_set order_less_irrefl
    by (metis (full_types))
  have "\<forall> v \<in> ?set. v < x"
    by simp
  hence "\<forall> v \<in> ?set. \<phi> v < ?i"
    using mono_\<phi> x_V
    by simp
  hence "\<forall> j \<in> {\<phi> v | v. v \<in> ?set}. ?i > j"
    by blast
  moreover have fin_img: "finite ?set"
    using fin_V
    by simp
  ultimately have "?i \<ge> card {\<phi> v | v. v \<in> ?set}"
    using set_card_upper_bound
    by simp
  also have "card {\<phi> v | v. v \<in> ?set} = ?c"
    using inj_\<phi>
    by (simp add: card_image inj_on_subset setcompr_eq_image)
  finally have geq: "?i \<ge> ?c"
    by simp
  have sorted_\<phi>:
    "\<forall> i j. i < card V \<and> j < card V \<and> i < j
            \<longrightarrow> (sorted_list_of_set V!i) < (sorted_list_of_set V!j)"
    by (simp add: sorted_wrt_nth_less)
  have leq: "?i \<le> ?c"
  proof (rule ccontr, cases "?c < card V")
    case True
    let ?A = "\<lambda> j. {sorted_list_of_set V!j}"
    assume "\<not> ?i \<le> ?c"
    hence "?i > ?c"
      by simp
    hence "\<forall> j \<le> ?c. sorted_list_of_set V!j \<in> V \<and> sorted_list_of_set V!j < x"
      using sorted_\<phi> dual_order.strict_trans2 geq index_\<phi> x_V fin_V
            nth_mem sorted_list_of_set.length_sorted_key_list_of_set
            sorted_list_of_set.set_sorted_key_list_of_set
      by (metis (mono_tags, lifting))
    hence "{sorted_list_of_set V!j | j. j \<le> ?c} \<subseteq> {v \<in> V. v < x}"
      by blast
    also have "{sorted_list_of_set V!j | j. j \<le> ?c}
               = {sorted_list_of_set V!j | j. j \<in> {0 ..< (?c+1)}}"
      using add.commute
      by auto
    also have "{sorted_list_of_set V!j | j. j \<in> {0 ..< (?c+1)}}
               = (\<Union> j \<in> {0 ..< (?c+1)}. {sorted_list_of_set V!j})"
      by blast
    finally have subset: "(\<Union> j \<in> {0 ..< (?c+1)}. ?A j) \<subseteq> {v \<in> V. v < x}"
      by simp
    have "\<forall> i \<le> ?c. \<forall> j \<le> ?c. i \<noteq> j \<longrightarrow> sorted_list_of_set V!i \<noteq> sorted_list_of_set V!j"
      using True
      by (simp add: nth_eq_iff_index_eq)
    hence "\<forall> i \<in> {0 ..< (?c+1)}. \<forall> j \<in> {0 ..< (?c+1)}.
              (i \<noteq> j \<longrightarrow> {sorted_list_of_set V!i} \<inter> {sorted_list_of_set V!j} = {})"
      by fastforce
    hence "disjoint_family_on ?A {0 ..< (?c+1)}"
      unfolding disjoint_family_on_def
      by simp
    moreover have "finite {0 ..< (?c+1)}"
      by simp
    moreover have "\<forall> j \<in> {0 ..< (?c+1)}. card (?A j) = 1"
      by simp
    ultimately have "card (\<Union> j \<in> {0 ..< (?c+1)}. ?A j) = (\<Sum> j \<in> {0 ..< (?c+1)}. 1)"
      using card_UN_disjoint'
      by fastforce
    also have "(\<Sum> j \<in> {0 ..< (?c+1)}. 1) = ?c + 1"
      by auto
    finally have "card (\<Union> j \<in> {0 ..< (?c+1)}. ?A j) = ?c + 1"
      by simp
    hence "?c + 1 \<le> ?c"
      using subset card_mono fin_img
      by (metis (no_types, lifting))
    thus "False"
      by simp
  next
    case False
    assume "\<not> ?i \<le> ?c"
    thus "False"
      using False x_V index_\<phi> geq order_le_less_trans 
      by blast
  qed
  thus ?thesis
    using geq leq x_V index_\<phi>
    by simp
qed

lemma to_list_permutes_under_bij:
  fixes
    \<pi> :: "'v::linorder \<Rightarrow> 'v" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    bij: "bij \<pi>"
  shows
    "let \<phi> = (\<lambda> i. card {v \<in> \<pi> ` V. v < \<pi> ((sorted_list_of_set V)!i)})
      in (to_list V p) = permute_list \<phi> (to_list (\<pi> ` V) (\<lambda> x. p (the_inv \<pi> x)))"
proof (cases "finite V")
  case False
  (* if V is infinite, both lists are empty *)
  hence "to_list V p = []"
    by simp
  moreover have "to_list (\<pi> ` V) (\<lambda> x. p (the_inv \<pi> x)) = []"
  proof -
    have "infinite (\<pi> ` V)"
      using False assms bij_betw_finite bij_betw_subset top_greatest
      by metis
    thus ?thesis
      by simp
  qed
  ultimately show ?thesis
    by simp
next
  case True
  let
    ?q = "\<lambda> x. p (the_inv \<pi> x)" and
    ?img = "\<pi> ` V" and
    ?n = "length (to_list V p)" and
    ?perm = "\<lambda> i. card {v \<in> \<pi> ` V. v < \<pi> ((sorted_list_of_set V)!i)}"
    (* auxiliary statements equating everything with ?n *)
  have card_eq: "card ?img = card V"
    using assms bij_betw_same_card bij_betw_subset top_greatest
    by metis
  also have card_length_V: "?n = card V"
    by simp
  also have card_length_img: "length (to_list ?img ?q) = card ?img"
    using True
    by simp
  finally have eq_length: "length (to_list ?img ?q) = ?n"
    by simp
  show ?thesis
  proof (unfold Let_def permute_list_def, rule nth_equalityI)
    (* the lists have equal lengths *)
    show "length (to_list V p) =
            length
              (map (\<lambda> i. to_list ?img ?q ! card {v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)})
                   [0 ..< length (to_list ?img ?q)])"
      using eq_length
      by simp
  next
    (* the ith entries of the lists coincide *)
    fix i :: "nat"
    assume in_bnds: "i < ?n"
    let ?c = "card {v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}"
    have "map (\<lambda> i. (to_list ?img ?q)!?c) [0 ..< ?n]!i = p ((sorted_list_of_set V)!i)"
    proof -
      have "\<forall> v. v \<in> ?img \<longrightarrow> {v' \<in> ?img. v' < v} \<subseteq> ?img - {v}"
        by blast
      moreover have elem_of_img: "\<pi> (sorted_list_of_set V!i) \<in> ?img"
        using True in_bnds image_eqI nth_mem card_length_V
              sorted_list_of_set.length_sorted_key_list_of_set
              sorted_list_of_set.set_sorted_key_list_of_set
        by metis
      ultimately have "{v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}
                        \<subseteq> ?img - {\<pi> (sorted_list_of_set V!i)}"
        by simp
      hence "{v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)} \<subset> ?img"
        using elem_of_img
        by blast
      moreover have img_card_eq_V_length: "card ?img = ?n"
        using card_eq card_length_V
        by presburger
      ultimately have card_in_bnds: "?c < ?n"
        using True finite_imageI psubset_card_mono
        by (metis (mono_tags, lifting))
      moreover have img_list_map:
        "map (\<lambda> i. to_list ?img ?q!?c) [0 ..< ?n]!i = to_list ?img ?q!?c"
        using in_bnds
        by simp
      also have img_list_card_eq_inv_img_list:
        "to_list ?img ?q!?c = ?q ((sorted_list_of_set ?img)!?c)"
        using in_bnds to_list_simp in_bnds img_card_eq_V_length card_in_bnds
        by (metis (no_types, lifting))
      also have img_card_eq_img_list_i:
        "(sorted_list_of_set ?img)!?c = \<pi> (sorted_list_of_set V!i)"
        using True elem_of_img sorted_list_of_set_nth_equals_card
        by blast
      finally show ?thesis
        using assms bij_betw_imp_inj_on the_inv_f_f
              img_list_map img_card_eq_img_list_i
              img_list_card_eq_inv_img_list
        by metis
    qed
    also have "to_list V p!i = p ((sorted_list_of_set V)!i)"
      using True in_bnds
      by simp
    finally show "to_list V p!i =
        map (\<lambda> i. (to_list ?img ?q)!(card {v \<in> ?img. v < \<pi> (sorted_list_of_set V ! i)}))
          [0 ..< length (to_list ?img ?q)]!i"
      using in_bnds eq_length Collect_cong card_eq
      by simp
  qed
qed

subsection \<open>Preference Counts and Comparisons\<close>

text \<open>
  The win count for an alternative a with respect to a finite voter set V in a profile p is
  the amount of ballots from V in p that rank alternative a in first position.
  If the voter set is infinite, counting is not generally possible.
\<close>

fun win_count :: "'v set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> enat" where
  "win_count V p a = (if (finite V)
    then card {v \<in> V. above (p v) a = {a}} else infinity)"

fun prefer_count :: "'v set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "prefer_count V p x y = (if (finite V)
      then card {v \<in> V. (let r = (p v) in (y \<preceq>\<^sub>r x))} else infinity)"

lemma pref_count_voter_set_card:
  fixes
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes fin_V: "finite V"
  shows "prefer_count V p a b \<le> card V"
proof (simp)
  have "{v \<in> V. (b, a) \<in> p v} \<subseteq> V"
    by simp
  hence "card {v \<in> V. (b, a) \<in> p v} \<le> card V"
    using fin_V Finite_Set.card_mono
    by metis
  thus "(finite V \<longrightarrow> card {v \<in> V. (b, a) \<in> p v} \<le> card V) \<and> finite V"
    using fin_V
    by simp
qed

lemma set_compr:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> 'a set"
  shows "{f x | x. x \<in> A} = f ` A"
  by auto

lemma pref_count_set_compr:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  shows "{prefer_count V p a a' | a'. a' \<in> A - {a}} = (prefer_count V p a) ` (A - {a})"
  by auto

lemma pref_count:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    prof: "profile V A p" and
    fin: "finite V" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    neq: "a \<noteq> b"
  shows "prefer_count V p a b = card V - (prefer_count V p b a)"
proof -
  have "\<forall> v \<in> V. connex A (p v)"
    using prof
    unfolding profile_def
    by (simp add: lin_ord_imp_connex)
  hence asym: "\<forall> v \<in> V. \<not> (let r = (p v) in (b \<preceq>\<^sub>r a)) \<longrightarrow> (let r = (p v) in (a \<preceq>\<^sub>r b))"
    using a_in_A b_in_A
    unfolding connex_def
    by metis
  have "\<forall> v \<in> V. ((b, a) \<in> (p v) \<longrightarrow> (a, b) \<notin> (p v))"
    using antisymD neq lin_imp_antisym prof
    unfolding profile_def
    by metis
  hence "{v \<in> V. (let r = (p v) in (b \<preceq>\<^sub>r a))} =
            V - {v \<in> V. (let r = (p v) in (a \<preceq>\<^sub>r b))}"
    using asym
    by auto
  thus ?thesis
    by (simp add: card_Diff_subset Collect_mono fin)
qed

lemma pref_count_sym:
  fixes
    p :: "('a, 'v) Profile" and
    V :: "'v set" and
    a :: "'a" and
    b :: "'a" and
    c :: "'a"
  assumes
    pref_count_ineq: "prefer_count V p a c \<ge> prefer_count V p c b" and
    prof: "profile V A p" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    c_in_A: "c \<in> A" and
    a_neq_c: "a \<noteq> c" and
    c_neq_b: "c \<noteq> b"
  shows "prefer_count V p b c \<ge> prefer_count V p c a"
proof (cases)
  assume fin_V: "finite V"
  have nat1: "prefer_count V p c a \<in> \<nat>"
    unfolding Nats_def
    using of_nat_eq_enat fin_V
    by simp
  have nat2: "prefer_count V p b c \<in> \<nat>"
    unfolding Nats_def
    using of_nat_eq_enat fin_V
    by simp
  have smaller: "prefer_count V p c a \<le> card V"
    using prof fin_V pref_count_voter_set_card
    by metis
  have "prefer_count V p a c = card V - (prefer_count V p c a)"
    using pref_count prof a_in_A c_in_A a_neq_c fin_V
    by (metis (no_types, opaque_lifting))
  moreover have pref_count_b_eq:
    "prefer_count V p c b = card V - (prefer_count V p b c)"
    using pref_count prof a_in_A c_in_A a_neq_c b_in_A c_neq_b fin_V
    by metis
  hence ineq: "card V - (prefer_count V p b c) \<le> card V - (prefer_count V p c a)"
    using calculation pref_count_ineq
    by simp
  hence "card V - (prefer_count V p b c) + (prefer_count V p c a) \<le>
          card V - (prefer_count V p c a) + (prefer_count V p c a)"
    using pref_count_b_eq pref_count_ineq
    by auto
  hence "card V + (prefer_count V p c a) \<le> card V + (prefer_count V p b c)"
    using nat1 nat2 fin_V smaller
    by simp
  thus ?thesis
    by simp
next
  assume inf_V: "infinite V"
  have "prefer_count V p c a = infinity"
    using inf_V
    by simp
  moreover have "prefer_count V p b c = infinity"
    using inf_V
    by simp
  thus ?thesis
    by simp
qed

lemma empty_prof_imp_zero_pref_count:
  fixes
    p :: "('a, 'v) Profile" and
    V :: "'v set" and
    a :: "'a" and
    b :: "'a"
  assumes "V = {}"
  shows "prefer_count V p a b = 0"
  unfolding zero_enat_def
  using assms
  by simp

(* lemma pref_count_code_incr:
  fixes
    p :: "'a Profile" and
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a" and
    n :: "nat"
  assumes
    "prefer_count_code p a b = n" and
    "b \<preceq>\<^sub>r a"
  shows "prefer_count_code (r#p) a b = n + 1"
  using assms
  by simp

lemma pref_count_code_not_smaller_imp_constant:
  fixes
    p :: "'a Profile" and
    r :: "'a Preference_Relation" and
    a :: "'a" and
    b :: "'a" and
    n :: "nat"
  assumes
    "prefer_count_code p a b = n" and
    "\<not> (b \<preceq>\<^sub>r a)"
  shows "prefer_count_code (r#p) a b = n"
  using assms
  by simp *)

fun wins :: "'v set \<Rightarrow> 'a \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins V a p b =
    (prefer_count V p a b > prefer_count V p b a)"

lemma wins_inf_voters:
  fixes
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a" and
    V :: "'v set"
  assumes "infinite V"
  shows "wins V b p a = False"
  using assms
  by simp

text \<open>
  Alternative a wins against b implies that b does not win against a.
\<close>

lemma wins_antisym:
  fixes
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a" and
    V :: "'v set"
  assumes "wins V a p b" (* \<Longrightarrow> finite V *)
  shows "\<not> wins V b p a"
  using assms
  by simp

lemma wins_irreflex:
  fixes
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    V :: "'v set"
  shows "\<not> wins V a p a"
  using wins_antisym
  by metis

subsection \<open>Condorcet Winner\<close>

fun condorcet_winner :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner V A p a =
      (finite_profile V A p \<and> a \<in> A \<and> (\<forall> x \<in> A - {a}. wins V a p x))"
(*
Could this be defined via
  "for all b \<noteq> a there is an injective map
    from ballots where b wins to ballots where a wins"
instead of prefer_count for infinite voter sets?
*)

lemma cond_winner_unique_eq:
  fixes
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    "condorcet_winner V A p a" and
    "condorcet_winner V A p b"
  shows "b = a"
proof (rule ccontr)
  assume b_neq_a: "b \<noteq> a"
  have "wins V b p a"
    using b_neq_a insert_Diff insert_iff assms
    by simp
  hence "\<not> wins V a p b"
    by (simp add: wins_antisym)
  moreover have a_wins_against_b: "wins V a p b"
    using Diff_iff b_neq_a singletonD assms
    by auto
  ultimately show False
    by simp
qed

lemma cond_winner_unique:
  fixes
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "condorcet_winner V A p a"
  shows "{a' \<in> A. condorcet_winner V A p a'} = {a}"
proof (safe)
  fix a' :: "'a"
  assume "condorcet_winner V A p a'"
  thus "a' = a"
    using assms cond_winner_unique_eq
    by metis
next
  show "a \<in> A"
    using assms
    unfolding condorcet_winner.simps
    by (metis (no_types))
next
  show "condorcet_winner V A p a"
    using assms
    by presburger
qed

lemma cond_winner_unique_2:
  fixes
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    "condorcet_winner V A p a" and
    "b \<noteq> a"
  shows "\<not> condorcet_winner V A p b"
  using cond_winner_unique_eq assms
  by metis

subsection \<open>Limited Profile\<close>

text \<open>
  This function restricts a profile p to a set A of alternatives and
  a set V of voters s.t. voters outside of V do not have any preferences or
  do not cast a vote.
  This keeps all of A's preferences.
\<close>

fun limit_profile :: "'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile" where
  "limit_profile A p = (\<lambda> v. limit A (p v))"

lemma limit_prof_trans:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    C :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B"
  shows "limit_profile C p = limit_profile C (limit_profile B p)"
  using assms
  by auto

lemma limit_profile_sound:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    profile: "profile V B p" and
    subset: "A \<subseteq> B"
  shows "profile V A (limit_profile A p)"
proof -
  have "\<forall> v \<in> V. linear_order_on A (limit A (p v))"
    using profile subset limit_presv_lin_ord
    unfolding profile_def
    by metis
  hence "\<forall> v \<in> V. linear_order_on A ((limit_profile A p) v)"
    by simp
  thus ?thesis
    unfolding profile_def
    by simp
qed

(* have limit_prof_simp: "limit_profile A p = map (limit A) p"
    by simp
  obtain n :: "nat" where
    prof_limit_n: "n < length (limit_profile A p) \<longrightarrow>
            linear_order_on A (limit_profile A p!n) \<longrightarrow> profile A (limit_profile A p)"
    using prof_is_lin_ord
    by metis
  have prof_n_lin_ord: "\<forall> n < length p. linear_order_on B (p!n)"
    using prof_is_lin_ord profile
    by simp
  have prof_length: "length p = length (map (limit A) p)"
    by simp
  have "n < length p \<longrightarrow> linear_order_on B (p!n)"
    using prof_n_lin_ord
    by simp
  thus "profile A V (limit_profile A p)"
    using prof_length prof_limit_n limit_prof_simp limit_presv_lin_ord nth_map subset
    by (metis (no_types)) *)

subsection \<open>Lifting Property\<close>

definition equiv_prof_except_a :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow>
        ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv_prof_except_a V A p p' a \<equiv>
    profile V A p \<and> profile V A p' \<and> a \<in> A \<and>
      (\<forall> v \<in> V. equiv_rel_except_a A (p v) (p' v) a)"
(* profile or finite_profile or finite A? [previously finite_profile was used] *)

text \<open>
  An alternative gets lifted from one profile to another iff
  its ranking increases in at least one ballot, and nothing else changes.
\<close>

definition lifted :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted V A p p' a \<equiv>
    finite_profile V A p \<and> finite_profile V A p' \<and> a \<in> A
      \<and> (\<forall> v \<in> V. \<not> Preference_Relation.lifted A (p v) (p' v) a \<longrightarrow> (p v) = (p' v))
      \<and> (\<exists> v \<in> V. Preference_Relation.lifted A (p v) (p' v) a)"

lemma lifted_imp_equiv_prof_except_a:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "lifted V A p p' a"
  shows "equiv_prof_except_a V A p p' a"
proof (unfold equiv_prof_except_a_def, safe)
  from assms
  show "profile V A p"
    unfolding lifted_def
    by metis
next
  from assms
  show "profile V A p'"
    unfolding lifted_def
    by metis
next
  from assms
  show "a \<in> A"
    unfolding lifted_def
    by metis
next
  fix v :: "'v"
  assume "v \<in> V"
  with assms
  show "equiv_rel_except_a A (p v) (p' v) a"
    using lifted_imp_equiv_rel_except_a trivial_equiv_rel
    unfolding lifted_def profile_def
    by (metis (no_types))
qed

(* 
With the current defs of equiv_prof_except_a and limit_prof we can only conclude that
the limited profiles coincide on the given voter set because limit_prof may change the 
profiles everywhere while equiv_prof_except_a only makes statements about the voter set. 
*)
lemma negl_diff_imp_eq_limit_prof:
  fixes
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    change: "equiv_prof_except_a V A' p q a" and
    subset: "A \<subseteq> A'" and
    not_in_A: "a \<notin> A"
  shows "\<forall> v \<in> V. (limit_profile A p) v = (limit_profile A q) v"
proof (clarify)
  fix
    v :: 'v
  assume "v \<in> V"
  hence "equiv_rel_except_a A' (p v) (q v) a"
    using change equiv_prof_except_a_def
    by metis
  hence "limit A (p v) = limit A (q v)"
    using not_in_A negl_diff_imp_eq_limit subset
    by metis
  thus "limit_profile A p v = limit_profile A q v"
    by simp
qed

lemma limit_prof_eq_or_lifted:
  fixes
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    lifted_a: "lifted V A' p p' a" and
    subset: "A \<subseteq> A'"
  shows "(\<forall> v \<in> V. limit_profile A p v = limit_profile A p' v) \<or>
            lifted V A (limit_profile A p) (limit_profile A p') a"
proof (cases)
  assume a_in_A: "a \<in> A"
  have "\<forall> v \<in> V. (Preference_Relation.lifted A' (p v) (p' v) a \<or> (p v) = (p' v))"
    using lifted_a
    unfolding lifted_def
    by metis
  hence one:
    "\<forall> v \<in> V.
         (Preference_Relation.lifted A (limit A (p v)) (limit A (p' v)) a \<or>
           (limit A (p v)) = (limit A (p' v)))"
    using limit_lifted_imp_eq_or_lifted subset
    by metis
  thus ?thesis
  proof (cases)
    assume "\<forall> v \<in> V. (limit A (p v)) = (limit A (p' v))"
    thus ?thesis
      by simp
  next
    assume forall_limit_p_q:
      "\<not> (\<forall> v \<in> V. (limit A (p v)) = (limit A (p' v)))"
    let ?p = "limit_profile A p"
    let ?q = "limit_profile A p'"
    have "profile V A ?p \<and> profile V A ?q"
      using lifted_a limit_profile_sound subset
      unfolding lifted_def
      by metis
    moreover have
      "\<exists> v \<in> V. Preference_Relation.lifted A (?p v) (?q v) a"
      using forall_limit_p_q lifted_a limit_profile.simps one
      unfolding lifted_def
      by (metis (no_types, lifting))
    moreover have
      "\<forall> v \<in> V. (\<not> Preference_Relation.lifted A (?p v) (?q v) a) \<longrightarrow> (?p v) = (?q v)"
      using lifted_a limit_profile.simps one
      unfolding lifted_def
      by metis
    ultimately have "lifted V A ?p ?q a"
      using a_in_A lifted_a rev_finite_subset subset
      unfolding lifted_def
      by (metis (no_types, lifting))
    thus ?thesis
      by simp
  qed
next
  assume "a \<notin> A"
  thus ?thesis
    using lifted_a negl_diff_imp_eq_limit_prof subset lifted_imp_equiv_prof_except_a
    by metis
qed

end
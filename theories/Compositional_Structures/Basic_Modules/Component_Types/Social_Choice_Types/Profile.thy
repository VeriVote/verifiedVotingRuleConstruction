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
          Auxiliary_Lemmas
          "HOL-Library.Extended_Nat"
          "HOL-Combinatorics.Permutations"
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
  a set of eligible alternatives, and a corresponding profile.
\<close>

type_synonym ('a, 'v) Profile = "'v \<Rightarrow> ('a Preference_Relation)"

type_synonym ('a, 'v) Election = "'a set \<times> 'v set \<times> ('a, 'v) Profile"

fun alternatives_\<E> :: "('a, 'v) Election \<Rightarrow> 'a set" where
  "alternatives_\<E> E = fst E"

fun voters_\<E> :: "('a, 'v) Election \<Rightarrow> 'v set" where
  "voters_\<E> E = fst (snd E)"

fun profile_\<E> :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Profile" where
  "profile_\<E> E = snd (snd E)"

fun election_equality :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election \<Rightarrow> bool" where
  "election_equality (A, V, p) (A', V', p') =
        (A = A' \<and> V = V' \<and> (\<forall> v \<in> V. p v = p' v))"

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
  "finite_election E \<equiv> finite_profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)"

definition finite_elections_\<V> :: "('a, 'v) Election set" where
  "finite_elections_\<V> = {E :: ('a, 'v) Election. finite (voters_\<E> E)}"

definition finite_elections :: "('a, 'v) Election set" where
  "finite_elections = {E :: ('a, 'v) Election. finite_election E}"

definition valid_elections :: "('a,'v) Election set" where
  "valid_elections = {E. profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)}"

\<comment> \<open>This function subsumes elections with fixed alternatives, finite voters, and
    a default value for the profile value on non-voters.\<close>
fun elections_\<A> :: "'a set \<Rightarrow> ('a, 'v) Election set" where
  "elections_\<A> A =
        valid_elections
      \<inter> {E. alternatives_\<E> E = A \<and> finite (voters_\<E> E)
            \<and> (\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {})}"

\<comment> \<open>Here, we count the occurrences of a ballot in an election,
    i.e., how many voters specifically chose that exact ballot.\<close>
fun vote_count :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election \<Rightarrow> nat" where
  "vote_count p E = card {v \<in> (voters_\<E> E). (profile_\<E> E) v = p}"

subsection \<open>Vote Count\<close>

lemma vote_count_sum:
  fixes E :: "('a, 'v) Election"
  assumes
    "finite (voters_\<E> E)" and
    "finite (UNIV::('a \<times> 'a) set)"
  shows "sum (\<lambda> p. vote_count p E) UNIV = card (voters_\<E> E)"
proof (unfold vote_count.simps)
  have "\<forall> p. finite {v \<in> voters_\<E> E. profile_\<E> E v = p}"
    using assms
    by force
  moreover have
    "disjoint {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    unfolding disjoint_def
    by blast
  moreover have partition:
    "voters_\<E> E = \<Union> {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    using Union_eq[of "{{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"]
    by blast
  ultimately have card_eq_sum':
    "card (voters_\<E> E) =
        sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    using card_Union_disjoint[of
            "{{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"]
    by auto
  have "finite {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    using partition assms
    by (simp add: finite_UnionD)
  moreover have
    "{{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV} =
        {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
      \<union> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"
    by blast
  moreover have
    "{} =
        {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
      \<inter> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"
    by blast
  ultimately have
    "sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV} =
        sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
      + sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"
    using sum.union_disjoint[of
            "{{v \<in> voters_\<E> E. profile_\<E> E v = p}
                | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
            "{{v \<in> voters_\<E> E. profile_\<E> E v = p}
                | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"]
    by simp
  moreover have
    "\<forall> X \<in> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}.
        card X = 0"
    using card_eq_0_iff
    by fastforce
  ultimately have card_eq_sum:
    "card (voters_\<E> E) =
        sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    using card_eq_sum'
    by simp
  have
    "inj_on (\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p})
        {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    unfolding inj_on_def
    by blast
  moreover have
    "(\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p})
            ` {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
        \<subseteq> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
              | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    by blast
  moreover have
    "(\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p})
            ` {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
        \<supseteq> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
              | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    by blast
  ultimately have
    "bij_betw (\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p})
            {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
        {{v \<in> voters_\<E> E. profile_\<E> E v = p}
          | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    unfolding bij_betw_def
    by simp
  hence sum_rewrite:
    "(\<Sum> x \<in> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}.
            card {v \<in> voters_\<E> E. profile_\<E> E v = x}) =
        sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    using sum_comp[of
            "\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p}"
            "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
            "{{v \<in> voters_\<E> E. profile_\<E> E v = p}
                | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
            "card"]
    unfolding comp_def
    by simp
  have "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}
        \<inter> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}} = {}"
    by blast
  moreover have
    "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}
        \<union> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}} = UNIV"
    by blast
  ultimately have
    "(\<Sum> p \<in> UNIV. card {v \<in> voters_\<E> E. profile_\<E> E v = p}) =
        (\<Sum> x \<in> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}.
          card {v \<in> voters_\<E> E. profile_\<E> E v = x})
      + (\<Sum> x \<in> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}.
          card {v \<in> voters_\<E> E. profile_\<E> E v = x})"
    using assms
          sum.union_disjoint[of
            "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"
            "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"]
    using Finite_Set.finite_set add.commute finite_Un
    by (metis (mono_tags, lifting))
  moreover have
    "\<forall> x \<in> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}.
        card {v \<in> voters_\<E> E. profile_\<E> E v = x} = 0"
    using card_eq_0_iff
    by fastforce
  ultimately show
    "(\<Sum> p \<in> UNIV. card {v \<in> voters_\<E> E. profile_\<E> E v = p}) =
        card (voters_\<E> E)"
    using card_eq_sum sum_rewrite
    by simp
qed

subsection \<open>Voter Permutations\<close>

text \<open>
  A common action of interest on elections is renaming the voters,
  e.g., when talking about anonymity.
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
  assume "v' \<in> V'"
  moreover have "V' = \<pi> ` V"
    using renamed
    by simp
  ultimately have "((the_inv \<pi>) v') \<in> V"
    using UNIV_I bij bij_is_inj bij_is_surj
          f_the_inv_into_f inj_image_mem_iff
    by metis
  thus "linear_order_on A (q v')"
    using renamed bij prof
    unfolding profile_def
    by simp
qed

lemma rename_finite:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    "finite_profile V A p" and
    "(A, V', q) = rename \<pi> (A, V, p)" and
    "bij \<pi>"
  shows "finite_profile V' A q"
  using assms
proof (safe)
  show "finite V'"
    using assms
    by simp
next
  show "profile V' A q"
    using assms rename_sound
    by metis
qed

lemma rename_finite':
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    "finite V" and
    "(A, V', q) = rename \<pi> (A, V, p)" and
    "bij \<pi>"
  shows "finite V'"
  using assms 
  by simp

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
    using assms surj_def inj_on_the_inv_into surj_imp_inv_eq the_inv_f_f
    unfolding bij_betw_def
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
proof (unfold inj_def split_paired_All rename.simps, safe)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile" and
    v :: "'v"
  assume
    "p \<circ> the_inv \<pi> = p' \<circ> the_inv \<pi>" and
    "\<pi> ` V = \<pi> ` V'"
  thus
    "v \<in> V \<Longrightarrow> v \<in> V'" and
    "v \<in> V' \<Longrightarrow> v \<in> V" and
    "p = p'"
    using assms
    by (metis bij_betw_imp_inj_on inj_image_eq_iff,
        metis bij_betw_imp_inj_on inj_image_eq_iff,
        metis bij_betw_the_inv_into bij_is_surj surj_fun_eq)
qed

lemma rename_surj:
  fixes \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows
    on_valid_elections: "rename \<pi> ` valid_elections = valid_elections" and
    on_finite_elections: "rename \<pi> ` finite_elections = finite_elections"
proof (safe)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  assume valid: "(A, V, p) \<in> valid_elections"
  hence "rename (the_inv \<pi>) (A, V, p) \<in> valid_elections"
    using assms bij_betw_the_inv_into rename_sound
    unfolding valid_elections_def
    by fastforce
  thus "(A, V, p) \<in> rename \<pi> ` valid_elections"
    using assms image_eqI rename_inv
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
  hence "rename (the_inv \<pi>) (A, V, p) \<in> finite_elections"
    using assms bij_betw_the_inv_into rename_finite
    unfolding finite_elections_def
    by fastforce
  thus "(A, V, p) \<in> rename \<pi> ` finite_elections"
    using assms image_eqI rename_inv
    by metis
  assume "(A', V', p') = rename \<pi> (A, V, p)"
  thus "(A', V', p') \<in> finite_elections"
    using rename_sound finite assms
    unfolding finite_elections_def
    by fastforce
qed

subsection \<open>List Representation for Ordered Voters\<close>

text \<open>
  A profile on a voter set that has a natural order can be viewed as a list of ballots.
\<close>

fun to_list :: "'v::linorder set \<Rightarrow> ('a, 'v) Profile
                  \<Rightarrow> ('a Preference_Relation) list" where
  "to_list V p = (if (finite V)
                    then (map p (sorted_list_of_set V))
                    else [])"

lemma map2_helper:
  fixes
    f :: "'x \<Rightarrow> 'y \<Rightarrow> 'z" and
    g :: "'x \<Rightarrow> 'x" and
    h :: "'y \<Rightarrow> 'y" and
    l :: "'x list" and
    l' :: "'y list"
  shows "map2 f (map g l) (map h l') = map2 (\<lambda> x y. f (g x) (h y)) l l'"
proof -
  have "map2 f (map g l) (map h l') =
          map (\<lambda> (x, y). f x y) (map (\<lambda> (x, y). (g x, h y)) (zip l l'))"
    using zip_map_map
    by metis
  also have "\<dots> = map2 (\<lambda> x y. f (g x) (h y)) l l'"
    by auto
  finally show ?thesis
    by presburger
qed

lemma to_list_simp:
  fixes
    i :: "nat" and
    V :: "'v::linorder set" and
    p :: "('a, 'v) Profile"
  assumes "i < card V"
  shows "(to_list V p)!i = p ((sorted_list_of_set V)!i)"
proof -
  have "(to_list V p)!i = (map p (sorted_list_of_set V))!i"
    by simp
  also have "\<dots> = p ((sorted_list_of_set V)!i)"
    using assms
    by simp
  finally show ?thesis
    by presburger
qed

lemma to_list_comp:
  fixes
    V :: "'v::linorder set" and
    p :: "('a, 'v) Profile" and
    f :: "'a rel \<Rightarrow> 'a rel"
  shows "to_list V (f \<circ> p) = map f (to_list V p)"
  by simp

lemma set_card_upper_bound:
  fixes
    i :: "nat" and
    V :: "nat set"
  assumes
    fin_V: "finite V" and
    bound_v: "\<forall> v \<in> V. v < i"
  shows "card V \<le> i"
proof (cases "V = {}")
  case True
  thus ?thesis
    by simp
next
  case False
  moreover with fin_V
  have "Max V \<in> V"
    by simp
  ultimately show ?thesis
    using assms Suc_leI card_le_Suc_Max order_trans
    by metis
qed

lemma sorted_list_of_set_nth_equals_card:
  fixes
    V :: "'v :: linorder set" and
    x :: "'v"
  assumes
    fin_V: "finite V" and
    x_V: "x \<in> V"
  shows "sorted_list_of_set V!(card {v \<in> V. v < x}) = x"
proof -
  let ?c = "card {v \<in> V. v < x}" and
      ?set = "{v \<in> V. v < x}"
  have "\<forall> v \<in> V. \<exists> n. n < card V \<and> (sorted_list_of_set V!n) = v"
    using length_sorted_list_of_set sorted_list_of_set_unique in_set_conv_nth fin_V
    by metis
  then obtain \<phi> :: "'v \<Rightarrow> nat" where
    index_\<phi>: "\<forall> v \<in> V. \<phi> v < card V \<and> (sorted_list_of_set V!(\<phi> v)) = v"
    by metis
  \<comment> \<open>\<open>\<phi> x = ?c\<close>, i.e., \<open>\<phi> x \<ge> ?c\<close> and \<open>\<phi> x \<le> ?c\<close>\<close>
  let ?i = "\<phi> x"
  have inj_\<phi>: "inj_on \<phi> V"
    using inj_onI index_\<phi>
    by metis
  have "\<forall> v \<in> V. \<forall> v' \<in> V. v < v' \<longrightarrow> \<phi> v < \<phi> v'"
    using leD linorder_le_less_linear sorted_list_of_set_unique
          sorted_sorted_list_of_set sorted_nth_mono fin_V index_\<phi>
    by metis
  hence "\<forall> j \<in> {\<phi> v | v. v \<in> ?set}. j < ?i"
    using x_V
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
  finally have geq: "?c \<le> ?i"
    by simp
  have sorted_\<phi>:
    "\<forall> i < card V. \<forall> j < card V. i < j
        \<longrightarrow> (sorted_list_of_set V!i) < (sorted_list_of_set V!j)"
    by (simp add: sorted_wrt_nth_less)
  have leq: "?i \<le> ?c"
  proof (rule ccontr, cases "?c < card V")
    case True
    let ?A = "\<lambda> j. {sorted_list_of_set V!j}"
    assume "\<not> ?i \<le> ?c"
    hence "?c < ?i"
      by simp
    hence "\<forall> j \<le> ?c. sorted_list_of_set V!j \<in> V \<and> sorted_list_of_set V!j < x"
      using sorted_\<phi> geq index_\<phi> x_V fin_V set_sorted_list_of_set
            length_sorted_list_of_set nth_mem order.strict_trans1
      by (metis (mono_tags, lifting))
    hence "{sorted_list_of_set V!j | j. j \<le> ?c} \<subseteq> {v \<in> V. v < x}"
      by blast
    also have "{sorted_list_of_set V!j | j. j \<le> ?c} =
                  {sorted_list_of_set V!j | j. j \<in> {0 ..< (?c + 1)}}"
      using add.commute
      by auto
    also have "{sorted_list_of_set V!j | j. j \<in> {0 ..< (?c + 1)}} =
                  (\<Union> j \<in> {0 ..< (?c + 1)}. {sorted_list_of_set V!j})"
      by blast
    finally have subset: "(\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) \<subseteq> {v \<in> V. v < x}"
      by simp
    have "\<forall> i \<le> ?c. \<forall> j \<le> ?c.
              i \<noteq> j \<longrightarrow> sorted_list_of_set V!i \<noteq> sorted_list_of_set V!j"
      using True
      by (simp add: nth_eq_iff_index_eq)
    hence "\<forall> i \<in> {0 ..< (?c + 1)}. \<forall> j \<in> {0 ..< (?c + 1)}.
              (i \<noteq> j \<longrightarrow> {sorted_list_of_set V!i} \<inter> {sorted_list_of_set V!j} = {})"
      by fastforce
    hence "disjoint_family_on ?A {0 ..< (?c + 1)}"
      unfolding disjoint_family_on_def
      by simp
    moreover have "\<forall> j \<in> {0 ..< (?c + 1)}. card (?A j) = 1"
      by simp
    ultimately have
      "card (\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) = (\<Sum> j \<in> {0 ..< (?c + 1)}. 1)"
      using card_UN_disjoint'
      by fastforce
    hence "card (\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) = ?c + 1"
      by simp
    hence "?c + 1 \<le> ?c"
      using subset card_mono fin_img
      by (metis (no_types, lifting))
    thus False
      by simp
  next
    case False
    thus False
      using x_V index_\<phi> geq order_le_less_trans
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
  assumes "bij \<pi>"
  shows
    "let \<phi> = (\<lambda> i. card {v \<in> \<pi> ` V. v < \<pi> ((sorted_list_of_set V)!i)})
      in (to_list V p) = permute_list \<phi> (to_list (\<pi> ` V) (\<lambda> x. p (the_inv \<pi> x)))"
proof (cases "finite V")
  case False
  \<comment> \<open>If \<open>V\<close> is infinite, both lists are empty.\<close>
  hence "to_list V p = []"
    by simp
  moreover have "infinite (\<pi> ` V)"
    using False assms bij_betw_finite bij_betw_subset top_greatest
    by metis
  hence "to_list (\<pi> ` V) (\<lambda> x. p (the_inv \<pi> x)) = []"
    by simp
  ultimately show ?thesis
    by simp
next
  case True
  let
    ?q = "\<lambda> x. p (the_inv \<pi> x)" and
    ?img = "\<pi> ` V" and
    ?n = "length (to_list V p)" and
    ?perm = "\<lambda> i. card {v \<in> \<pi> ` V. v < \<pi> ((sorted_list_of_set V)!i)}"
    \<comment> \<open>These are auxiliary statements equating everything with \<open>?n\<close>.\<close>
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
    \<comment> \<open>The lists have equal lengths.\<close>
    show
      "length (to_list V p) =
          length (map
            (\<lambda> i. to_list ?img ?q!(card {v \<in> ?img.
                v < \<pi> (sorted_list_of_set V!i)}))
              [0 ..< length (to_list ?img ?q)])"
      using eq_length
      by simp
  next
    \<comment> \<open>The \<open>i\<close>th entries of the lists coincide.\<close>
    fix i :: "nat"
    assume in_bnds: "i < ?n"
    let ?c = "card {v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}"
    have "map (\<lambda> i. (to_list ?img ?q)!?c) [0 ..< ?n]!i =
            p ((sorted_list_of_set V)!i)"
    proof -
      have "\<forall> v. v \<in> ?img \<longrightarrow> {v' \<in> ?img. v' < v} \<subseteq> ?img - {v}"
        by blast
      moreover have elem_of_img: "\<pi> (sorted_list_of_set V!i) \<in> ?img"
        using True in_bnds image_eqI nth_mem card_length_V
              length_sorted_list_of_set set_sorted_list_of_set
        by metis
      ultimately have
        "{v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}
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
        map (\<lambda> i. (to_list ?img ?q)!(card {v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}))
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
  assumes "finite V"
  shows "prefer_count V p a b \<le> card V"
  using assms
  by (simp add: card_mono)

lemma set_compr:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> 'a set"
  shows "{f x | x. x \<in> A} = f ` A"
  by blast

lemma pref_count_set_compr:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  shows "{prefer_count V p a a' | a'. a' \<in> A - {a}} =
            (prefer_count V p a) ` (A - {a})"
  by blast

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
  have "\<forall> v \<in> V. \<not> (let r = (p v) in (b \<preceq>\<^sub>r a)) \<longrightarrow> (let r = (p v) in (a \<preceq>\<^sub>r b))"
    using a_in_A b_in_A prof lin_ord_imp_connex
    unfolding profile_def connex_def
    by metis
  moreover have "\<forall> v \<in> V. ((b, a) \<in> (p v) \<longrightarrow> (a, b) \<notin> (p v))"
    using antisymD neq lin_imp_antisym prof
    unfolding profile_def
    by metis
  ultimately have
    "{v \<in> V. (let r = (p v) in (b \<preceq>\<^sub>r a))} =
        V - {v \<in> V. (let r = (p v) in (a \<preceq>\<^sub>r b))}"
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
proof (cases "finite V")
  case True
  moreover have
    nat1: "prefer_count V p c a \<in> \<nat>" and
    nat2: "prefer_count V p b c \<in> \<nat>"
    unfolding Nats_def
    using True of_nat_eq_enat
    by (simp, simp)
  moreover have smaller: "prefer_count V p c a \<le> card V"
    using True prof pref_count_voter_set_card
    by metis
  moreover have
    "prefer_count V p a c = card V - (prefer_count V p c a)" and
    pref_count_b_eq:
    "prefer_count V p c b = card V - (prefer_count V p b c)"
    using True pref_count prof c_in_A
    by (metis (no_types, opaque_lifting) a_in_A a_neq_c,
        metis (no_types, opaque_lifting) b_in_A c_neq_b)
  hence "card V - (prefer_count V p b c) + (prefer_count V p c a)
      \<le> card V - (prefer_count V p c a) + (prefer_count V p c a)"
    using pref_count_b_eq pref_count_ineq
    by simp
  ultimately show ?thesis
    by simp
next
  case False
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
  shows "\<not> wins V b p a"
  using assms
  by simp

text \<open>
  Having alternative \<open>a\<close> win against \<open>b\<close> implies that \<open>b\<close> does not win against \<open>a\<close>.
\<close>

lemma wins_antisym:
  fixes
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    b :: "'a" and
    V :: "'v set"
  assumes "wins V a p b" \<comment> \<open>This already implies that \<open>V\<close> is finite.\<close>
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
  hence "wins V b p a"
    using insert_Diff insert_iff assms
    by simp
  hence "\<not> wins V a p b"
    by (simp add: wins_antisym)
  moreover have "wins V a p b"
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
    "profile V B p" and
    "A \<subseteq> B"
  shows "profile V A (limit_profile A p)"
proof (unfold profile_def)
  have "\<forall> v \<in> V. linear_order_on A (limit A (p v))"
    using assms limit_presv_lin_ord
    unfolding profile_def
    by metis
  thus "\<forall> v \<in> V. linear_order_on A ((limit_profile A p) v)"
    by simp
qed

subsection \<open>Lifting Property\<close>

definition equiv_prof_except_a :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow>
        ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv_prof_except_a V A p p' a \<equiv>
    profile V A p \<and> profile V A p' \<and> a \<in> A \<and>
      (\<forall> v \<in> V. equiv_rel_except_a A (p v) (p' v) a)"

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
  show
    "profile V A p" and
    "profile V A p'" and
    "a \<in> A"
    using assms
    unfolding lifted_def
    by (metis, metis, metis)
next
  fix v :: "'v"
  assume "v \<in> V"
  thus "equiv_rel_except_a A (p v) (p' v) a"
    using assms lifted_imp_equiv_rel_except_a trivial_equiv_rel
    unfolding lifted_def profile_def
    by (metis (no_types))
qed

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
  \<comment> \<open>With the current definitions of \<open>equiv_prof_except_a\<close> and \<open>limit_prof\<close>, we can
      only conclude that the limited profiles coincide on the given voter set, since
      \<open>limit_prof\<close> may change the profiles everywhere, while \<open>equiv_prof_except_a\<close>
      only makes statements about the voter set.\<close>
proof (clarify)
  fix
    v :: 'v
  assume "v \<in> V"
  hence "equiv_rel_except_a A' (p v) (q v) a"
    using change equiv_prof_except_a_def
    by metis
  thus "limit_profile A p v = limit_profile A q v"
    using subset not_in_A negl_diff_imp_eq_limit
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
  shows "(\<forall> v \<in> V. limit_profile A p v = limit_profile A p' v)
        \<or> lifted V A (limit_profile A p) (limit_profile A p') a"
proof (cases "a \<in> A")
  case True
  have "\<forall> v \<in> V. Preference_Relation.lifted A' (p v) (p' v) a \<or> (p v) = (p' v)"
    using lifted_a
    unfolding lifted_def
    by metis
  hence one:
    "\<forall> v \<in> V.
         Preference_Relation.lifted A (limit A (p v)) (limit A (p' v)) a \<or>
           (limit A (p v)) = (limit A (p' v))"
    using limit_lifted_imp_eq_or_lifted subset
    by metis
  thus ?thesis
  proof (cases "\<forall> v \<in> V. limit A (p v) = limit A (p' v)")
    case True
    thus ?thesis
      by simp
  next
    case False
    let ?p = "limit_profile A p"
    let ?q = "limit_profile A p'"
    have
      "profile V A ?p" and
      "profile V A ?q"
      using lifted_a subset limit_profile_sound
      unfolding lifted_def
      by (safe, safe)
    moreover have
      "\<exists> v \<in> V. Preference_Relation.lifted A (?p v) (?q v) a"
      using False one
      unfolding limit_profile.simps
      by (metis (no_types, lifting))
    ultimately have "lifted V A ?p ?q a"
      using True lifted_a one rev_finite_subset subset
      unfolding lifted_def limit_profile.simps
      by (metis (no_types, lifting))
    thus ?thesis
      by simp
  qed
next
  case False
  thus ?thesis
    using lifted_a negl_diff_imp_eq_limit_prof subset lifted_imp_equiv_prof_except_a
    by metis
qed

end
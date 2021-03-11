(*  File:       Electoral_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Module\<close>

theory Electoral_Module
  imports Preference_Relation
begin

text
\<open>Electoral modules are the principal component type of the composable modules
voting framework, as they are a generalization of voting rules in the sense of
social choice functions.
These are only the types used for electoral modules. Further restrictions are
encompassed by the electoral-module predicate.

An electoral module does not need to make final decisions for all alternatives,
but can instead defer the decision for some or all of them to other modules.
Hence, electoral modules partition the received (possibly empty) set of
alternatives into elected, rejected and deferred alternatives. In particular,
any of those sets, e.g., the set of winning (elected) alternatives, may also
be left empty, as long as they collectively still hold all the received
alternatives. Just like a voting rule, an electoral module also receives a
profile which holds the voters’ preferences, which, unlike a voting rule,
consider only the (sub-)set of alternatives that the module receives.\<close>

subsection \<open>Definition\<close>

(*A profile contains one ballot for each voter.*)
type_synonym 'a Profile = "('a Preference_Relation) list"

(*
   A result contains three sets of alternatives:
   elected, rejected, and deferred alternatives.
*)
type_synonym 'a Result = "'a set * 'a set * 'a set"

(*An electoral module maps a set of alternatives and a profile to a result.*)
type_synonym 'a Electoral_Module = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result"

subsection \<open>Preference Profile\<close>

(*
   A profile on a finite set of alternatives A contains only ballots that are
   linear orders on A.
*)
definition profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where 
  "profile A p \<equiv> \<forall>i::nat. i < size p \<longrightarrow> linear_order_on A (p!i)"

lemma profile_set : "profile A p \<equiv> (\<forall>b \<in> (set p). linear_order_on A b)"
  by (simp add: all_set_conv_all_nth profile_def)

abbreviation finite_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "finite_profile A p \<equiv> finite A \<and> profile A p"

subsection \<open>Preference Counts and Comparisons\<close>

(*
   The win count for an alternative a in a profile p is
   the amount of ballots in p that rank alternative a in first position.
*)
fun win_count :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count p a =
    card {i::nat. i < size p \<and> above (p!i) a = {a}}"

fun win_count_code :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count_code Nil a = 0" |
  "win_count_code (p#ps) a =
      (if (above p a = {a}) then 1 else 0) + win_count_code ps a"

fun prefer_count :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count p x y = 
      card {i::nat. i < size p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"

fun prefer_count_code :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count_code Nil x y = 0" |
  "prefer_count_code (p#ps) x y =
      (if y \<preceq>\<^sub>p x then 1 else 0) + prefer_count_code ps x y"

lemma set_compr: "{ f x | x . x \<in> S } = f ` S"
  by auto

lemma pref_count_set_compr: "{prefer_count p x y | y . y \<in> A-{x}} =
          (prefer_count p x) ` (A-{x})"
  by auto

lemma pref_count:
  assumes prof: "profile A p"
  assumes x_in_A: "x \<in> A"
  assumes y_in_A: "y \<in> A"
  assumes neq: "x \<noteq> y"
  shows "prefer_count p x y = (size p) - (prefer_count p y x)"
proof -
  have 00: "card {i::nat. i < size p} = size p"
    by simp
  have 10:
    "{i::nat. i < size p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))} =
        {i::nat. i < size p} -
          {i::nat. i < size p \<and> \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"
    by auto
  have 0: "\<forall> i::nat . i < size p \<longrightarrow> linear_order_on A (p!i)"
    using prof profile_def
    by metis
  hence "\<forall> i::nat . i < size p \<longrightarrow> connex A (p!i)"
    by (simp add: lin_ord_imp_connex)
  hence 1: "\<forall> i::nat . i < size p \<longrightarrow>
              \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x)) \<longrightarrow> (let r = (p!i) in (x \<preceq>\<^sub>r y))"
    using connex_def x_in_A y_in_A
    by metis
  from 0 have
    "\<forall> i::nat . i < size p \<longrightarrow> antisym  (p!i)"
    using lin_imp_antisym
    by metis
  hence "\<forall> i::nat . i < size p \<longrightarrow>
          ((let r = (p!i) in (y \<preceq>\<^sub>r x)) \<longrightarrow> \<not> (let r = (p!i) in (x \<preceq>\<^sub>r y)))"
    using antisymD neq is_less_preferred_than.simps
    by metis
  with 1 have
    "\<forall> i::nat . i < size p \<longrightarrow>
      \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x)) = (let r = (p!i) in (x \<preceq>\<^sub>r y))"
    by metis
  hence 2:
    "{i::nat. i < size p \<and> \<not> (let r = (p!i) in (y \<preceq>\<^sub>r x))} =
        {i::nat. i < size p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))}"
    by metis
  hence 20:
    "{i::nat. i < size p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))} =
        {i::nat. i < size p} - {i::nat. i < size p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))}"
    using "10" "2"
    by simp 
  have "{i::nat. i < size p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))} \<subseteq> {i::nat. i < size p}"
    by (simp add: Collect_mono)
  hence 30:
    "card ({i::nat. i < size p} -
        {i::nat. i < size p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))}) =
      (card {i::nat. i < size p}) -
        card({i::nat. i < size p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))})"
    by (simp add: card_Diff_subset)
  have "prefer_count p x y =
          card {i::nat. i < size p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"
    by simp
  also have
    "... = card({i::nat. i < size p} -
            {i::nat. i < size p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))})"
    using "20"
    by simp
  also have
    "... = (card {i::nat. i < size p}) -
              card({i::nat. i < size p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r y))})"
    using "30"
    by metis
  also have
    "... = size p - (prefer_count p y x)"
    by simp
  finally show ?thesis
    by (simp add: "20" "30")
qed

lemma pref_count_sym:
    assumes p1: "prefer_count p a x \<ge> prefer_count p x b"
    assumes prof: "profile A p"
    assumes a_in_A: "a \<in> A"
    assumes b_in_A: "b \<in> A"
    assumes x_in_A: "x \<in> A"
    assumes neq1: "a \<noteq> x"
    assumes neq2: "x \<noteq> b"
    shows "prefer_count p b x \<ge> prefer_count p x a" 
proof -
  from prof a_in_A x_in_A neq1 have 0:
    "prefer_count p a x = (size p) - (prefer_count p x a)"
    using pref_count
    by metis
  moreover from prof x_in_A b_in_A neq2 have 1:
    "prefer_count p x b = (size p) - (prefer_count p b x)"
    using pref_count
    by (metis (mono_tags, lifting))
  hence 2: "(size p) - (prefer_count p x a) \<ge>
              (size p) - (prefer_count p b x)"
    using calculation p1
    by auto
  hence 3: "(prefer_count p x a) - (size p) \<le>
              (prefer_count p b x) - (size p)"
    using a_in_A diff_is_0_eq diff_le_self neq1
          pref_count prof x_in_A
    by (metis (no_types))
  hence "(prefer_count p x a) \<le> (prefer_count p b x)"
    using "1" "3" calculation p1
    by linarith
  thus ?thesis
    by linarith
qed

lemma empty_prof_imp_zero_pref_count:
  assumes "p = []"
  shows "\<forall> x y. prefer_count p x y = 0"
  using assms
  by simp

lemma pref_count_code_incr:
  assumes "prefer_count_code ps x y = n \<and> y \<preceq>\<^sub>p x"
  shows "prefer_count_code (p#ps) x y = n+1"
  using is_less_preferred_than.simps assms
  by simp

lemma pref_count_code_not_smaller_imp_constant:
  assumes "prefer_count_code ps x y = n \<and> \<not>(y \<preceq>\<^sub>p x)"
  shows "prefer_count_code (p#ps) x y = n"
  using is_less_preferred_than.simps assms
  by simp

fun wins :: "'a \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins x p y =
    (prefer_count p x y > prefer_count p y x)"

fun wins_code :: "'a \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins_code x p y =
    (prefer_count_code p x y > prefer_count_code p y x)"

(* Alternative a wins against b implies that b does not win against a. *)
lemma wins_antisym: "wins a p b \<Longrightarrow> \<not> wins b p a"
  by simp

lemma wins_irreflex: "\<not> wins w p w"
  using wins_antisym
  by metis

subsection \<open>Condorcet Winner\<close>

fun condorcet_winner :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner A p w =
      (finite_profile A p \<and>  w \<in> A \<and> (\<forall>x \<in> A - {w} . wins w p x))"

fun condorcet_winner_code :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner_code A p w =
    (finite_profile A p \<and>  w \<in> A \<and>
      (\<forall>x \<in> A - {w} . wins_code w p x))"

lemma cond_winner_unique:
  assumes winner_c: "condorcet_winner A p c" and
          winner_w: "condorcet_winner A p w"
  shows "w = c"
proof (rule ccontr)
  assume
    assumption: "w \<noteq> c"
  from winner_w
  have "wins w p c"
    using assumption condorcet_winner.simps
          insert_Diff insert_iff winner_c
    by metis 
  hence "\<not> wins c p w"
    by (simp add: wins_antisym)
  moreover from winner_c
  have
    c_wins_against_w: "wins c p w"
    using Diff_iff assumption condorcet_winner.simps
          singletonD winner_w
    by metis
  ultimately show False
    by simp
qed

lemma cond_winner_unique2:
  assumes winner: "condorcet_winner A p w" and
          not_w:  "x \<noteq> w" and
          in_A:   "x \<in> A"
        shows "\<not> condorcet_winner A p x"
  using not_w cond_winner_unique winner
  by metis

lemma cond_winner_unique3:
  assumes "condorcet_winner A p w"
  shows "{a \<in> A. condorcet_winner A p a} = {w}"
  using Collect_cong assms condorcet_winner.simps
        singleton_conv cond_winner_unique
  by (metis (mono_tags, lifting))

subsection \<open>Limited Profile\<close>

(*
   This function restricts a profile p to a set A and
   keeps all of A's preferences.
*)
fun limit_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile" where
  "limit_profile A p = map (limit A) p"

lemma limit_prof_trans:
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B" and
    "finite_profile A p"
  shows "limit_profile C p = limit_profile C (limit_profile B p)"
  using assms
  by auto

lemma limit_profile_sound:
  assumes
    profile: "finite_profile S p" and
    subset: "A \<subseteq> S"
  shows "finite_profile A (limit_profile A p)"
  using assms(1) imageE infinite_super limit_presv_lin_ord
        limit_profile.simps set_map subset profile_set
  by (metis (no_types, lifting))

lemma limit_prof_presv_size:
  assumes f_prof: "finite_profile S p" and
          subset:  "A \<subseteq> S"
  shows "size p = size (limit_profile A p)"
  by simp

subsection \<open>Election Result\<close>

(*
   A partition of a set A are pairwise disjoint sets that set_equals_partition A.
   For this specific predicate, we have three disjoint sets in a three-tuple.
*)
fun disjoint3 :: "'a Result \<Rightarrow> bool" where
  "disjoint3 (e, r, d) =
    ((e \<inter> r = {}) \<and>
      (e \<inter> d = {}) \<and>
      (r \<inter> d = {}))"

fun set_equals_partition :: "'a set \<Rightarrow>'a Result \<Rightarrow> bool" where
  "set_equals_partition A (e, r, d) = (e \<union> r \<union> d = A)"

fun well_formed :: "'a set \<Rightarrow> 'a Result \<Rightarrow> bool" where
  "well_formed A result = (disjoint3 result \<and> set_equals_partition A result)"

(*
   Electoral modules partition a given set of alternatives A into a set of
   elected alternatives e, a set of rejected alternatives r, and a set of
   deferred alternatives d, using a profile.
   e, r, and d partition A.
   Electoral modules can be used as voting rules. They can also be composed
   in multiple structures to create more complex electoral modules.
*)
definition electoral_module :: " 'a Electoral_Module \<Rightarrow> bool" where
  "electoral_module m \<equiv> \<forall>A p. finite_profile A p \<longrightarrow> well_formed A (m A p)"

lemma electoral_modI:
  "((\<And>A p. \<lbrakk> finite_profile A p \<rbrakk> \<Longrightarrow> well_formed A (m A p)) \<Longrightarrow>
       electoral_module m)"
  unfolding electoral_module_def
  by auto

(*These three functions return the elect, reject, or defer set of a result.*)
abbreviation elect_r :: "'a Result \<Rightarrow> 'a set" where
  "elect_r r \<equiv> fst r"

abbreviation reject_r :: "'a Result \<Rightarrow> 'a set" where
  "reject_r r \<equiv> fst (snd r)"

abbreviation defer_r :: "'a Result \<Rightarrow> 'a set" where
  "defer_r r \<equiv> snd (snd r)"

(*
   The next three functions take an electoral module and turn it into a
   function only outputting the elect, reject, or defer set respectively.
*)
abbreviation elect ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "elect m A p \<equiv> elect_r (m A p)"

abbreviation reject ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "reject m A p \<equiv> reject_r (m A p)"

abbreviation "defer" ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "defer m A p \<equiv> defer_r (m A p)"

subsection \<open>Auxiliary Definitions\<close>

(*
   "defers n" is true for all electoral modules that defer exactly
   n alternatives, whenever there are n or more alternatives.
*)
definition defers :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "defers n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow>
          card (defer m A p) = n)"

(*
   "rejects n" is true for all electoral modules that reject exactly
   n alternatives, whenever there are n or more alternatives.
*)
definition rejects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (reject m A p) = n)"

(*
   As opposed to "rejects", "eliminates" allows to stop rejecting if no
   alternatives were to remain.
*)
definition eliminates :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (card A > n \<and> finite_profile A p) \<longrightarrow> card (reject m A p) = n)"

(*
   "elects n" is true for all electoral modules that
   elect exactly n alternatives, whenever there are n or more alternatives.
*)
definition elects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "elects n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (elect m A p) = n)"

(*
(*
   An Electoral module m is rejecting iff at least one alternative gets
   rejected when possible
*)
definition rejecting :: "'a Electoral_Module \<Rightarrow> bool" where
  "
  "rejecting m \<equiv> \<forall>A . card A > 1 \<longrightarrow> (\<exists>n . (n > 0 \<and> rejects n m))"

(*WRONG definition, choose `n > card A` and already it is always true.*)
(*An electoral module m is eliminating iff the following holds*)
(*
   If there is at least one alternative that can be rejected,
   at least one alternative gets rejected.
*)
definition eliminating :: "'a Electoral_Module \<Rightarrow> bool" where
  "eliminating m \<equiv>  \<exists> n . (n > 0 \<and> eliminates n m)"
*)

definition prof_contains_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                       'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_contains_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer m A q)"

definition prof_leq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_leq_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> elect m A q)"

definition prof_geq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_geq_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> reject m A q)"

definition mod_contains_result :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
                                      'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "mod_contains_result m n A p a \<equiv>
    electoral_module m \<and> electoral_module n \<and> finite_profile A p \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect n A p) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject n A p) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer n A p)"

subsection \<open>Auxiliary Lemmata\<close>

lemma combine_ele_rej_def:
  assumes
    ele: "elect m A p = e" and
    rej: "reject m A p = r" and
    def: "defer m A p = d"
  shows "m A p = (e, r, d)"
  using def ele rej
  by auto

lemma result_imp_rej: "well_formed A (e, r, d) \<longrightarrow>  A - (e \<union> d) = r"
proof -
  have f1: "\<forall>A Aa. (Aa::'a set) - (A - Aa) = Aa"
    by auto
  hence f2: "\<forall>A Aa Ab. (Ab::'a set) - (Aa - Ab \<union> A) = Ab \<inter> (Ab - A)"
    by (simp add: Diff_Un)
  have f3: "\<forall>A. (A::'a set) - A = {}"
    by simp
  have f4: "\<forall>A Aa Ab. (Ab::'a set) - Aa - A = Ab - (Aa \<union> A)"
    by (simp add: Diff_eq inf_sup_aci(2))
  {
    assume "\<exists>A. r \<union> A - d \<noteq> r \<union> (A - d)"
    hence "r - d \<noteq> r"
      using Un_Diff
      by metis
    hence "\<not> disjoint3 (e, r, d)"
      using Un_Diff_Int disjoint3.simps sup_bot.comm_neutral
      by metis
  }
  moreover
  {
    assume "\<exists>Aa. r \<union> d - Aa \<noteq> A - (e \<union> Aa)"
    {
      assume "\<exists>A. A \<union> d - e \<noteq> A - e \<union> d"
      hence "d - e \<noteq> d"
        using Un_Diff
        by metis
      hence "\<not> disjoint3 (e, r, d)"
        using f1 disjoint3.simps Diff_triv
        by metis
    }
    hence
      "disjoint3 (e, r, d) \<longrightarrow> well_formed A (e, r, d) \<longrightarrow>
          A - (e \<union> d) = r"
      using f4 f3 f2 f1 Un_Diff Un_Diff_Int disjoint3.simps Int_Diff
            well_formed.simps set_equals_partition.simps Diff_cancel
            Int_absorb Int_Un_eq(2) Int_commute Un_commute Un_left_commute
            sup_assoc Un_Int_eq(1) sup_bot_left calculation Un_empty_right
      by metis
  }
  ultimately show ?thesis
    using f3 well_formed.simps sup_bot.comm_neutral
    by (metis (no_types))
qed

lemma par_comp_result_sound:
  assumes
    mod_m: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "well_formed A (m A p)"
  using electoral_module_def mod_m f_prof
  by auto

lemma result_presv_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
proof -
  from e_mod f_prof have "set_equals_partition A (m A p)"
    using electoral_module_def well_formed.simps
    by blast
  hence "set_equals_partition A (elect m A p, reject m A p, defer m A p)"
    by simp
  thus ?thesis
    using set_equals_partition.simps
    by metis
qed

lemma result_disj:
  assumes
    module: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "(elect m A p) \<inter> (reject m A p) = {} \<and>
        (elect m A p) \<inter> (defer m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
  using disjoint3.simps electoral_module_def module
        well_formed.simps prod.exhaust_sel profile
  by metis

lemma elect_in_alts:
  assumes 
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "elect m A p \<subseteq> A"
  using le_supI1 e_mod f_prof result_presv_alts sup_ge1
  by metis

lemma reject_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "reject m A p \<subseteq> A"
  using le_supI1 e_mod f_prof result_presv_alts sup_ge2
  by fastforce

lemma defer_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "defer m A p \<subseteq> A"
  using e_mod f_prof result_presv_alts
  by auto

lemma def_presv_fin_prof:
  assumes module:  "electoral_module m" and
          f_prof: "finite_profile A p"
  shows
    "let new_A = defer m A p in
        finite_profile new_A (limit_profile new_A p)"
  using defer_in_alts infinite_super
        limit_profile_sound module f_prof
  by metis

(*
   An electoral module can never reject, defer or elect more than
   |A| alternatives.
*)
lemma upper_card_bounds_for_result:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows
    "card (elect m A p) \<le> card A \<and>
      card (reject m A p) \<le> card A \<and>
      card (defer m A p) \<le> card A "
  by (simp add: card_mono defer_in_alts elect_in_alts
                e_mod f_prof reject_in_alts)

lemma result_count:
  assumes
    "well_formed A (e, r, d)" and
    "finite A"
  shows "card A = card e + card r + card d"
  using well_formed.simps set_equals_partition.simps
        Int_Un_distrib2 assms card_Un_disjoint
        disjoint3.simps finite_Un sup_bot.right_neutral
  by metis

lemma reject_not_elec_or_def:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "reject m A p = A - (elect m A p) - (defer m A p)"
proof -
  from e_mod f_prof have 0: "well_formed A (m A p)"
    by (simp add: electoral_module_def)
  with e_mod f_prof
    have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
      using result_presv_alts
      by simp
    moreover from 0 have
      "(elect m A p) \<inter> (reject m A p) = {} \<and>
          (reject m A p) \<inter> (defer m A p) = {}"
    using e_mod f_prof result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma elec_and_def_not_rej:
  assumes
    e_mod: "electoral_module m" and 
    f_prof: "finite_profile A p"
  shows "elect m A p \<union> defer m A p = A - (reject m A p)"
proof -
  from e_mod f_prof have 0: "well_formed A (m A p)"
    by (simp add: electoral_module_def)
  with e_mod f_prof
  have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using e_mod well_formed.simps f_prof result_presv_alts
    by blast
  moreover from 0 have
    "(elect m A p) \<inter> (reject m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
    using e_mod f_prof result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma defer_not_elec_or_rej:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "defer m A p = A - (elect m A p) - (reject m A p)"
proof -
  from e_mod f_prof have 0: "well_formed A (m A p)"
    by (simp add: electoral_module_def)
  hence "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using e_mod f_prof result_presv_alts
    by auto
  moreover from 0 have
    "(elect m A p) \<inter> (defer m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
      using e_mod f_prof result_disj
      by blast
  ultimately show ?thesis
    by blast
qed

lemma electoral_mod_defer_elem:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    alternative: "x \<in> A" and
    not_elected: "x \<notin> elect m A p" and
    not_rejected: "x \<notin> reject m A p"
  shows "x \<in> defer m A p"
  using DiffI e_mod f_prof alternative
        not_elected not_rejected
        reject_not_elec_or_def
  by metis

lemma mod_contains_result_comm:
  assumes "mod_contains_result m n A p a"
  shows "mod_contains_result n m A p a"
  using IntI assms electoral_mod_defer_elem empty_iff
        mod_contains_result_def result_disj
  by (smt (verit, ccfv_threshold))

lemma not_rej_imp_elec_or_def:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    alternative: "x \<in> A" and
    not_rejected: "x \<notin> reject m A p"
  shows "x \<in> elect m A p \<or> x \<in> defer m A p"
  using alternative electoral_mod_defer_elem
        e_mod not_rejected f_prof
  by metis

lemma single_elim_imp_red_def_set:
  assumes
    eliminating: "eliminates 1 m" and
    leftover_alternatives: "card A > 1" and
    f_prof: "finite_profile A p"
  shows "defer m A p \<subset> A"
  using Diff_eq_empty_iff Diff_subset card_eq_0_iff defer_in_alts
        eliminates_def eliminating eq_iff leftover_alternatives
        not_one_le_zero f_prof psubsetI reject_not_elec_or_def
  by metis

lemma eq_alts_in_profs_imp_eq_results:
  assumes 
    eq: "\<forall>a \<in> A. prof_contains_result m A p q a" and
    (*for empty A*)
    input: "electoral_module m \<and> finite_profile A p \<and> finite_profile A q"
  shows "m A p = m A q"
proof -
  have "\<forall>a \<in> elect m A p. a \<in> elect m A q"
    using elect_in_alts eq prof_contains_result_def input in_mono
    by metis
  moreover have "\<forall>a \<in> elect m A q. a \<in> elect m A p"
    using contra_subsetD disjoint_iff_not_equal elect_in_alts
          electoral_mod_defer_elem eq prof_contains_result_def input
          result_disj
    by (smt (verit, best))
  moreover have "\<forall>a \<in> reject m A p. a \<in> reject m A q"
    using reject_in_alts eq prof_contains_result_def input in_mono
    by fastforce
  moreover have "\<forall>a \<in> reject m A q. a \<in> reject m A p"
    using contra_subsetD disjoint_iff_not_equal reject_in_alts
          electoral_mod_defer_elem eq prof_contains_result_def
          input result_disj
    by (smt (verit, ccfv_SIG))
  moreover have "\<forall>a \<in> defer m A p. a \<in> defer m A q"
    using defer_in_alts eq prof_contains_result_def input in_mono
    by fastforce
  moreover have "\<forall>a \<in> defer m A q. a \<in> defer m A p"
    using contra_subsetD disjoint_iff_not_equal defer_in_alts
          electoral_mod_defer_elem eq prof_contains_result_def
          input result_disj
    by (smt (verit, best))
  ultimately show ?thesis
    using prod.collapse subsetI subset_antisym
    by metis
qed

lemma eq_def_and_elect_imp_eq:
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p" and
    "finite_profile A q" and
    "elect m A p = elect n A q" and
    "defer m A p = defer n A q"
  shows "m A p = n A q"
proof -
  have "set_equals_partition A ((elect m A p),(reject m A p),(defer m A p))"
    using assms(1) assms(3) result_presv_alts set_equals_partition.simps
    by (metis (mono_tags, hide_lams))
  moreover have
    "disjoint3 ((elect m A p),(reject m A p),(defer m A p))"
    using assms(1) assms(3) electoral_module_def
          well_formed.simps prod.collapse
    by metis
  ultimately have reject_p:
    "reject m A p = A - ((elect m A p) \<union> (defer m A p))"
    using assms(1) assms(3) combine_ele_rej_def
          electoral_module_def result_imp_rej
    by metis
  have
    "set_equals_partition A
      ((elect n A q),(reject n A q),(defer n A q))"
    using assms(2) assms(4) result_presv_alts set_equals_partition.simps
    by (metis (mono_tags, hide_lams))
  moreover have
    "disjoint3 ((elect n A q),(reject n A q),(defer n A q))"
    using assms(2) assms(4) electoral_module_def
          well_formed.simps prod.collapse
    by metis
  ultimately have reject_q:
    "reject n A q = A - ((elect n A q) \<union> (defer n A q))"
    using assms(2) assms(4) combine_ele_rej_def
          electoral_module_def result_imp_rej
    by metis
  from reject_p reject_q show ?thesis
    by (simp add: assms(5) assms(6) prod_eqI)
qed

subsection \<open>Lifting Property\<close>

definition equiv_prof_except_a :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow>
                                        'a \<Rightarrow> bool" where
  "equiv_prof_except_a A p q a \<equiv>
    finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and> size p = size q \<and>
    (\<forall>i::nat.
      i < size p \<longrightarrow>
        Preference_Relation.equiv_rel_except_a A (p!i) (q!i) a)"

(*
   An electoral module is independent of an alternative a iff
   a's ranking does not influence the outcome.
*)
definition indep_of_alt :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "indep_of_alt m A a \<equiv>
    electoral_module m \<and> (\<forall>p q. equiv_prof_except_a A p q a \<longrightarrow> m A p = m A q)"

(*
   An alternative gets lifted from one profile to another iff
   its ranking increases in at least one ballot, and nothing else changes.
*)
definition lifted :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A p q a \<equiv>
    finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and> size p = size q \<and>
    (\<forall>i::nat.
      (i < size p \<and> \<not>Preference_Relation.lifted A (p!i) (q!i) a) \<longrightarrow>
        (p!i) = (q!i)) \<and>
    (\<exists>i::nat. i < size p \<and> Preference_Relation.lifted A (p!i) (q!i) a)"

lemma lifted_imp_equiv_prof_except_a:
  assumes lifted: "lifted A p q a"
  shows "equiv_prof_except_a A p q a"
proof -
  have
    "\<forall>i::nat. i < size p \<longrightarrow>
      Preference_Relation.equiv_rel_except_a A (p!i) (q!i) a"
  proof
    fix i::nat
    show
      "i < size p \<longrightarrow>
        Preference_Relation.equiv_rel_except_a A (p!i) (q!i) a"
    proof
      assume i_ok: "i < size p"
      show "Preference_Relation.equiv_rel_except_a A (p!i) (q!i) a"
        using Electoral_Module.lifted_def i_ok lifted
              Preference_Relation.lifted_imp_equiv_rel_except_a
              profile_def trivial_equiv_rel
        by metis
    qed
  qed
  thus ?thesis
    using Electoral_Module.lifted_def lifted
          equiv_prof_except_a_def
    by metis
qed

lemma negl_diff_imp_eq_limit_prof:
  assumes
    change: "equiv_prof_except_a S p q a" and
    subset: "A \<subseteq> S" and
    notInA: "a \<notin> A"
  shows "limit_profile A p = limit_profile A q"
proof -
  have
    "\<forall>i::nat. i < size p \<longrightarrow>
      Preference_Relation.equiv_rel_except_a S (p!i) (q!i) a"
    using change equiv_prof_except_a_def
    by metis
  hence "\<forall>i::nat. i < size p \<longrightarrow> limit A (p!i) = limit A (q!i)"
    using notInA negl_diff_imp_eq_limit subset
    by metis
  thus ?thesis
    using change equiv_prof_except_a_def
          length_map limit_profile.simps
          nth_equalityI nth_map
    by (metis (mono_tags, lifting))
qed

lemma limit_prof_eq_or_lifted:
  assumes
    lifted: "lifted S p q a" and
    subset: "A \<subseteq> S"
  shows
    "limit_profile A p = limit_profile A q \<or>
        lifted A (limit_profile A p) (limit_profile A q) a"
proof cases
  assume inA: "a \<in> A"
  have
    "\<forall>i::nat. i < size p \<longrightarrow>
        (Preference_Relation.lifted S (p!i) (q!i) a \<or> (p!i) = (q!i))"
    using Electoral_Module.lifted_def lifted
    by metis
  hence one:
    "\<forall>i::nat. i < size p \<longrightarrow>
         (Preference_Relation.lifted A (limit A (p!i)) (limit A (q!i)) a \<or>
           (limit A (p!i)) = (limit A (q!i)))"
    using limit_lifted_imp_eq_or_lifted subset
    by metis
  thus ?thesis
  proof cases
    assume "\<forall>i::nat. i < size p \<longrightarrow> (limit A (p!i)) = (limit A (q!i))"
    thus ?thesis
      using Electoral_Module.lifted_def length_map lifted
            limit_profile.simps nth_equalityI nth_map
      by (metis (mono_tags, lifting))
  next
    assume assm:
      "\<not>(\<forall>i::nat. i < size p \<longrightarrow> (limit A (p!i)) = (limit A (q!i)))"
    let ?p = "limit_profile A p"
    let ?q = "limit_profile A q"
    have "profile A ?p \<and> profile A ?q"
      using Electoral_Module.lifted_def lifted limit_profile_sound subset
      by metis
    moreover have "size ?p = size ?q"
      using Electoral_Module.lifted_def lifted
      by fastforce
    moreover have
      "\<exists>i::nat. i < size ?p \<and> Preference_Relation.lifted A (?p!i) (?q!i) a"
      using assm Electoral_Module.lifted_def length_map lifted
            limit_profile.simps nth_map one
      by (metis (no_types, lifting))
    moreover have
      "\<forall>i::nat.
        (i < size ?p \<and> \<not>Preference_Relation.lifted A (?p!i) (?q!i) a) \<longrightarrow>
          (?p!i) = (?q!i)"
      using Electoral_Module.lifted_def length_map lifted
            limit_profile.simps nth_map one
      by metis
    ultimately have "lifted A ?p ?q a"
      using Electoral_Module.lifted_def inA lifted rev_finite_subset subset
      by (metis (no_types, lifting))
    thus ?thesis
      by simp
  qed
next
  assume "a \<notin> A"
  thus ?thesis
    using lifted negl_diff_imp_eq_limit_prof subset
          lifted_imp_equiv_prof_except_a
    by metis
qed

subsection \<open>(Non-)Electing, Decrementing, Defer-Deciding and Blocking Property\<close>

(*
   An electoral module is non-electing iff
   it never elects an alternative.
*)
definition non_electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_electing m \<equiv>
    electoral_module m \<and> (\<forall>A p. finite_profile A p \<longrightarrow> elect m A p = {})"

lemma single_elim_decr_def_card:
  assumes
    rejecting: "rejects 1 m" and
    not_empty: "A \<noteq> {}" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p"
  shows "card (defer m A p) = card A - 1"
  using Diff_empty One_nat_def Suc_leI card_Diff_subset card_gt_0_iff
        defer_not_elec_or_rej finite_subset non_electing
        non_electing_def not_empty f_prof reject_in_alts rejecting
        rejects_def
  by (smt (verit, ccfv_threshold))

lemma single_elim_decr_def_card2:
  assumes
    eliminating: "eliminates 1 m" and
    not_empty: "card A > 1" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p"
  shows "card (defer m A p) = card A - 1"
  using Diff_empty One_nat_def Suc_leI card_Diff_subset card_gt_0_iff
        defer_not_elec_or_rej finite_subset non_electing
        non_electing_def not_empty f_prof reject_in_alts
        eliminating eliminates_def
  by (smt (verit))

(*
   An electoral module decrements iff
   this module rejects at least one alternative whenever possible (|A|>1).
*)
definition decrementing :: "'a Electoral_Module \<Rightarrow> bool" where
  "decrementing m \<equiv>
    electoral_module m \<and> (
      \<forall> A p . finite_profile A p \<longrightarrow>
          (card A > 1 \<longrightarrow> card (reject m A p) \<ge> 1))"

(*
   An electoral module is defer-deciding iff
   this module chooses exactly 1 alternative to defer and
   rejects any other alternative.
   Note that `rejects n-1 m` can be omitted due to the
   well-formedness property.
*)
definition defer_deciding :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_deciding m \<equiv>
    electoral_module m \<and> non_electing m \<and> defers 1 m"

(*
   An electoral module is non-blocking iff
   this module never rejects all alternatives.
*)
definition non_blocking :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_blocking m \<equiv>
    electoral_module m \<and>
      (\<forall>A p.
          ((A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> reject m A p \<noteq> A))"

(*
   An electoral module is electing iff
   it always elects at least one alternative.
*)
definition electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "electing m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect m A p \<noteq> {})"

lemma electing_for_only_alt:
  assumes
    one_alt: "card A = 1" and
    electing: "electing m" and
    f_prof: "finite_profile A p"
  shows "elect m A p = A"
  using Int_empty_right Int_insert_right card_1_singletonE
        elect_in_alts electing electing_def inf.orderE
        one_alt f_prof
  by (smt (verit, del_insts))

theorem electing_imp_non_blocking:
  assumes electing: "electing m"
  shows "non_blocking m"
  using Diff_disjoint Diff_empty Int_absorb2 electing
        defer_in_alts elect_in_alts electing_def
        non_blocking_def reject_not_elec_or_def
  by (smt (verit, ccfv_SIG))

subsection \<open>Properties\<close>

definition defer_condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<and> finite A \<longrightarrow> 
      (m A p =
        ({},
        A - (defer m A p),
        {d \<in> A. condorcet_winner A p d})))"

definition condorcet_compatibility :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_compatibility m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<and> finite A \<longrightarrow>
      (w \<notin> reject m A p \<and>
        (\<forall>l. \<not>condorcet_winner A p l \<longrightarrow> l \<notin> elect m A p) \<and>
          (w \<in> elect m A p \<longrightarrow>
            (\<forall>l. \<not>condorcet_winner A p l \<longrightarrow> l \<in> reject m A p))))"

(*
   An electoral module is defer-monotone iff,
   when a deferred alternative is lifted, this alternative remains deferred.
*)
definition defer_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q w.
          (finite A \<and> w \<in> defer m A p \<and> lifted A p q w) \<longrightarrow> w \<in> defer m A q)"

(*
   An electoral module is defer-lift-invariant iff
   lifting a deferred alternative does not affect the outcome.
*)
definition defer_lift_invariance :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_lift_invariance m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q a.
          (a \<in> (defer m A p) \<and> lifted A p q a) \<longrightarrow> m A p = m A q)"

(*
   Two electoral modules are disjoint-compatible if they only make decisions
   over disjoint sets of alternatives. Electoral modules reject alternatives
   for which they make no decision.
*)
definition disjoint_compatibility :: "'a Electoral_Module \<Rightarrow>
                                         'a Electoral_Module \<Rightarrow> bool" where
  "disjoint_compatibility m n \<equiv>
    electoral_module m \<and> electoral_module n \<and>
        (\<forall>S. finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> A. indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))))"

(*
   Lifting an elected alternative a from an invariant-monotone
   electoral module either does not change the elect set, or
   makes a the only elected alternative.
*)
definition invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "invariant_monotonicity m \<equiv>
    electoral_module m \<and>
        (\<forall>A p q a. (a \<in> elect m A p \<and> lifted A p q a) \<longrightarrow>
          (elect m A q = elect m A p \<or> elect m A q = {a}))"

(*
   Lifting a deferred alternative a from a defer-invariant-monotone
   electoral module either does not change the defer set, or
   makes a the only deferred alternative.
*)
definition defer_invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_invariant_monotonicity m \<equiv>
    electoral_module m \<and> non_electing m \<and>
        (\<forall>A p q a. (a \<in> defer m A p \<and> lifted A p q a) \<longrightarrow>
          (defer m A q = defer m A p \<or> defer m A q = {a}))"

subsection \<open>Inference Rules\<close>

lemma ccomp_and_dd_imp_def_only_winner:
  assumes ccomp: "condorcet_compatibility m" and
          dd: "defer_deciding m" and
          winner: "condorcet_winner A p w"
  shows "defer m A p = {w}"
proof (rule ccontr)
  assume not_w: "defer m A p \<noteq> {w}"
  from dd have "defers 1 m"
    using defer_deciding_def
    by metis
  hence "card (defer m A p) = 1"
    using One_nat_def Suc_leI card_gt_0_iff condorcet_winner.simps
          defers_def equals0D winner
    by metis
  hence 0: "\<exists>x \<in> A . defer m A p ={x}"
    using card_1_singletonE condorcet_winner.simps dd
          defer_deciding_def defer_in_alts insert_subset
          winner
    by metis
  with not_w have "\<exists>l \<in> A . l \<noteq> w \<and> defer m A p = {l}"
    by metis
  hence not_in_defer: "w \<notin> defer m A p"
    by auto
  have "non_electing m"
    using dd defer_deciding_def
    by metis
  hence not_in_elect: "w \<notin> elect m A p"
    using condorcet_winner.simps equals0D non_electing_def winner
    by metis
  from not_in_defer not_in_elect have one_side: "w \<in> reject m A p"
    using ccomp condorcet_compatibility_def condorcet_winner.simps
          electoral_mod_defer_elem winner
    by metis
  from ccomp have other_side: "w \<notin> reject m A p"
    using condorcet_compatibility_def condorcet_winner.simps winner
    by (metis (no_types, hide_lams))
  thus False
    by (simp add: one_side)
qed

theorem ccomp_and_dd_imp_dcc[simp]:
  assumes ccomp: "condorcet_compatibility m" and
          dd: "defer_deciding m"
  shows "defer_condorcet_consistency m"
proof (unfold defer_condorcet_consistency_def, auto)
  show "electoral_module m"
    using dd defer_deciding_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    finiteness: "finite A" and
    assm: "\<forall>x\<in>A - {w}.
          card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)}"
  have winner: "condorcet_winner A p w"
    using prefer_count.simps wins.elims
          condorcet_winner.simps assm
          finiteness prof_A w_in_A
    by simp
  hence
    "m A p =
      ({},
        A - defer m A p,
        {d \<in> A. condorcet_winner A p d})"
  proof -
    (*Elect*)
    from dd have 0: "elect m A p = {}"
      using condorcet_winner.simps defer_deciding_def
            non_electing_def winner
      by metis
    (*Defers*)
    from dd ccomp have 1: "defer m A p = {w}"
      using ccomp_and_dd_imp_def_only_winner winner
      by simp
    (*Reject*)
    from 0 1 have 2: "reject m A p = A - defer m A p"
      using Diff_empty condorcet_winner.simps dd defer_deciding_def
            reject_not_elec_or_def winner
      by metis
    from 0 1 2 have 3: "m A p = ({}, A - defer m A p, {w})"
      using combine_ele_rej_def
      by metis
    have "{w} = {d \<in> A. condorcet_winner A p d}"
      using cond_winner_unique3 winner
      by metis
    thus ?thesis
      using "3"
      by auto
  qed
  hence
    "m A p =
      ({},
        A - defer m A p,
        {d \<in> A. \<forall>x\<in>A - {d}. wins d p x})"
    using finiteness prof_A winner Collect_cong
          condorcet_winner.elims
    by auto
  hence
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall>x\<in>A - {d}.
            prefer_count p x d < prefer_count p d x})"
    using wins.simps
    by simp
  hence
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall>x\<in>A - {d}.
            card {i. i < length p \<and> (let r = (p!i) in (d \<preceq>\<^sub>r x))} <
                card {i. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r d))}})"
    using prefer_count.simps
    by simp
  thus
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall>x\<in>A - {d}.
            card {i. i < length p \<and> (d, x) \<in> (p!i)} <
              card {i. i < length p \<and> (x, d) \<in> (p!i)}})"
    using is_less_preferred_than.simps
    by simp
qed

(*If m and n are disjoint compatible, so are n and m.*)
theorem disj_compat_comm[simp]:
  assumes compatible: "disjoint_compatibility m n"
  shows "disjoint_compatibility n m"
proof -
  have
    "\<forall>S. finite S \<longrightarrow>
        (\<exists>A \<subseteq> S.
          (\<forall>a \<in> A. indep_of_alt n S a \<and>
            (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
          (\<forall>a \<in> S-A. indep_of_alt m S a \<and>
            (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
  proof
    fix S
    obtain A where old_A:
      "finite S \<longrightarrow>
          (A \<subseteq> S \<and>
            (\<forall>a \<in> A. indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)))"
      using compatible disjoint_compatibility_def
      by fastforce
    hence
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
            (\<forall>a \<in> A. indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      by auto
    hence
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
            (\<forall>a \<in> S-(S-A). indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      using double_diff order_refl
      by metis
    thus
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      by fastforce
  qed
  moreover have "electoral_module m \<and> electoral_module n"
    using compatible disjoint_compatibility_def
    by auto
  ultimately show ?thesis
    by (simp add: disjoint_compatibility_def)
qed

(*
   Every electoral module which is defer-lift-invariant is
   also defer-monotone.
*)
theorem dl_inv_imp_def_mono[simp]:
  assumes "defer_lift_invariance m"
  shows "defer_monotonicity m"
  using assms defer_monotonicity_def defer_lift_invariance_def
  by fastforce

subsection \<open>Social Choice Properties\<close>

subsubsection \<open>Condorcet Consistency\<close>

definition condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<longrightarrow>
      (m A p =
        ({e \<in> A. condorcet_winner A p e},
          A - (elect m A p),
          {})))"

lemma condorcet_consistency2:
  "condorcet_consistency m \<longleftrightarrow>
      electoral_module m \<and>
        (\<forall> A p w. condorcet_winner A p w \<longrightarrow>
            (m A p =
              ({w}, A - (elect m A p), {})))"
proof (auto)
  show "condorcet_consistency m \<Longrightarrow> electoral_module m"
    using condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    cc: "condorcet_consistency m"
  have assm0:
    "condorcet_winner A p w \<Longrightarrow> m A p = ({w}, A - elect m A p, {})"
    using cond_winner_unique3 condorcet_consistency_def cc
    by (metis (mono_tags, lifting))
  assume
    finite_A: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A"
  also have
    "\<forall>x\<in>A - {w}.
      prefer_count p w x > prefer_count p x w \<Longrightarrow>
        condorcet_winner A p w"
    using finite_A prof_A w_in_A wins.elims
    by simp
  ultimately show
    "\<forall>x\<in>A - {w}.
        card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)} \<Longrightarrow>
                m A p = ({w}, A - elect m A p, {})"
    using assm0
    by auto
next
  have assm0:
    "electoral_module m \<Longrightarrow>
      \<forall>A p w. condorcet_winner A p w \<longrightarrow> 
          m A p = ({w}, A - elect m A p, {}) \<Longrightarrow>
            condorcet_consistency m"
    using condorcet_consistency_def cond_winner_unique3
    by (smt (verit, del_insts))
  assume e_mod:
    "electoral_module m"
  thus
    "\<forall>A p w. finite A \<and> profile A p \<and> w \<in> A \<and>
       (\<forall>x\<in>A - {w}.
          card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)}) \<longrightarrow>
       m A p = ({w}, A - elect m A p, {}) \<Longrightarrow>
          condorcet_consistency m"
    using wins.elims prefer_count.simps assm0 e_mod
          condorcet_winner.elims(2)
    by simp
qed

subsubsection \<open>(Weak) Monotonicity\<close>

(*
   An electoral module is monotone iff
   when an elected alternative is lifted, this alternative remains elected.
*)
definition monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q w.
          (finite A \<and> w \<in> elect m A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect m A q)"

subsubsection \<open>Homogeneity\<close>

fun times :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "times n l = concat (replicate n l)"

definition homogeneity :: "'a Electoral_Module \<Rightarrow> bool" where
"homogeneity m \<equiv>
  electoral_module m \<and>
    (\<forall> A p n .
      (finite_profile A p \<and> n > 0 \<longrightarrow> 
          (m A p = m A (times n p))))"

end

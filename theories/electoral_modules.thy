theory electoral_modules
imports linear_orders

begin

(************************************)
(*** Definition: Electoral Module ***)
(************************************)

(* These are only the used types for electoral modules. Further restrictions follow in the
   electoral_module predicate.
*)
(* A profile contains one ballot for each voter. *)
type_synonym 'a Profile = "('a rel) list"
(* A result contains three sets of alternatives: elected, rejected, and deferred alternatives. *)
type_synonym 'a Result = "'a set * 'a set * 'a set"
(* An electoral module maps a set of alternatives and a profile to a result. *)
type_synonym 'a Electoral_module = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result"

(* A profile on a finite set of alternatives A contains only ballots, which are linear orders on A.
*)
definition profile_on :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "profile_on A p \<equiv> finite A \<and> (\<forall>b \<in> (set p). linear_order_on A b)"
abbreviation finite_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "finite_profile A p \<equiv> finite A \<and> profile_on A p"

(* A partition of a set A are pairwise disjoint sets that unify to A. For this specific predicate,
   the partition consists of three sets in a tuple.
*)
fun disjoint3 :: "'a Result \<Rightarrow> bool" where
  "disjoint3 (e, r, d) =
    ((e \<inter> r = {})
    \<and> (e \<inter> d = {})
    \<and> (r \<inter> d = {}))"
fun unify_to :: "'a set \<Rightarrow>'a Result \<Rightarrow> bool" where
  "unify_to A (e, r, d) \<longleftrightarrow> (e \<union> r \<union> d = A)"
definition partition_of :: "'a set \<Rightarrow> 'a Result \<Rightarrow> bool" where
  "partition_of A result \<equiv> disjoint3 result \<and> unify_to A result"

(* Electoral modules partition a given set of alternatives A into a set of elected alternatives e, a
   set of rejected alternatives r, and a set of deferred alternatives d using a profile. e, r, and d
   partition A. Electoral modules can be used as voting rules. They can also be composed in multiple
   structures to create more complex electoral modules.
*)
definition electoral_module :: " 'a Electoral_module \<Rightarrow> bool" where
  "electoral_module m \<equiv>
    \<forall>A p. finite_profile A p \<longrightarrow> partition_of A (m A p)"
lemma electoral_module_intro[intro]:
  "((\<And>A p. \<lbrakk> finite_profile A p \<rbrakk> \<Longrightarrow> partition_of A (m A p)) \<Longrightarrow> electoral_module m)"
  unfolding electoral_module_def
  by auto

(*************************************************)
(*** Supportive Definitions (Electoral Module) ***)
(*************************************************)

(* The next three functions return the elect, reject, or defer set of a result. *)
abbreviation elect_r :: "'a Result \<Rightarrow> 'a set" where
  "elect_r r \<equiv> fst r"
abbreviation reject_r :: "'a Result \<Rightarrow> 'a set" where
  "reject_r r \<equiv> fst (snd r)"
abbreviation defer_r :: "'a Result \<Rightarrow> 'a set" where
  "defer_r r \<equiv> snd (snd r)"

(* The next three functions take an electoral module and turn it into a function only outputting
   the elect, reject, or defer set respectively. *)
abbreviation elect :: "'a Electoral_module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "elect m A p \<equiv> elect_r (m A p)"
abbreviation reject :: "'a Electoral_module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "reject m A p \<equiv> reject_r (m A p)"
abbreviation "defer" :: "'a Electoral_module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "defer m A p \<equiv> defer_r (m A p)"

(* This function limits a profile p to a set A, keeping all preferences in A. *)
fun limit_profile_to :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile" where
  "limit_profile_to A p = map (limit_to A) p"
lemma limit_profile_consistent:
  assumes profile: "finite_profile S p" and
          subset:  "A \<subseteq> S"
  shows "finite_profile A (limit_profile_to A p)"
  by (metis (mono_tags, lifting) assms(1) imageE infinite_super limit_preserves_linear_order
      limit_profile_to.simps profile_on_def set_map subset)

(* An alternative gets lifted for a profile to another if it's ranking increases in at least one
   ballot and nothing else changes.
*)
definition lifted :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A p q a \<equiv> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and> size p = size q \<and>
    (\<exists>i::nat. i < size p \<and> linear_orders.lifted A (p!i) (q!i) a) \<and>
    (\<forall>i::nat. (i < size p \<and> \<not>linear_orders.lifted A (p!i) (q!i) a) \<longrightarrow> (p!i) = (q!i))"

definition only_change :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "only_change A p q a \<equiv> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and> size p = size q \<and>
    (\<forall>i::nat. i < size p \<longrightarrow> linear_orders.only_change A (p!i) (q!i) a)"

definition eq_module_result ::
    "'a Electoral_module \<Rightarrow> 'a Electoral_module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "eq_module_result m n A p a \<equiv>
    electoral_module m \<and> electoral_module n \<and> finite_profile A p \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect n A p) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject n A p) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer n A p)"

definition eq_result_for ::
    "'a Electoral_module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "eq_result_for m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer m A q)"

definition leq_result_for ::
    "'a Electoral_module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "leq_result_for m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> elect m A q)"

definition geq_result_for ::
    "'a Electoral_module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "geq_result_for m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> reject m A q)"

(************************************)
(*** Lemmas for Electoral Modules ***)
(************************************)

lemma combine_ele_rej_def:
  assumes ele: "elect m A p = e" and
          rej: "reject m A p = r" and
          def: "defer m A p = d"
  shows "m A p = (e, r, d)"
  using def ele rej
  by auto

lemma partition_reject:
  shows "partition_of A (e, r, d) \<longrightarrow>  A - (e \<union> d) = r"
proof - (* autogenerated proof *)
  have f1: "\<forall>A Aa. (Aa::'a set) - (A - Aa) = Aa"
    by blast
  hence f2: "\<forall>A Aa Ab. (Ab::'a set) - (Aa - Ab \<union> A) = Ab \<inter> (Ab - A)"
    by (metis Diff_Un)
  have f3: "\<forall>A. (A::'a set) - A = {}"
    by blast
  have f4: "\<forall>A Aa Ab. (Ab::'a set) - Aa - A = Ab - (Aa \<union> A)"
    by auto
  { assume "\<exists>A. r \<union> A - d \<noteq> r \<union> (A - d)"
    hence "r - d \<noteq> r"
      by (metis Un_Diff)
    hence "\<not> disjoint3 (e, r, d)"
      by (metis Un_Diff_Int disjoint3.simps sup_bot.comm_neutral)
  }
  moreover
  { assume "\<exists>Aa. r \<union> d - Aa \<noteq> A - (e \<union> Aa)"
    { assume "\<exists>A. A \<union> d - e \<noteq> A - e \<union> d"
      hence "d - e \<noteq> d"
        by (metis Un_Diff)
      hence "\<not> disjoint3 (e, r, d)"
        using f1
        by (metis Un_Diff_Int disjoint3.simps sup_bot.comm_neutral)
    }
    hence "disjoint3 (e, r, d) \<longrightarrow> partition_of A (e, r, d) \<longrightarrow> A - (e \<union> d) = r"
      using f4 f3 f2 f1
      by (metis Un_Diff Un_Diff_Int disjoint3.simps partition_of_def sup_bot.comm_neutral
          unify_to.simps)
  }
  ultimately show ?thesis
    using f3
    by (metis (no_types) partition_of_def sup_bot.comm_neutral)
qed

lemma split_unify_result:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
proof -
  from module profile
  have "unify_to A (m A p)"
    using electoral_module_def partition_of_def
    by blast
  hence "unify_to A (elect m A p, reject m A p, defer m A p)"
    by simp
  thus ?thesis
    by (metis (mono_tags, lifting) unify_to.simps)
qed

lemma split_disjoint3:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "(elect m A p) \<inter> (reject m A p) = {} \<and>
         (elect m A p) \<inter> (defer m A p) = {} \<and>
         (reject m A p) \<inter> (defer m A p) = {}"
  by (metis disjoint3.simps electoral_module_def module partition_of_def prod.exhaust_sel profile)

lemma elect_from_input:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "elect m A p \<subseteq> A"
  by (metis le_supI1 module profile split_unify_result sup_ge1)

lemma reject_from_input:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "reject m A p \<subseteq> A"
  by (metis le_supI1 module profile split_unify_result sup_ge2)

lemma defer_from_input:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "defer m A p \<subseteq> A"
  using module profile split_unify_result by auto

lemma reject_alternative_representation:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "reject m A p = A - (elect m A p) - (defer m A p)"
proof -
  from module profile
  have 0: "partition_of A (m A p)"
    by (simp add: electoral_module_def)
  from this module profile
  have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using module partition_of_def profile split_unify_result
    by blast
  moreover from 0
  have "(elect m A p) \<inter> (reject m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
    using module profile split_disjoint3
    by blast
  ultimately show ?thesis
    by blast
qed

lemma elect_defer_alt_representation:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "elect m A p \<union> defer m A p = A - (reject m A p)"
proof -
  from module profile
  have 0: "partition_of A (m A p)"
    by (simp add: electoral_module_def)
  from this module profile
  have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using module partition_of_def profile split_unify_result
    by blast
  moreover from 0
  have "(elect m A p) \<inter> (reject m A p) = {}
        \<and> (reject m A p) \<inter> (defer m A p) = {}"
    using module profile split_disjoint3 by blast
  ultimately show ?thesis
    by blast
qed

lemma defer_alternative_representation:
  assumes module:  "electoral_module m" and
          profile: "finite_profile A p"
  shows "defer m A p = A - (elect m A p) - (reject m A p)"
proof -
  from module profile
  have 0: "partition_of A (m A p)"
    by (simp add: electoral_module_def)
  hence "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using module profile split_unify_result
    by auto
  moreover from 0
  have "(elect m A p) \<inter> (defer m A p) = {} \<and> (reject m A p) \<inter> (defer m A p) = {}"
    using module profile split_disjoint3
    by blast
  ultimately show ?thesis
    by blast
qed

lemma electoral_module_element_in_defer:
  assumes module:       "electoral_module m" and
          profile:      "finite_profile A p" and
          candidate:    "x \<in> A" and
          not_elected:  "x \<notin> elect m A p" and
          not_rejected: "x \<notin> reject m A p"
  shows "x \<in> defer m A p"
  by (metis DiffI module profile candidate not_elected not_rejected
      reject_alternative_representation)

lemma electoral_module_element_in_elect_or_defer:
  assumes module:       "electoral_module m" and
          profile:      "finite_profile A p" and
          candidate:    "x \<in> A" and
          not_rejected: "x \<notin> reject m A p"
  shows "x \<in> elect m A p \<or> x \<in> defer m A p"
  by (meson candidate electoral_module_element_in_defer module not_rejected profile)

(****************************)
(*** Property Definitions ***)
(****************************)

(* In monotone electoral modules, if an elected alternative is lifted, it remains elected. *)
definition monotone :: "'a Electoral_module \<Rightarrow> bool" where
  "monotone m \<equiv> electoral_module m \<and> (
    \<forall>A p q w. (finite A \<and> w \<in> elect m A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect m A q)"

(* In defer monotone electoral modules, if a deferred alternative is lifted, it remains deferred. *)
definition defer_monotone :: "'a Electoral_module \<Rightarrow> bool" where
  "defer_monotone m \<equiv> electoral_module m \<and> (
    \<forall>A p q w. (finite A \<and> w \<in> defer m A p \<and> lifted A p q w) \<longrightarrow> w \<in> defer m A q)"

(* In defer lift invariant electoral modules, lifting a deferred alternative does not influence the
   outcome.
*)
definition defer_lift_invariant :: "'a Electoral_module \<Rightarrow> bool" where
  "defer_lift_invariant m \<equiv> electoral_module m \<and> (
    \<forall>A p q a. (a \<in> (defer m A p) \<and> lifted A p q a) \<longrightarrow> m A p = m A q)"

(* An electoral module is non blocking, if it never rejects all alternatives. *)
definition non_blocking :: "'a Electoral_module \<Rightarrow> bool" where
  "non_blocking m \<equiv>
    electoral_module m \<and> (\<forall>A p. ((A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> reject m A p \<noteq> A))"

(* An electoral module is electing, if it always elects at least one alternative. *)
definition electing :: "'a Electoral_module \<Rightarrow> bool" where
  "electing m \<equiv>
    electoral_module m \<and> (\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect m A p \<noteq> {})"

(* An electoral module is non electing, if it never elects an alternative. *)
definition non_electing :: "'a Electoral_module \<Rightarrow> bool" where
  "non_electing m \<equiv>
    electoral_module m \<and> (\<forall>A p. finite_profile A p \<longrightarrow> elect m A p = {})"

(* "defers n" is true for all electoral modules, that defer exactly n alternatives, whenever there
   are n or more alternatives.
*)
definition defers :: "nat \<Rightarrow> 'a Electoral_module \<Rightarrow> bool" where
  "defers n m \<equiv>
    electoral_module m \<and> (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (defer m A p) = n)"

(* "rejects n" is true for all electoral modules, that reject exactly n alternatives, whenever
   there are n or more alternatives.
*)
definition rejects :: "nat \<Rightarrow> 'a Electoral_module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    electoral_module m \<and> (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (reject m A p) = n)"

(* As opposed to "rejects", "eliminates" allows to stop rejecting if no Alternative would remain. *)
definition eliminates :: "nat \<Rightarrow> 'a Electoral_module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    electoral_module m \<and> (\<forall>A p. (card A > n \<and> finite_profile A p) \<longrightarrow> card (reject m A p) = n)"

(* "elects n" is true for all electoral modules, that elect exactly n alternatives, whenever
   there are n or more alternatives.
*)
definition elects :: "nat \<Rightarrow> 'a Electoral_module \<Rightarrow> bool" where
  "elects n m \<equiv>
    electoral_module m \<and> (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (elect m A p) = n)"

(* An electoral module is independent of an alternative a, if a's ranking does not influence the
   outcome. *)
definition independent_of :: "'a Electoral_module \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "independent_of m A a \<equiv> electoral_module m \<and>
    (\<forall>p q. only_change A p q a \<longrightarrow> m A p = m A q)"

(* Two electoral modules are disjoint compatible, if they make decisions over disjoint sets of
   alternatives. Electoral modules reject alternatives for which they make no decision. *)
definition disjoint_compatible :: "'a Electoral_module \<Rightarrow> 'a Electoral_module \<Rightarrow> bool" where
  "disjoint_compatible m n \<equiv> electoral_module m \<and> electoral_module n \<and>
    (\<forall>S. finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. independent_of m S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
      (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))))"

(* Lifting an elected alternative a in an invariant monotone electoral module either does not change
   the elect set, or makes a the only elected alternative.
*)
definition invariant_monotone :: "'a Electoral_module \<Rightarrow> bool" where
  "invariant_monotone m \<equiv> electoral_module m \<and>
    (\<forall>A p q a. (a \<in> elect m A p \<and> lifted A p q a) \<longrightarrow>
               (elect m A q = elect m A p \<or> elect m A q = {a}))"

(* Lifting a deferred alternative a in an defer invariant monotone electoral module either does not
   change the defer set, or makes a the only deferred alternative.
*)
definition defer_invariant_monotone :: "'a Electoral_module \<Rightarrow> bool" where
  "defer_invariant_monotone m \<equiv> electoral_module m \<and> non_electing m \<and>
    (\<forall>A p q a. (a \<in> defer m A p \<and> lifted A p q a) \<longrightarrow>
               (defer m A q = defer m A p \<or> defer m A q = {a}))"

(*******************************)
(*** Theorems for Properties ***)
(*******************************)

lemma partition_card:
  assumes "partition_of A (e, r, d)" and
          "finite A"
  shows "card A = card e + card r + card d"
  by (metis partition_of_def unify_to.simps Int_Un_distrib2 assms card_Un_disjoint disjoint3.simps
      finite_Un partition_of_def sup_bot.right_neutral)

lemma eq_module_result_commutative:
  assumes "eq_module_result m n A p a"
  shows "eq_module_result n m A p a"
  by (smt IntI assms electoral_module_element_in_defer empty_iff eq_module_result_def
      split_disjoint3)

lemma forall_eq_result:
  assumes eq:    "\<forall>a \<in> A. eq_result_for m A p q a" and
          (* for empty A *)
          input: "electoral_module m \<and> finite_profile A p \<and> finite_profile A q"
  shows "m A p = m A q"
proof -
  have "\<forall>a \<in> elect m A p. a \<in> elect m A q"
    by (meson contra_subsetD elect_from_input eq eq_result_for_def input)
  moreover have "\<forall>a \<in> elect m A q. a \<in> elect m A p"
    by (smt contra_subsetD disjoint_iff_not_equal elect_from_input electoral_module_element_in_defer
        eq eq_result_for_def input split_disjoint3)
  moreover have "\<forall>a \<in> reject m A p. a \<in> reject m A q"
    by (meson contra_subsetD reject_from_input eq eq_result_for_def input)
  moreover have "\<forall>a \<in> reject m A q. a \<in> reject m A p"
    by (smt contra_subsetD disjoint_iff_not_equal reject_from_input
        electoral_module_element_in_defer eq eq_result_for_def input split_disjoint3)
  moreover have "\<forall>a \<in> defer m A p. a \<in> defer m A q"
    by (meson contra_subsetD defer_from_input eq eq_result_for_def input)
  moreover have "\<forall>a \<in> defer m A q. a \<in> defer m A p"
    by (smt contra_subsetD disjoint_iff_not_equal defer_from_input electoral_module_element_in_defer
        eq eq_result_for_def input split_disjoint3)
  ultimately show ?thesis
    by (metis prod.collapse subsetI subset_antisym)
qed

lemma lifted_impl_only_change:
  assumes lifted: "lifted A p q a"
  shows "only_change A p q a"
proof -
  { have "\<forall>i::nat. i < size p \<longrightarrow> linear_orders.only_change A (p!i) (q!i) a"
    proof
      { fix i::nat show "i < size p \<longrightarrow> linear_orders.only_change A (p!i) (q!i) a"
        proof
          { assume i_ok: "i < size p"
            show "linear_orders.only_change A (p!i) (q!i) a"
              by (metis electoral_modules.lifted_def i_ok lifted lifted_implies_only_change nth_mem
                  profile_on_def trivial_only_change)
          }
        qed }
    qed }
  thus ?thesis
    by (meson electoral_modules.lifted_def electoral_modules.only_change_def lifted)
qed

lemma limit_profile_twice:
  assumes "B \<subseteq> A" and
          "C \<subseteq> B" and
          "finite_profile A p"
  shows "limit_profile_to C p = limit_profile_to C (limit_profile_to B p)"
  using assms by auto

lemma remove_only_difference_profile:
  assumes change: "only_change S p q a" and
          subset: "A \<subseteq> S" and
          notInA: "a \<notin> A"
  shows "limit_profile_to A p = limit_profile_to A q"
proof -
  have "\<forall>i::nat. i < size p \<longrightarrow> linear_orders.only_change S (p!i) (q!i) a"
    by (meson change electoral_modules.only_change_def)
  hence "\<forall>i::nat. i < size p \<longrightarrow> limit_to A (p!i) = limit_to A (q!i)"
    by (meson notInA remove_only_difference subset)
  thus ?thesis
    by (metis (mono_tags, lifting) change electoral_modules.only_change_def length_map
        limit_profile_to.simps nth_equalityI nth_map)
qed

lemma limit_lifted_profile_interaction:
  assumes lifted: "lifted S p q a" and
          subset: "A \<subseteq> S"
  shows "limit_profile_to A p = limit_profile_to A q \<or>
         lifted A (limit_profile_to A p) (limit_profile_to A q) a"
proof cases
  { assume inA: "a \<in> A"
    have "\<forall>i::nat. i < size p \<longrightarrow> (linear_orders.lifted S (p!i) (q!i) a \<or> (p!i) = (q!i))"
      by (meson electoral_modules.lifted_def lifted)
    hence one: "\<forall>i::nat. i < size p \<longrightarrow>
                 (linear_orders.lifted A (limit_to A (p!i)) (limit_to A (q!i)) a
                  \<or> (limit_to A (p!i)) = (limit_to A (q!i)))"
      by (metis limit_lifted_interaction subset)
    thus ?thesis
    proof cases
      { assume "\<forall>i::nat. i < size p \<longrightarrow> (limit_to A (p!i)) = (limit_to A (q!i))"
        thus ?thesis
          by (metis (mono_tags, lifting) electoral_modules.lifted_def length_map lifted
              limit_profile_to.simps nth_equalityI nth_map)
      }
    next
      { assume assm: "\<not>(\<forall>i::nat. i < size p \<longrightarrow> (limit_to A (p!i)) = (limit_to A (q!i)))"
        let ?p = "limit_profile_to A p"
        let ?q = "limit_profile_to A q"
        have "profile_on A ?p \<and> profile_on A ?q"
          by (meson electoral_modules.lifted_def lifted limit_profile_consistent subset)
        moreover have "size ?p = size ?q"
          using electoral_modules.lifted_def lifted
          by fastforce
        moreover have "\<exists>i::nat. i < size ?p \<and> linear_orders.lifted A (?p!i) (?q!i) a"
          by (metis (no_types, lifting) assm electoral_modules.lifted_def length_map lifted
              limit_profile_to.simps nth_map one)
        moreover have "\<forall>i::nat. (i < size ?p \<and> \<not>linear_orders.lifted A (?p!i) (?q!i) a) \<longrightarrow>
                         (?p!i) = (?q!i)"
          by (metis electoral_modules.lifted_def length_map lifted limit_profile_to.simps
              nth_map one)
        ultimately have "lifted A ?p ?q a"
          by (metis (no_types, lifting) electoral_modules.lifted_def inA lifted
              rev_finite_subset subset)
        thus ?thesis
          by simp
      }
    qed }
next
  { assume "a \<notin> A"
    thus ?thesis
      by (meson lifted lifted_impl_only_change remove_only_difference_profile subset)
  }
qed

lemma single_elimination_reduces_defer_set_2:
  assumes eliminating: "eliminates 1 m" and
          leftover_alternatives: "card A > 1" and
          profile: "finite_profile A p"
        shows "defer m A p \<subset> A"
  by (metis Diff_eq_empty_iff Diff_subset card_empty defer_from_input eliminates_def eliminating
      eq_iff leftover_alternatives not_one_le_zero profile psubsetI
      reject_alternative_representation)

lemma single_elimination_reduces_defer_set_by_one:
  assumes rejecting: "rejects 1 m" and
          not_empty: "A \<noteq> {}" and
          non_electing: "non_electing m" and
          profile: "finite_profile A p"
        shows "card (defer m A p) = card A - 1"
  by (smt Diff_empty One_nat_def Suc_leI card_Diff_subset card_gt_0_iff
      defer_alternative_representation finite_subset non_electing non_electing_def not_empty profile
      reject_from_input rejecting rejects_def)

lemma single_elimination_reduces_defer_set_by_one2:
  assumes eliminating: "eliminates 1 m" and
          not_empty: "card A > 1" and
          non_electing: "non_electing m" and
          profile: "finite_profile A p"
        shows "card (defer m A p) = card A - 1"
  by (smt Diff_empty One_nat_def Suc_leI card_Diff_subset card_gt_0_iff
      defer_alternative_representation finite_subset non_electing non_electing_def not_empty profile
      reject_from_input eliminating eliminates_def)

(* If m and n are disjoint compatible, so are n and m. *)
theorem disjoint_compatible_commutative[simp]:
  assumes compatible: "disjoint_compatible m n"
  shows "disjoint_compatible n m"
proof -
  have "\<forall>S. finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
      (\<forall>a \<in> S-A. independent_of m S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
  proof
    fix S
    obtain A where old_A: "finite S \<longrightarrow> (A \<subseteq> S \<and>
      (\<forall>a \<in> A. independent_of m S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
      (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)))"
      using compatible disjoint_compatible_def by fastforce
    hence "finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
      (\<forall>a \<in> A. independent_of m S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      by auto
    hence  "finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> S-A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
      (\<forall>a \<in> S-(S-A). independent_of m S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      by (metis double_diff order_refl)
    thus "finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. independent_of n S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
      (\<forall>a \<in> S-A. independent_of m S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      by fastforce
  qed
  moreover have "electoral_module m \<and> electoral_module n"
    using compatible disjoint_compatible_def
    by auto
  ultimately show ?thesis
    by (simp add: disjoint_compatible_def)
qed

theorem electing_implies_non_blocking:
  assumes electing: "electing m"
  shows "non_blocking m"
  by (smt Diff_disjoint Diff_empty Int_absorb2 electing defer_from_input
      elect_from_input electing_def non_blocking_def reject_alternative_representation)

(* Every electoral module which is defer lift invariant is also defer monotone. *)
theorem strict_def_monotone_implies_def_monotone[simp]:
  assumes "defer_lift_invariant m"
  shows "defer_monotone m"
  using assms defer_monotone_def defer_lift_invariant_def
  by fastforce

end

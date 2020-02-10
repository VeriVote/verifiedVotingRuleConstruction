theory parallel_composition
imports max_aggregator drop_module pass_module sequential_composition

begin

(****************************************)
(*** Definition: Parallel Composition ***)
(****************************************)

(* The parallel composition creates a new electoral module out of two electoral modules and an
   aggregator. In a parallel composition the two electoral modules both make a decision and the
   aggregator aggregates them to a single result.
*)
fun parallel_comp :: "'a Electoral_module \<Rightarrow> 'a Electoral_module \<Rightarrow> 'a Aggregator \<Rightarrow>
    'a Electoral_module" where
  "parallel_comp m n agg A p = agg A (m A p) (n A p)"
abbreviation parallel :: "'a Electoral_module \<Rightarrow>'a Aggregator \<Rightarrow> 'a Electoral_module \<Rightarrow>
    'a Electoral_module"  ("_ \<parallel>\<^sub>_ _" [50, 1000, 51] 50) where
  "m \<parallel>\<^sub>a n == parallel_comp m n a"

lemma parallel_a_input_sound:
  assumes mod_m: "electoral_module m" and
          mod_n: "electoral_module n" and
          profile: "finite_profile A p"
  shows "partition_of A (m A p) \<and> partition_of A (n A p)"
  using electoral_module_def mod_m mod_n profile by auto

(* A parallel composition of 2 electoral modules and an aggregator creates an electoral module. *)
theorem par_creates_modules:
  assumes mod_m: "electoral_module m" and
          mod_n: "electoral_module n" and
          agg_a: "aggregator a"
  shows "electoral_module (m \<parallel>\<^sub>a n)"
proof -
  have "\<forall>A p. finite_profile A p \<longrightarrow> partition_of A ((m \<parallel>\<^sub>a n) A p)"
  proof fix A show "\<forall>p. finite_profile A p \<longrightarrow> partition_of A ((m \<parallel>\<^sub>a n) A p)"
  proof fix p show "finite_profile A p \<longrightarrow> partition_of A ((m \<parallel>\<^sub>a n) A p)"
  proof assume profile: "finite_profile A p"
    show "partition_of A ((m \<parallel>\<^sub>a n) A p)"
    proof -
      obtain AA :: "'a set \<times> 'a set \<Rightarrow> 'a set" and AAa :: "'a set \<times> 'a set \<Rightarrow> 'a set" where
          "\<forall>p. p = (AA p, AAa p)"
        by (meson surj_pair)
      hence "\<forall>A Aa Ab Ac Ad p f.
          partition_of (Ab::'a set) (f Ab (Ac, A, Ad) (Aa, p)) \<or>
          \<not> partition_of Ab (Ac, A, Ad) \<or>
          \<not> partition_of Ab (Aa, p) \<or>
          \<not> aggregator f"
        by (metis aggregator_def)
      hence "\<forall>A p pa f.
          partition_of (A::'a set) (f A p pa) \<or>
          \<not> partition_of A p \<or>
          \<not> partition_of A pa \<or>
          \<not> aggregator f"
        by auto
      thus ?thesis
        by (metis agg_a electoral_module_def mod_m mod_n parallel_comp.simps profile)
    qed
  qed qed qed
  thus ?thesis
    by auto
qed

(***************************************)
(*** Lemmas for Parallel Composition ***)
(***************************************)

lemma max_agg_eq_result:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          max_agg:  "a = Max_aggregator" and
          profile:  "finite_profile A p" and
          in_A:     "x \<in> A"
  shows "eq_module_result (m \<parallel>\<^sub>a n) m A p x \<or> eq_module_result (m \<parallel>\<^sub>a n) n A p x"
proof cases
  assume a1: "x \<in> elect (m \<parallel>\<^sub>a n) A p"
  hence "let (e1, r1, d1) = m A p; (e2, r2, d2) = n A p in
      x \<in> e1 \<union> e2"
    using max_agg by auto
  hence "x \<in> (elect m A p) \<union> (elect n A p)"
    by auto
  thus ?thesis
    by (smt IntI Un_iff a1 empty_iff eq_module_result_def in_A max_agg max_aggregator_sound module_m
        module_n par_creates_modules profile split_disjoint3)
next
  assume not_a1: "x \<notin> elect (m \<parallel>\<^sub>a n) A p"
  thus ?thesis
  proof cases
    assume a2: "x \<in> defer (m \<parallel>\<^sub>a n) A p"
    thus ?thesis
      by (smt CollectD DiffD1 DiffD2 Max_aggregator.simps Un_iff case_prod_conv
          defer_alternative_representation eq_module_result_def max_agg max_aggregator_sound
          module_m module_n par_creates_modules parallel_comp.simps prod.collapse profile sndI)
  next
    assume not_a2: "x \<notin> defer (m \<parallel>\<^sub>a n) A p"
    from this not_a1 have a3: "x \<in> reject (m \<parallel>\<^sub>a n) A p"
      by (metis electoral_module_element_in_defer in_A max_agg max_aggregator_sound module_m
          module_n par_creates_modules profile)
    hence "let (e1, r1, d1) = m A p; (e2, r2, d2) = n A p in
        x \<in> fst (snd (Max_aggregator A (e1, r1, d1) (e2, r2, d2)))"
      by (metis (mono_tags, lifting) case_prod_unfold max_agg parallel_comp.simps
          surjective_pairing)
    hence "let (e1, r1, d1) = m A p; (e2, r2, d2) = n A p in
        x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    thus ?thesis
      by (smt Un_iff combine_ele_rej_def conservative_def contra_subsetD disjoint_iff_not_equal
          electoral_module_def eq_module_result_def in_A max_agg max_aggregator_conservative
          module_m module_n par_creates_modules parallel_comp.simps profile split_disjoint3)
  qed
qed

lemma max_reject_iff_both_reject:
  assumes max_agg:  "a = Max_aggregator" and
          profile:  "finite_profile A p" and
          module_m: "electoral_module m" and
          module_n: "electoral_module n"
  shows "x \<in> reject (m \<parallel>\<^sub>a n) A p \<longleftrightarrow> (x \<in> reject m A p \<and> x \<in> reject n A p)"
proof -
  have "x \<in> reject (m \<parallel>\<^sub>a n) A p \<longrightarrow> (x \<in> reject m A p \<and> x \<in> reject n A p)"
  proof assume a: "x \<in> reject (m \<parallel>\<^sub>a n) A p"
    hence "let (e1, r1, d1) = m A p; (e2, r2, d2) = n A p in
        x \<in> fst (snd (Max_aggregator A (e1, r1, d1) (e2, r2, d2)))"
      by (smt case_prodI2 max_agg parallel_comp.simps)
    hence "let (e1, r1, d1) = m A p; (e2, r2, d2) = n A p in
        x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    thus "x \<in> reject m A p \<and> x \<in> reject n A p"
      by (smt Int_iff a electoral_module_def max_agg max_aggregator_reject_set module_m module_n
          parallel_comp.simps profile surjective_pairing)
  qed
  moreover have "(x \<in> reject m A p \<and> x \<in> reject n A p) \<longrightarrow> x \<in> reject (m \<parallel>\<^sub>a n) A p"
  proof assume a: "x \<in> reject m A p \<and> x \<in> reject n A p"
    hence "x \<notin> elect m A p \<and> x \<notin> defer m A p \<and> x \<notin> elect n A p \<and> x \<notin> defer n A p"
      by (metis IntI empty_iff module_m module_n profile split_disjoint3)
    thus "x \<in> reject (m \<parallel>\<^sub>a n) A p"
      by (smt CollectD DiffD1 Max_aggregator.simps Un_iff a electoral_module_element_in_defer
          max_agg max_aggregator_sound module_m module_n old.prod.inject par_creates_modules
          parallel_comp.simps prod.collapse prod.simps(2) profile reject_alternative_representation)
  qed
  ultimately show ?thesis
    by blast
qed

lemma max_reject_interaction1:
  assumes max_agg:  "a = Max_aggregator" and
          profile:  "finite_profile A p" and
          module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          rejected: "x \<in> reject n A p"
  shows "eq_module_result m (m \<parallel>\<^sub>a n) A p x"
  by (smt Set.set_insert contra_subsetD disjoint_insert(2) eq_module_result_commutative
      eq_module_result_def max_agg max_agg_eq_result max_reject_iff_both_reject module_m module_n
      profile reject_from_input rejected split_disjoint3)

lemma max_reject_interaction2:
  assumes max_agg:  "a = Max_aggregator" and
          profile:  "finite_profile A p" and
          module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          rejected: "x \<in> reject n A p"
  shows "eq_module_result (m \<parallel>\<^sub>a n) m A p x"
  by (simp add: eq_module_result_commutative max_agg max_reject_interaction1 module_m module_n
      profile rejected)

lemma max_reject_interaction3:
  assumes max_agg:  "a = Max_aggregator" and
          profile:  "finite_profile A p" and
          module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          rejected: "x \<in> reject m A p"
  shows "eq_module_result n (m \<parallel>\<^sub>a n) A p x"
  by (smt contra_subsetD disjoint_iff_not_equal eq_module_result_commutative eq_module_result_def
      max_agg max_agg_eq_result max_reject_iff_both_reject module_m module_n profile
      reject_from_input rejected split_disjoint3)

lemma max_reject_interaction4:
  assumes max_agg:  "a = Max_aggregator" and
          profile:  "finite_profile A p" and
          module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          rejected: "x \<in> reject m A p"
  shows "eq_module_result (m \<parallel>\<^sub>a n) n A p x"
  by (simp add: eq_module_result_commutative max_agg max_reject_interaction3 module_m module_n
      profile rejected)

lemma compatible_one_decides:
  assumes compatible:  "disjoint_compatible m n" and
          in_A:        "x \<in> A" and
          max_agg:     "a = Max_aggregator"
  shows "(\<forall>p. finite_profile A p \<longrightarrow> eq_module_result m (m \<parallel>\<^sub>a n) A p x) \<or>
         (\<forall>p. finite_profile A p \<longrightarrow> eq_module_result n (m \<parallel>\<^sub>a n) A p x)"
  by (metis DiffI compatible disjoint_compatible_def in_A max_agg max_reject_interaction1
      max_reject_interaction3)

lemma max_agg_reject_diffrent_representation:
  assumes max_agg:  "a = Max_aggregator" and
          module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          profile:  "finite_profile A p"
  shows "reject (m \<parallel>\<^sub>a n) A p = (reject m A p) \<inter> (reject n A p)"
proof -
  have "A = (elect m A p) \<union> (reject m A p) \<union> (defer m A p) \<and>
        A = (elect n A p) \<union> (reject n A p) \<union> (defer n A p)"
    by (simp add: module_m module_n profile split_unify_result)
  hence "A - ((elect m A p) \<union> (defer m A p)) = (reject m A p) \<and>
         A - ((elect n A p) \<union> (defer n A p)) = (reject n A p)"
    using module_m module_n profile reject_alternative_representation by auto
  hence "A - ((elect m A p) \<union> (elect n A p) \<union> (defer m A p) \<union> (defer n A p)) =
        (reject m A p) \<inter> (reject n A p)"
    by blast
  hence "let (e1, r1, d1) = m A p; (e2, r2, d2) = n A p in
      A - (e1 \<union> e2 \<union> d1 \<union> d2) = r1 \<inter> r2"
    by fastforce
  thus ?thesis
    using max_agg by fastforce
qed

(**************************************************)
(*** Composition Rules for Parallel Composition ***)
(**************************************************)

(* For any natural number and any linear order the affiliated pass and drop modules are compatible.
*)
theorem drop_pass_compatible[simp]:
  assumes order: "linear_order r"
  shows "disjoint_compatible (Drop_module n r) (Pass_module n r)"
proof -
  have "\<forall>S. finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. independent_of (Drop_module n r) S a \<and>
               (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Drop_module n r) S p)) \<and>
      (\<forall>a \<in> S-A. independent_of (Pass_module n r) S a \<and>
                 (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Pass_module n r) S p)))"
  proof fix S
  show "finite S \<longrightarrow> (\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. independent_of (Drop_module n r) S a \<and>
               (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Drop_module n r) S p)) \<and>
      (\<forall>a \<in> S-A. independent_of (Pass_module n r) S a \<and>
                 (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Pass_module n r) S p)))"
  proof assume fin: "finite S"
    obtain p where "finite_profile S p"
      by (metis empty_iff empty_set fin profile_on_def)
    show "\<exists>A \<subseteq> S.
        (\<forall>a \<in> A. independent_of (Drop_module n r) S a \<and>
                 (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Drop_module n r) S p)) \<and>
        (\<forall>a \<in> S-A. independent_of (Pass_module n r) S a \<and>
                   (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Pass_module n r) S p))"
    proof
      have same_A: "\<forall>p q. (finite_profile S p \<and> finite_profile S q) \<longrightarrow>
                          reject (Drop_module n r) S p = reject (Drop_module n r) S q"
        by auto
      let ?A = "reject (Drop_module n r) S p"
        have "?A \<subseteq> S"
          by auto
        moreover have "(\<forall>a \<in> ?A. independent_of (Drop_module n r) S a)"
          by (simp add: independent_of_def order)
        moreover have "\<forall>a \<in> ?A. \<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Drop_module n r) S p"
          by auto
        moreover have "(\<forall>a \<in> S-?A. independent_of (Pass_module n r) S a)"
          by (simp add: independent_of_def order)
        moreover have "\<forall>a \<in> S-?A. \<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Pass_module n r) S p"
          by auto
        ultimately show "?A \<subseteq> S \<and>
            (\<forall>a \<in> ?A. independent_of (Drop_module n r) S a \<and>
                      (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Drop_module n r) S p)) \<and>
            (\<forall>a \<in> S-?A. independent_of (Pass_module n r) S a \<and>
                        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (Pass_module n r) S p))"
        by simp
    qed
  qed qed
  thus ?thesis
    by (simp add: disjoint_compatible_def order)
qed

(* Using the max aggregator composing two compatible, defer lift invariant electoral modules
   creates a defer lift invariant electoral module.
*)
theorem defer_lift_invariant_par[simp]:
  assumes compatible: "disjoint_compatible m n" and
          monotone_m: "defer_lift_invariant m" and
          monotone_n: "defer_lift_invariant n" and
          max_agg:    "a = Max_aggregator"
  shows "defer_lift_invariant (m \<parallel>\<^sub>a n)"
proof -
  have "\<forall>S p q x. (x \<in> (defer (m \<parallel>\<^sub>a n) S p) \<and> lifted S p q x) \<longrightarrow> (m \<parallel>\<^sub>a n) S p = (m \<parallel>\<^sub>a n) S q"
  proof fix S
  show "\<forall>p q x. (x \<in> (defer (m \<parallel>\<^sub>a n) S p) \<and> lifted S p q x) \<longrightarrow> (m \<parallel>\<^sub>a n) S p = (m \<parallel>\<^sub>a n) S q"
  proof fix p
  show "\<forall>q x. (x \<in> (defer (m \<parallel>\<^sub>a n) S p) \<and> lifted S p q x) \<longrightarrow> (m \<parallel>\<^sub>a n) S p = (m \<parallel>\<^sub>a n) S q"
  proof fix q show "\<forall> x. (x \<in> (defer (m \<parallel>\<^sub>a n) S p) \<and> lifted S p q x) \<longrightarrow> (m \<parallel>\<^sub>a n) S p = (m \<parallel>\<^sub>a n) S q"
  proof fix x show "(x \<in> (defer (m \<parallel>\<^sub>a n) S p) \<and> lifted S p q x) \<longrightarrow> (m \<parallel>\<^sub>a n) S p = (m \<parallel>\<^sub>a n) S q"
  proof assume a: "x \<in> (defer (m \<parallel>\<^sub>a n) S p) \<and> lifted S p q x"
    hence profiles: "finite_profile S p \<and> finite_profile S q"
      by (simp add: lifted_def)
    from compatible obtain A::"'a set" where A: "A \<subseteq> S \<and>
        (\<forall>x \<in> A. independent_of m S x \<and> (\<forall>p. finite_profile S p \<longrightarrow> x \<in> reject m S p)) \<and>
        (\<forall>x \<in> S-A. independent_of n S x \<and> (\<forall>p. finite_profile S p \<longrightarrow> x \<in> reject n S p))"
      by (metis (no_types, lifting) disjoint_compatible_def profiles)
    have "\<forall>x \<in> S. eq_result_for (m \<parallel>\<^sub>a n) S p q x"
    proof cases
      assume a0: "x \<in> A"
      hence "x \<in> reject m S p"
        using A profiles by blast
      from this a have defer_n: "x \<in> defer n S p"
        by (metis DiffD1 DiffD2 compatible compatible_one_decides defer_alternative_representation
            disjoint_compatible_def electoral_module_element_in_elect_or_defer eq_module_result_def
            max_agg max_aggregator_sound par_creates_modules profiles)
      have "\<forall>x \<in> A. eq_module_result (m \<parallel>\<^sub>a n) n S p x"
        by (metis A compatible disjoint_compatible_def max_agg max_reject_interaction4 profiles)
      moreover have "\<forall>x \<in> S. eq_result_for n S p q x"
        by (smt defer_n a eq_result_for_def monotone_n profiles defer_lift_invariant_def)
      moreover have "\<forall>x \<in> A. eq_module_result n (m \<parallel>\<^sub>a n) S q x"
        by (metis A compatible disjoint_compatible_def max_agg max_reject_interaction3 profiles)
      ultimately have 00: "\<forall>x \<in> A. eq_result_for (m \<parallel>\<^sub>a n) S p q x"
        by (simp add: eq_module_result_def eq_result_for_def)
      have "\<forall>x \<in> S-A. eq_module_result (m \<parallel>\<^sub>a n) m S p x"
        by (metis A max_agg max_reject_interaction2 monotone_m monotone_n profiles
            defer_lift_invariant_def)
      moreover have "\<forall>x \<in> S. eq_result_for m S p q x"
        by (smt A a a0 eq_result_for_def independent_of_def lifted_impl_only_change profiles)
      moreover have "\<forall>x \<in> S-A. eq_module_result m (m \<parallel>\<^sub>a n) S q x"
        by (metis A max_agg max_reject_interaction1 monotone_m monotone_n profiles
            defer_lift_invariant_def)
      ultimately have 01: "\<forall>x \<in> S-A. eq_result_for (m \<parallel>\<^sub>a n) S p q x"
        by (smt eq_module_result_def eq_result_for_def profiles)
      from 00 01 show ?thesis
        by blast
    next
      assume "x \<notin> A"
      hence a1: "x \<in> S-A"
        by (metis (no_types, lifting) DiffI a compatible defer_from_input disjoint_compatible_def
            max_agg max_aggregator_sound par_creates_modules profiles subsetCE)
      hence "x \<in> reject n S p"
        using A profiles by blast
      from this a have defer_n: "x \<in> defer m S p"
        by (metis DiffD1 DiffD2 compatible compatible_one_decides defer_alternative_representation
            disjoint_compatible_def electoral_module_element_in_elect_or_defer eq_module_result_def
            max_agg max_aggregator_sound par_creates_modules profiles)
      have "\<forall>x \<in> A. eq_module_result (m \<parallel>\<^sub>a n) n S p x"
        by (metis A compatible disjoint_compatible_def max_agg max_reject_interaction4 profiles)
      moreover have "\<forall>x \<in> S. eq_result_for n S p q x"
        by (smt A a a1 eq_result_for_def independent_of_def lifted_impl_only_change profiles)
      moreover have "\<forall>x \<in> A. eq_module_result n (m \<parallel>\<^sub>a n) S q x"
        by (metis A compatible disjoint_compatible_def max_agg max_reject_interaction3 profiles)
      ultimately have 10: "\<forall>x \<in> A. eq_result_for (m \<parallel>\<^sub>a n) S p q x"
        by (simp add: eq_module_result_def eq_result_for_def)
      have "\<forall>x \<in> S-A. eq_module_result (m \<parallel>\<^sub>a n) m S p x"
        by (metis A max_agg max_reject_interaction2 monotone_m monotone_n profiles
            defer_lift_invariant_def)
      moreover have "\<forall>x \<in> S. eq_result_for m S p q x"
        by (smt a defer_n eq_result_for_def monotone_m profiles defer_lift_invariant_def)
      moreover have "\<forall>x \<in> S-A. eq_module_result m (m \<parallel>\<^sub>a n) S q x"
        by (metis A max_agg max_reject_interaction1 monotone_m monotone_n profiles
            defer_lift_invariant_def)
      ultimately have 11: "\<forall>x \<in> S-A. eq_result_for (m \<parallel>\<^sub>a n) S p q x"
        by (smt eq_module_result_def eq_result_for_def profiles)
      from 10 11 show ?thesis
        by blast
    qed
    thus "(m \<parallel>\<^sub>a n) S p = (m \<parallel>\<^sub>a n) S q"
      by (metis compatible disjoint_compatible_def forall_eq_result max_agg max_aggregator_sound
          par_creates_modules profiles)
  qed qed qed qed qed
  thus ?thesis
    by (smt max_agg max_aggregator_sound monotone_m monotone_n par_creates_modules
        defer_lift_invariant_def)
qed

(* Using a conservative aggregator composing two non electing electoral modules creates a non
   electing electoral module.
*)
theorem conservative_agg_comp_preserves_non_electing[simp]:
  assumes non_electing_m: "non_electing m" and
          non_electing_n: "non_electing n" and
          conservative: "conservative a"
        shows "non_electing (m \<parallel>\<^sub>a n)"
proof -
  have "(\<forall>A p. finite_profile A p \<longrightarrow> elect m A p = {} \<and> elect n A p = {})"
    using non_electing_def non_electing_m non_electing_n by blast
  hence "(\<forall>A p. finite_profile A p \<longrightarrow> elect_r (m A p) = {} \<and> elect_r (n A p) = {})"
    by simp
  moreover have "\<forall>A p. finite_profile A p \<longrightarrow> partition_of A (m A p)"
    using electoral_module_def non_electing_def non_electing_m by auto
  moreover have "\<forall>A p. finite_profile A p \<longrightarrow> partition_of A (n A p)"
    using electoral_module_def non_electing_def non_electing_n by auto
  moreover have conservative_def_inline: "aggregator a \<and> (\<forall>A e1 e2 d1 d2 r1 r2.
    ((partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
    elect_r (a A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
    reject_r (a A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2) \<and>
    defer_r (a A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2)))"
    using conservative conservative_def by blast
  ultimately have  "(\<forall>A p. finite_profile A p \<longrightarrow>
    elect_r (a A (elect m A p, reject m A p, defer m A p) (elect n A p, reject n A p, defer n A p))
    \<subseteq> {})"
    by (smt combine_ele_rej_def fst_def sup_bot_right)
  hence "(\<forall>A p. finite_profile A p \<longrightarrow>
    elect_r (a A (m A p) (n A p)) \<subseteq> {})"
    by simp
  thus ?thesis
    by (metis conservative_def_inline non_electing_def non_electing_m non_electing_n
        par_creates_modules parallel_comp.simps subset_empty)
qed

lemma eliminates_1_par_help:
  assumes max_agg:           "a = Max_aggregator" and
          compatible:        "disjoint_compatible x y" and
          profile:           "finite_profile S p" and
          reject_sum:        "card (reject x S p) + card (reject y S p) = card S + n"
  shows "card (reject (x \<parallel>\<^sub>a y) S p) = n"
proof -
  from compatible obtain A where A: "A \<subseteq> S \<and>
      (\<forall>a \<in> A. independent_of x S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject x S p)) \<and>
      (\<forall>a \<in> S-A. independent_of y S a \<and> (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject y S p))"
    by (metis disjoint_compatible_def profile)
  from profile compatible
  have reject_representation: "reject (x \<parallel>\<^sub>a y) S p = (reject x S p) \<inter> (reject y S p)"
    using max_agg max_agg_reject_diffrent_representation disjoint_compatible_def by blast
  have "electoral_module x \<and> electoral_module y"
    using compatible disjoint_compatible_def by auto
  hence subsets: "(reject x S p) \<subseteq> S \<and> (reject y S p) \<subseteq> S"
    by (simp add: profile reject_from_input)
  hence "finite (reject x S p) \<and> finite (reject y S p)"
    using rev_finite_subset profile reject_from_input by auto
  hence 0: "card (reject (x \<parallel>\<^sub>a y) S p) =
         card S + n - card ((reject x S p) \<union> (reject y S p))"
    using card_Un_Int reject_representation reject_sum by fastforce
  have "\<forall>a \<in> S. a \<in> (reject x S p) \<or> a \<in> (reject y S p)"
    using A profile by blast
  hence 1: "card ((reject x S p) \<union> (reject y S p)) = card S"
    by (smt subsets subset_eq sup.absorb_iff1 sup.cobounded1 sup_left_commute)
  from 0 1 show "card (reject (x \<parallel>\<^sub>a y) S p) = n"
    by simp
qed

(* Using the max aggregator composing two compatible modules, one which is non electing and defers
   exactly 1 alternative, and one which rejects exactly 2 alternatives, results in an electoral
   module, that eliminates exactly 1 alternative.
*)
theorem eliminates_1_par[simp]:
  assumes "defers 1 m" and
          "non_electing m" and
          "rejects 2 n" and
          "disjoint_compatible m n" and
          "a = Max_aggregator"
shows "eliminates 1 (m \<parallel>\<^sub>a n)"
proof -
  have "\<forall>A p. (card A > 1 \<and> finite_profile A p) \<longrightarrow> card (reject (m \<parallel>\<^sub>a n) A p) = 1"
  proof fix A show "\<forall>p. (card A > 1 \<and> finite_profile A p) \<longrightarrow> card (reject (m \<parallel>\<^sub>a n) A p) = 1"
  proof fix p show "(card A > 1 \<and> finite_profile A p) \<longrightarrow> card (reject (m \<parallel>\<^sub>a n) A p) = 1"
  proof assume asm0: "card A > 1 \<and> finite_profile A p"
    have card_geq_1: "card A \<ge> 1"
      using asm0 dual_order.strict_trans2 less_imp_le_nat by blast
    have module: "electoral_module m"
      using assms(2) non_electing_def by auto
    have "card (elect m A p) = 0"
      by (metis asm0 assms(2) card_empty non_electing_def)
    moreover from card_geq_1 have "card (defer m A p) = 1"
      using assms(1) module by (simp add: asm0 defers_def)
    ultimately have card_reject_m: "card (reject m A p) = card A - 1"
    proof -
      have "finite A"
        by (simp add: asm0)
      moreover have "partition_of A (elect m A p, reject m A p, defer m A p)"
        using asm0 electoral_module_def module by auto
      ultimately have "card A = card (elect m A p) + card (reject m A p) + card (defer m A p)"
        using partition_card by blast
      thus ?thesis
        by (simp add: \<open>card (defer m A p) = 1\<close> \<open>card (elect m A p) = 0\<close>)
    qed
    have case1: "card A \<ge> 2"
      using asm0 by auto
    from case1 have card_reject_n: "card (reject n A p) = 2"
      using asm0 assms(3) rejects_def by blast
    from card_reject_m card_reject_n have "card (reject m A p) + card (reject n A p) = card A + 1"
      using card_geq_1 by linarith
    from this assms(5) assms(4) asm0 card_reject_m card_reject_n
    show "card (reject (m \<parallel>\<^sub>a n) A p) = 1"
      using eliminates_1_par_help by blast
  qed qed qed
  moreover have "electoral_module (m \<parallel>\<^sub>a n)"
    by (metis assms(4) assms(5) disjoint_compatible_def max_aggregator_sound par_creates_modules)
  ultimately show ?thesis
    using eliminates_def by blast
qed

end

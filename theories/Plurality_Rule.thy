(*  File:       Plurality_Rule.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Voting Rules\<close>

section \<open>Plurality Rule\<close>

theory Plurality_Rule
  imports "Compositional_Structures/Basic_Modules/Plurality_Module"
          "Compositional_Structures/Revision_Composition"
          "Compositional_Structures/Elect_Composition"
begin

text \<open>
  This is a definition of the plurality voting rule as elimination module as well as directly.
  In the former one, the max operator of the set of the scores of all alternatives is evaluated
  and is used as the threshold value.
\<close>

subsection \<open>Definition\<close>

fun plurality_rule :: "('a, 'v, 'a Result) Electoral_Module" where
  "plurality_rule V A p = elector plurality V A p"

fun plurality_rule' :: "('a, 'v, 'a Result) Electoral_Module" where
  "plurality_rule' V A p =
      (if finite A
        then ({a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a},
              {a \<in> A. \<exists> x \<in> A. win_count V p x > win_count V p a},
              {})
        else (A, {}, {}))"

lemma plurality_revision_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "plurality V A p = (plurality_rule\<down>) V A p"
  by fastforce

lemma plurality'_revision_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "plurality' V A p = (plurality_rule'\<down>) V A p"
proof (unfold plurality'.simps revision_composition.simps,
        intro prod_eqI equalityI subsetI prod.sel)
  fix b :: "'a"
  assume
    assm: "b \<in> fst
              (if finite A
               then ({}, {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x},
                     {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})
               else ({}, {}, A))"
  have "finite A \<longrightarrow> b \<in> {}"
    using assm
    by force
  moreover have "infinite A \<longrightarrow> b \<in> {}"
    using assm
    by fastforce
  ultimately show
    "b \<in> fst ({}, A - elect plurality_rule' V A p, elect plurality_rule' V A p)"
    by safe
next
  fix b :: "'a"
  assume "b \<in> fst ({}, A - elect plurality_rule' V A p, elect plurality_rule' V A p)"
  thus "b \<in> fst
          (if finite A
           then ({}, {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x},
                 {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})
           else ({}, {}, A))"
    by force
next
  fix b :: "'a"
  assume
    assm: "b \<in> fst (snd
              (if finite A
               then ({}, {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x},
                     {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})
               else ({}, {}, A)))"
  have "finite A \<longrightarrow>
    b \<in> A - {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a}"
    using assm
    by fastforce
  moreover have "infinite A \<longrightarrow> b \<in> {}"
    using assm
    by fastforce
  ultimately show
    "b \<in> fst (snd ({}, A - elect plurality_rule' V A p, elect plurality_rule' V A p))"
    by force
next
  fix b :: "'a"
  assume
    assm: "b \<in>
      fst (snd ({}, A - elect plurality_rule' V A p, elect plurality_rule' V A p))"
  have "finite A \<longrightarrow>
    b \<in> A - {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a}"
    using assm
    by fastforce
  moreover have "infinite A \<longrightarrow> b \<in> {}"
    using assm
    by fastforce
  ultimately show
    "b \<in> fst (snd
        (if finite A
         then ({}, {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x},
               {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})
         else ({}, {}, A)))"
    using linorder_not_less
    by force
next
  fix b :: "'a"
  assume
    assm: "b \<in> snd (snd
              (if finite A
               then ({}, {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x},
                     {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})
               else ({}, {}, A)))"
  have "finite A \<longrightarrow>
    b \<in> A - {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x}"
    using assm
    by fastforce
  moreover have "infinite A \<longrightarrow> b \<in> A"
    using assm
    by fastforce
  ultimately have "b \<in> elect plurality_rule' V A p"
    by force
  thus "b \<in> snd (snd
    ({}, A - elect plurality_rule' V A p, elect plurality_rule' V A p))"
    by simp
next
  fix b :: "'a"
  assume assm:
    "b \<in> snd (snd ({}, A - elect plurality_rule' V A p, elect plurality_rule' V A p))"
  have "finite A \<longrightarrow>
    b \<in> A - {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x}"
    using assm
    by fastforce
  moreover have "infinite A \<longrightarrow> b \<in> A"
    using assm
    by fastforce
  ultimately show "b \<in> snd (snd
              (if finite A
               then ({}, {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x},
                     {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a})
               else ({}, {}, A)))"
    by force
qed

lemma plurality_rule_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "plurality_rule V A p = plurality_rule' V A p"
proof (unfold plurality_rule.simps)
  have plurality_rule'_rev_equiv_plurality:
    "plurality V A p = (plurality_rule'\<down>) V A p"
    using plurality_mod_equiv plurality'_revision_equiv
    by metis
  have "defer (elector plurality) V A p = defer plurality_rule' V A p"
    by force
  moreover have "reject (elector plurality) V A p = reject plurality_rule' V A p"
    using plurality_rule'_rev_equiv_plurality
    by force
  moreover have "elect (elector plurality) V A p = elect plurality_rule' V A p"
    using plurality_rule'_rev_equiv_plurality
    by force
  ultimately show "elector plurality V A p = plurality_rule' V A p"
    using prod_eqI
    by (metis (mono_tags, lifting))
qed

subsection \<open>Soundness\<close>

theorem plurality_rule_sound[simp]: "\<S>\<C>\<F>_result.electoral_module plurality_rule"
  unfolding plurality_rule.simps
  using elector_sound plurality_sound
  by metis

theorem plurality_rule'_sound[simp]: "\<S>\<C>\<F>_result.electoral_module plurality_rule'"
proof (unfold \<S>\<C>\<F>_result.electoral_module.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  have "disjoint3 (
      {a \<in> A. \<forall> a' \<in> A. win_count V p a' \<le> win_count V p a},
      {a \<in> A. \<exists> a' \<in> A. win_count V p a < win_count V p a'},
      {})"
    by auto
  moreover have
    "{a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a} \<union>
      {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x} = A"
    using not_le_imp_less
    by auto
  ultimately show "well_formed_\<S>\<C>\<F> A (plurality_rule' V A p)"
    by simp
qed

lemma voters_determine_plurality_rule: "voters_determine_election plurality_rule"
  unfolding plurality_rule.simps
  using voters_determine_elector voters_determine_plurality
  by blast

lemma voters_determine_plurality_rule': "voters_determine_election plurality_rule'"
proof (unfold voters_determine_election.simps, safe)
  fix
    A :: "'k set" and
    V :: "'v set" and
    p p' :: "('k, 'v) Profile"
  assume "\<forall> v \<in> V. p v = p' v"
  thus "plurality_rule' V A p = plurality_rule' V A p'"
    using voters_determine_plurality_rule plurality_rule_equiv
    unfolding voters_determine_election.simps
    by (metis (full_types))
qed

subsection \<open>Electing\<close>

lemma plurality_rule_elect_non_empty:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "A \<noteq> {}" and
    "finite A"
  shows "elect plurality_rule V A p \<noteq> {}"
proof
  assume plurality_elect_none: "elect plurality_rule V A p = {}"
  obtain max :: "enat" where
    max: "max = Max (win_count V p ` A)"
    by simp
  then obtain a :: "'a" where
    max_a: "win_count V p a = max \<and> a \<in> A"
    using Max_in assms empty_is_image finite_imageI imageE
    by (metis (no_types, lifting))
  hence "\<forall> a' \<in> A. win_count V p a' \<le> win_count V p a"
    using assms max
    by simp
  moreover have "a \<in> A"
    using max_a
    by simp
  ultimately have "a \<in> {a' \<in> A. \<forall> c \<in> A. win_count V p c \<le> win_count V p a'}"
    by blast
  hence "a \<in> elect plurality_rule' V A p"
    by simp
  moreover have "elect plurality_rule' V A p = defer plurality V A p"
    using plurality_revision_equiv plurality_rule_equiv snd_conv
    unfolding revision_composition.simps
    by (metis (no_types, opaque_lifting))
  ultimately have "a \<in> defer plurality V A p"
    by blast
  hence "a \<in> elect plurality_rule V A p"
    by simp
  thus False
    using plurality_elect_none all_not_in_conv
    by metis
qed

lemma plurality_rule'_elect_non_empty:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "A \<noteq> {}" and
    "profile V A p" and
    "finite A"
  shows "elect plurality_rule' V A p \<noteq> {}"
  using assms plurality_rule_elect_non_empty plurality_rule_equiv
  by metis

text \<open>
  The plurality module is electing.
\<close>

theorem plurality_rule_electing[simp]: "electing plurality_rule"
proof (unfold electing_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module plurality_rule"
    using plurality_rule_sound
    by simp
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile" and
    a :: "'b"
  assume
    fin_A: "finite A" and
    prof_p: "profile V A p" and
    elect_none: "elect plurality_rule V A p = {}" and
    a_in_A: "a \<in> A"
  have "\<forall> B W q. B \<noteq> {} \<and> finite B \<and> profile W B q
          \<longrightarrow> elect plurality_rule W B q \<noteq> {}"
    using plurality_rule_elect_non_empty
    by (metis (no_types))
  hence empty_A: "A = {}"
    using fin_A prof_p elect_none
    by (metis (no_types))
  thus "a \<in> {}"
    using a_in_A
    by simp
qed

theorem plurality_rule'_electing[simp]: "electing plurality_rule'"
proof (unfold electing_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module plurality_rule'"
    using plurality_rule'_sound
    by metis
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile" and
    a :: "'b"
  assume
    fin_A: "finite A" and
    prof_p: "profile V A p" and
    no_elect': "elect plurality_rule' V A p = {}" and
    a_in_A: "a \<in> A"
  have A_nonempty: "A \<noteq> {}"
    using a_in_A
    by blast
  have "elect plurality_rule V A p = {}"
    using no_elect' plurality_rule_equiv
    by metis
  moreover have "elect plurality_rule V A p \<noteq> {}"
    using fin_A prof_p A_nonempty plurality_rule'_elect_non_empty plurality_rule_equiv
    by metis
  ultimately show "a \<in> {}"
    by force
qed

subsection \<open>Properties\<close>

lemma plurality_rule_inv_mono_eq:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    elect_a: "a \<in> elect plurality_rule V A p" and
    lift_a: "lifted V A p q a"
  shows "elect plurality_rule V A q = elect plurality_rule V A p
          \<or> elect plurality_rule V A q = {a}"
proof -
  have "a \<in> elect (elector plurality) V A p"
    using elect_a
    by simp
  moreover have eq_p: "elect (elector plurality) V A p = defer plurality V A p"
    by simp
  ultimately have "a \<in> defer plurality V A p"
    by blast
  hence "defer plurality V A q = defer plurality V A p
          \<or> defer plurality V A q = {a}"
    using lift_a plurality_def_inv_mono_alts
    by metis
  moreover have "elect (elector plurality) V A q = defer plurality V A q"
    by simp
  ultimately show
    "elect plurality_rule V A q = elect plurality_rule V A p
      \<or> elect plurality_rule V A q = {a}"
    using eq_p
    by simp
qed

lemma plurality_rule'_inv_mono_eq:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    "a \<in> elect plurality_rule' V A p" and
    "lifted V A p q a"
  shows "elect plurality_rule' V A q = elect plurality_rule' V A p
          \<or> elect plurality_rule' V A q = {a}"
  using assms plurality_rule_equiv plurality_rule_inv_mono_eq
  by (metis (no_types))

text \<open>
  The plurality rule is invariant-monotone.
\<close>

theorem plurality_rule_inv_mono[simp]: "invariant_monotonicity plurality_rule"
proof (unfold invariant_monotonicity_def, intro conjI impI allI)
  show "\<S>\<C>\<F>_result.electoral_module plurality_rule"
    using plurality_rule_sound
    by metis
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p q :: "('b, 'a) Profile" and
    a :: "'b"
  assume "a \<in> elect plurality_rule V A p \<and> Profile.lifted V A p q a"
  thus "elect plurality_rule V A q = elect plurality_rule V A p
          \<or> elect plurality_rule V A q = {a}"
    using plurality_rule_inv_mono_eq
    by metis
qed

theorem plurality_rule'_inv_mono[simp]: "invariant_monotonicity plurality_rule'"
proof -
  have "(plurality_rule::('k, 'v, 'k Result) Electoral_Module) = plurality_rule'"
    using plurality_rule_equiv
    by blast
  thus ?thesis
    using plurality_rule_inv_mono
    by (metis (full_types))
qed

subsubsection \<open>(Weak) Monotonicity\<close>

theorem plurality_rule_monotone: "monotonicity plurality_rule"
proof (unfold monotonicity_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module plurality_rule"
    using plurality_rule_sound
    by (metis (no_types))
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p q :: "('b, 'a) Profile" and
    a :: "'b"
  assume
    "a \<in> elect plurality_rule V A p" and
    "Profile.lifted V A p q a"
  thus "a \<in> elect plurality_rule V A q"
    using insertI1 plurality_rule_inv_mono_eq
    by (metis (no_types))
qed

end
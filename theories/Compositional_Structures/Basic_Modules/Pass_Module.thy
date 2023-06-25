(*  File:       Pass_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Pass Module\<close>

theory Pass_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  This is a family of electoral modules. For a natural number n and a
  lexicon (linear order) r of all alternatives, the according pass module
  defers the lexicographically first n alternatives (from A) and rejects
  the rest. It is primarily used as counterpart to the drop module in a
  parallel composition in order to segment the alternatives into two groups.
\<close>

subsection \<open>Definition\<close>

fun pass_module :: "nat \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "pass_module n r A p =
    ({},
    {a \<in> A. rank (limit A r) a > n},
    {a \<in> A. rank (limit A r) a \<le> n})"

subsection \<open>Soundness\<close>

theorem pass_mod_sound[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: nat
  shows "electoral_module (pass_module n r)"
proof (intro electoral_modI)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  let ?mod = "pass_module n r"
  have "\<forall> a \<in> A. a \<in> {x \<in> A. rank (limit A r) x > n} \<or>
                 a \<in> {x \<in> A. rank (limit A r) x \<le> n}"
    using CollectI not_less
    by metis
  hence "{a \<in> A. rank (limit A r) a > n} \<union> {a \<in> A. rank (limit A r) a \<le> n} = A"
    by blast
  hence "set_equals_partition A (pass_module n r A p)"
    by simp
  moreover have
    "\<forall> a \<in> A.
      \<not> (a \<in> {x \<in> A. rank (limit A r) x > n} \<and> a \<in> {x \<in> A. rank (limit A r) x \<le> n})"
    by simp
  hence "{a \<in> A. rank (limit A r) a > n} \<inter> {a \<in> A. rank (limit A r) a \<le> n} = {}"
    by blast
  ultimately show "well_formed A (?mod A p)"
    by simp
qed

subsection \<open>Non-Blocking\<close>

text \<open>
  The pass module is non-blocking.
\<close>

theorem pass_mod_non_blocking[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: nat
  assumes
    order: "linear_order r" and
    g0_n:  "n > 0"
  shows "non_blocking (pass_module n r)"
proof (unfold non_blocking_def, safe)
  show "electoral_module (pass_module n r)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    a :: "'a"
  assume
    fin_A: "finite A" and
    rej_pass_A: "reject (pass_module n r) A p = A" and
    a_in_A: "a \<in> A"
  moreover have "linear_order_on A (limit A r)"
    using limit_presv_lin_ord order top_greatest
    by metis
  moreover have
    "\<exists> b \<in> A. above (limit A r) b = {b} \<and>
      (\<forall> c \<in> A. above (limit A r) c = {c} \<longrightarrow> c = b)"
    using calculation above_one
    by blast
  ultimately have "{b \<in> A. rank (limit A r) b > n} \<noteq> A"
    using Suc_leI g0_n leD mem_Collect_eq above_rank
    unfolding One_nat_def
    by (metis (no_types, lifting))
  hence "reject (pass_module n r) A p \<noteq> A"
    by simp
  thus "a \<in> {}"
    using rej_pass_A
    by simp
qed

subsection \<open>Non-Electing\<close>

text \<open>
  The pass module is non-electing.
\<close>

theorem pass_mod_non_electing[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: nat
  assumes "linear_order r"
  shows "non_electing (pass_module n r)"
  unfolding non_electing_def
  using assms
  by simp

subsection \<open>Properties\<close>


text \<open>
  The pass module is strictly defer-monotone.
\<close>

theorem pass_mod_dl_inv[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: nat
  assumes "linear_order r"
  shows "defer_lift_invariance (pass_module n r)"
  unfolding defer_lift_invariance_def
  using assms
  by simp

theorem pass_zero_mod_def_zero[simp]:
  fixes r :: "'a Preference_Relation"
  assumes "linear_order r"
  shows "defers 0 (pass_module 0 r)"
proof (unfold defers_def, safe)
  show "electoral_module (pass_module 0 r)"
    using pass_mod_sound assms
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    card_pos: "0 \<le> card A" and
    finite_A: "finite A" and
    prof_A: "profile A p"
  have "linear_order_on A (limit A r)"
    using assms limit_presv_lin_ord
    by blast
  hence limit_is_connex: "connex A (limit A r)"
    using lin_ord_imp_connex
    by simp
  have "\<forall> n. (n::nat) \<le> 0 \<longrightarrow> n = 0"
    by blast
  hence "\<forall> a A'. a \<in> A' \<and> a \<in> A \<longrightarrow> connex A' (limit A r) \<longrightarrow> \<not> rank (limit A r) a \<le> 0"
    using above_connex above_presv_limit card_eq_0_iff equals0D finite_A assms rev_finite_subset
    unfolding rank.simps
    by (metis (no_types))
  hence "{a \<in> A. rank (limit A r) a \<le> 0} = {}"
    using limit_is_connex
    by simp
  hence "card {a \<in> A. rank (limit A r) a \<le> 0} = 0"
    using card.empty
    by metis
  thus "card (defer (pass_module 0 r) A p) = 0"
    by simp
qed

text \<open>
  For any natural number n and any linear order, the according pass module
  defers n alternatives (if there are n alternatives).
  NOTE: The induction proof is still missing. The following are the proofs
  for n=1 and n=2.
\<close>

theorem pass_one_mod_def_one[simp]:
  fixes r :: "'a Preference_Relation"
  assumes "linear_order r"
  shows "defers 1 (pass_module 1 r)"
proof (unfold defers_def, safe)
  show "electoral_module (pass_module 1 r)"
    using pass_mod_sound assms
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    card_pos: "1 \<le> card A" and
    finite_A: "finite A" and
    prof_A: "profile A p"
  show "card (defer (pass_module 1 r) A p) = 1"
  proof -
    have "A \<noteq> {}"
      using card_pos
      by auto
    moreover have lin_ord_on_A: "linear_order_on A (limit A r)"
      using assms limit_presv_lin_ord
      by blast
    ultimately have winner_exists:
      "\<exists> a \<in> A. above (limit A r) a = {a} \<and> (\<forall> b \<in> A. above (limit A r) b = {b} \<longrightarrow> b = a)"
      using finite_A
      by (simp add: above_one)
    then obtain w where w_unique_top:
      "above (limit A r) w = {w} \<and> (\<forall> a \<in> A. above (limit A r) a = {a} \<longrightarrow> a = w)"
      using above_one
      by auto
    hence "{a \<in> A. rank (limit A r) a \<le> 1} = {w}"
    proof
      assume
        w_top: "above (limit A r) w = {w}" and
        w_unique: "\<forall> a \<in> A. above (limit A r) a = {a} \<longrightarrow> a = w"
      have "rank (limit A r) w \<le> 1"
        using w_top
        by auto
      hence "{w} \<subseteq> {a \<in> A. rank (limit A r) a \<le> 1}"
        using winner_exists w_unique_top
        by blast
      moreover have "{a \<in> A. rank (limit A r) a \<le> 1} \<subseteq> {w}"
      proof
        fix a :: "'a"
        assume a_in_winner_set: "a \<in> {b \<in> A. rank (limit A r) b \<le> 1}"
        hence a_in_A: "a \<in> A"
          by auto
        hence connex_limit: "connex A (limit A r)"
          using lin_ord_imp_connex lin_ord_on_A
          by simp
        hence "let q = limit A r in a \<preceq>\<^sub>q a"
          using connex_limit above_connex pref_imp_in_above a_in_A
          by metis
        hence "(a, a) \<in> limit A r"
          by simp
        hence a_above_a: "a \<in> above (limit A r) a"
          unfolding above_def
          by simp
        have "above (limit A r) a \<subseteq> A"
          using above_presv_limit assms
          by fastforce
        hence above_finite: "finite (above (limit A r) a)"
          using finite_A finite_subset
          by simp
        have "rank (limit A r) a \<le> 1"
          using a_in_winner_set
          by simp
        moreover have "rank (limit A r) a \<ge> 1"
          using One_nat_def Suc_leI above_finite card_eq_0_iff equals0D neq0_conv a_above_a
          unfolding rank.simps
          by metis
        ultimately have "rank (limit A r) a = 1"
          by simp
        hence "{a} = above (limit A r) a"
          using a_above_a lin_ord_on_A rank_one_2
          by metis
        hence "a = w"
          using w_unique
          by (simp add: a_in_A)
        thus "a \<in> {w}"
          by simp
      qed
      ultimately have "{w} = {a \<in> A. rank (limit A r) a \<le> 1}"
        by auto
      thus ?thesis
        by simp
    qed
    thus "card (defer (pass_module 1 r) A p) = 1"
      by simp
  qed
qed

theorem pass_two_mod_def_two:
  fixes r :: "'a Preference_Relation"
  assumes "linear_order r"
  shows "defers 2 (pass_module 2 r)"
proof (unfold defers_def, safe)
  show "electoral_module (pass_module 2 r)"
    using assms
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    min_2_card: "2 \<le> card A" and
    fin_A: "finite A" and
    prof_A: "profile A p"
  from min_2_card
  have not_empty_A: "A \<noteq> {}"
    by auto
  moreover have limit_A_order: "linear_order_on A (limit A r)"
    using limit_presv_lin_ord assms
    by auto
  ultimately obtain a where
    "above (limit A r) a = {a}"
    using above_one min_2_card fin_A prof_A
    by blast
  hence "\<forall> b \<in> A. let q = limit A r in (b \<preceq>\<^sub>q a)"
    using limit_A_order pref_imp_in_above empty_iff insert_iff insert_subset above_presv_limit
          assms connex_def lin_ord_imp_connex
    by metis
  hence a_best: "\<forall> b \<in> A. (b, a) \<in> limit A r"
    by simp
  hence a_above: "\<forall> b \<in> A. a \<in> above (limit A r) b"
    unfolding above_def
    by simp
  from a_above
  have "a \<in> {a \<in> A. rank (limit A r) a \<le> 2}"
    using CollectI Suc_leI not_empty_A a_above card_UNIV_bool card_eq_0_iff card_insert_disjoint
          empty_iff fin_A finite.emptyI insert_iff limit_A_order above_one UNIV_bool nat.simps(3)
          zero_less_Suc One_nat_def above_rank
    by (metis (no_types, lifting))
  hence a_in_defer: "a \<in> defer (pass_module 2 r) A p"
    by simp
  have "finite (A - {a})"
    using fin_A
    by simp
  moreover have A_not_only_a: "A - {a} \<noteq> {}"
    using min_2_card Diff_empty Diff_idemp Diff_insert0 One_nat_def not_empty_A card.insert_remove
          card_eq_0_iff finite.emptyI insert_Diff numeral_le_one_iff semiring_norm(69) card.empty
    by metis
  moreover have limit_A_without_a_order:
    "linear_order_on (A - {a}) (limit (A - {a}) r)"
    using limit_presv_lin_ord assms top_greatest
    by blast
  ultimately obtain b where
    b: "above (limit (A - {a}) r) b = {b}"
    using above_one
    by metis
  hence "\<forall> c \<in> A - {a}. let q = limit (A - {a}) r in (c \<preceq>\<^sub>q b)"
    using limit_A_without_a_order pref_imp_in_above empty_iff insert_iff insert_subset
          above_presv_limit assms connex_def lin_ord_imp_connex
    by metis
  hence b_in_limit: "\<forall> c \<in> A - {a}. (c, b) \<in> limit (A - {a}) r"
    by simp
  hence b_best: "\<forall> c \<in> A - {a}. (c, b) \<in> limit A r"
    by auto
  hence c_not_above_b: "\<forall> c \<in> A - {a, b}. c \<notin> above (limit A r) b"
    using b Diff_iff Diff_insert2 above_presv_limit insert_subset assms limit_presv_above
          limit_presv_above_2
    by metis
  moreover have above_subset: "above (limit A r) b \<subseteq> A"
    using above_presv_limit assms
    by metis
  moreover have b_above_b: "b \<in> above (limit A r) b"
    using b b_best above_presv_limit mem_Collect_eq assms insert_subset
    unfolding above_def
    by metis
  ultimately have above_b_eq_ab: "above (limit A r) b = {a, b}"
    using a_above
    by auto
  hence card_above_b_eq_two: "rank (limit A r) b = 2"
    using A_not_only_a b_in_limit
    by auto
  hence b_in_defer: "b \<in> defer (pass_module 2 r) A p"
    using b_above_b above_subset
    by auto
  from b_best
  have b_above: "\<forall> c \<in> A - {a}. b \<in> above (limit A r) c"
    using mem_Collect_eq
    unfolding above_def
    by metis
  have "connex A (limit A r)"
    using limit_A_order lin_ord_imp_connex
    by auto
  hence "\<forall> c \<in> A. c \<in> above (limit A r) c"
    by (simp add: above_connex)
  hence "\<forall> c \<in> A - {a, b}. {a, b, c} \<subseteq> above (limit A r) c"
    using a_above b_above
    by auto
  moreover have "\<forall> c \<in> A - {a, b}. card {a, b, c} = 3"
    using DiffE Suc_1 above_b_eq_ab card_above_b_eq_two above_subset card_insert_disjoint
          fin_A finite_subset insert_commute numeral_3_eq_3
    unfolding One_nat_def rank.simps
    by metis
  ultimately have "\<forall> c \<in> A - {a, b}. rank (limit A r) c \<ge> 3"
    using card_mono fin_A finite_subset above_presv_limit assms
    unfolding rank.simps
    by metis
  hence "\<forall> c \<in> A - {a, b}. rank (limit A r) c > 2"
    using less_le_trans numeral_less_iff order_refl semiring_norm(79)
    by metis
  hence "\<forall> c \<in> A - {a, b}. c \<notin> defer (pass_module 2 r) A p"
    by (simp add: not_le)
  moreover have "defer (pass_module 2 r) A p \<subseteq> A"
    by auto
  ultimately have "defer (pass_module 2 r) A p \<subseteq> {a, b}"
    by blast
  hence "defer (pass_module 2 r) A p = {a, b}"
    using a_in_defer b_in_defer
    by fastforce
  thus "card (defer (pass_module 2 r) A p) = 2"
    using above_b_eq_ab card_above_b_eq_two
    unfolding rank.simps
    by presburger
qed

end

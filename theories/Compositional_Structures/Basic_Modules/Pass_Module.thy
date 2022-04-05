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
    {a \<in> A. card(above (limit A r) a) > n},
    {a \<in> A. card(above (limit A r) a) \<le> n})"

subsection \<open>Soundness\<close>

theorem pass_mod_sound[simp]:
  assumes "linear_order r"
  shows "electoral_module (pass_module n r)"
proof (intro electoral_modI)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  let ?mod = "pass_module n r"
  have
    "(\<forall> a \<in> A. a \<in> {x \<in> A. card(above (limit A r) x) > n} \<or>
              a \<in> {x \<in> A. card(above (limit A r) x) \<le> n})"
    using CollectI not_less
    by metis
  hence
    "{a \<in> A. card(above (limit A r) a) > n} \<union>
      {a \<in> A. card(above (limit A r) a) \<le> n} = A"
    by blast
  hence 0: "set_equals_partition A (pass_module n r A p)"
    by simp
  have
    "(\<forall> a \<in> A. \<not>(a \<in> {x \<in> A. card(above (limit A r) x) > n} \<and>
                 a \<in> {x \<in> A. card(above (limit A r) x) \<le> n}))"
    by auto
  hence
    "{a \<in> A. card(above (limit A r) a) > n} \<inter>
      {a \<in> A. card(above (limit A r) a) \<le> n} = {}"
    by blast
  hence 1: "disjoint3 (?mod A p)"
    by simp
  from 0 1
  show "well_formed A (?mod A p)"
    by simp
qed

subsection \<open>Non-Blocking\<close>

text \<open>
  The pass module is non-blocking.
\<close>

theorem pass_mod_non_blocking[simp]:
  assumes
    order: "linear_order r" and
    g0_n:  "n > 0"
  shows "non_blocking (pass_module n r)"
proof (unfold non_blocking_def, safe, simp_all)
  show "electoral_module (pass_module n r)"
    using pass_mod_sound order
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    card_A:
    "{a \<in> A. n <
      card (above
        {(a, b). (a, b) \<in> r \<and>
          a \<in> A \<and> b \<in> A} a)} = A" and
    x_in_A: "x \<in> A"
  have lin_ord_A:
    "linear_order_on A (limit A r)"
    using limit_presv_lin_ord order top_greatest
    by metis
  have
    "\<exists> a \<in> A. above (limit A r) a = {a} \<and>
      (\<forall> x \<in> A. above (limit A r) x = {x} \<longrightarrow> x = a)"
    using above_one fin_A lin_ord_A x_in_A
    by blast
  hence not_all:
    "{a \<in> A. card(above (limit A r) a) > n} \<noteq> A"
    using Suc_leI assms(2) is_singletonI
          is_singleton_altdef leD mem_Collect_eq
    unfolding One_nat_def
    by (metis (no_types, lifting))
  hence "reject (pass_module n r) A p \<noteq> A"
    by simp
  thus False
    using order card_A
    by simp
qed

subsection \<open>Non-Electing\<close>

text \<open>
  The pass module is non-electing.
\<close>

theorem pass_mod_non_electing[simp]:
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
  assumes "linear_order r"
  shows "defer_lift_invariance (pass_module n r)"
  unfolding defer_lift_invariance_def
  using assms
  by simp

theorem pass_zero_mod_def_zero[simp]:
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
  have lin_ord_on_A:
    "linear_order_on A (limit A r)"
    using assms limit_presv_lin_ord
    by blast
  have f1: "connex A (limit A r)"
    using lin_ord_imp_connex lin_ord_on_A
    by simp
  obtain select_alt :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
    "\<forall> p. (Collect p = {} \<longrightarrow> (\<forall> a. \<not> p a)) \<and>
        (Collect p \<noteq> {} \<longrightarrow> p (select_alt p))"
    by moura
  have "\<forall> n. \<not> (n::nat) \<le> 0 \<or> n = 0"
    by blast
  hence
    "\<forall> a A'. \<not> connex A' (limit A r) \<or> a \<notin> A' \<or> a \<notin> A \<or>
              \<not> card (above (limit A r) a) \<le> 0"
    using above_connex above_presv_limit card_eq_0_iff
          equals0D finite_A assms rev_finite_subset
    by (metis (no_types))
  hence "{a \<in> A. card (above (limit A r) a) \<le> 0} = {}"
    using f1
    by auto
  hence "card {a \<in> A. card (above (limit A r) a) \<le> 0} = 0"
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
    moreover have lin_ord_on_A:
      "linear_order_on A (limit A r)"
      using assms limit_presv_lin_ord
      by blast
    ultimately have winner_exists:
      "\<exists> a \<in> A. above (limit A r) a = {a} \<and>
        (\<forall> x \<in> A. above (limit A r) x = {x} \<longrightarrow> x = a)"
      using finite_A
      by (simp add: above_one)
    then obtain w where w_unique_top:
      "above (limit A r) w = {w} \<and>
        (\<forall> x \<in> A. above (limit A r) x = {x} \<longrightarrow> x = w)"
      using above_one
      by auto
    hence "{a \<in> A. card(above (limit A r) a) \<le> 1} = {w}"
    proof
      assume
        w_top: "above (limit A r) w = {w}" and
        w_unique: "\<forall> x \<in> A. above (limit A r) x = {x} \<longrightarrow> x = w"
      have "card (above (limit A r) w) \<le> 1"
        using w_top
        by auto
      hence "{w} \<subseteq> {a \<in> A. card (above (limit A r) a) \<le> 1}"
        using winner_exists w_unique_top
        by blast
      moreover have
        "{a \<in> A. card(above (limit A r) a) \<le> 1} \<subseteq> {w}"
      proof
        fix x :: "'a"
        assume x_in_winner_set: "x \<in> {a \<in> A. card (above (limit A r) a) \<le> 1}"
        hence x_in_A: "x \<in> A"
          by auto
        hence connex_limit:
          "connex A (limit A r)"
          using lin_ord_imp_connex lin_ord_on_A
          by simp
        hence "let q = limit A r in x \<preceq>\<^sub>q x"
          using connex_limit above_connex
                pref_imp_in_above x_in_A
          by metis
        hence "(x,x) \<in> limit A r"
          by simp
        hence x_above_x: "x \<in> above (limit A r) x"
          unfolding above_def
          by simp
        have "above (limit A r) x \<subseteq> A"
          using above_presv_limit assms
          by fastforce
        hence above_finite: "finite (above (limit A r) x)"
          using finite_A finite_subset
          by simp
        have "card (above (limit A r) x) \<le> 1"
          using x_in_winner_set
          by simp
        moreover have
          "card (above (limit A r) x) \<ge> 1"
          using One_nat_def Suc_leI above_finite card_eq_0_iff
                equals0D neq0_conv x_above_x
          by metis
        ultimately have
          "card (above (limit A r) x) = 1"
          by simp
        hence "{x} = above (limit A r) x"
          using is_singletonE is_singleton_altdef singletonD x_above_x
          by metis
        hence "x = w"
          using w_unique
          by (simp add: x_in_A)
        thus "x \<in> {w}"
          by simp
      qed
      ultimately have
        "{w} = {a \<in> A. card (above (limit A r) a) \<le> 1}"
        by auto
      thus ?thesis
        by simp
    qed
    hence "defer (pass_module 1 r) A p = {w}"
      by simp
    thus "card (defer (pass_module 1 r) A p) = 1"
      by simp
  qed
qed

theorem pass_two_mod_def_two:
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
    finA: "finite A" and
    profA: "profile A p"
  from min_2_card
  have not_empty_A: "A \<noteq> {}"
    by auto
  moreover have limitA_order:
    "linear_order_on A (limit A r)"
    using limit_presv_lin_ord assms
    by auto
  ultimately obtain a where
    a: "above (limit A r) a = {a}"
    using above_one min_2_card finA profA
    by blast
  hence "\<forall> b \<in> A. let q = limit A r in (b \<preceq>\<^sub>q a)"
    using limitA_order pref_imp_in_above empty_iff
          insert_iff insert_subset above_presv_limit
          assms connex_def lin_ord_imp_connex
    by metis
  hence a_best: "\<forall> b \<in> A. (b, a) \<in> limit A r"
    by simp
  hence a_above: "\<forall> b \<in> A. a \<in> above (limit A r) b"
    unfolding above_def
    by simp
  from a have "a \<in> {a \<in> A. card(above (limit A r) a) \<le> 2}"
    using CollectI Suc_leI not_empty_A a_above card_UNIV_bool
          card_eq_0_iff card_insert_disjoint empty_iff finA
          finite.emptyI insert_iff limitA_order above_one
          UNIV_bool nat.simps(3) zero_less_Suc
    by (metis (no_types, lifting))
  hence a_in_defer: "a \<in> defer (pass_module 2 r) A p"
    by simp
  have "finite (A - {a})"
    by (simp add: finA)
  moreover have A_not_only_a: "A - {a} \<noteq> {}"
    using min_2_card Diff_empty Diff_idemp Diff_insert0
          One_nat_def not_empty_A card.insert_remove
          card_eq_0_iff finite.emptyI insert_Diff
          numeral_le_one_iff semiring_norm(69) card.empty
    by metis
  moreover have limitAa_order:
    "linear_order_on (A - {a}) (limit (A - {a}) r)"
    using limit_presv_lin_ord assms top_greatest
    by blast
  ultimately obtain b where
    b: "above (limit (A - {a}) r) b = {b}"
    using above_one
    by metis
  hence "\<forall> c \<in> A - {a}. let q = limit (A - {a}) r in (c \<preceq>\<^sub>q b)"
    using limitAa_order pref_imp_in_above empty_iff insert_iff
          insert_subset above_presv_limit assms connex_def
          lin_ord_imp_connex
    by metis
  hence b_in_limit: "\<forall> c \<in> A - {a}. (c, b) \<in> limit (A - {a}) r"
    by simp
  hence b_best: "\<forall> c \<in> A - {a}. (c, b) \<in> limit A r"
    by auto
  hence c_not_above_b: "\<forall> c \<in> A - {a, b}. c \<notin> above (limit A r) b"
    using b Diff_iff Diff_insert2 above_presv_limit insert_subset
          assms limit_presv_above limit_presv_above2
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
  hence card_above_b_eq_2: "card (above (limit A r) b) = 2"
    using A_not_only_a b_in_limit
    by auto
  hence b_in_defer: "b \<in> defer (pass_module 2 r) A p"
    using b_above_b above_subset
    by auto
  from b_best have b_above:
    "\<forall> c \<in> A - {a}. b \<in> above (limit A r) c"
    using mem_Collect_eq
    unfolding above_def
    by metis
  have "connex A (limit A r)"
    using limitA_order lin_ord_imp_connex
    by auto
  hence "\<forall> c \<in> A. c \<in> above (limit A r) c"
    by (simp add: above_connex)
  hence "\<forall> c \<in> A - {a, b}. {a, b, c} \<subseteq> above (limit A r) c"
    using a_above b_above
    by auto
  moreover have "\<forall> c \<in> A - {a, b}. card {a, b, c} = 3"
    using DiffE Suc_1 above_b_eq_ab card_above_b_eq_2
          above_subset card_insert_disjoint finA finite_subset
          insert_commute numeral_3_eq_3
    unfolding One_nat_def
    by metis
  ultimately have
    "\<forall> c \<in> A - {a, b}. card (above (limit A r) c) \<ge> 3"
    using card_mono finA finite_subset above_presv_limit assms
    by metis
  hence "\<forall> c \<in> A - {a, b}. card (above (limit A r) c) > 2"
    using less_le_trans numeral_less_iff order_refl semiring_norm(79)
    by metis
  hence "\<forall> c \<in> A - {a, b}. c \<notin> defer (pass_module 2 r) A p"
    by (simp add: not_le)
  moreover have "defer (pass_module 2 r) A p \<subseteq> A"
    by auto
  ultimately have "defer (pass_module 2 r) A p \<subseteq> {a, b}"
    by blast
  with a_in_defer b_in_defer have
    "defer (pass_module 2 r) A p = {a, b}"
    by fastforce
  thus "card (defer (pass_module 2 r) A p) = 2"
    using above_b_eq_ab card_above_b_eq_2
    by presburger
qed

end

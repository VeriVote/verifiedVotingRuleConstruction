(*  File:       Pass_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Pass Module\<close>

theory Pass_Module
  imports Electoral_Module
begin

text
\<open>This is a family of electoral modules. For a natural number n and a
lexicon (linear order) r of all alternatives, the according pass module
defers the lexicographically first n alternatives (from A) and rejects
the rest. It is primarily used as counterpart to the drop module in a
parallel composition in order to segment the alternatives into two groups.\<close>

subsection \<open>Definition\<close>

fun pass_module :: "nat \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "pass_module n r A p =
    ({},
    {a \<in> A. card(above (limit A r) a) > n},
    {a \<in> A. card(above (limit A r) a) \<le> n})"

subsection \<open>Soundness\<close>

theorem pass_mod_sound[simp]:
  assumes order: "linear_order r"
  shows "electoral_module (pass_module n r)"
proof -
  let ?mod = "pass_module n r"
  have
    "\<forall> A p. finite_profile A p \<longrightarrow>
          (\<forall>a \<in> A. a \<in> {x \<in> A. card(above (limit A r) x) > n} \<or>
                   a \<in> {x \<in> A. card(above (limit A r) x) \<le> n})"
    using CollectI not_less
    by metis
  hence
    "\<forall> A p. finite_profile A p \<longrightarrow>
          {a \<in> A. card(above (limit A r) a) > n} \<union>
          {a \<in> A. card(above (limit A r) a) \<le> n} = A"
    by blast
  hence 0:
    "\<forall> A p. finite_profile A p \<longrightarrow> set_equals_partition A (pass_module n r A p)"
    by simp
  have
    "\<forall> A p. finite_profile A p \<longrightarrow>
      (\<forall>a \<in> A. \<not>(a \<in> {x \<in> A. card(above (limit A r) x) > n} \<and>
                 a \<in> {x \<in> A. card(above (limit A r) x) \<le> n}))"
    by auto
  hence
    "\<forall> A p. finite_profile A p \<longrightarrow>
      {a \<in> A. card(above (limit A r) a) > n} \<inter>
      {a \<in> A. card(above (limit A r) a) \<le> n} = {}"
    by blast
  hence 1:
    "\<forall> A p. finite_profile A p \<longrightarrow> disjoint3 (?mod A p)"
    by simp
  from 0 1
  have "\<forall> A p. finite_profile A p \<longrightarrow> partition A (?mod A p)"
    by simp
  hence "\<forall> A p. finite_profile A p \<longrightarrow> partition A (?mod A p)"
    by simp
  thus ?thesis
    using electoral_modI
    by metis
qed

subsection \<open>Non-Blocking\<close>

(*The pass module is non-blocking.*)
theorem pass_mod_non_blocking[simp]:
  assumes order: "linear_order r" and
          g0_n:  "n > 0"
  shows "non_blocking (pass_module n r)"
proof -
  have "\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow>
          reject (pass_module n r) A p \<noteq> A"
  proof
    fix A
    show
      "\<forall>p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow>
          reject (pass_module n r) A p \<noteq> A"
    proof
      fix p
      show
        "(A \<noteq> {} \<and> finite_profile A p) \<longrightarrow>
          reject (pass_module n r) A p \<noteq> A"
      proof
        assume input_fine: "A \<noteq> {} \<and> finite_profile A p"
        hence "finite A"
          by simp
        moreover have "A \<noteq> {}"
          by (simp add: input_fine)
        moreover have "linear_order_on A (limit A r)"
          using limit_presv_lin_ord order
          by auto
        ultimately have
          "\<exists>a\<in>A. above (limit A r) a = {a} \<and>
                (\<forall>x\<in>A. above (limit A r) x = {x} \<longrightarrow> x = a)"
          by (simp add: above_one)  
        thus "reject (pass_module n r) A p \<noteq> A"
          using One_nat_def pass_module.simps
                Suc_leI assms(2) fst_conv is_singletonI
                is_singleton_altdef leD mem_Collect_eq snd_conv
          by (metis (no_types, lifting))
      qed
    qed
  qed
  thus ?thesis
    by (simp add: non_blocking_def order)
qed

subsection \<open>Non-Electing\<close>

(*The pass module is non-electing.*)
theorem pass_mod_non_electing[simp]:
  assumes order: "linear_order r"
  shows "non_electing (pass_module n r)"
  by (simp add: non_electing_def order)

subsection \<open>Properties\<close>

(*The pass module is strictly defer-monotone.*)
theorem pass_mod_dl_inv[simp]:
  assumes order: "linear_order r"
  shows "defer_lift_invariance (pass_module n r)"
  by (simp add: order defer_lift_invariance_def)

(*
   For any natural number n and any linear order, the according pass module
   defers n alternatives (if there are n alternatives).
   NOTE: The induction proof is still missing. Following are the proofs for
   n=1 and n=2.
*)
theorem pass_one_mod_def_one[simp]:
  assumes order: "linear_order r"
  shows "defers 1 (pass_module 1 r)"
proof -
  have "\<forall>A p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
          card (defer (pass_module 1 r) A p) = 1"
  proof
    fix A
    show
      "\<forall>p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
          card (defer (pass_module 1 r) A p) = 1"
    proof
      fix p
      show
        "(card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
            card (defer (pass_module 1 r) A p) = 1"
      proof
        assume A_valid: "(card A \<ge> 1 \<and> finite_profile A p)"
        hence finite_A: "finite A"
          by simp
        moreover have "A \<noteq> {}"
          using A_valid
          by auto
        moreover have lin_ord_on_A:
          "linear_order_on A (limit A r)"
          using order limit_presv_lin_ord
          by blast
        ultimately have winner_exists:
          "\<exists>a\<in>A. above (limit A r) a = {a} \<and>
            (\<forall>x\<in>A. above (limit A r) x = {x} \<longrightarrow> x = a)"
          by (simp add: above_one)
        then obtain w where w_unique_top:
          "above (limit A r) w = {w} \<and>
            (\<forall>x\<in>A. above (limit A r) x = {x} \<longrightarrow> x = w)"
          using above_one
          by auto
        hence "{a \<in> A. card(above (limit A r) a) \<le> 1} = {w}"
        proof
          assume
            w_top: "above (limit A r) w = {w}" and
            w_unique: "\<forall>x\<in>A. above (limit A r) x = {x} \<longrightarrow> x = w"
          have "card (above (limit A r) w) \<le> 1"
            using w_top
            by auto
          hence "{w} \<subseteq> {a \<in> A. card(above (limit A r) a) \<le> 1}"
            using winner_exists w_unique_top
            by blast
          moreover have
            "{a \<in> A. card(above (limit A r) a) \<le> 1} \<subseteq> {w}"
          proof
            fix x
            assume x_in_winner_set:
              "x \<in> {a \<in> A. card (above (limit A r) a) \<le> 1}"
            hence x_in_A: "x \<in> A"
              by auto
            hence "(x,x) \<in> limit A r"
              using lin_ord_on_A pref_imp_in_above
                    lin_ord_imp_connex above_connex
                    is_less_preferred_than.simps
              by metis
            hence x_above_x: "x \<in> above (limit A r) x"
              by (simp add: above_def)
            have "above (limit A r) x \<subseteq> A"
              using above_presv_limit order
              by fastforce
            hence above_finite: "finite (above (limit A r) x)"
              by (simp add: A_valid finite_subset)
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
  qed
  thus ?thesis
    using defers_def order pass_mod_sound
    by blast
qed

theorem pass_two_mod_def_two:
  assumes order: "linear_order r"
  shows "defers 2 (pass_module 2 r)"
proof -
  have "\<forall>A p. (card A \<ge> 2 \<and> finite_profile A p) \<longrightarrow>
          card (defer (pass_module 2 r) A p) = 2"
  proof
    fix A
    show
      "\<forall>p. (card A \<ge> 2 \<and> finite_profile A p) \<longrightarrow>
        card (defer (pass_module 2 r) A p) = 2"
    proof
      fix p
      show
        "(card A \<ge> 2 \<and> finite_profile A p) \<longrightarrow>
            card (defer (pass_module 2 r) A p) = 2"
      proof
        assume A_ok: "card A \<ge> 2 \<and> finite_profile A p"
        hence finA: "finite A"
          by simp
        moreover from A_ok
        have not_empty_A: "A \<noteq> {}"
          by auto
        moreover have limitA_order:
          "linear_order_on A (limit A r)"
          using limit_presv_lin_ord order
          by auto
        ultimately obtain a where
          a: "above (limit A r) a = {a}"
          using above_one
          by blast
        hence a_best: "\<forall>b \<in> A. (b, a) \<in> limit A r"
          using limitA_order pref_imp_in_above empty_iff
                insert_iff insert_subset above_presv_limit
                linear_order_on_def order total_on_def
                is_less_preferred_than.simps
          by metis
        hence a_above: "\<forall>b \<in> A. a \<in> above (limit A r) b"
          by (simp add: above_def)
        from a have a_in_defer: "a \<in> defer (pass_module 2 r) A p"
          using CollectI pass_module.simps Suc_leI not_empty_A a_above
                card_UNIV_bool card_eq_0_iff card_gt_0_iff
                card_insert_disjoint empty_iff empty_not_UNIV finA
                finite.emptyI finite_UNIV insert_iff limitA_order
                above_one UNIV_bool nat.simps(3) snd_conv zero_less_Suc
          by (metis (no_types, lifting))
        have "finite (A-{a})"
          by (simp add: finA)
        moreover have A_not_only_a: "A-{a} \<noteq> {}"
          using A_ok Diff_empty Diff_idemp Diff_insert0 One_nat_def
                not_empty_A card.insert_remove card_eq_0_iff
                finite.emptyI insert_Diff numeral_le_one_iff
                semiring_norm(69) card.empty
          by metis
        moreover have limitAa_order:
          "linear_order_on (A-{a}) (limit (A-{a}) r)"
          using limit_presv_lin_ord order top_greatest
          by blast
        ultimately obtain b where b: "above (limit (A-{a}) r) b = {b}"
          using above_one
          by metis
        hence b_in_limit: "\<forall>c \<in> A-{a}. (c, b) \<in> limit (A-{a}) r"
          using limitAa_order pref_imp_in_above empty_iff insert_iff
                insert_subset above_presv_limit order connex_def
                is_less_preferred_than.simps lin_ord_imp_connex
          by metis
        hence b_best: "\<forall>c \<in> A-{a}. (c, b) \<in> limit A r"
          by auto
        hence c_not_above_b: "\<forall>c \<in> A-{a, b}. c \<notin> above (limit A r) b"
          using DiffD2 a_best above_def b insertCI limit_presv_prefs1
                limit_presv_prefs2 mem_Collect_eq Diff_iff Diff_insert2
                is_less_preferred_than.simps above_presv_limit
                insert_subset order
          by (metis (no_types, lifting))
        moreover have above_subset: "above (limit A r) b \<subseteq> A"
          using above_presv_limit order
          by metis
        moreover have b_above_b: "b \<in> above (limit A r) b"
          using above_def b b_best above_presv_limit
                mem_Collect_eq order insert_subset
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
          "\<forall>c \<in> A-{a}. b \<in> above (limit A r) c"
          using pref_imp_in_above is_less_preferred_than.simps
          by metis
        have "connex A (limit A r)"
          using limitA_order lin_ord_imp_connex
          by auto
        hence "\<forall>c \<in> A. c \<in> above (limit A r) c"
          by (simp add: above_connex)
        hence "\<forall>c \<in> A-{a, b}. {a, b, c} \<subseteq> above (limit A r) c"
          using a_above b_above
          by auto
        moreover have "\<forall>c \<in> A-{a, b}. card{a, b, c} = 3"
          using DiffE One_nat_def Suc_1 above_b_eq_ab card_above_b_eq_2
                above_subset card_insert_disjoint finA finite_subset
                insert_commute numeral_3_eq_3
          by metis
        ultimately have
          "\<forall>c \<in> A-{a, b}. card (above (limit A r) c) \<ge> 3"
          using card_mono finA finite_subset above_presv_limit order
          by metis
        hence "\<forall>c \<in> A-{a, b}. card (above (limit A r) c) > 2"
          using less_le_trans numeral_less_iff order_refl semiring_norm(79)
          by metis
        hence "\<forall>c \<in> A-{a, b}. c \<notin> defer (pass_module 2 r) A p"
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
    qed
  qed
  thus ?thesis
    using defers_def order pass_mod_sound
    by blast
qed

end

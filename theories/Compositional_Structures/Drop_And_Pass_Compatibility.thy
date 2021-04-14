(*  File:       Drop_And Pass_Compatibility.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Compositional Structures\<close>

section \<open>Drop And Pass Compatibility\<close>

theory Drop_And_Pass_Compatibility
  imports "Basic_Modules/Drop_Module"
          "Basic_Modules/Pass_Module"
begin

text
\<open>This is a collection of properties about the interplay and compatibility
of both the drop module and the pass module.\<close>

subsection \<open>Properties\<close>

theorem drop_zero_mod_rej_zero[simp]:
  assumes order: "linear_order r"
  shows "rejects 0 (drop_module 0 r)"
  unfolding rejects_def
proof (safe)
  show "electoral_module (drop_module 0 r)"
    using order
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    card_pos: "0 \<le> card A" and
    finite_A: "finite A" and
    prof_A: "profile A p"
  have f1: "connex UNIV r"
    using assms lin_ord_imp_connex
    by auto
  obtain aa :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
    f2:
    "\<forall>p. (Collect p = {} \<longrightarrow> (\<forall>a. \<not> p a)) \<and>
          (Collect p \<noteq> {} \<longrightarrow> p (aa p))"
    by moura
  have f3: "\<forall>a. (a::'a) \<notin> {}"
    using empty_iff
    by simp
  have connex:
    "connex A (limit A r)"
    using f1 limit_presv_connex subset_UNIV
    by metis
  have
    "\<forall>A a. A \<noteq> {} \<or> (a::'a) \<notin> A"
    by simp
  hence f4:
    "\<forall>a Aa.
      \<not> connex Aa (limit A r) \<or> a \<notin> Aa \<or> a \<notin> A \<or>
        \<not> card (above (limit A r) a) \<le> 0"
    using above_connex above_presv_limit card_eq_0_iff
          finite_A finite_subset le_0_eq order
    by (metis (no_types))
  have "{a \<in> A. card(above (limit A r) a) \<le> 0} = {}"
    using connex f4
    by auto
  hence "card {a \<in> A. card(above (limit A r) a) \<le> 0} = 0"
    using card.empty
    by (metis (full_types))
  thus "card (reject (drop_module 0 r) A p) = 0"
    by simp
qed

(*
  The drop module rejects n alternatives (if there are n alternatives).
  NOTE: The induction proof is still missing. Following is the proof for n=2.
*)
theorem drop_two_mod_rej_two[simp]:
  assumes order: "linear_order r"
  shows "rejects 2 (drop_module 2 r)"
proof -
  have rej_drop_eq_def_pass:
    "reject (drop_module 2 r) = defer (pass_module 2 r)"
    by simp
  thus ?thesis
  proof -
    obtain
      AA :: "('a Electoral_Module) \<Rightarrow> nat \<Rightarrow> 'a set" and
      rrs :: "('a Electoral_Module) \<Rightarrow> nat \<Rightarrow> 'a Profile" where
      "\<forall>x0 x1. (\<exists>v2 v3. (x1 \<le> card v2 \<and> finite_profile v2 v3) \<and>
          card (reject x0 v2 v3) \<noteq> x1) =
              ((x1 \<le> card (AA x0 x1) \<and>
                finite_profile (AA x0 x1) (rrs x0 x1)) \<and>
                card (reject x0 (AA x0 x1) (rrs x0 x1)) \<noteq> x1)"
      by moura
    hence
      "\<forall>n f. (\<not> rejects n f \<or> electoral_module f \<and>
          (\<forall>A rs. (\<not> n \<le> card A \<or> infinite A \<or> \<not> profile A rs) \<or>
              card (reject f A rs) = n)) \<and>
          (rejects n f \<or> \<not> electoral_module f \<or> (n \<le> card (AA f n) \<and>
              finite_profile (AA f n) (rrs f n)) \<and>
              card (reject f (AA f n) (rrs f n)) \<noteq> n)"
      using rejects_def
      by force
    hence f1:
      "\<forall>n f. (\<not> rejects n f \<or> electoral_module f \<and>
        (\<forall>A rs. \<not> n \<le> card A \<or> infinite A \<or> \<not> profile A rs \<or>
            card (reject f A rs) = n)) \<and>
        (rejects n f \<or> \<not> electoral_module f \<or> n \<le> card (AA f n) \<and>
            finite (AA f n) \<and> profile (AA f n) (rrs f n) \<and>
            card (reject f (AA f n) (rrs f n)) \<noteq> n)"
      by presburger
    have
      "\<not> 2 \<le> card (AA (drop_module 2 r) 2) \<or>
          infinite (AA (drop_module 2 r) 2) \<or>
          \<not> profile (AA (drop_module 2 r) 2) (rrs (drop_module 2 r) 2) \<or>
          card (reject (drop_module 2 r) (AA (drop_module 2 r) 2)
              (rrs (drop_module 2 r) 2)) = 2"
      using rej_drop_eq_def_pass defers_def order
            pass_two_mod_def_two
      by (metis (no_types))
    thus ?thesis
      using f1 drop_mod_sound order
      by blast
  qed
qed

(*The pass and drop module are (disjoint-)compatible.*)
theorem drop_pass_disj_compat[simp]:
  assumes order: "linear_order r"
  shows "disjoint_compatibility (drop_module n r) (pass_module n r)"
  unfolding disjoint_compatibility_def
proof (safe)
  show "electoral_module (drop_module n r)"
    using order
    by simp
next
  show "electoral_module (pass_module n r)"
    using order
    by simp
next
  fix
    S :: "'a set"
  assume
    fin: "finite S"
  obtain
    p :: "'a Profile"
    where "finite_profile S p"
    using empty_iff empty_set fin profile_set
    by metis
  show
    "\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. indep_of_alt (drop_module n r) S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow>
          a \<in> reject (drop_module n r) S p)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt (pass_module n r) S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow>
          a \<in> reject (pass_module n r) S p))"
  proof
    have same_A:
      "\<forall>p q. (finite_profile S p \<and> finite_profile S q) \<longrightarrow>
        reject (drop_module n r) S p =
          reject (drop_module n r) S q"
      by auto
    let ?A = "reject (drop_module n r) S p"
    have "?A \<subseteq> S"
      by auto
    moreover have
      "(\<forall>a \<in> ?A. indep_of_alt (drop_module n r) S a)"
      using order
      by (simp add: indep_of_alt_def)
    moreover have
      "\<forall>a \<in> ?A. \<forall>p. finite_profile S p \<longrightarrow>
        a \<in> reject (drop_module n r) S p"
      by auto
    moreover have
      "(\<forall>a \<in> S-?A. indep_of_alt (pass_module n r) S a)"
      using order
      by (simp add: indep_of_alt_def)
    moreover have
      "\<forall>a \<in> S-?A. \<forall>p. finite_profile S p \<longrightarrow>
        a \<in> reject (pass_module n r) S p"
      by auto
    ultimately show
      "?A \<subseteq> S \<and>
        (\<forall>a \<in> ?A. indep_of_alt (drop_module n r) S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow>
            a \<in> reject (drop_module n r) S p)) \<and>
        (\<forall>a \<in> S-?A. indep_of_alt (pass_module n r) S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow>
            a \<in> reject (pass_module n r) S p))"
      by simp
  qed
qed

end

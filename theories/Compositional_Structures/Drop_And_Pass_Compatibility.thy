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

text \<open>
  This is a collection of properties about the interplay and compatibility
  of both the drop module and the pass module.
\<close>

subsection \<open>Properties\<close>

theorem drop_zero_mod_rej_zero[simp]:
  fixes r :: "'a Preference_Relation"
  assumes "linear_order r"
  shows "rejects 0 (drop_module 0 r)"
proof (unfold rejects_def, safe)
  show "electoral_module (drop_module 0 r)"
    using assms
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    finite_A: "finite A" and
    prof_A: "profile A p"
  have "connex UNIV r"
    using assms lin_ord_imp_connex
    by auto
  hence connex: "connex A (limit A r)"
    using limit_presv_connex subset_UNIV
    by metis
  have "\<forall> B a. B \<noteq> {} \<or> (a::'a) \<notin> B"
    by simp
  hence "\<forall> a B. a \<in> A \<and> a \<in> B \<longrightarrow> connex B (limit A r) \<longrightarrow> \<not> card (above (limit A r) a) \<le> 0"
    using above_connex above_presv_limit card_eq_0_iff
          finite_A finite_subset le_0_eq assms
    by (metis (no_types))
  hence "{a \<in> A. card (above (limit A r) a) \<le> 0} = {}"
    using connex
    by auto
  hence "card {a \<in> A. card (above (limit A r) a) \<le> 0} = 0"
    using card.empty
    by (metis (full_types))
  thus "card (reject (drop_module 0 r) A p) = 0"
    by simp
qed

text \<open>
  The drop module rejects n alternatives (if there are n alternatives).
  NOTE: The induction proof is still missing. Following is the proof for n=2.
\<close>

theorem drop_two_mod_rej_two[simp]:
  fixes r :: "'a Preference_Relation"
  assumes "linear_order r"
  shows "rejects 2 (drop_module 2 r)"
proof -
  have rej_drop_eq_def_pass: "reject (drop_module 2 r) = defer (pass_module 2 r)"
    by simp
  obtain
    m :: "('a Electoral_Module) \<Rightarrow> nat \<Rightarrow> 'a set" and
    m' :: "('a Electoral_Module) \<Rightarrow> nat \<Rightarrow> 'a Profile" where
      "\<forall> f n. (\<exists> A p. n \<le> card A \<and> finite_profile A p \<and> card (reject f A p) \<noteq> n) =
          (n \<le> card (m f n) \<and> finite_profile (m f n) (m' f n) \<and>
            card (reject f (m f n) (m' f n)) \<noteq> n)"
    by moura
  hence rejected_card:
    "\<forall> f n.
      (\<not> rejects n f \<and> electoral_module f \<longrightarrow>
        n \<le> card (m f n) \<and> finite_profile (m f n) (m' f n) \<and>
          card (reject f (m f n) (m' f n)) \<noteq> n)"
    unfolding rejects_def
    by blast
  have
    "2 \<le> card (m (drop_module 2 r) 2) \<and> finite (m (drop_module 2 r) 2) \<and>
      profile (m (drop_module 2 r) 2) (m' (drop_module 2 r) 2) \<longrightarrow>
        card (reject (drop_module 2 r) (m (drop_module 2 r) 2) (m' (drop_module 2 r) 2)) = 2"
    using rej_drop_eq_def_pass assms pass_two_mod_def_two
    unfolding defers_def
    by (metis (no_types))
  thus ?thesis
    using rejected_card drop_mod_sound assms
    by blast
qed

text \<open>
  The pass and drop module are (disjoint-)compatible.
\<close>

theorem drop_pass_disj_compat[simp]:
  fixes
    r :: "'a Preference_Relation" and
    n :: nat
  assumes "linear_order r"
  shows "disjoint_compatibility (drop_module n r) (pass_module n r)"
proof (unfold disjoint_compatibility_def, safe)
  show "electoral_module (drop_module n r)"
    using assms
    by simp
next
  show "electoral_module (pass_module n r)"
    using assms
    by simp
next
  fix A :: "'a set"
  assume "finite A"
  then obtain p :: "'a Profile" where
    "finite_profile A p"
    using empty_iff empty_set profile_set
    by metis
  show
    "\<exists> B \<subseteq> A.
      (\<forall> a \<in> B. indep_of_alt (drop_module n r) A a \<and>
        (\<forall> p. finite_profile A p \<longrightarrow> a \<in> reject (drop_module n r) A p)) \<and>
      (\<forall> a \<in> A - B. indep_of_alt (pass_module n r) A a \<and>
        (\<forall> p. finite_profile A p \<longrightarrow> a \<in> reject (pass_module n r) A p))"
  proof
    have same_A:
      "\<forall> p q. (finite_profile A p \<and> finite_profile A q) \<longrightarrow>
        reject (drop_module n r) A p = reject (drop_module n r) A q"
      by auto
    let ?A = "reject (drop_module n r) A p"
    have "?A \<subseteq> A"
      by auto
    moreover have "\<forall> a \<in> ?A. indep_of_alt (drop_module n r) A a"
      using assms
      unfolding indep_of_alt_def
      by simp
    moreover have "\<forall> a \<in> ?A. \<forall> p. finite_profile A p \<longrightarrow> a \<in> reject (drop_module n r) A p"
      by auto
    moreover have "\<forall> a \<in> A - ?A. indep_of_alt (pass_module n r) A a"
      using assms
      unfolding indep_of_alt_def
      by simp
    moreover have "\<forall> a \<in> A - ?A. \<forall> p. finite_profile A p \<longrightarrow> a \<in> reject (pass_module n r) A p"
      by auto
    ultimately show
      "?A \<subseteq> A \<and>
        (\<forall> a \<in> ?A. indep_of_alt (drop_module n r) A a \<and>
          (\<forall> p. finite_profile A p \<longrightarrow> a \<in> reject (drop_module n r) A p)) \<and>
        (\<forall> a \<in> A - ?A. indep_of_alt (pass_module n r) A a \<and>
          (\<forall> p. finite_profile A p \<longrightarrow> a \<in> reject (pass_module n r) A p))"
      by simp
  qed
qed

end

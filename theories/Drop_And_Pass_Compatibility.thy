(*  File:       Drop_And Pass_Compatibility.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Drop And Pass Compatibility\<close>

theory Drop_And_Pass_Compatibility
  imports Drop_Module Pass_Module
begin

text
\<open>This is a collection of properties about the interplay and compatibility
of both the drop module and the pass module.\<close>

subsection \<open>Properties\<close>

(*
  The drop module rejects n alternatives (if there are n alternatives).
  NOTE: The induction proof is still missing. Following is the proof for n=2.
*)
theorem drop_two_mod_rej_two[simp]:
  assumes order: "linear_order r"
  shows "rejects 2 (drop_module 2 r)"
proof -
  have "reject (drop_module 2 r) = defer (pass_module 2 r)"
    by simp
  thus ?thesis
  proof - (*generated proof*)
    obtain
      AA ::
      "('a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> 'a set \<times> 'a set \<times> 'a set)
          \<Rightarrow> nat \<Rightarrow> 'a set" and
      rrs ::
      "('a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> 'a set \<times> 'a set \<times> 'a set)
          \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a) set list" where
      "\<forall>x0 x1. (\<exists>v2 v3. (x1 \<le> card v2 \<and> finite_profile v2 v3) \<and>
          card (reject x0 v2 v3) \<noteq> x1) =
              ((x1 \<le> card (AA x0 x1) \<and> finite_profile (AA x0 x1) (rrs x0 x1)) \<and>
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
      using \<open>reject (drop_module 2 r) = defer (pass_module 2 r)\<close>
            defers_def order pass_two_mod_def_two
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
proof -
  have
    "\<forall>S. finite S \<longrightarrow>
        (\<exists>A \<subseteq> S.
          (\<forall>a \<in> A. indep_of_alt (drop_module n r) S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow>
                a \<in> reject (drop_module n r) S p)) \<and>
          (\<forall>a \<in> S-A. indep_of_alt (pass_module n r) S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow>
                a \<in> reject (pass_module n r) S p)))"
  proof
    fix S
    show
      "finite S \<longrightarrow>
        (\<exists>A \<subseteq> S.
          (\<forall>a \<in> A. indep_of_alt (drop_module n r) S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow>
                  a \<in> reject (drop_module n r) S p)) \<and>
          (\<forall>a \<in> S-A. indep_of_alt (pass_module n r) S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow>
                  a \<in> reject (pass_module n r) S p)))"
    proof
      assume fin: "finite S"
      obtain p where "finite_profile S p"
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
          by (simp add: indep_of_alt_def order)
        moreover have
          "\<forall>a \<in> ?A. \<forall>p. finite_profile S p \<longrightarrow>
              a \<in> reject (drop_module n r) S p"
          by auto
        moreover have
          "(\<forall>a \<in> S-?A. indep_of_alt (pass_module n r) S a)"
          by (simp add: indep_of_alt_def order)
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
  qed
  thus ?thesis
    by (simp add: disjoint_compatibility_def order)
qed

end

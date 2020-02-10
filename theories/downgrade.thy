theory downgrade
imports electoral_modules

begin

(*****************************)
(*** Definition: Downgrade ***)
(*****************************)

(* A downgraded electoral module rejects all originally rejected or deferred alternatives, and
   deferres the originally elected alternatives. It does not elect alternatives. *)
fun Downgrade :: "'a Electoral_module \<Rightarrow> 'a Electoral_module" where
  "Downgrade m A p = ({}, A - elect m A p, elect m A p)"

(* Downgrading an electoral module results in an electoral module. *)
theorem downgrade_sound[simp]:
  assumes module: "electoral_module m"
  shows "electoral_module (Downgrade m)"
proof -
  from module have "\<forall>A p. finite_profile A p \<longrightarrow> elect m A p \<subseteq> A"
    using elect_from_input by auto
  hence "\<forall>A p. finite_profile A p \<longrightarrow> (A - elect m A p) \<union> elect m A p = A"
    by blast
  hence unity: "\<forall>A p. finite_profile A p \<longrightarrow> unify_to A (Downgrade m A p)"
    by simp
  have "\<forall>A p. finite_profile A p \<longrightarrow> (A - elect m A p) \<inter> elect m A p = {}"
    by blast
  hence disjoint: "\<forall>A p. finite_profile A p \<longrightarrow> disjoint3 (Downgrade m A p)"
    by simp
  from unity disjoint show ?thesis
    by (simp add: electoral_module_intro partition_of_def)
qed
abbreviation down :: "'a Electoral_module \<Rightarrow> 'a Electoral_module" ("_\<down>" 50) where
  "m\<down> == Downgrade m"

(*****************************************)
(*** Composition Rules for Downgrading ***)
(*****************************************)

(* An electoral module received by downgrading is never electing. *)
theorem downgrade_non_electing[simp]:
  assumes "electoral_module m"
  shows "non_electing (m\<down>)"
  by (simp add: assms non_electing_def)

(* Downgrading an invariant monotone electoral module results in a defer invariant monotone
   electoral module.
*)
theorem invariant_monotone_downgrade[simp]:
  assumes "invariant_monotone m"
  shows "defer_invariant_monotone (m\<down>)"
proof -
  have "\<forall>A p q w. (w \<in> defer (m\<down>) A p \<and> lifted A p q w) \<longrightarrow>
                  (defer (m\<down>) A q = defer (m\<down>) A p \<or> defer (m\<down>) A q = {w})"
    using assms by (simp add: invariant_monotone_def)
  moreover have "electoral_module (m\<down>)"
    using assms downgrade_sound invariant_monotone_def by auto
  moreover have "non_electing (m\<down>)"
    using assms downgrade_non_electing invariant_monotone_def by auto
  ultimately have "electoral_module (m\<down>) \<and> non_electing (m\<down>) \<and>
      (\<forall>A p q w. (w \<in> defer (m\<down>) A p \<and> lifted A p q w) \<longrightarrow>
                 (defer (m\<down>) A q = defer (m\<down>) A p \<or> defer (m\<down>) A q = {w}))"
    by blast
  thus ?thesis
    using defer_invariant_monotone_def by (simp add: defer_invariant_monotone_def)
qed

(* Downgrading an electing electoral module results in a non blocking electoral module. *)
lemma blocking_downgrade[simp]:
  assumes "electing m"
  shows "non_blocking (m\<down>)"
  by (metis (no_types, lifting) Diff_cancel Diff_empty Downgrade.simps assms
      defer_alternative_representation electing_def downgrade_non_electing non_blocking_def
      non_electing_def prod.sel(2))

end

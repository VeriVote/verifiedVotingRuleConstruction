(*  File:       Parallel_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Parallel Composition\<close>

theory Parallel_Composition
  imports Aggregator
begin

text
\<open>The parallel composition composes a new electoral module from
two electoral modules combined with an aggregator.
Therein, the two modules each make a decision and the aggregator combines
them to a single (aggregated) result.\<close>

subsection \<open>Definition\<close>

fun parallel_composition :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Aggregator \<Rightarrow> 'a Electoral_Module" where
  "parallel_composition m n agg A p = agg A (m A p) (n A p)"

abbreviation parallel ::
"'a Electoral_Module \<Rightarrow>'a Aggregator \<Rightarrow> 'a Electoral_Module \<Rightarrow>
    'a Electoral_Module"  ("_ \<parallel>\<^sub>_ _" [50, 1000, 51] 50) where
  "m \<parallel>\<^sub>a n == parallel_composition m n a"

subsection \<open>Soundness\<close>

theorem par_comp_sound[simp]:
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n" and
    agg_a: "aggregator a"
  shows "electoral_module (m \<parallel>\<^sub>a n)"
proof -
  have "\<forall>A p. finite_profile A p \<longrightarrow> partition A ((m \<parallel>\<^sub>a n) A p)"
  proof
    fix A
    show "\<forall>p. finite_profile A p \<longrightarrow> partition A ((m \<parallel>\<^sub>a n) A p)"
    proof
      fix p
      show "finite_profile A p \<longrightarrow> partition A ((m \<parallel>\<^sub>a n) A p)"
      proof
        assume f_prof: "finite_profile A p"
        show "partition A ((m \<parallel>\<^sub>a n) A p)"
        proof -
          obtain
            AA :: "'a set \<times> 'a set \<Rightarrow> 'a set" and
            AAa :: "'a set \<times> 'a set \<Rightarrow> 'a set" where
              "\<forall>p. p = (AA p, AAa p)"
            using surj_pair
            by metis
          hence
            "\<forall>A Aa Ab Ac Ad p f.
                partition (Ab::'a set) (f Ab (Ac, A, Ad) (Aa, p)) \<or>
                \<not> partition Ab (Ac, A, Ad) \<or>
                \<not> partition Ab (Aa, p) \<or>
                \<not> aggregator f"
            using aggregator_def
            by (smt (verit, best))
          hence
            "\<forall>A p pa f.
                partition (A::'a set) (f A p pa) \<or>
                \<not> partition A p \<or>
                \<not> partition A pa \<or>
                \<not> aggregator f"
            by auto
          thus ?thesis
            using agg_a electoral_module_def mod_m mod_n
                  parallel_composition.simps f_prof
            by metis
        qed
      qed
    qed
  qed
  thus ?thesis
    by (simp add: electoral_modI)
qed

subsection \<open>Composition Rule\<close>

(*
   Using a conservative aggregator, the parallel composition
   preserves the property non-electing.
*)
theorem conserv_agg_presv_non_electing[simp]:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n" and
    conservative: "agg_conservative a"
  shows "non_electing (m \<parallel>\<^sub>a n)"
proof -
  have
    "(\<forall>A p. finite_profile A p \<longrightarrow>
        elect m A p = {} \<and> elect n A p = {})"
    using non_electing_def non_electing_m non_electing_n
    by blast
  hence
    "(\<forall>A p. finite_profile A p \<longrightarrow>
        elect_r (m A p) = {} \<and> elect_r (n A p) = {})"
    by simp
  moreover have "\<forall>A p. finite_profile A p \<longrightarrow> partition A (m A p)"
    using electoral_module_def non_electing_def non_electing_m
    by auto
  moreover have "\<forall>A p. finite_profile A p \<longrightarrow> partition A (n A p)"
    using electoral_module_def non_electing_def non_electing_n
    by auto
  moreover have conservative_def_inline:
    "aggregator a \<and>
      (\<forall>A e1 e2 d1 d2 r1 r2. 
          ((partition A (e1, r1, d1) \<and> partition A (e2, r2, d2)) \<longrightarrow>
              elect_r (a A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
              reject_r (a A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2) \<and>
              defer_r (a A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2)))"
    using conservative agg_conservative_def
    by blast
  ultimately have
    "(\<forall>A p. finite_profile A p \<longrightarrow>
        elect_r (a A (elect m A p, reject m A p, defer m A p)
          (elect n A p, reject n A p, defer n A p))
        \<subseteq> {})"
    using combine_ele_rej_def fst_def sup_bot_right
    by (smt (z3))
  hence
    "(\<forall>A p. finite_profile A p \<longrightarrow>
        elect_r (a A (m A p) (n A p)) \<subseteq> {})"
    by simp
  thus ?thesis
    using conservative_def_inline non_electing_def
          non_electing_m non_electing_n subset_empty
          par_comp_sound parallel_composition.simps
    by metis
qed

end

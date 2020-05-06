theory plurality_module
imports electoral_modules

begin

(************************************)
(*** Definition: Plurality Module ***)
(************************************)

(* The win count of an alternative a in a profile p is the number of ballots in p ranking a first.
*)
abbreviation win_count where
  "win_count p a \<equiv>
    card{i::nat. i < size p \<and> above (p!i) a = {a}}"

(* The plurality module elects all modules with the maximum win count among all alternatives, and
   rejects all the other alternatives. *)
fun Plurality_module :: "'a Electoral_module" where
  "Plurality_module A p =
    ({a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a},
     {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a},
     {})"

(* Soundness: Plurality Module *)
(* The plurality module satisfies the electoral_module predicate. This ensures it can be used as
   electoral module in compositions.
*)
lemma plurality_module_sound[simp]:
  shows "electoral_module Plurality_module"
proof -
  have "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
          reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
        elect \<inter> reject = {}"
    by auto
  hence disjoint: "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
          reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
        disjoint3 (elect, reject, {})"
    by simp
  have "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
          reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
        elect \<union> reject = A"
    using not_le_imp_less
    by auto
  hence unity: "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
          reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
        unify_to A (elect, reject, {})"
    by simp
  from disjoint unity show ?thesis
    by (simp add: electoral_module_intro partition_of_def)
qed

(******************************************)
(*** Properties of the Plurality Module ***)
(******************************************)

(* The plurality module is invariant monotone. *)
theorem plurality_invariant_mono[simp]:
  shows "invariant_monotone Plurality_module"
proof -
  { have "\<forall>A p q a. (a \<in> elect Plurality_module A p \<and> lifted A p q a) \<longrightarrow>
      (elect Plurality_module A q = elect Plurality_module A p \<or> elect Plurality_module A q = {a})"
    proof
      { fix A show "\<forall>p q a. (a \<in> elect Plurality_module A p \<and> lifted A p q a) \<longrightarrow>
                      (elect Plurality_module A q = elect Plurality_module A p
                        \<or> elect Plurality_module A q = {a})"
        proof
          { fix p show "\<forall>q a. (a \<in> elect Plurality_module A p \<and> lifted A p q a) \<longrightarrow>
                          (elect Plurality_module A q = elect Plurality_module A p
                            \<or> elect Plurality_module A q = {a})"
            proof
              { fix q show "\<forall>a. (a \<in> elect Plurality_module A p \<and> lifted A p q a) \<longrightarrow>
                              (elect Plurality_module A q = elect Plurality_module A p
                                \<or> elect Plurality_module A q = {a})"
                proof
                  { fix a show "(a \<in> elect Plurality_module A p \<and> lifted A p q a) \<longrightarrow>
                                  (elect Plurality_module A q = elect Plurality_module A p
                                    \<or> elect Plurality_module A q = {a})"
                    proof
                      assume asm1: "a \<in> elect Plurality_module A p \<and> lifted A p q a"
                      have lifted_winner: "\<forall>x \<in> A.\<forall>i::nat. i < size p \<longrightarrow>
                                            (above (p!i) x = {x} \<longrightarrow>
                                              (above (q!i) x = {x} \<or> above (q!i) a = {a}))"
                        by (metis (no_types, lifting) asm1 electoral_modules.lifted_def
                            lifted_above_winner)
                      hence "\<forall>i::nat. i < size p \<longrightarrow> (above (p!i) a = {a} \<longrightarrow> above (q!i) a = {a})"
                        using asm1
                        by auto
                      hence a_win_subset: "{i::nat. i < size p \<and> above (p!i) a = {a}} \<subseteq>
                                              {i::nat. i < size p \<and> above (q!i) a = {a}}"
                        by blast
                      moreover have sizes: "size p = size q"
                        by (metis asm1 electoral_modules.lifted_def)
                      ultimately have win_count_a: "win_count p a \<le> win_count q a"
                        by (simp add: card_mono)
                      have fin_A: "finite A"
                        using asm1 electoral_modules.lifted_def
                        by fastforce
                      hence "\<forall>x \<in> A-{a}.\<forall>i::nat. i < size p \<longrightarrow>
                              (above (q!i) a = {a} \<longrightarrow> above (q!i) x \<noteq> {x})"
                        using linear_order_above_one_winner
                        by (metis (no_types, hide_lams) Diff_iff asm1 electoral_modules.lifted_def
                            insert_iff nth_mem profile_on_def)
                      from this lifted_winner
                      have above_QtoP: "\<forall>x \<in> A-{a}.\<forall>i::nat. i < size p \<longrightarrow>
                                         (above (q!i) x = {x} \<longrightarrow> above (p!i) x = {x})"
                        using lifted_above_winner3
                        by (metis asm1 electoral_modules.lifted_def)
                      hence "\<forall>x \<in> A-{a}. {i::nat. i < size p \<and> above (q!i) x = {x}} \<subseteq>
                                           {i::nat. i < size p \<and> above (p!i) x = {x}}"
                        by (simp add: Collect_mono)
                      hence win_count_other: "\<forall>x \<in> A-{a}. win_count p x \<ge> win_count q x"
                        by (simp add: card_mono sizes)
                        { show "elect Plurality_module A q =
                                    elect Plurality_module A p \<or> elect Plurality_module A q = {a}"
                          proof cases
                            assume "win_count p a = win_count q a"
                            hence "card{i::nat. i < size p \<and> above (p!i) a = {a}} =
                                    card{i::nat. i < size p \<and> above (q!i) a = {a}}"
                              by (simp add: sizes)
                            moreover have "finite {i::nat. i < size p \<and> above (q!i) a = {a}}"
                              by simp
                            ultimately have "{i::nat. i < size p \<and> above (p!i) a = {a}} =
                                              {i::nat. i < size p \<and> above (q!i) a = {a}}"
                              by (simp add: a_win_subset card_subset_eq)
                            hence above_pq: "\<forall>i::nat. i < size p \<longrightarrow>
                                              above (p!i) a = {a} \<longleftrightarrow> above (q!i) a = {a}"
                              by blast
                            moreover have "\<forall>x \<in> A-{a}.\<forall>i::nat. i < size p \<longrightarrow>
                                            (above (p!i) x = {x} \<longrightarrow>
                                              (above (q!i) x = {x} \<or> above (q!i) a = {a}))"
                              using lifted_winner
                              by auto
                            moreover
                              { have "\<forall>x \<in> A-{a}.\<forall>i::nat. i < size p \<longrightarrow>
                                        (above (p!i) x = {x} \<longrightarrow> above (p!i) a \<noteq> {a})"
                                proof (rule ccontr)
                                  assume "\<not>(\<forall>x \<in> A-{a}.\<forall>i::nat. i < size p \<longrightarrow>
                                            (above (p!i) x = {x} \<longrightarrow> above (p!i) a \<noteq> {a}))"
                                  hence "\<exists>x \<in> A-{a}.\<exists>i::nat.
                                          i < size p \<and> above (p!i) x = {x} \<and> above (p!i) a = {a}"
                                    by auto
                                  moreover from this
                                  have "finite A \<and> A \<noteq> {}"
                                    using fin_A
                                    by blast
                                  moreover from asm1
                                  have "\<forall>i::nat. i < size p \<longrightarrow> linear_order_on A (p!i)"
                                    using lifted_def
                                    by (simp add: electoral_modules.lifted_def profile_on_def)
                                  ultimately have "\<exists>x \<in> A-{a}. x = a"
                                    using linear_order_above_one_winner2
                                    by fastforce
                                  thus "False"
                                    by simp
                                qed }
                            ultimately have above_PtoQ: "\<forall>x \<in> A-{a}.\<forall>i::nat. i < size p \<longrightarrow>
                              (above (p!i) x = {x} \<longrightarrow> above (q!i) x = {x})"
                              by (simp add: above_pq)
                            have "\<forall>x \<in> A. win_count p x = win_count q x"
                              by (smt Collect_cong DiffI above_pq above_QtoP above_PtoQ
                                  insert_absorb insert_iff insert_not_empty sizes)
                            hence "{a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a} =
                                    {a \<in> A. \<forall>x \<in> A. win_count q x \<le> win_count q a}"
                              by auto
                            thus ?thesis
                              by simp
                          next
                            assume "win_count p a \<noteq> win_count q a"
                            hence strict_less: "win_count p a < win_count q a"
                              using win_count_a
                              by auto
                            have a_in_win_p: "a \<in> {a \<in> A. \<forall>x \<in> A.
                                                    win_count p x \<le> win_count p a}"
                              using asm1
                              by auto
                            hence "\<forall>x \<in> A. win_count p x \<le> win_count p a"
                              by simp
                            from this strict_less win_count_other
                            have less: "\<forall>x \<in> A-{a}. win_count q x < win_count q a"
                              by (smt DiffD1 antisym dual_order.trans not_le_imp_less win_count_a)
                            hence "\<forall>x \<in> A-{a}. \<not>(\<forall>y \<in> A. win_count q y \<le> win_count q x)"
                              by (meson asm1 electoral_modules.lifted_def not_le)
                            hence "\<forall>x \<in> A-{a}. x \<notin> {a \<in> A. \<forall>x \<in> A.
                                                      win_count q x \<le> win_count q a}"
                              by blast
                            hence "\<forall>x \<in> A-{a}. x \<notin> elect Plurality_module A q"
                              by simp
                            moreover
                              { have "a \<in> elect Plurality_module A q"
                                proof -
                                  from less
                                  have "\<forall>x \<in> A-{a}. win_count q x \<le> win_count q a"
                                    using less_imp_le
                                    by blast
                                  moreover have "win_count q a \<le> win_count q a"
                                    by simp
                                  ultimately have "\<forall>x \<in> A. win_count q x \<le> win_count q a"
                                    by blast
                                  moreover have "a \<in> A"
                                    using a_in_win_p
                                    by auto
                                  ultimately have "a \<in> {a \<in> A. \<forall>x \<in> A.
                                                          win_count q x \<le> win_count q a}"
                                    by blast
                                  thus ?thesis
                                    by simp
                              qed }
                            moreover have "elect Plurality_module A q \<subseteq> A"
                              by auto
                            ultimately show ?thesis
                              by blast
                        qed }
                  qed }
              qed }
          qed }
      qed }
  qed }
  thus ?thesis
    by (simp add: invariant_monotone_def)
qed

(* The plurality module is electing. *)
lemma plurality_module_electing[simp]: "electing Plurality_module"
proof -
  { have "\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect Plurality_module A p \<noteq> {}"
    proof
      { fix A
        show "\<forall>p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect Plurality_module A p \<noteq> {}"
        proof
          { fix p
            show "(A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect Plurality_module A p \<noteq> {}"
            proof assume asm0: "A \<noteq> {} \<and> finite_profile A p"
              obtain max where max: "max = Max(win_count p ` A)"
                by simp
              then obtain a where a: "win_count p a = max \<and> a \<in> A"
                by (metis (no_types, lifting) Max_in asm0 empty_is_image finite_imageI imageE)
              hence "\<forall>x \<in> A. win_count p x \<le> win_count p a"
                by (simp add: max asm0)
              moreover have "a \<in> A"
                by (simp add: a)
              ultimately have "a \<in> {a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a}"
                by blast
              hence "a \<in> elect Plurality_module A p"
                by simp
              thus "elect Plurality_module A p \<noteq> {}"
                by blast
            qed }
        qed }
    qed }
  thus ?thesis
    by (simp add: electing_def)
qed

end
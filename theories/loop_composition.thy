theory loop_composition
imports sequential_composition defer_module termination_conditions

begin

(************************************)
(*** Definition: Loop Composition ***)
(************************************)

lemma loop_termination_helper:
  assumes not_term: "\<not>t (acc A p)" and
          subset:   "defer (acc \<triangleright> m) A p \<subset> defer acc A p" and
          not_inf:  "\<not>infinite (defer acc A p)"
  shows " ((acc \<triangleright> m, m, t, A, p), (acc, m, t, A, p)) \<in>
    measure (\<lambda>(acc, m, t, A, p). card (defer acc A p))"
  using assms psubset_card_mono by auto

(* This function handles the accumulator for the following loop composition function. *)
function loop_comp_helper :: "'a Electoral_module \<Rightarrow> 'a Electoral_module \<Rightarrow> 'a Termination_condition
      \<Rightarrow> 'a Electoral_module" where
    "t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or> infinite (defer acc A p) \<Longrightarrow>
      loop_comp_helper acc m t A p = acc A p" |
    "\<not>(t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or> infinite (defer acc A p)) \<Longrightarrow>
      loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
  apply (metis prod_cases5)
    by auto
termination
  apply (relation "measure (\<lambda>(acc, m, t, A, p). card (defer acc A p))")
  apply (simp)
  using loop_termination_helper by blast

(* The loop composition uses the same module in sequence, until a termination condition is met, or
   no new decisions are made.
*)
function loop_comp :: "'a Electoral_module \<Rightarrow> 'a Termination_condition \<Rightarrow> 'a Electoral_module" where
    "t ({}, {}, A) \<Longrightarrow> loop_comp m t A p = Defer_module A p" |
    "\<not>(t ({}, {}, A)) \<Longrightarrow> loop_comp m t A p = (loop_comp_helper m m t) A p"
  apply fastforce
  apply simp
  apply blast
  by blast
termination
  using "termination" by blast
abbreviation loop :: "'a Electoral_module \<Rightarrow> 'a Termination_condition \<Rightarrow> 'a Electoral_module"
    ("_ \<circlearrowleft>\<^sub>_" 50) where
  "m \<circlearrowleft>\<^sub>t \<equiv> loop_comp m t"

lemma loop_comp_helper_partitions:
  assumes module_m: "electoral_module m" and
          profile:  "finite_profile A p"
  shows "electoral_module acc \<and> (n = card (defer acc A p)) \<longrightarrow>
    partition_of A (loop_comp_helper acc m t A p)"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  thus ?case
    by (smt electoral_module_def loop_comp_helper.simps(1) loop_comp_helper.simps(2) module_m
        profile psubset_card_mono seq_creates_modules)
qed

(* The loop compositions creates an electoral module out of an electoral module and a termination
   condition.
*)
theorem loop_comp_creates_modules:
  assumes m_module: "electoral_module m"
  shows "electoral_module (m \<circlearrowleft>\<^sub>t)"
  by (metis (mono_tags, lifting) defer_module_sound electoral_module_def loop_comp.simps(1)
      loop_comp.simps(2) loop_comp_helper_partitions m_module)

lemma loop_comp_helper_does_not_add_to_defer:
  assumes module_m: "electoral_module m" and
          profile:  "finite_profile A p"
  shows "(electoral_module acc \<and> n = card (defer acc A p)) \<longrightarrow>
         defer (loop_comp_helper acc m t) A p \<subseteq> defer acc A p"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  thus ?case
    by (smt dual_order.trans eq_iff less_imp_le loop_comp_helper.simps(1) loop_comp_helper.simps(2)
        module_m psubset_card_mono seq_creates_modules)
qed

(***********************************)
(*** Lemmas for Loop Composition ***)
(***********************************)

lemma loop_comp_helper_defer_lift_invariant_helper:
  assumes monotone_m: "defer_lift_invariant m" and
          profile:    "finite_profile A p"
  shows "(defer_lift_invariant acc \<and> n = card (defer acc A p)) \<longrightarrow>
     (\<forall>q a. (a \<in> (defer (loop_comp_helper acc m t) A p) \<and> lifted A p q a) \<longrightarrow>
            (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q)"
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have defer_card_comp: "defer_lift_invariant acc \<longrightarrow>
                         (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                                card (defer (acc \<triangleright> m) A p) = card (defer (acc \<triangleright> m) A q))"
    by (metis monotone_m lift_invariant_seq_help)
  have defer_card_acc: "defer_lift_invariant acc \<longrightarrow>
                        (\<forall>q a. (a \<in> (defer (acc) A p) \<and> lifted A p q a) \<longrightarrow>
                               card (defer (acc) A p) = card (defer (acc) A q))"
    by (simp add: defer_lift_invariant_def)
  hence defer_card_acc_2: "defer_lift_invariant acc \<longrightarrow>
                           (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                                  card (defer (acc) A p) = card (defer (acc) A q))"
    by (smt defer_from_input monotone_m prod.sel(2) profile seq_comp.simps seq_n_input_sound
        defer_lift_invariant_def subsetCE)
  thus ?case
  proof cases
    assume card_unchanged: "card (defer (acc \<triangleright> m) A p) = card (defer acc A p)"
    from this defer_card_comp defer_card_acc monotone_m
    have "defer_lift_invariant (acc) \<longrightarrow> (\<forall>q a. (a \<in> (defer (acc) A p) \<and> lifted A p q a) \<longrightarrow>
                                                 (loop_comp_helper acc m t) A q = acc A q)"
      by (smt card_subset_eq defer_from_input less_irrefl loop_comp_helper.simps(1) profile
          psubset_card_mono seq_comp.simps seq_n_input_sound snd_conv defer_lift_invariant_def)
    moreover from card_unchanged have  "(loop_comp_helper acc m t) A p = acc A p"
      by (metis loop_comp_helper.simps(1) order.strict_iff_order psubset_card_mono)
    ultimately have "(defer_lift_invariant (acc \<triangleright> m) \<and> defer_lift_invariant acc) \<longrightarrow>
                     (\<forall>q a. (a \<in> (defer (loop_comp_helper acc m t) A p) \<and> lifted A p q a) \<longrightarrow>
                            (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q)"
      by (metis defer_lift_invariant_def)
    thus ?thesis
      using monotone_m defer_lift_invariant_seq by blast
  next
    assume card_changed: "\<not> (card (defer (acc \<triangleright> m) A p) = card (defer acc A p))"
    from this profile seq_comp_does_not_grow_deferred_set
    have card_smaller_for_p: "electoral_module (acc) \<longrightarrow>
                              (card (defer (acc \<triangleright> m) A p) < card (defer acc A p))"
      by (metis (full_types) monotone_m order.not_eq_order_implies_strict defer_lift_invariant_def)
    from this defer_card_acc_2 defer_card_comp
    have card_changed_for_q: "defer_lift_invariant (acc) \<longrightarrow>
                              (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                                     (card (defer (acc \<triangleright> m) A q) < card (defer acc A q)))"
      by (metis (no_types, hide_lams) defer_lift_invariant_def)
    thus ?thesis
    proof cases
      assume t_not_satisfied_for_p: "\<not> t (acc A p)"
      hence t_not_satisfied_for_q: " defer_lift_invariant (acc) \<longrightarrow>
         (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow> \<not> t (acc A q))"
        by (smt defer_from_input monotone_m prod.sel(2) profile seq_comp.simps seq_n_input_sound
            defer_lift_invariant_def subsetCE)
      from card_changed defer_card_comp defer_card_acc
      have "(defer_lift_invariant (acc \<triangleright> m) \<and> defer_lift_invariant (acc)) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                   card (defer (acc \<triangleright> m) A q) \<noteq> (card (defer acc A q)))"
        by (smt defer_from_input monotone_m profile seq_comp.simps seq_n_input_sound snd_conv
            defer_lift_invariant_def subsetCE)
      hence "defer_lift_invariant (acc \<triangleright> m) \<and> defer_lift_invariant (acc) \<longrightarrow>
         (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                defer (acc \<triangleright> m) A q \<subset> defer acc A q)"
        by (smt defer_card_acc defer_from_input monotone_m prod.sel(2) profile psubsetI
            seq_comp.simps seq_n_input_sound defer_lift_invariant_def subsetCE)
      from this t_not_satisfied_for_p
      have rec_step_q: "(defer_lift_invariant (acc \<triangleright> m) \<and> defer_lift_invariant (acc)) \<longrightarrow>
                        (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                               loop_comp_helper acc m t A q = loop_comp_helper (acc \<triangleright> m) m t A q)"
        by (smt defer_from_input loop_comp_helper.simps(2) monotone_m prod.sel(2) profile
            seq_comp.simps seq_n_input_sound defer_lift_invariant_def subsetCE)
      have rec_step_p: "electoral_module acc \<longrightarrow>
                        loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
        by (smt card_changed defer_from_input loop_comp_helper.simps(2) monotone_m prod.sel(2)
            profile psubsetI seq_comp.simps seq_n_input_sound defer_lift_invariant_def
            t_not_satisfied_for_p)
      thus ?thesis
        by (smt card_smaller_for_p less.hyps loop_comp_helper_does_not_add_to_defer monotone_m
            defer_lift_invariant_seq profile rec_step_q defer_lift_invariant_def subsetCE)
    next
      assume t_satisfied_for_p: "\<not> \<not>t (acc A p)"
      thus ?thesis
        by (metis loop_comp_helper.simps(1) defer_lift_invariant_def)
    qed
  qed
qed

lemma loop_comp_helper_defer_lift_invariant:
  assumes monotone_m:   "defer_lift_invariant m" and
          monotone_acc: "defer_lift_invariant acc" and
          profile:      "finite_profile A p"
  shows "\<forall>q a. (lifted A p q a \<and> a \<in> (defer (loop_comp_helper acc m t) A p)) \<longrightarrow>
               (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q"
  using loop_comp_helper_defer_lift_invariant_helper monotone_m monotone_acc profile by blast

lemma loop_comp_helper_defer_lift_invariant2:
  assumes monotone_m: "defer_lift_invariant m" and
          monotone_acc: "defer_lift_invariant acc"
  shows "\<forall>A p q a. (finite_profile A p \<and>
                    lifted A p q a \<and>
                    a \<in> (defer (loop_comp_helper acc m t) A p)) \<longrightarrow>
                      (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q"
  using loop_comp_helper_defer_lift_invariant monotone_acc monotone_m by blast

lemma lifted_impl_finite_profile:
  assumes "lifted A p q a"
  shows "finite_profile A p"
  using assms electoral_modules.lifted_def by fastforce

lemma loop_comp_helper_preserves_defer_lift_invariant:
  assumes monotone_m:   "defer_lift_invariant m" and
          monotone_acc: "defer_lift_invariant acc"
  shows "defer_lift_invariant (loop_comp_helper acc m t)"
  by (smt electoral_module_def loop_comp_helper_partitions loop_comp_helper_defer_lift_invariant
      monotone_acc monotone_m defer_lift_invariant_def lifted_impl_finite_profile)

lemma loop_preserves_non_electing_helper:
  assumes non_electing_m: "non_electing m"and
          profile:        "finite_profile A p"
  shows "(n = card (defer acc A p) \<and> non_electing acc) \<longrightarrow>
         elect (loop_comp_helper acc m t) A p = {}"
proof (induct n arbitrary: acc rule: less_induct)
  case(less n)
  thus ?case
    by (smt loop_comp_helper.simps(1) loop_comp_helper.simps(2) non_electing_def non_electing_m
        profile psubset_card_mono seq_comp_preserves_non_electing)
qed

lemma loop_comp_helper_iterative_elimination_number_of_survivors_helper_for_eliminates:
  assumes non_electing_m:      "non_electing m" and
          single_elimination:  "eliminates 1 m" and
          terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
          x_greater_zero:      "x > 0" and
          profile:             "finite_profile A p"
  shows "(n = card (defer acc A p) \<and> n \<ge> x \<and> card (defer acc A p) > 1 \<and> non_electing acc) \<longrightarrow>
         card (defer (loop_comp_helper acc m t) A p) = x"
proof (induct n arbitrary: acc rule: less_induct)
  case(less n)
  have subset: "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> electoral_module acc) \<longrightarrow>
                defer (acc \<triangleright> m) A p \<subset> defer acc A p"
    using seq_comp_defer_set_single_elimination_reject single_elimination by blast
  hence step_reduces_defer_set: "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> non_electing acc)
                                 \<longrightarrow> defer (acc \<triangleright> m) A p \<subset> defer acc A p"
    using non_electing_def by auto
  thus ?case
  proof cases
    assume term_satisfied: "t (acc A p)"
    have "card (defer_r (loop_comp_helper acc m t A p)) = x"
      by (metis loop_comp_helper.simps(1) term_satisfied terminate_if_n_left)
    thus ?case
      by blast
  next
    assume term_not_satisfied: "\<not>(t (acc A p))"
    hence card_not_eq_x: "card (defer acc A p) \<noteq> x"
      by (simp add: terminate_if_n_left)
    have rec_step: "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> non_electing acc) \<longrightarrow>
                      loop_comp_helper acc m t A p =
                      loop_comp_helper (acc \<triangleright> m) m t A p" (*need this for step*)
      by (metis loop_comp_helper.simps(2) non_electing_def seq_n_input_sound step_reduces_defer_set
          term_not_satisfied)
    thus ?case
    proof cases
      assume card_too_small: "card (defer acc A p) < x"
      thus ?thesis
        using not_le by blast
    next
      assume old_card_at_least_x: "\<not>(card (defer acc A p) < x)"
      obtain i where i_is_new_card: "i = card (defer (acc \<triangleright> m) A p)"
        by blast
      from this card_not_eq_x have card_too_big: "card (defer acc A p) > x"
        using nat_neq_iff old_card_at_least_x by blast
      hence enough_leftover: "card (defer acc A p) > 1"
        using x_greater_zero by auto
      have "electoral_module acc \<longrightarrow> (defer acc A p) \<subseteq> A"
        by (simp add: defer_from_input profile)
      hence step_profile: "electoral_module acc \<longrightarrow>
                           finite_profile (defer acc A p) (limit_profile_to (defer acc A p) p)"
        using profile limit_profile_consistent by auto
      hence "electoral_module acc \<longrightarrow>
               card (defer m (defer acc A p) (limit_profile_to (defer acc A p) p)) =
               card (defer acc A p) - 1"
        using non_electing_m single_elimination single_elimination_reduces_defer_set_by_one2
              enough_leftover by blast
      hence "electoral_module acc \<longrightarrow> i = card (defer acc A p) - 1"
        by (metis seq_comp.simps snd_conv i_is_new_card)
      hence "electoral_module acc \<longrightarrow> i \<ge> x"
        using card_too_big by linarith
      hence new_card_still_big_enough: "electoral_module acc \<longrightarrow> x \<le> i"
        by blast
      have "electoral_module acc \<and> electoral_module m \<longrightarrow> defer (acc \<triangleright> m) A p \<subseteq> defer acc A p"
        using enough_leftover profile subset by blast
      hence "electoral_module acc \<and> electoral_module m \<longrightarrow> i \<le> card (defer acc A p)"
        using card_mono i_is_new_card step_profile by blast
      hence i_geq_x: "electoral_module acc \<and> electoral_module m \<longrightarrow> (i = x \<or> i > x)"
        using nat_less_le new_card_still_big_enough by blast
      thus ?thesis
      proof cases
        assume new_card_greater_x: "electoral_module acc \<longrightarrow> i > x"
        hence "electoral_module acc \<longrightarrow> 1 < card (defer (acc \<triangleright> m) A p)"
          using x_greater_zero i_is_new_card
          by linarith
        moreover have new_card_still_big_enough2: "electoral_module acc \<longrightarrow> x \<le> i"
                                                  (*Need this for step*)
          using i_is_new_card new_card_still_big_enough by blast
        moreover have "n = card (defer acc A p) \<longrightarrow>
                       (electoral_module acc \<longrightarrow> i < n)" (*Need this for step*)
          using subset step_profile enough_leftover profile psubset_card_mono i_is_new_card by blast
        moreover have "electoral_module acc \<longrightarrow> electoral_module (acc \<triangleright> m)" (*Need this for step*)
          using non_electing_def non_electing_m seq_creates_modules by blast
        moreover have non_electing_new: "non_electing acc \<longrightarrow> non_electing (acc \<triangleright> m)"
          by (simp add: non_electing_m)
        ultimately have "(n = card (defer acc A p) \<and> non_electing acc \<and> electoral_module acc) \<longrightarrow>
                         card (defer (loop_comp_helper (acc \<triangleright> m) m t) A p) = x"
          using less.hyps i_is_new_card new_card_greater_x by blast
        thus ?thesis
          using profile rec_step by (metis non_electing_def)
      next
        assume i_not_gt_x: "\<not>(electoral_module acc \<longrightarrow> i > x)"
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> i = x"
          using i_geq_x by blast
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> t ((acc \<triangleright> m) A p)"
          using i_is_new_card terminate_if_n_left by blast
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow>
               card (defer_r (loop_comp_helper (acc \<triangleright> m) m t A p)) = x"
          by (metis loop_comp_helper.simps(1) terminate_if_n_left)
        thus ?thesis
          by (metis i_not_gt_x dual_order.strict_iff_order i_is_new_card loop_comp_helper.simps(1)
              new_card_still_big_enough profile rec_step terminate_if_n_left)
      qed
    qed
  qed
qed

lemma loop_comp_helper_iterative_elimination_number_of_survivors_for_eliminates:
  assumes non_electing_m:      "non_electing m" and
          single_elimination:  "eliminates 1 m" and
          terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
          x_greater_zero:      "x > 0" and
          profile:             "finite_profile A p" and
          acc_defers_enough:   "card (defer acc A p) \<ge> x" and
          non_electing_acc:    "non_electing acc"
    shows "card (defer (loop_comp_helper acc m t) A p) = x"
  by (metis (no_types, hide_lams) acc_defers_enough eq_iff less_le less_one
      loop_comp_helper.simps(1)
      loop_comp_helper_iterative_elimination_number_of_survivors_helper_for_eliminates nat_neq_iff
      non_electing_acc non_electing_m profile single_elimination terminate_if_n_left x_greater_zero)

lemma iterative_elimination_number_of_survivors_helper_for_eliminates:
  assumes non_electing_m:      "non_electing m" and
          single_elimination:  "eliminates 1 m" and
          terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
          x_greater_zero:      "x > 0" and
          profile:             "finite_profile A p" and
          enough_alternatives: "card A \<ge> x"
  shows "card (defer (m \<circlearrowleft>\<^sub>t) A p) = x"
proof cases
  assume "card A = x"
  thus ?thesis
    by (simp add: terminate_if_n_left)
next
  assume card_not_x: "\<not> card A = x"
  thus ?thesis
  proof cases
    assume "card A < x"
    thus ?thesis
      using enough_alternatives not_le by blast
  next
    assume "\<not>card A < x"
    hence card_big_enough_A: "card A > x"
      using card_not_x by linarith
    hence card_m: "card (defer m A p) = card A - 1"
      using non_electing_m profile single_elimination single_elimination_reduces_defer_set_by_one2
            x_greater_zero by fastforce
    hence card_big_enough_m: "card (defer m A p) \<ge> x"
      using card_big_enough_A by linarith
    hence "(m \<circlearrowleft>\<^sub>t) A p = (loop_comp_helper m m t) A p"
      by (simp add: card_not_x terminate_if_n_left)
    thus ?thesis
      by (metis (no_types, hide_lams) card_big_enough_m
          loop_comp_helper_iterative_elimination_number_of_survivors_for_eliminates non_electing_m
          profile single_elimination terminate_if_n_left x_greater_zero)
  qed
qed

(**********************************************)
(*** Composition Rules for Loop Composition ***)
(**********************************************)

(* Looping a defer lift invariant electoral module creates a defer lift invariant electoral module.
*)
theorem loop_comp_preserves_defer_lift_invariant[simp]:
  assumes monotone_m: "defer_lift_invariant m"
  shows "defer_lift_invariant (m \<circlearrowleft>\<^sub>t)"
proof -
  fix A
  have "\<forall> p q a. (a \<in> (defer (m \<circlearrowleft>\<^sub>t) A p) \<and> lifted A p q a) \<longrightarrow>
                 (m \<circlearrowleft>\<^sub>t) A p = (m \<circlearrowleft>\<^sub>t) A q"
    by (metis (full_types) Defer_module.simps loop_comp.simps(1) loop_comp.simps(2)
        loop_comp_helper_defer_lift_invariant2 monotone_m lifted_impl_finite_profile)
  thus ?thesis
    by (smt defer_module_defer_lift_invariant loop_comp.simps(1) loop_comp.simps(2)
        loop_comp_creates_modules loop_comp_helper_defer_lift_invariant2 monotone_m
        defer_lift_invariant_def lifted_impl_finite_profile)
qed

(* Looping a non electing electoral module creates a non electing electoral module. *)
theorem loop_preserves_non_electing[simp]:
  assumes non_electing_m: "non_electing m"
  shows "non_electing (m \<circlearrowleft>\<^sub>t)"
  by (metis defer_module_non_electing loop_comp.simps(1) loop_comp.simps(2)
      loop_comp_creates_modules loop_preserves_non_electing_helper non_electing_def non_electing_m)

theorem iterative_elimination_number_of_survivors_for_eliminates[simp]:
  assumes non_electing_m:      "non_electing m" and
          single_elimination:  "eliminates 1 m" and
          terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = n))" and
          x_greater_zero: "n > 0"
  shows "defers n (m \<circlearrowleft>\<^sub>t)"
proof -
  have "\<forall> A p. finite_profile A p \<and> card A \<ge> n \<longrightarrow> card (defer (m \<circlearrowleft>\<^sub>t) A p) = n"
    using iterative_elimination_number_of_survivors_helper_for_eliminates non_electing_m
          single_elimination terminate_if_n_left x_greater_zero by blast
  moreover have "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_creates_modules eliminates_def single_elimination by blast
  thus ?thesis
    by (simp add: calculation defers_def)
qed

end

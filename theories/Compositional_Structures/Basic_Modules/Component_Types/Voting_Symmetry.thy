section \<open>Symmetry Properties of Voting Rules\<close>

theory Voting_Symmetry
  imports Symmetry_Of_Functions
          Electoral_Module
begin    

text \<open>
  We describe symmetry properties of voting rules as invariance 
  and equivariance under relations.
\<close>      

subsection \<open>Auxiliary Definitions\<close>

text \<open>
  We only require voting rules to behave a specific way on admissible elections,
  i.e. elections that are valid profiles (= votes are linear orders on the alternatives).
  Note that we do not assume finiteness of voter or alternative sets by default.
\<close>

definition valid_elections :: "('a,'v) Election set" where
  "valid_elections = {E. profile (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E)}"

fun (in result) results_closed_under_rel :: "('a,'v) Election rel \<Rightarrow> bool" where
  "results_closed_under_rel r = 
    (\<forall> (E, E') \<in> r. limit_set (alts_\<E> E) UNIV = limit_set (alts_\<E> E') UNIV)"

subsection \<open>Anonymity\<close>

text \<open>
  Anonymity is invariance under the natural action 
  of the voter permutation group on elections.
\<close>

definition anon_group :: "('v \<Rightarrow> 'v) monoid" where
  "anon_group = BijGroup (UNIV::'v set)"

fun \<phi>_anon :: "('v \<Rightarrow> 'v) \<Rightarrow> (('a, 'v) Election \<Rightarrow> ('a, 'v) Election)" where
  "\<phi>_anon \<pi> = extensional_continuation (rename \<pi>) finite_elections"

definition anonymity2 :: "(('a, 'v) Election, 'r Result) property" where
  "anonymity2 = Invariance (rel_induced_by_action (carrier anon_group) valid_elections \<phi>_anon)"

subsection \<open>Neutrality\<close>

text \<open>
  Neutrality is equivariance under consistent renaming of 
  candidates in the candidate set and election results.
\<close>

subsubsection \<open>Definitions\<close>

fun pref_rename :: "('a \<Rightarrow> 'a, 'a Preference_Relation) binary_fun" where
  "pref_rename \<pi> r = {(\<pi> a, \<pi> b) | a b. (a,b) \<in> r}"

definition neutr_group :: "('a \<Rightarrow> 'a) monoid" where
  "neutr_group = BijGroup (UNIV::'a set)"

fun \<phi>_neutr :: "('a \<Rightarrow> 'a, ('a,'v) Election) binary_fun" where
  "\<phi>_neutr \<pi> E = (\<pi> ` (alts_\<E> E), votrs_\<E> E, (pref_rename \<pi>) \<circ> (prof_\<E> E))"

fun \<psi>_neutr_soc_choice :: "('a \<Rightarrow> 'a, 'a) binary_fun" where
  "\<psi>_neutr_soc_choice \<pi> r = \<pi> r"

fun \<psi>_neutr_soc_welfare :: "('a \<Rightarrow> 'a, 'a rel) binary_fun" where
  "\<psi>_neutr_soc_welfare \<pi> r = pref_rename \<pi> r"

(* definition (in result) neutrality :: "(('a, 'v) Election, 'r Result) property" where
  "neutrality = equivar_ind_by_act (carrier neutr_group) valid_elections \<phi>_neutr \<psi>_neutr" *)

subsubsection \<open>Auxiliary Lemmas\<close>

lemma pref_rename_comp:
  fixes
    f :: "'a \<Rightarrow> 'a" and
    g :: "'a \<Rightarrow> 'a" 
  shows "pref_rename (f \<circ> g) = pref_rename f \<circ> pref_rename g"
proof
  fix 
    r :: "'a rel"
  have "pref_rename (f \<circ> g) r = {(f (g a), f (g b)) |a b. (a, b) \<in> r}"
    by auto
  also have 
    "{(f (g a), f (g b)) |a b. (a, b) \<in> r} = {(f a, f b) |a b. (a, b) \<in> pref_rename g r}"
    sorry
  also have 
    "{(f a, f b) |a b. (a, b) \<in> pref_rename g r} = (pref_rename f \<circ> pref_rename g) r"
    unfolding comp_def
    sorry
  finally show "pref_rename (f \<circ> g) r = (pref_rename f \<circ> pref_rename g) r"
    by simp
qed

lemma bij_\<phi>_neutr:
  fixes
    x :: "('a \<Rightarrow> 'a)"
  assumes "bij x"
  shows 
    bij_neutr: "bij (\<phi>_neutr x)" and
    bij_fin_neutr: "bij_betw (\<phi>_neutr x) finite_elections finite_elections" and
    Bij_el_neutr: "\<phi>_neutr x \<in> carrier (BijGroup UNIV)"
  sorry

subsubsection \<open>Group Actions\<close>

interpretation \<phi>_neutr_act: 
  group_action neutr_group UNIV \<phi>_neutr
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def neutr_group_def,
        safe, (rule group_BijGroup)+, rule Bij_el_neutr, rule bij_car_el, simp)
  fix
    x :: "'a \<Rightarrow> 'a" and
    y :: "'a \<Rightarrow> 'a"
  assume
    x_el: "x \<in> carrier (BijGroup UNIV)" and
    y_el: "y \<in> carrier (BijGroup UNIV)"
   hence bij: "bij x \<and> bij y"
    by (metis bij_car_el)
  hence "\<phi>_neutr x \<in> carrier (BijGroup UNIV) \<and> 
          \<phi>_neutr y \<in> carrier (BijGroup UNIV)"
    using Bij_el_neutr
    by metis
  hence "\<phi>_neutr x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_neutr y = \<phi>_neutr x \<circ> \<phi>_neutr y"
    using rewrite_mult_univ
    by blast
  also have "\<phi>_neutr x \<circ> \<phi>_neutr y = \<phi>_neutr (x \<circ> y)"
  proof 
    fix 
      E :: "('a, 'v) Election"
    have "(\<phi>_neutr x \<circ> \<phi>_neutr y) E = \<phi>_neutr x (\<phi>_neutr y E)"
      by simp
    also have "\<phi>_neutr x (\<phi>_neutr y E) = 
      \<phi>_neutr x (y ` (alts_\<E> E), votrs_\<E> E, (pref_rename y) \<circ> (prof_\<E> E))"
      by simp
    also have "\<phi>_neutr x (y ` (alts_\<E> E), votrs_\<E> E, (pref_rename y) \<circ> (prof_\<E> E))
      = (x ` y ` (alts_\<E> E), votrs_\<E> E, (pref_rename x) \<circ> (pref_rename y) \<circ> (prof_\<E> E))"
      by (simp add: fun.map_comp)
    also have 
      "(x ` y ` (alts_\<E> E), votrs_\<E> E, (pref_rename x) \<circ> (pref_rename y) \<circ> (prof_\<E> E)) = 
        ((x \<circ> y) ` (alts_\<E> E), votrs_\<E> E, (pref_rename (x \<circ> y)) \<circ> (prof_\<E> E))"
      using pref_rename_comp image_comp
      by metis
    also have 
      "((x \<circ> y) ` (alts_\<E> E), votrs_\<E> E, (pref_rename (x \<circ> y)) \<circ> (prof_\<E> E)) = \<phi>_neutr (x \<circ> y) E"
      sorry
    finally show "(\<phi>_neutr x \<circ> \<phi>_neutr y) E = \<phi>_neutr (x \<circ> y) E"
      by blast
  qed
  also have "x \<circ> y = x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y"
    using rewrite_mult_univ x_el y_el
    by fastforce
  finally have "\<phi>_neutr x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_neutr y = \<phi>_neutr (x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y)"
    sorry
  thus "\<phi>_neutr (x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y) = \<phi>_neutr x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_neutr y"
    using eq_commute[of "\<phi>_neutr x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_neutr y" "\<phi>_neutr (x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y)"]
    by blast
qed

interpretation \<psi>_neutr_act:
  group_action neutr_group UNIV \<psi>_neutr_soc_choice
  sorry

subsubsection \<open>Well-Formedness\<close>

(* TODO *)

section \<open>Homogeneity\<close>

subsection \<open>Definitions\<close>

abbreviation shift_by_prod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "shift_by_prod n m x \<equiv> x + n*m"

definition shift :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
  "shift X n = (shift_by_prod n (Max X + 1)) ` X"

definition copy_nat_set :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
  "copy_nat_set X n = \<Union> {(shift X m) | m. m \<in> {0..<n}}"

abbreviation modulo :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "modulo m n \<equiv> n mod m"

definition homogeneity_monoid :: "nat monoid" where
  "homogeneity_monoid = \<lparr>carrier = UNIV, mult = (\<lambda>a b. a * b), one = 1\<rparr>"

definition \<phi>_homogeneity :: "(nat, ('a, nat) Election) binary_fun" where
  "\<phi>_homogeneity n E = 
    (alts_\<E> E, copy_nat_set (votrs_\<E> E) n, (prof_\<E> E) \<circ> (modulo (Max (votrs_\<E> E) + 1)))"

definition ordered_homogeneity :: "('a, nat, 'r) Electoral_Module \<Rightarrow> bool" where
  "ordered_homogeneity m = 
    has_prop (on_els m) (Invariance
      (rel_induced_by_action (carrier homogeneity_monoid) valid_elections \<phi>_homogeneity))"

definition distance_ordered_homogeneity :: "('a, nat) Election Distance \<Rightarrow> bool" where
  "distance_ordered_homogeneity d = 
    totally_invariant_dist d
      (rel_induced_by_action (carrier homogeneity_monoid) valid_elections \<phi>_homogeneity )"

subsection \<open>Auxiliary Lemmas\<close>

lemma copy_nat_set_card:
  fixes
    n :: nat and
    X :: "nat set"
  assumes
    "finite X" and "X \<noteq> {}"    
  shows
    "card (copy_nat_set X n) = n * (card X)"
proof -
  have "\<And>a b. a > b \<Longrightarrow> (shift X a \<inter> shift X b = {})"
  proof (unfold shift_def, safe)
    fix 
      a :: nat and b :: nat and x :: nat and y :: nat
    assume
      x_el: "x \<in> X" and y_el: "y \<in> X" and "b < a" and
      eq: "shift_by_prod a (Max X + 1) x = shift_by_prod b (Max X + 1) y"
    hence "a \<ge> b + 1" by simp
    hence "a * (Max X + 1) + x - (b * (Max X + 1) + y) \<ge> 
            (b+1) * (Max X + 1) + x - (b * (Max X + 1) + y)"
      by (meson eq add_mono_thms_linordered_semiring(3) diff_le_mono mult_le_cancel2)
    moreover have "(b+1) * (Max X + 1) + x - (b * (Max X + 1) + y) = (Max X + 1) + x - y"
      by auto
    moreover have "(Max X + 1) + x - y > 0"
      by (metis assms(1) y_el Max_ge add_cancel_right_right 
                add_less_same_cancel1  gr_zeroI le_add1 le_add_diff 
                le_eq_less_or_eq le_trans not_add_less1 zero_neq_one)
    ultimately have "a * (Max X + 1) + x - (b * (Max X + 1) + y) > 0"
      by presburger
    hence "False" using eq by simp
    thus "shift_by_prod a (Max X + 1) x \<in> {}" by simp
  qed
  hence empty_int: "\<forall>a b. a \<noteq> b \<longrightarrow> shift X a \<inter> shift X b = {}"
    by (metis antisym_conv3 inf_sup_aci(1))
  moreover have 
    "\<forall>a \<in> {(shift X m) | m. m \<in> {0..<n}}. \<forall> b \<in> {(shift X m) | m. m \<in> {0..<n}}. 
          a \<noteq> b \<longrightarrow> (\<exists> x y. x \<noteq> y \<and> a = shift X x \<and> b = shift X y)"
    by force
  ultimately have 
    "\<forall>a \<in> {(shift X m) | m. m \<in> {0..<n}}. \<forall> b \<in> {(shift X m) | m. m \<in> {0..<n}}. 
          a \<noteq> b \<longrightarrow> a \<inter> b = {}"
    by (metis (no_types, lifting))  
  moreover have fin: "finite {(shift X m) | m. m \<in> {0..<n}}"
    by simp
  moreover have "finite (copy_nat_set X n)"
    unfolding copy_nat_set_def shift_def
    using assms(1)
    by (simp add: setcompr_eq_image)
  moreover have "\<forall>a \<in> {(shift X m) | m. m \<in> {0..<n}}. card a = card X"
    sorry
  ultimately have eq: "card X * card {(shift X m) | m. m \<in> {0..<n}} = card (copy_nat_set X n)"
    unfolding copy_nat_set_def
    using card_partition
    by (metis (no_types, lifting))
  also have "card {(shift X m) | m. m \<in> {0..<n}} = n"
    sorry
  finally have "card X * n = card (copy_nat_set X n)"
    by simp
  thus "card (copy_nat_set X n) = n * card X"
    by (simp add: mult.commute)   
qed

subsection \<open>Monoid Actions\<close>

interpretation monoid_homogeneity_monoid: monoid homogeneity_monoid
  sorry

lemma \<phi>_homogeneity_hom: 
  "\<phi>_homogeneity \<in> hom homogeneity_monoid (BijGroup finite_elections)"
  sorry

subsection \<open>Well-Formedness\<close>

(* TODO *)

subsection \<open>Reversal Symmetry\<close>

text \<open>
  A social welfare rule is reversal symmetric if reversing all voters' preferences
  reverses the result rankings as well.
\<close>

fun rev_rel :: "'a rel \<Rightarrow> 'a rel" where
  "rev_rel r = {(a,b). (b,a) \<in> r}"

definition rev_group :: "('a rel \<Rightarrow> 'a rel) monoid" where
  "rev_group = \<lparr>carrier = {rev_rel, id}, mult = (\<lambda>f. \<lambda>g. f \<circ> g), one = id\<rparr>"

fun \<phi>_rev :: "('a rel \<Rightarrow> 'a rel, ('a, 'v) Election) binary_fun" where
  "\<phi>_rev \<phi> E = (alts_\<E> E, votrs_\<E> E, \<phi> \<circ> (prof_\<E> E))"

fun \<psi>_rev :: "('a rel \<Rightarrow> 'a rel, 'a rel Result) binary_fun" where
  "\<psi>_rev \<phi> r = (\<phi> ` (elect_r r), \<phi> ` (reject_r r), \<phi> ` (elect_r r))"

definition rev_symmetry :: "(('a, 'v) Election, 'a rel Result) property" where
  "rev_symmetry = equivar_ind_by_act (carrier rev_group) valid_elections \<phi>_rev \<psi>_rev"

definition rev_symmetry_dist :: "('a, 'v) Election Distance \<Rightarrow> bool" where
  "rev_symmetry_dist d \<equiv> invariant_dist d (carrier rev_group) UNIV \<phi>_rev"

abbreviation apply_to_res :: "('r \<Rightarrow> 'r) \<Rightarrow> 'r Result \<Rightarrow> 'r Result"
  where "apply_to_res f r \<equiv> (f ` (elect_r r), f ` (reject_r r), f ` (defer_r r))"

subsubsection \<open>Auxiliary Lemmas\<close>

lemma rev_rev_id:
  "rev_rel \<circ> rev_rel = id"
  by auto

lemma bij_rev:
  "bij rev_rel"
  unfolding bij_def inj_def
  by auto

interpretation rev_group_group: group rev_group
proof
  show "\<one>\<^bsub>rev_group\<^esub> \<in> carrier rev_group"
    unfolding rev_group_def
    by simp
next
  show "carrier rev_group \<subseteq> Units rev_group"
    unfolding rev_group_def Units_def
    using rev_rev_id
    by auto
next
  fix
    x :: "'a rel \<Rightarrow> 'a rel"
  assume
    x_el: "x \<in> carrier rev_group"
  thus
    "\<one>\<^bsub>rev_group\<^esub> \<otimes>\<^bsub>rev_group\<^esub> x = x"
    unfolding rev_group_def
    by auto
  show 
    "x \<otimes>\<^bsub>rev_group\<^esub> \<one>\<^bsub>rev_group\<^esub> = x"
    unfolding rev_group_def
    by auto
  fix
    y :: "'a rel \<Rightarrow> 'a rel"
  assume
    y_el: "y \<in> carrier rev_group"
  thus "x \<otimes>\<^bsub>rev_group\<^esub> y \<in> carrier rev_group"
    using x_el rev_rev_id
    unfolding rev_group_def
    by auto
  fix
    z :: "'a rel \<Rightarrow> 'a rel"
  assume
    z_el: "z \<in> carrier rev_group"
  thus 
    "x \<otimes>\<^bsub>rev_group\<^esub> y \<otimes>\<^bsub>rev_group\<^esub> z = x \<otimes>\<^bsub>rev_group\<^esub> (y \<otimes>\<^bsub>rev_group\<^esub> z)"
    using x_el y_el
    unfolding rev_group_def
    by auto
qed

lemma \<phi>_rev_\<phi>_rev_id:
  "\<And>x. x \<in> carrier rev_group \<Longrightarrow> (\<phi>_rev x) \<circ> (\<phi>_rev x) = id"
proof
  fix 
    x :: "'a rel \<Rightarrow> 'a rel" and
    E :: "('a, 'b) Election"
  show "x \<in> carrier rev_group \<Longrightarrow> (\<phi>_rev x \<circ> \<phi>_rev x) E = id E"
  proof (cases "x = id")
    case True
    hence "\<phi>_rev x E = E"
      by simp
    thus ?thesis
      by simp
  next
    case False
    assume "x \<in> carrier rev_group"
    hence "x = rev_rel"
      unfolding rev_group_def
      using False
      by simp
    hence "(\<phi>_rev x) ((\<phi>_rev x) E) = (alts_\<E> E, votrs_\<E> E, rev_rel \<circ> (rev_rel \<circ> (prof_\<E> E)))"
      by simp
    also have "rev_rel \<circ> (rev_rel \<circ> (prof_\<E> E)) = prof_\<E> E"
      using rev_rev_id
      by (metis fun.map_comp id_comp)
    finally show "(\<phi>_rev x \<circ> \<phi>_rev x) E = id E"
      by simp
  qed
qed

lemma \<phi>_rev_bij:
  "\<And>x. x \<in> carrier rev_group \<Longrightarrow> bij (\<phi>_rev x)"
  unfolding bij_def
  by (metis \<phi>_rev_\<phi>_rev_id bij_betw_def comp_eq_id_dest fun.map_id id_def involuntory_imp_bij)

subsection \<open>Group Actions\<close>

interpretation \<phi>_rev_act:
  group_action rev_group UNIV \<phi>_rev
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, 
        safe, rule group_BijGroup)
  fix
    x :: "'a rel \<Rightarrow> 'a rel" and
    y :: "'a rel \<Rightarrow> 'a rel"
  assume 
    x_el: "x \<in> carrier rev_group" and
    y_el: "y \<in> carrier rev_group"
  thus x_car: "\<phi>_rev x \<in> carrier (BijGroup UNIV)"
    using rewrite_carrier \<phi>_rev_bij
    by auto
  moreover have "\<phi>_rev y \<in> carrier (BijGroup UNIV)"
    using rewrite_carrier y_el \<phi>_rev_bij
    by auto
  ultimately have eq_comp:
    "\<phi>_rev x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_rev y = (\<phi>_rev x) \<circ> (\<phi>_rev y)" 
    using rewrite_mult_univ
    by auto
  have "\<forall>E. \<phi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y) E = (alts_\<E> E, votrs_\<E> E, (x \<circ> y) \<circ> (prof_\<E> E))"
    unfolding rev_group_def
    by simp
  moreover have "\<forall>E. (alts_\<E> E, votrs_\<E> E, (x \<circ> y) \<circ> (prof_\<E> E)) = 
                  (alts_\<E> E, votrs_\<E> E, x \<circ> (y \<circ> prof_\<E> E))"
    by auto
  moreover have "\<forall>E. (alts_\<E> E, votrs_\<E> E, x \<circ> (y \<circ> prof_\<E> E)) = 
                  \<phi>_rev x (alts_\<E> E, votrs_\<E> E, y \<circ> (prof_\<E> E))"
    by simp
  ultimately have "\<forall>E. \<phi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y) E = \<phi>_rev x (\<phi>_rev y E)"
    by (simp add: rev_group_def)
  hence "\<forall>E. \<phi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y) E = ((\<phi>_rev x) \<circ> (\<phi>_rev y)) E"
    by simp
  hence "\<phi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y) = (\<phi>_rev x) \<circ> (\<phi>_rev y)"
    by blast
  thus "\<phi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y) = \<phi>_rev x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_rev y"
    by (simp add: eq_comp)
qed

interpretation \<psi>_rev_act: 
  group_action rev_group UNIV \<psi>_rev
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, 
        safe, rule group_BijGroup)
  fix 
    x :: "'a rel \<Rightarrow> 'a rel" and
    y :: "'a rel \<Rightarrow> 'a rel"
  assume
    x_el: "x \<in> carrier rev_group" and
    y_el: "y \<in> carrier rev_group"
  hence bij: "bij (\<psi>_rev x) \<and> bij (\<psi>_rev y)"
    sorry
  thus "\<psi>_rev x \<in> carrier (BijGroup UNIV)"
    using rewrite_carrier \<phi>_rev_bij
    by auto
  moreover have "\<psi>_rev y \<in> carrier (BijGroup UNIV)"
    using y_el rewrite_carrier \<phi>_rev_bij bij
    by blast
  ultimately have "\<psi>_rev x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<psi>_rev y = (\<psi>_rev x) \<circ> (\<psi>_rev y)"
    using rewrite_mult_univ
    by blast
  also have "(\<psi>_rev x) \<circ> (\<psi>_rev y) = \<psi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y)"
    unfolding rev_group_def
    sorry
  finally show "\<psi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y) = \<psi>_rev x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<psi>_rev y"
    by simp
qed

subsection \<open>Well-Formedness\<close>

lemma \<phi>_\<psi>_rev_well_formed:
  defines "equivar_prop_global_set_valued \<equiv> 
    equivar_ind_by_act (carrier rev_group) valid_elections \<phi>_rev (\<lambda>g. image (\<psi>_rev g))"
  shows 
    "has_prop (\<lambda>E. limit_set (alts_\<E> E) UNIV) equivar_prop_global_set_valued"
  sorry

end
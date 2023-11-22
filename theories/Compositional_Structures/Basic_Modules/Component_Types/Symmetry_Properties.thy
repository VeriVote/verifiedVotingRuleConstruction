theory Symmetry_Properties
  imports Symmetry
begin

section \<open>Auxiliary Lemmas\<close>

subsection \<open>TODO\<close>

lemma \<K>_els_fin:
  fixes
    C :: "('a, 'v, 'r Result) Consensus_Class"
  shows
    "\<K>_els C \<subseteq> finite_elections"
proof
  fix 
    E :: "('a,'v) Election"
  assume 
    "E \<in> \<K>_els C"
  hence "finite_election E"
    unfolding \<K>\<^sub>\<E>.simps
    by force
  thus "E \<in> finite_elections"
    unfolding finite_elections_def
    by simp
qed

lemma \<K>_els_univ:
  fixes
    C :: "('a, 'v, 'r Result) Consensus_Class"
  shows
    "\<K>_els C \<subseteq> UNIV"
  by simp

lemma the_inv_comp:
  fixes
    f :: "'x \<Rightarrow> 'x" and
    g :: "'x \<Rightarrow> 'x"
  assumes
    "bij f" and
    "bij g"
  shows "the_inv (x \<circ> y) = (the_inv y) \<circ> (the_inv x)"
  sorry

subsection \<open>Groups\<close>

abbreviation extensional_continuation :: "('x \<Rightarrow> 'x) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'x)" where
  "extensional_continuation f S \<equiv> (\<lambda>x. if (x \<in> S) then (f x) else undefined)"

lemma extensional_univ:
  "extensional_continuation f UNIV = f"
  unfolding If_def
  by simp

lemma rewrite_sym_group:
  shows
    rewrite_carrier: "carrier (BijGroup UNIV) = {f. bij f}" and
    bij_car_el: "\<And>f. f \<in> carrier (BijGroup UNIV) \<Longrightarrow> bij f" and
    rewrite_mult: 
      "\<And> S x y. x \<in> carrier (BijGroup S) \<Longrightarrow> 
                  y \<in> carrier (BijGroup S) \<Longrightarrow> 
                  x \<otimes>\<^bsub>BijGroup S\<^esub> y = extensional_continuation (x \<circ> y) S" and
    rewrite_mult_univ:
      "\<And>x y. x \<in> carrier (BijGroup UNIV) \<Longrightarrow> 
              y \<in> carrier (BijGroup UNIV) \<Longrightarrow> 
              x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y = x \<circ> y"
proof -
  show rew: "carrier (BijGroup UNIV) = {f. bij f}"
    unfolding BijGroup_def Bij_def
    by simp
  fix 
    f :: "'b \<Rightarrow> 'b"
  assume 
    "f \<in> carrier (BijGroup UNIV)"
  thus "bij f"
    using rew
    by blast 
next
  fix
    S :: "'c set" and
    x :: "'c \<Rightarrow> 'c" and
    y :: "'c \<Rightarrow> 'c"
  assume
    "x \<in> carrier (BijGroup S)" and
    "y \<in> carrier (BijGroup S)"
  thus "x \<otimes>\<^bsub>BijGroup S\<^esub> y = extensional_continuation (x \<circ> y) S"
    unfolding BijGroup_def compose_def comp_def
    by (simp add: restrict_def)
next
  fix
    x :: "'d \<Rightarrow> 'd" and
    y :: "'d \<Rightarrow> 'd"
  assume
    "x \<in> carrier (BijGroup UNIV)" and
    "y \<in> carrier (BijGroup UNIV)"
  thus "x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y = x \<circ> y"
    unfolding BijGroup_def compose_def comp_def
    by (simp add: restrict_def)
qed
    
section \<open>Reversal Symmetry\<close>

text \<open>
  A social welfare rule is reversal symmetric if reversing all voters' preferences
  reverses the result rankings as well.
\<close>

subsection \<open>Definitions\<close>

definition rev_rel :: "'a rel \<Rightarrow> 'a rel" where
  "rev_rel r = {(a,b). (b,a) \<in> r}"

definition rev_group :: "('a rel \<Rightarrow> 'a rel) monoid" where
  "rev_group = \<lparr>carrier = {rev_rel, id}, mult = (\<lambda>f. \<lambda>g. f \<circ> g), one = id\<rparr>"

definition \<phi>_rev :: "('a rel \<Rightarrow> 'a rel, ('a, 'v) Election) binary_fun" where
  "\<phi>_rev \<phi> E = (alts_\<E> E, votrs_\<E> E, \<phi> \<circ> (prof_\<E> E))"

definition \<psi>_rev :: "('a rel \<Rightarrow> 'a rel, 'a rel) binary_fun" where
  "\<psi>_rev \<phi> r = (\<phi> r)"

definition rev_symmetry :: "('a, 'v, 'a rel) Electoral_Module \<Rightarrow> bool" where
  "rev_symmetry m \<equiv> equivariant (on_els m) (carrier rev_group) UNIV \<phi>_rev \<psi>_rev"

definition rev_symmetry_dist :: "('a, 'v) Election Distance \<Rightarrow> bool" where
  "rev_symmetry_dist d \<equiv> invariant_dist d (carrier rev_group) UNIV \<phi>_rev"

subsection \<open>Auxiliary Lemmas\<close>

lemma rev_rev_id:
  "rev_rel \<circ> rev_rel = id"
  unfolding rev_rel_def
  by auto

lemma bij_rev:
  "bij rev_rel"
  unfolding rev_rel_def bij_def inj_def
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
      unfolding \<phi>_rev_def
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
      unfolding \<phi>_rev_def
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
    unfolding rev_group_def \<phi>_rev_def
    by simp
  moreover have "\<forall>E. (alts_\<E> E, votrs_\<E> E, (x \<circ> y) \<circ> (prof_\<E> E)) = 
                  (alts_\<E> E, votrs_\<E> E, x \<circ> (y \<circ> prof_\<E> E))"
    by auto
  moreover have "\<forall>E. (alts_\<E> E, votrs_\<E> E, x \<circ> (y \<circ> prof_\<E> E)) = 
                  \<phi>_rev x (alts_\<E> E, votrs_\<E> E, y \<circ> (prof_\<E> E))"
    unfolding \<phi>_rev_def
    by simp
  ultimately have "\<forall>E. \<phi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y) E = \<phi>_rev x (\<phi>_rev y E)"
    unfolding \<phi>_rev_def
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
    unfolding \<psi>_rev_def
    using bij_rev
    by (metis bij_id insertE partial_object.select_convs(1) rev_group_def singleton_iff)
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
    unfolding rev_group_def \<psi>_rev_def
    by simp
  finally show "\<psi>_rev (x \<otimes>\<^bsub>rev_group\<^esub> y) = \<psi>_rev x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<psi>_rev y"
    by simp
qed

subsection \<open>Well-Formedness\<close>

lemma \<phi>_\<psi>_rev_well_formed:
  defines "rel \<equiv> (rel_induced_by_action (carrier rev_group) \<phi>_rev UNIV)"
  shows
    \<phi>_rev_presv_fin: "set_closed_under_rel finite_elections rel"  and
    welfare_results_closed: 
      "equivariant (\<lambda>E. limit_set_welfare (alts_\<E> E) UNIV) (carrier G) UNIV \<phi> (\<lambda>g. \<lambda>S. \<psi> g ` S)"
proof (unfold set_closed_under_rel_def finite_elections_def 
        rel_def rel_induced_by_action_def, safe)
  fix
    A :: "'a set" and
    V :: "'b set" and
    p :: "('a, 'b) Profile" and
    A' :: "'a set" and
    V' :: "'b set" and
    p' :: "('a, 'b) Profile" and
    x :: "'a rel \<Rightarrow> 'a rel"
  assume 
    x_el: "x \<in> carrier rev_group" and
    "\<phi>_rev x (A,V,p) = (A',V',p')" and
    fin_A: "finite (alts_\<E> (A, V, p))" and
    fin_V: "finite (votrs_\<E> (A, V, p))" and
    prof: "on_els profile (A, V, p)"
  hence rew: "(A', V', p') = (A, V, x \<circ> p)"
    unfolding \<phi>_rev_def
    by simp
  thus "finite (alts_\<E> (A',V',p'))"
    using fin_A
    by simp
  show "finite (votrs_\<E> (A',V',p'))"
    using fin_V rew
    by simp
  have "\<forall> v \<in> V'. p' v = p v \<or> p' v = rev_rel (p v)" 
    using x_el rew
    unfolding rev_group_def
    by auto
  moreover have "\<forall> v \<in> V'. linear_order_on A' (rev_rel (p v))"
    sorry
  ultimately have "profile V' A' p'"
    by (metis prof rew fst_eqD profile_def sndI)
  thus "on_els profile (A', V', p')"
    by auto
next
  show "equivariant (\<lambda>E. limit_set_welfare (alts_\<E> E) UNIV) (carrier G) UNIV \<phi> (\<lambda>g. (`) (\<psi> g))"
    sorry
qed


section \<open>Anonymity\<close>

text \<open>
  Anonymity is invariance under the natural action of the voter permutation group on elections.
\<close>

subsection \<open>Definitions\<close>

definition anon_group :: "('v \<Rightarrow> 'v) monoid" where
  "anon_group = BijGroup (UNIV::'v set)"

definition \<phi>_anon :: "('v \<Rightarrow> 'v) \<Rightarrow> (('a, 'v) Election \<Rightarrow> ('a, 'v) Election)" where
  "\<phi>_anon \<pi> = extensional_continuation (rename \<pi>) finite_elections"

subsection \<open>Auxiliary Lemmas\<close>

lemma ext_\<phi>_anon:
  fixes
    x :: "('v \<Rightarrow> 'v)"
  assumes "bij x"
  shows 
    "\<phi>_anon \<pi> \<in> extensional finite_elections"
  unfolding \<phi>_anon_def extensional_def
  by fastforce

lemma bij_\<phi>_anon:
  fixes
    x :: "('v \<Rightarrow> 'v)"
  assumes "bij x"
  shows 
    bij: "bij (\<phi>_anon x)" and
    bij_restr: "bij_betw (\<phi>_anon x) finite_elections finite_elections" and
    Bij_el: "\<phi>_anon x \<in> carrier (BijGroup finite_elections)"
proof -
  show "bij (\<phi>_anon x)" sorry
next
  show bij_restr: "bij_betw (\<phi>_anon x) finite_elections finite_elections" sorry
  show "\<phi>_anon x \<in> carrier (BijGroup finite_elections)"
    unfolding BijGroup_def Bij_def
    using bij_restr ext_\<phi>_anon
    by auto
qed

subsection \<open>Group Actions\<close>

interpretation \<phi>_anon_act: 
  group_action anon_group finite_elections \<phi>_anon
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def anon_group_def, 
        safe, (rule group_BijGroup)+, rule Bij_el, rule bij_car_el, simp)
  fix 
    x :: "'a \<Rightarrow> 'a" and y :: "'a \<Rightarrow> 'a" 
  assume x_el: "x \<in> carrier (BijGroup UNIV)" and y_el: "y \<in> carrier (BijGroup UNIV)"
  hence bij: "bij x \<and> bij y"
    by (metis bij_car_el)
  hence "\<phi>_anon x \<in> carrier (BijGroup finite_elections) \<and> 
          \<phi>_anon y \<in> carrier (BijGroup finite_elections)"
    using Bij_el
    by metis
  hence "\<phi>_anon x \<otimes>\<^bsub>BijGroup finite_elections\<^esub> \<phi>_anon y = 
          extensional_continuation ((\<phi>_anon x) \<circ> (\<phi>_anon y)) finite_elections"
    using rewrite_mult[of "\<phi>_anon x"  finite_elections "\<phi>_anon y"]
    by blast
  also have 
    "extensional_continuation ((\<phi>_anon x) \<circ> (\<phi>_anon y)) finite_elections = \<phi>_anon (x \<circ> y)"
  proof (standard)
    fix 
      E :: "('c,'a) Election"
    show 
      "extensional_continuation ((\<phi>_anon x) \<circ> (\<phi>_anon y)) finite_elections E = \<phi>_anon (x \<circ> y) E"
    proof (cases "E \<in> finite_elections")
      case True
      have "\<phi>_anon y E \<in> finite_elections"
        by (metis (mono_tags, lifting) bij True bij_betw_apply bij_restr)
      hence "(\<phi>_anon x \<circ> \<phi>_anon y) E = rename x (rename y E)"
        unfolding \<phi>_anon_def If_def
        using True
        by simp
      hence conc_rename:
        "extensional_continuation (\<phi>_anon x \<circ> \<phi>_anon y) finite_elections E
          = rename x (rename y E)"
        unfolding If_def
        by (simp add: True)
      have "\<phi>_anon (x \<circ> y) E = rename (x \<circ> y) E"
        unfolding \<phi>_anon_def If_def
        by (simp add: True)
      also have 
        "rename (x \<circ> y) E = (alts_\<E> E, (x \<circ> y) ` (votrs_\<E> E), (prof_\<E> E) \<circ> (the_inv (x \<circ> y)))"
        by (metis prod.collapse rename.simps)
      also have "(x \<circ> y) ` (votrs_\<E> E) = x ` y ` (votrs_\<E> E)"
        unfolding comp_def
        by auto
      also have "(the_inv (x \<circ> y)) = (the_inv y) \<circ> (the_inv x)"
        using bij the_inv_comp
        by blast
      also have 
        "(alts_\<E> E, x ` y ` votrs_\<E> E, prof_\<E> E \<circ> (the_inv y \<circ> the_inv x)) = 
          rename x (rename y E)"
        by (metis (no_types, lifting) fun.map_comp prod.collapse rename.simps)
      finally have
        "\<phi>_anon (x \<circ> y) E = rename x (rename y E)"
        by blast
      thus ?thesis
        using conc_rename
        by simp
    next
      case False
      hence
        "extensional_continuation (\<phi>_anon x \<circ> \<phi>_anon y) finite_elections E = undefined"
        unfolding If_def
        by simp
      also have "\<phi>_anon (x \<circ> y) E = undefined"
        unfolding \<phi>_anon_def If_def
        by (simp add: False)
      finally show ?thesis 
        by presburger
    qed
  qed 
  also have "\<phi>_anon (x \<circ> y) = \<phi>_anon (x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y)"
    using rewrite_mult_univ x_el y_el
    by fastforce
  finally show 
    "\<phi>_anon (x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y) = \<phi>_anon x \<otimes>\<^bsub>BijGroup finite_elections\<^esub> \<phi>_anon y"
    by (rule sym)
qed

subsection \<open>Well-Formedness\<close>

lemma (in result) \<phi>_anon_well_formed:
  defines
    "rel \<equiv> (rel_induced_by_action (carrier anon_group) \<phi>_anon finite_elections)"
  shows
    results_closed: "results_closed_under_rel rel" and
    fin_closed: "set_closed_under_rel finite_elections rel"
proof (unfold rel_def results_closed_under_rel_def rel_induced_by_action_def 
          set_closed_under_rel_def anon_group_def, safe)
  fix
    A :: "'a set" and
    V :: "'b set" and
    p :: "('a, 'b) Profile" and
    A' :: "'a set" and
    V' :: "'b set" and
    p' :: "('a, 'b) Profile" and
    \<pi> :: "'b \<Rightarrow> 'b" and
    r :: 'r
  assume 
    "\<pi> \<in> carrier (BijGroup UNIV)" and
    "\<phi>_anon \<pi> (A,V,p) = (A',V',p')" and
    "(A,V,p) \<in> finite_elections"
  hence "rename \<pi> (A,V,p) = (A',V',p')"
    unfolding \<phi>_anon_def
    by presburger
  hence "A' = A"
    unfolding rename.simps
    by simp
  hence "limit_set A UNIV = limit_set A' UNIV"
    by blast
  moreover have "(alts_\<E> (A',V',p')) = A'"
    by simp
  ultimately have 
    claim_1: "r \<in> limit_set (alts_\<E> (A,V,p)) UNIV \<Longrightarrow> r \<in> limit_set (alts_\<E> (A',V',p')) UNIV" and
    claim_2: "r \<in> limit_set (alts_\<E> (A',V',p')) UNIV \<Longrightarrow> r \<in> limit_set (alts_\<E> (A,V,p)) UNIV"
    by auto
  show "r \<in> limit_set (alts_\<E> (A,V,p)) UNIV \<Longrightarrow> r \<in> limit_set (alts_\<E> (A',V',p')) UNIV"
    by (rule claim_1)
  show "r \<in> limit_set (alts_\<E> (A',V',p')) UNIV \<Longrightarrow> r \<in> limit_set (alts_\<E> (A,V,p)) UNIV"
    by (rule claim_2)
qed         

subsection \<open>TODO\<close>

lemma (in result) inv_cons_and_dist_imp_inv_dr:
  defines
    "rel \<equiv> (rel_induced_by_action (carrier anon_group) \<phi>_anon finite_elections)"
  fixes
    d :: "('a,'v) Election Distance" and
    C :: "('a,'v,'r Result) Consensus_Class"
  assumes
    inv_d: "invariant_dist d (carrier anon_group) finite_elections \<phi>_anon" and
    closed_C: 
      "rel \<inter> ((\<K>_els C) \<times> finite_elections) \<subseteq> 
        (rel_induced_by_action (carrier anon_group) \<phi>_anon (\<K>_els C))" and
    inv_C: 
      "invariant (elect_r \<circ> (on_els (rule_\<K> C))) 
                 (rel_induced_by_action (carrier anon_group) \<phi>_anon (\<K>_els C))"
  shows 
    "invariant (on_els (distance_\<R> d C)) rel"
  using \<phi>_anon_act.group_action_axioms assms results_closed \<K>_els_fin
        invariant_under_group_action_equiv_dist[of anon_group finite_elections \<phi>_anon d C]
  by metis
    
subsection \<open>Equivalent Definitions\<close>

text \<open>
  The anonymity definition from the Electoral_Module theory is equivalent to 
  invariance of an electoral module under renaming voters.
\<close>

theorem (in result) anon_rule_inv_under_\<phi>_anon:
  defines 
    "rel \<equiv> (rel_induced_by_action (carrier anon_group) \<phi>_anon finite_elections)"
  fixes
    m :: "('a,'v,'r Result) Electoral_Module"
  shows
    "anonymity m = (electoral_module m \<and> invariant (on_els m) rel)"
proof (unfold invariant_def finite_elections_def, safe)
  assume 
    anon: "anonymity m"
  thus "electoral_module m"
    unfolding anonymity_def
    by simp
next
  fix 
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    A' :: "'a set" and
    V' :: "'v set" and
    p' :: "('a, 'v) Profile"
  assume
    anon: "anonymity m" and
    rel: "((A,V,p), (A',V',p')) \<in> rel"
  then obtain \<pi> :: "'v \<Rightarrow> 'v" where bij: "bij \<pi>" and img: "\<phi>_anon \<pi> (A,V,p) = (A',V',p')"
    unfolding rel_def rel_induced_by_action_def anon_group_def
    using bij_car_el 
    by auto
  have fin: "finite_profile V A p \<and> finite_profile V' A' p'"
    using rel
    unfolding rel_def finite_elections_def rel_induced_by_action_def
    by simp
  hence "rename \<pi> (A,V,p) = (A',V',p')"
    using img
    unfolding \<phi>_anon_def finite_elections_def
    by simp
  hence "m V A p = m V' A' p'"
    using anon bij fin
    unfolding anonymity_def
    by auto
  thus "on_els m (A, V, p) = on_els m (A', V', p')"
    by simp
next
  show "electoral_module m \<Longrightarrow> \<forall>a b. (a, b) \<in> rel \<longrightarrow> on_els m a = on_els m b \<Longrightarrow> anonymity m"
  proof (unfold anonymity_def Let_def, safe)
    fix 
      A :: "'a set" and
      V :: "'v set" and
      p :: "('a, 'v) Profile" and
      A' :: "'a set" and
      V' :: "'v set" and
      p' :: "('a, 'v) Profile" and
      \<pi> :: "'v \<Rightarrow> 'v"
    assume
      module: "electoral_module m" and
      invariant: "\<forall>a b. (a, b) \<in> rel \<longrightarrow> on_els m a = on_els m b" and
      bij: "bij \<pi>" and
      rel: "rename \<pi> (A, V, p) = (A', V', p')" and
      fin_A: "finite A" and
      fin_V: "finite V" and
      prof: "profile V A p"
    hence fin: "(A, V, p) \<in> finite_elections"
      unfolding finite_elections_def
      by simp
    moreover have "(A', V', p') \<in> finite_elections"
      unfolding finite_elections_def
      using bij rename_finite fin_A fin_V prof rel 
      by fastforce
    moreover have "\<pi> \<in> (carrier anon_group)"
      unfolding anon_group_def
      using bij rewrite_carrier
      by blast
    moreover have "\<phi>_anon \<pi> (A,V,p) = (A',V',p')"
      using fin rel
      unfolding \<phi>_anon_def
      by simp
    ultimately have "(on_els m) (A,V,p) = (on_els m) (A',V',p')"
      using invariant
      unfolding rel_def invariant_def rel_induced_by_action_def
      by blast
    thus "m V A p = m V' A' p'"
      by simp
  qed
qed

text \<open>
  The distance_anonymity definition from the Distance theory is 
  equivalent to invariance of a distance under renaming voters.
\<close>

theorem (in result) anon_dist_equiv_under_\<phi>_anon:
  defines 
    "rel \<equiv> (rel_induced_by_action (carrier anon_group) \<phi>_anon finite_elections)"
  fixes
    d :: "('a,'v) Election Distance"
  shows
    "distance_anonymity d = (invariant_dist d (carrier anon_group) finite_elections \<phi>_anon)"
  sorry

text \<open>
  The consensus_rule_anonymity definition from the Consensus_Class theory is 
  equivalent to invariance of a consensus rule under renaming voters.
\<close>

lemma c_anon_imp_inv:
  fixes
    C :: "('a,'v,'r Result) Consensus_Class"
  defines
      "rel \<equiv> (rel_induced_by_action (carrier anon_group) \<phi>_anon finite_elections)" and
      "rel_restr \<equiv> (rel_induced_by_action (carrier anon_group) \<phi>_anon (\<K>_els C))"
  shows
    "consensus_rule_anonymity C = (invariant (elect_r \<circ> (on_els (rule_\<K> C))) rel_restr) 
                                    \<and> rel \<inter> ((\<K>_els C) \<times> finite_elections) \<subseteq> rel_restr"
  sorry


section \<open>Neutrality\<close>

text \<open>
  Neutrality is equivariance under consistent renaming of 
  candidates in the candidate set and election results.
\<close>

subsection \<open>Definitions\<close>

definition pref_rename :: "('a \<Rightarrow> 'a, 'a Preference_Relation) binary_fun" where
  "pref_rename \<pi> r = {(\<pi> a, \<pi> b) | a b. (a,b) \<in> r}"

definition neutr_group :: "('a \<Rightarrow> 'a) monoid" where
  "neutr_group = BijGroup (UNIV::'a set)"

definition \<phi>_neutr :: "('a \<Rightarrow> 'a, ('a,'v) Election) binary_fun" where
  "\<phi>_neutr \<pi> E = (\<pi> ` (alts_\<E> E), votrs_\<E> E, (pref_rename \<pi>) \<circ> (prof_\<E> E))"

definition \<psi>_neutr_soc_choice :: "('a \<Rightarrow> 'a, 'a) binary_fun" where
  "\<psi>_neutr_soc_choice \<pi> r = \<pi> r"

definition \<psi>_neutr_soc_welfare :: "('a \<Rightarrow> 'a, 'a rel) binary_fun" where
  "\<psi>_neutr_soc_welfare \<pi> r = pref_rename \<pi> r"

subsection \<open>Auxiliary Lemmas\<close>

lemma pref_rename_comp:
  fixes
    f :: "'a \<Rightarrow> 'a" and
    g :: "'a \<Rightarrow> 'a" 
  shows "pref_rename (f \<circ> g) = pref_rename f \<circ> pref_rename g"
proof
  fix 
    r :: "'a rel"
  have "pref_rename (f \<circ> g) r = {(f (g a), f (g b)) |a b. (a, b) \<in> r}"
    unfolding pref_rename_def
    by auto
  also have 
    "{(f (g a), f (g b)) |a b. (a, b) \<in> r} = {(f a, f b) |a b. (a, b) \<in> pref_rename g r}"
    unfolding pref_rename_def
    by blast
  also have 
    "{(f a, f b) |a b. (a, b) \<in> pref_rename g r} = (pref_rename f \<circ> pref_rename g) r"
    unfolding pref_rename_def comp_def
    by blast
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

subsection \<open>Group Actions\<close>

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
      unfolding \<phi>_neutr_def
      by simp
    also have "\<phi>_neutr x (y ` (alts_\<E> E), votrs_\<E> E, (pref_rename y) \<circ> (prof_\<E> E))
      = (x ` y ` (alts_\<E> E), votrs_\<E> E, (pref_rename x) \<circ> (pref_rename y) \<circ> (prof_\<E> E))"
      unfolding \<phi>_neutr_def
      by (simp add: fun.map_comp)
    also have 
      "(x ` y ` (alts_\<E> E), votrs_\<E> E, (pref_rename x) \<circ> (pref_rename y) \<circ> (prof_\<E> E)) = 
        ((x \<circ> y) ` (alts_\<E> E), votrs_\<E> E, (pref_rename (x \<circ> y)) \<circ> (prof_\<E> E))"
      using pref_rename_comp image_comp
      by metis
    also have 
      "((x \<circ> y) ` (alts_\<E> E), votrs_\<E> E, (pref_rename (x \<circ> y)) \<circ> (prof_\<E> E)) = \<phi>_neutr (x \<circ> y) E"
      unfolding \<phi>_neutr_def
      by blast
    finally show "(\<phi>_neutr x \<circ> \<phi>_neutr y) E = \<phi>_neutr (x \<circ> y) E"
      by blast
  qed
  also have "x \<circ> y = x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y"
    using rewrite_mult_univ x_el y_el
    by fastforce
  finally have "\<phi>_neutr x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_neutr y = \<phi>_neutr (x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y)"
    by simp
  thus "\<phi>_neutr (x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y) = \<phi>_neutr x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_neutr y"
    using eq_commute[of "\<phi>_neutr x \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<phi>_neutr y" "\<phi>_neutr (x \<otimes>\<^bsub>BijGroup UNIV\<^esub> y)"]
    by blast
qed

interpretation \<psi>_neutr_act:
  group_action neutr_group UNIV \<psi>_neutr_soc_choice
  sorry

subsection \<open>Well-Formedness\<close>

lemma results_equivariant_under_\<phi>_\<psi>_neutr: 
  "equivariant (\<lambda>E. limit_set_soc_choice (alts_\<E> E) UNIV) 
                (carrier neutr_group) UNIV 
                \<phi>_neutr (\<lambda>g. \<lambda>S. \<psi>_neutr_soc_choice g ` S)"
proof (unfold equivariant_def, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a,'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    a :: 'a
  assume
    "\<pi> \<in> carrier neutr_group" and
    "a \<in> limit_set_soc_choice (alts_\<E> (\<phi>_neutr \<pi> (A, V, p))) UNIV"
  hence "a \<in> \<pi> ` A"
    unfolding \<phi>_neutr_def
    by simp
  thus "a \<in> \<psi>_neutr_soc_choice \<pi> ` limit_set_soc_choice (alts_\<E> (A,V,p)) UNIV"
    unfolding \<psi>_neutr_soc_choice_def
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a,'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    a :: 'a
  assume
    "\<pi> \<in> carrier neutr_group" and
    "a \<in> limit_set_soc_choice (alts_\<E> (A, V, p)) UNIV"
  hence "a \<in> A"
    unfolding \<phi>_neutr_def
    by simp
  thus 
    "\<psi>_neutr_soc_choice \<pi> a \<in> limit_set_soc_choice (alts_\<E> (\<phi>_neutr \<pi> (A, V, p))) UNIV"
    unfolding \<psi>_neutr_soc_choice_def \<phi>_neutr_def
    by simp
qed

subsection \<open>TODO\<close>

theorem name:
  defines
    "rel \<equiv> (rel_induced_by_action (carrier neutr_group) \<phi>_neutr UNIV)"
  fixes
    d :: "('a,'v) Election Distance" and
    C :: "('a,'v,'a Result) Consensus_Class"
  assumes
    inv_d: "invariant_dist d (carrier neutr_group) UNIV \<phi>_neutr" and
    closed_C:
      "(rel_induced_by_action (carrier neutr_group) \<phi>_neutr UNIV) \<inter> ((\<K>_els C) \<times> UNIV) 
          \<subseteq> (rel_induced_by_action (carrier neutr_group) \<phi>_neutr (\<K>_els C))" and
    equiv_C:
      "equivariant (elect_r \<circ> (on_els (rule_\<K> C))) (carrier neutr_group) UNIV 
                                                    \<phi>_neutr (\<lambda>g. \<lambda>S. \<psi>_neutr_soc_choice g ` S)"
  shows 
    "equivariant (on_els (social_choice_result.distance_\<R> d C)) 
                  (carrier neutr_group) UNIV 
                  \<phi>_neutr (\<lambda>g. apply_to_res (\<psi>_neutr_soc_choice g))"
  using results_equivariant_under_\<phi>_\<psi>_neutr \<K>_els_univ assms
        \<phi>_neutr_act.group_action_axioms \<psi>_neutr_act.group_action_axioms
        social_choice_result.equivariant_under_group_action 
          [of neutr_group UNIV \<phi>_neutr \<psi>_neutr_soc_choice d C]
  by blast


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
    invariant (on_els m) 
      (rel_induced_by_action (carrier homogeneity_monoid) \<phi>_homogeneity finite_elections)"

definition distance_ordered_homogeneity :: "('a, nat) Election Distance \<Rightarrow> bool" where
  "distance_ordered_homogeneity d = 
    totally_invariant_dist d
      (rel_induced_by_action (carrier homogeneity_monoid) \<phi>_homogeneity finite_elections)"

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

lemma (in result) results_well_formed_under_\<phi>_homogeneity: 
  defines
    "rel \<equiv> (rel_induced_by_action (carrier homogeneity_monoid) \<phi>_homogeneity finite_elections)"
  shows
    "results_closed_under_rel rel"
  sorry

subsection \<open>TODO\<close>

theorem (in result) inv_cons_and_totally_inv_dist_imp_inv_dr:
  defines
    "rel \<equiv> (rel_induced_by_action (carrier homogeneity_monoid) \<phi>_homogeneity finite_elections)"
  fixes
    d :: "('a, nat) Election Distance" and
    C :: "('a, nat, 'r Result) Consensus_Class"
  assumes
    inv_d: "distance_ordered_homogeneity d" and
    closed_C: 
      "rel \<inter> ((\<K>_els C) \<times> finite_elections) \<subseteq> 
        (rel_induced_by_action (carrier homogeneity_monoid) \<phi>_homogeneity (\<K>_els C))" and
    inv_C: 
      "invariant (elect_r \<circ> (on_els (rule_\<K> C))) 
                 (rel_induced_by_action (carrier homogeneity_monoid) \<phi>_homogeneity (\<K>_els C))"
  shows 
    "ordered_homogeneity (distance_\<R> d C)"
  using 
    invariant_under_group_action_inv_dist[of \<phi>_homogeneity homogeneity_monoid finite_elections C d] 
    \<phi>_homogeneity_hom results_well_formed_under_\<phi>_homogeneity \<K>_els_fin assms 
    monoid_homogeneity_monoid.monoid_axioms
  unfolding distance_ordered_homogeneity_def rel_def ordered_homogeneity_def
  by metis

end
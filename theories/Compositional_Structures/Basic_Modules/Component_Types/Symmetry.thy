theory Symmetry
  imports Distance_Rationalization

begin    

section \<open>General Definitions\<close>

subsection \<open>Invariance and Equivariance\<close>

text \<open>
  We describe symmetry properties of voting rules as invariance and equivariance under relations
  that may be induced by group actions.
\<close>

type_synonym ('x,'y) binary_fun = "'x \<Rightarrow> 'y \<Rightarrow> 'y"

definition invariant :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x rel \<Rightarrow> bool" 
  where "invariant f r = (\<forall>a. \<forall>b. (a,b) \<in> r \<longrightarrow> f a = f b)"

definition equivariant :: 
  "('y \<Rightarrow> 'z) \<Rightarrow> 'x set \<Rightarrow> 'y set \<Rightarrow> ('x, 'y) binary_fun \<Rightarrow> ('x, 'z) binary_fun  \<Rightarrow> bool" where
  "equivariant f X Y \<phi> \<psi> = (\<forall> x \<in> X. \<forall> y \<in> Y. (\<phi> x y) \<in> Y \<longrightarrow> f (\<phi> x y) = \<psi> x (f y))"

abbreviation product_rel :: "'x rel \<Rightarrow> ('x * 'x) rel" where
  "product_rel r \<equiv> {(pair1, pair2). (fst pair1, fst pair2) \<in> r \<and> (snd pair1, snd pair2) \<in> r}"

abbreviation equivariance_rel :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x,'y) binary_fun \<Rightarrow> ('y * 'y) rel" where
  "equivariance_rel X Y \<phi> \<equiv> {((a,b), (c,d)). (a,b) \<in> Y \<times> Y \<and> (\<exists>x \<in> X. c = \<phi> x a \<and> d = \<phi> x b)}"

abbreviation uncurried_dist :: "'x Distance \<Rightarrow> ('x * 'x \<Rightarrow> ereal)" where
  "uncurried_dist d \<equiv> (\<lambda>pair. d (fst pair) (snd pair))"

abbreviation totally_invariant_dist :: "'x Distance \<Rightarrow> 'x rel \<Rightarrow> bool" where
  "totally_invariant_dist d r \<equiv> invariant (uncurried_dist d) (product_rel r)"
                       
abbreviation invariant_dist :: 
  "'y Distance \<Rightarrow> 'x set \<Rightarrow> 'y set \<Rightarrow> ('x,'y) binary_fun \<Rightarrow> bool" where
  "invariant_dist d X Y \<phi> \<equiv> invariant (uncurried_dist d) (equivariance_rel X Y \<phi>)"

subsection \<open>Well-Formedness of Relations\<close>

text \<open>
  We require that relations on elections be well-formed, i.e. they should preserve (finite) profiles 
  and the admissible results of related elections should be identical.
\<close>

definition sym_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "sym_on A r \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"

abbreviation sym :: "'a rel \<Rightarrow> bool" where "sym r \<equiv> sym_on UNIV r"

abbreviation refl_on_supset :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "refl_on_supset A r \<equiv> \<forall> a \<in> A. (a,a) \<in> r"

definition (in result) results_closed_under_rel :: "('a,'v) Election rel \<Rightarrow> bool" where
  "results_closed_under_rel r \<equiv> 
    (\<forall> (E, E') \<in> r. limit_set (alts_\<E> E) UNIV = limit_set (alts_\<E> E') UNIV)"

definition set_closed_under_rel :: "('a,'v) Election set \<Rightarrow> ('a,'v) Election rel \<Rightarrow> bool" where
  "set_closed_under_rel X r \<equiv> (\<forall> E E'. (E,E') \<in> r \<longrightarrow> E \<in> X \<longrightarrow> E' \<in> X)" 

definition rel_induced_by_action :: "'x set \<Rightarrow> ('x,'y) binary_fun \<Rightarrow> 'y set \<Rightarrow> 'y rel" where
  "rel_induced_by_action X \<phi> Y = {(y1, y2) \<in> Y \<times> Y. \<exists> x \<in> X. \<phi> x y1 = y2}"

section \<open>Auxiliary Lemmas\<close>

lemma rewrite_totally_invariant_dist [simp]:
  fixes
    d :: "'x Distance" and
    r :: "'x rel"
  shows "totally_invariant_dist d r = (\<forall> (x, y) \<in> r. \<forall> (a, b) \<in> r. d x a = d y b)"
proof (safe)
  fix 
    a :: 'x and b :: 'x and x :: 'x and y :: 'x
  assume 
    inv: "totally_invariant_dist d r" and
    "(a, b) \<in> r" and "(x, y) \<in> r"
  hence "((x,a), (y,b)) \<in> product_rel r"
    by simp
  thus "d x a = d y b" 
    using inv
    unfolding invariant_def
    by simp
next
  show "\<forall>(x, y)\<in>r. \<forall>(a, b)\<in>r. d x a = d y b \<Longrightarrow> totally_invariant_dist d r"
  proof (unfold invariant_def, safe)
    fix 
      a :: 'x  and b :: 'x and x :: 'x and y :: 'x
    assume 
      "\<forall>(x, y)\<in>r. \<forall>(a, b)\<in>r. d x a = d y b" and
      "(fst (x, a), fst (y, b)) \<in> r" and " (snd (x, a), snd (y, b)) \<in> r"
    thus "d (fst (x, a)) (snd (x, a)) = d (fst (y, b)) (snd (y, b))"
      by blast
  qed
qed

lemma rewrite_invariant_dist [simp]:
  fixes
    d :: "'y Distance" and
    X :: "'x set" and
    Y :: "'y set" and
    \<phi> :: "('x,'y) binary_fun"
  shows "invariant_dist d X Y \<phi> = (\<forall> x \<in> X. \<forall> y \<in> Y. \<forall> z \<in> Y. d y z = d (\<phi> x y) (\<phi> x z))"
proof (safe)
  fix x :: 'x and y :: 'y and z :: 'y
  assume
    "x \<in> X" and "y \<in> Y" and "z \<in> Y" and
    "invariant_dist d X Y \<phi>"
  thus "d y z = d (\<phi> x y) (\<phi> x z)"
    unfolding invariant_def
    by fastforce
next
  show "\<forall>x\<in>X. \<forall>y\<in>Y. \<forall>z\<in>Y. d y z = d (\<phi> x y) (\<phi> x z) \<Longrightarrow> invariant_dist d X Y \<phi>"
  proof (unfold invariant_def, safe)
    fix x :: 'x and a :: 'y and b :: 'y
    assume 
      "\<forall>x\<in>X. \<forall>y\<in>Y. \<forall>z\<in>Y. d y z = d (\<phi> x y) (\<phi> x z)" and 
      "x \<in> X" and "a \<in> Y" and "b \<in> Y"
    hence "d a b = d (\<phi> x a) (\<phi> x b)" 
      by blast
    thus "uncurried_dist d (a, b) = uncurried_dist d (\<phi> x a, \<phi> x b)"
      by simp
  qed
qed

lemma rel_induced_by_monoid_action_refl:
  fixes
    X :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes
    "\<phi> \<in> hom X (BijGroup Y)" and
    "monoid X"
  shows "refl_on Y (rel_induced_by_action (carrier X) \<phi> Y)"
proof (unfold rel_induced_by_action_def refl_on_def, safe)
  fix
    y :: 'y
  assume
    el: "y \<in> Y"
  interpret monoid: monoid X
    using assms
    by blast
  interpret group: group "(BijGroup Y)"
    by (simp add: group_BijGroup)
  have "\<one>\<^bsub>X\<^esub> \<in> carrier X"
    by simp
  moreover have "\<phi> \<one>\<^bsub>X\<^esub> = \<one>\<^bsub>BijGroup Y\<^esub>"
  proof -
    have "(\<phi> \<one>\<^bsub>X\<^esub>) \<otimes>\<^bsub>BijGroup Y\<^esub> \<one>\<^bsub>BijGroup Y\<^esub> = (\<phi> \<one>\<^bsub>X\<^esub>) \<otimes>\<^bsub>BijGroup Y\<^esub> (\<phi> \<one>\<^bsub>X\<^esub>)"
      using assms(1) hom_in_carrier hom_mult 
      by fastforce
    thus ?thesis
      using assms(1) hom_in_carrier 
      by fastforce
  qed
  ultimately show "\<exists> x \<in> carrier X. \<phi> x y = y"
    using el
    unfolding BijGroup_def
    by (metis monoid.select_convs(2) restrict_apply')
qed

lemma rel_induced_by_group_action_sym_refl:
  fixes
    X :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes
    "group_action X Y \<phi>"
  shows "sym_on Y (rel_induced_by_action (carrier X) \<phi> Y)" and
        "refl_on Y (rel_induced_by_action (carrier X) \<phi> Y)"
proof (unfold sym_def sym_on_def rel_induced_by_action_def, simp, safe)
  fix
    x :: 'x and y :: 'y
  assume
    grp_el: "x \<in> carrier X" and img_el: "y \<in> Y" and acts_el: "\<phi> x y \<in> Y"
  interpret act: group_action X Y \<phi>
    using assms
    by simp
  show "\<exists> x' \<in> carrier X. \<phi> x' (\<phi> x y) = y"
    using grp_el acts_el img_el
          act.group_hom assms group.inv_closed group_action.orbit_sym_aux group_hom.axioms(1)
    by meson
next
  have "monoid X"
    using assms group.is_monoid group_action.group_hom group_hom.axioms(1) 
    by blast
  moreover have "\<phi> \<in> hom X (BijGroup Y)"
    by (simp add: assms group_action.group_hom)
  ultimately show "refl_on Y {(y1, y2). (y1, y2) \<in> Y \<times> Y \<and> (\<exists>x\<in>carrier X. \<phi> x y1 = y2)}" 
    using rel_induced_by_monoid_action_refl
    unfolding rel_induced_by_action_def
    by blast   
qed

lemma invariant_subset_rel:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    X :: "'x rel" and
    Y :: "'x rel"
  assumes
    subset: "Y \<subseteq> X" and
    inv: "invariant f X"
  shows
    "invariant f Y"
  using subset inv
  unfolding invariant_def
  by blast

section \<open>Invariance\<close>

subsection \<open>Invariance under Relations\<close>

text \<open>
  If the distance of a DR decomposition is invariant under a well-formed reflexive relation,
  then the DR rule is also invariant under that relation.
  Note that this does not make any assumptions about the consensus rule.
\<close>

lemma (in result) score_invariant_under_refl_rel:
  fixes
    r :: "('a, 'v) Election rel" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    d :: "('a, 'v) Election Distance"
  assumes
    r_refl: "refl_on_supset (\<K>_els C) r" and
    inv_d: "totally_invariant_dist d r"
  shows "invariant (score d C) r"
proof (unfold invariant_def, standard, standard, standard, standard)
  fix
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election" and
    x :: 'r
  assume 
    rel: "(E,E') \<in> r"
  have "\<forall> F \<in> (\<K>_els C). (F,F) \<in> r"
    using r_refl 
    by (simp add: refl_onD)
  hence "\<forall> F \<in> (\<K>_els C). d E F = d E' F"
    using rel inv_d
    unfolding rewrite_totally_invariant_dist
    by blast
  thus "score d C E x = score d C E' x"
    unfolding score.simps
    by (meson INF_cong UnionI rangeI)
qed

lemma (in result) arg_min_set_inv_under_refl_rel:
 fixes
    r :: "('a, 'v) Election rel" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    d :: "('a, 'v) Election Distance"
  assumes
    r_refl: "refl_on_supset (\<K>_els C) r" and
    inv_d: "totally_invariant_dist d r"
  shows "invariant (\<lambda>E. arg_min_set (score d C E)) r"
proof (unfold invariant_def, standard, standard, standard, standard)
  fix
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election" and
    X :: "'r set"
  assume 
    rel: "(E,E') \<in> r"
  have "invariant (score d C) r"
    using assms
    by (rule score_invariant_under_refl_rel)
  hence "score d C E = score d C E'"
    using rel
    unfolding invariant_def
    by blast
  hence "\<forall>x. (score d C E) x = (score d C E') x"
    by presburger
  hence "\<forall>x \<in> X. is_arg_min (score d C E) (\<lambda> x. x \<in> X) x 
                  \<longleftrightarrow> is_arg_min (score d C E') (\<lambda> x. x \<in> X) x"
    by (simp add: is_arg_min_linorder)
  thus "arg_min_set (score d C E) X = arg_min_set (score d C E') X"
    unfolding arg_min_set.simps
    by (metis (mono_tags, lifting) Collect_cong is_arg_min_linorder)
qed

theorem (in result) invariant_under_refl_rel:
  fixes
    r :: "('a, 'v) Election rel" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    d :: "('a, 'v) Election Distance" and
    X :: "('a, 'v) Election set"
  assumes
    r_refl: "refl_on_supset (\<K>_els C) r" and
    r_well_formed: "results_closed_under_rel r" and
    inv_d: "totally_invariant_dist d r"
  shows "invariant (on_els (distance_\<R> d C)) r"
proof (unfold invariant_def, standard, standard, standard)
  fix 
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election"
  assume 
    rel: "(E, E') \<in> r"
  hence eq_results: "(limit_set (alts_\<E> E') UNIV) = (limit_set (alts_\<E> E) UNIV)"
    using r_well_formed 
    unfolding results_closed_under_rel_def
    by blast
  hence "arg_min_set (score d C E) (limit_set (alts_\<E> E) UNIV)
            = arg_min_set (score d C E') (limit_set (alts_\<E> E') UNIV)"
    using assms rel arg_min_set_inv_under_refl_rel[of C r d]
    unfolding invariant_def
    by presburger
  thus "on_els (distance_\<R> d C) E = on_els (distance_\<R> d C) E'"
    unfolding distance_\<R>.simps
    using eq_results
    by auto
qed

subsection \<open>Invariance under Group Actions\<close>

text \<open>
  If the distance of a DR decomposition is invariant under a group action
  then the DR rule is invariant under that equivalence relation.
  Note that this does not make any assumptions about the consensus class.
\<close>

theorem (in result) invariant_under_group_action_inv_dist:
  fixes
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    d :: "('a, 'v) Election Distance" and
    G :: "'x monoid" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    X :: "('a,'v) Election set"
  assumes        
    hom: "\<phi> \<in> hom G (BijGroup X)" and
    mon: "monoid G" and
    contains_cons_els: "(\<K>_els C) \<subseteq> X" and
    r_well_formed: "results_closed_under_rel (rel_induced_by_action (carrier G) \<phi> X)" and
    inv_d: "totally_invariant_dist d (rel_induced_by_action (carrier G) \<phi> X)"
  shows "invariant (on_els (distance_\<R> d C)) (rel_induced_by_action (carrier G) \<phi> X)"
proof (unfold invariant_def, standard, standard, standard)
  let ?r = "rel_induced_by_action (carrier G) \<phi> X"
  fix 
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election"
  assume 
    rel: "(E, E') \<in> ?r"
  have "refl_on X ?r" 
    using mon hom rel_induced_by_monoid_action_refl
    by blast
  hence "refl_on_supset (\<K>_els C) ?r"
    using contains_cons_els
    by (meson refl_onD subsetD)
  hence "invariant (on_els (distance_\<R> d C)) ?r"
    using r_well_formed inv_d invariant_under_refl_rel[of C ?r d]
    by blast
  thus "on_els (distance_\<R> d C) E = on_els (distance_\<R> d C) E'"
    unfolding invariant_def
    using rel
    by blast
qed

text \<open>
  If we add requirements for the consensus class, we can weaken the requirements for the distance:
  If the consensus rule of a DR decomposition is invariant under a group action and the distance is 
  equivariant under the same group action, then the resulting DR rule is invariant.
\<close>

abbreviation finite_election :: "('a,'v) Election \<Rightarrow> bool" where
  "finite_election E \<equiv> finite_profile (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E)"

theorem (in result) invariant_under_group_action_equiv_dist:
  fixes
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    d :: "('a, 'v) Election Distance" and
    G :: "'x monoid" and
    \<phi> :: "'x \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election"
  assumes        
    grp_act: "group_action G X \<phi>" and
    results_closed: "results_closed_under_rel (rel_induced_by_action (carrier G) \<phi> X)" and
    inv_d: "invariant_dist d (carrier G) X \<phi>" and
    closed_C: "(rel_induced_by_action (carrier G) \<phi> X) \<inter> ((\<K>_els C) \<times> X) 
                \<subseteq> (rel_induced_by_action (carrier G) \<phi> (\<K>_els C))" and
    (* closed_C could probably be weakened *)
    inv_C: 
      "invariant (elect_r \<circ> (on_els (rule_\<K> C))) (rel_induced_by_action (carrier G) \<phi> (\<K>_els C))" and
    contains_cons_els: "\<K>_els C \<subseteq> X"
  shows "invariant (on_els (distance_\<R> d C)) (rel_induced_by_action (carrier G) \<phi> X)"
proof (unfold invariant_def, standard, standard, standard)
  let ?r = "(rel_induced_by_action (carrier G) \<phi> X)"
  fix
    E :: "('a,'v) Election" and
    E' :: "('a,'v) Election"
  assume
    rel: "(E,E') \<in> ?r"
  then obtain g::'x where car: "g \<in> carrier G" and acts: "\<phi> g E = E'" 
    unfolding rel_induced_by_action_def 
    by blast
  interpret grp_act: group_action G X \<phi> by (rule grp_act)
  from rel obtain inv_g::'x where acts_inv: "inv_g \<in> carrier G \<and> \<phi> inv_g E' = E"
    unfolding rel_induced_by_action_def
    using grp_act.orbit_sym_aux acts car
          Product_Type.Collect_case_prodD SigmaD1 fst_eqD 
          group.inv_closed group_hom.axioms(1) grp_act.group_hom
    by (metis (no_types, lifting))
  have cons_sets_closed: "\<forall> x. \<forall> g \<in> carrier G. \<phi> g ` (\<K>\<^sub>\<E> C x) \<subseteq> \<K>\<^sub>\<E> C x"
  proof (safe)
    fix
      A :: "'a set" and 
      V :: "'v set" and 
      p :: "('a,'v) Profile" and
      A' :: "'a set" and 
      V' :: "'v set" and 
      p' :: "('a,'v) Profile" and
      g :: 'x and
      x :: 'r
    assume
      grp_el: "g \<in> carrier G" and 
      cons_el: "(A,V,p) \<in> \<K>\<^sub>\<E> C x" and
      rel: "(A',V',p') = \<phi> g (A,V,p)"
    hence X_el: "(A',V',p') \<in> X"
      using grp_act UnionI contains_cons_els grp_act.element_image in_mono rangeI
      by (metis (no_types, lifting))
    hence "((A,V,p), (A',V',p')) \<in> (rel_induced_by_action (carrier G) \<phi> X)"
      using rel cons_el contains_cons_els grp_el
      unfolding rel_induced_by_action_def
      by auto
    moreover have "((A,V,p), (A',V',p')) \<in> ((\<K>_els C) \<times> X)"
      using cons_el X_el
      by blast
    ultimately have cons_img: 
      "((A,V,p), (A',V',p')) \<in> (rel_induced_by_action (carrier G) \<phi> (\<K>_els C))"
      using closed_C
      by blast
    hence " elect V' (rule_\<K> C) A' p' = elect V (rule_\<K> C) A p"
      using inv_C
      unfolding invariant_def
      by simp
    also have "elect V (rule_\<K> C) A p = {x}"
      using cons_el
      unfolding \<K>\<^sub>\<E>.simps
      by simp
    finally have "elect V' (rule_\<K> C) A' p' = {x}"
      by simp
    thus "(A',V',p') \<in> \<K>\<^sub>\<E> C x"
      using cons_img
      unfolding \<K>\<^sub>\<E>.simps rel_induced_by_action_def
      by auto
  qed
  moreover have "\<forall> x. \<forall> g \<in> carrier G. \<phi> g ` (\<K>\<^sub>\<E> C x) \<supseteq> \<K>\<^sub>\<E> C x"
  proof (safe)
    fix
      A :: "'a set" and 
      V :: "'v set" and 
      p :: "('a,'v) Profile" and
      g :: 'x and
      x :: 'r                             
    assume
      grp_el: "g \<in> carrier G" and 
      cons_el: "(A,V,p) \<in> \<K>\<^sub>\<E> C x"
    hence "\<phi> (inv\<^bsub>G\<^esub> g) (A,V,p) \<in> \<K>\<^sub>\<E> C x"
      using cons_sets_closed group.subgroupE(3) group.subgroup_self 
            group_hom_def grp_act.group_hom rev_image_eqI subset_eq
      by (metis (no_types, lifting))
    moreover have "(A,V,p) = \<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) (A,V,p))"
      using UnionI cons_el contains_cons_els grp_act.bij_prop1 
            grp_act.orbit_sym_aux grp_el in_mono rangeI
      by (metis (no_types, lifting))
    ultimately show "(A,V,p) \<in> \<phi> g ` \<K>\<^sub>\<E> C x"
      by simp
  qed
  ultimately have "\<forall> x. \<forall> g \<in> carrier G. \<phi> g ` (\<K>\<^sub>\<E> C x) = \<K>\<^sub>\<E> C x"
    by blast
  moreover have "\<forall> x. d E ` \<K>\<^sub>\<E> C x = d E' ` (\<phi> g ` (\<K>\<^sub>\<E> C x))"
  proof (standard, standard, standard)
    fix 
      z :: ereal and
      x :: 'r
    assume 
      cons_dist: "z \<in> d E ` \<K>\<^sub>\<E> C x"
    then obtain F :: "('a, 'v) Election" where cons_el: "F \<in> \<K>\<^sub>\<E> C x" and dist: "d E F = z"
      by blast
    hence "F \<in> X"
      using contains_cons_els
      by auto
    hence "d E F = d E' (\<phi> g F)" 
      using car acts rel inv_d rewrite_invariant_dist[of d X "carrier G" \<phi>]
      unfolding rel_induced_by_action_def
      by auto
    thus "z \<in> d E' ` \<phi> g ` \<K>\<^sub>\<E> C x"
      using cons_el dist
      by blast
  next
    fix 
      x :: 'r
    show "d E' ` \<phi> g ` \<K>\<^sub>\<E> C x \<subseteq> d E ` \<K>\<^sub>\<E> C x"
    proof (standard)
      fix 
        z :: ereal
      assume 
        cons_img_dist: "z \<in> d E' ` \<phi> g ` \<K>\<^sub>\<E> C x"
    then obtain F :: "('a, 'v) Election" where cons_el: "F \<in> \<K>\<^sub>\<E> C x" and dist: "d E' (\<phi> g F) = z"
      by blast
    hence "F \<in> X"
      using contains_cons_els
      by auto
    hence "d E F = d E' (\<phi> g F)" 
      using car acts rel inv_d rewrite_invariant_dist[of d X "carrier G" \<phi>]
      unfolding rel_induced_by_action_def
      by auto
    thus "z \<in> d E ` \<K>\<^sub>\<E> C x"
      using cons_el dist
      by auto
    qed
  qed
  ultimately have "\<forall> r. (score d C E) r = (score d C E') r"
    using car
    unfolding score.simps
    by simp
  hence "\<forall> X. arg_min_set (score d C E) X = arg_min_set (score d C E') X"
    by presburger
  hence "\<R>\<^sub>\<W> d C (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E) = \<R>\<^sub>\<W> d C (votrs_\<E> E') (alts_\<E> E') (prof_\<E> E')"
    using results_closed rel 
    unfolding \<R>\<^sub>\<W>.simps results_closed_under_rel_def
    by fastforce
  thus "on_els (distance_\<R> d C) E = on_els (distance_\<R> d C) E'"
    using rel results_closed
    unfolding distance_\<R>.simps results_closed_under_rel_def
    by auto
qed


section \<open>Equivariance\<close>

text \<open>
  If the consensus rule and distance of a DR decomposition are equivariant under a group action, 
  then the resulting DR rule is equivariant.
\<close>

abbreviation apply_to_res :: "('r \<Rightarrow> 'r) \<Rightarrow> 'r Result \<Rightarrow> 'r Result"
  where "apply_to_res f r \<equiv> (f ` (elect_r r), f ` (reject_r r), f ` (defer_r r))"

theorem (in result) equivariant_under_group_action:
  fixes
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    d :: "('a, 'v) Election Distance" and
    G :: "'x monoid" and
    \<phi> :: "('x, ('a, 'v) Election) binary_fun" and
    \<psi> :: "('x, 'r) binary_fun" and
    X :: "('a,'v) Election set"
  assumes        
    grp_act: "group_action G X \<phi>" and
    grp_act_results: "group_action G UNIV \<psi>" and
    results_equivariant: 
      "equivariant (\<lambda>E. limit_set (alts_\<E> E) UNIV) (carrier G) X \<phi> (\<lambda>g. \<lambda>S. \<psi> g ` S)" and
    inv_d: "invariant_dist d (carrier G) X \<phi>" and
    closed_C: "(rel_induced_by_action (carrier G) \<phi> X) \<inter> ((\<K>_els C) \<times> X) 
                \<subseteq> (rel_induced_by_action (carrier G) \<phi> (\<K>_els C))" and
    (* closed_C could probably be weakened *)
    equiv_C: "equivariant (elect_r \<circ> (on_els (rule_\<K> C))) (carrier G) X \<phi> (\<lambda>g. \<lambda>S. \<psi> g ` S)" and
    contains_cons_els: "\<K>_els C \<subseteq> X"
  shows "equivariant (on_els (distance_\<R> d C)) (carrier G) X \<phi> (\<lambda>g. apply_to_res (\<psi> g))"
proof (unfold equivariant_def, standard, standard, standard)
  fix    
    E :: "('a, 'v) Election" and
    g :: 'x
  assume
    grp_el: "g \<in> carrier G" and
    el_x: "E \<in> X" and
    img_x: "\<phi> g E \<in> X"
  let ?E' = "\<phi> g E" and
      ?r = "rel_induced_by_action (carrier G) \<phi> X"
  interpret grp_act: group_action G X \<phi> by (rule grp_act)
  interpret grp_act_results: group_action G UNIV \<psi> by (rule grp_act_results)
  have inv: "E = \<phi> (inv\<^bsub>G\<^esub> g) ?E'"
    using el_x grp_act.orbit_sym_aux grp_el 
    by auto
  have grp_el_inv: "(inv\<^bsub>G\<^esub> g) \<in> carrier G"
    by (meson group.inv_closed group_hom.axioms(1) grp_act.group_hom grp_el)
  have "\<forall> r. (\<K>\<^sub>\<E> C (\<psi> g r)) \<subseteq> ((\<phi> g) ` (\<K>\<^sub>\<E> C r))"
  proof (standard, standard)
    fix 
      r :: 'r and 
      F :: "('a,'v) Election"
    assume 
      el: "F \<in> \<K>\<^sub>\<E> C (\<psi> g r)"
    obtain F' where img: "F' = \<phi> (inv\<^bsub>G\<^esub> g) F"
      by simp
    hence "F' \<in> X"
      using grp_act grp_el_inv UnionI contains_cons_els el grp_act.element_image rangeI subsetD
      by meson
    hence "(F, F') \<in> ?r \<inter> ((\<K>_els C) \<times> X)"
      using img grp_el_inv el contains_cons_els
      unfolding rel_induced_by_action_def
      by blast
    hence cons': "F' \<in> \<K>_els C"
      using closed_C SigmaD2 case_prodD in_mono mem_Collect_eq
      unfolding rel_induced_by_action_def
      by (metis (no_types, lifting))
    moreover have "elect (votrs_\<E> F) (rule_\<K> C) (alts_\<E> F) (prof_\<E> F) = {(\<psi> g r)}"
      using el
      unfolding \<K>\<^sub>\<E>.simps
      by force
    moreover have "\<psi> (inv\<^bsub>G\<^esub> g) (\<psi> g r) = r"
      using grp_act_results.group_hom
      by (simp add: grp_act_results.orbit_sym_aux grp_el)
    moreover have 
      "elect (votrs_\<E> F') (rule_\<K> C) (alts_\<E> F') (prof_\<E> F') = 
        (\<psi> (inv\<^bsub>G\<^esub> g)) ` (elect (votrs_\<E> F) (rule_\<K> C) (alts_\<E> F) (prof_\<E> F))"
      using el el_x img equiv_C grp_el_inv
      unfolding \<K>\<^sub>\<E>.simps equivariant_def comp_def
      by (meson UnionI contains_cons_els el grp_act.element_image rangeI subsetD)
    ultimately have el_r: "elect (votrs_\<E> F') (rule_\<K> C) (alts_\<E> F') (prof_\<E> F') = {r}"
      by auto
    hence eq_img: "F' \<in> \<K>\<^sub>\<E> C r"
      using cons'
      unfolding \<K>\<^sub>\<E>.simps
      by force
    have "F = \<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) F)"
      using grp_act grp_el_inv grp_el
            UnionI contains_cons_els el group.inv_inv group_hom.axioms(1) 
            grp_act.group_hom grp_act.orbit_sym_aux rangeI subset_iff
      by (metis (no_types, opaque_lifting))
    hence "F = \<phi> g F'"
      using img
      by meson
    thus "F \<in> (\<phi> g) ` (\<K>\<^sub>\<E> C r)"
      using eq_img
      by blast
  qed
  moreover have "\<forall> r. \<K>\<^sub>\<E> C (\<psi> g r) \<supseteq> (\<phi> g) ` (\<K>\<^sub>\<E> C r)"
  proof (standard, standard)
    fix 
      r :: 'r and 
      F :: "('a,'v) Election"
    assume el: "F \<in> ((\<phi> g) ` (\<K>\<^sub>\<E> C r))"
    then obtain F' where el': "F' \<in> (\<K>\<^sub>\<E> C r)" and img: "\<phi> g F' = F"
      by blast
    have el_X': "F' \<in> X"
      using contains_cons_els el' 
      by blast
    hence "(F', F) \<in> (rel_induced_by_action (carrier G) \<phi> X)"
      using img grp_el grp_act.element_image
      unfolding rel_induced_by_action_def
      by auto
    moreover have "F' \<in> \<K>_els C"
      using el'
      by blast
    moreover have el_X: "F \<in> X"
      using el_X' img grp_act.element_image grp_el 
      by blast
    ultimately have "(F', F) \<in> (rel_induced_by_action (carrier G) \<phi> X) \<inter> (\<K>_els C \<times> X)"
      by blast
    hence "(F', F) \<in> (rel_induced_by_action (carrier G) \<phi> (\<K>_els C))"
      using closed_C
      by blast
    hence cons: "F \<in> \<K>_els C"
      unfolding rel_induced_by_action_def
      by force
    moreover have "elect (votrs_\<E> F') (rule_\<K> C) (alts_\<E> F') (prof_\<E> F') = {r}"
      using el'
      unfolding \<K>\<^sub>\<E>.simps
      by force 
    ultimately have "elect (votrs_\<E> F) (rule_\<K> C) (alts_\<E> F) (prof_\<E> F) = {\<psi> g r}"
      using img grp_el equiv_C el_X el_X'
      unfolding equivariant_def
      by force
    thus "F \<in> \<K>\<^sub>\<E> C (\<psi> g r)"
      using cons
      unfolding \<K>\<^sub>\<E>.simps
      by force
  qed
  ultimately have "\<forall> r. \<K>\<^sub>\<E> C (\<psi> g r) = (\<phi> g) ` (\<K>\<^sub>\<E> C r)"
    by blast
  hence "\<forall> r. d ?E' ` \<K>\<^sub>\<E> C (\<psi> g r) = d ?E' ` (\<phi> g) ` (\<K>\<^sub>\<E> C r)"
    by presburger
  moreover have "\<forall> r. d ?E' ` (\<phi> g) ` (\<K>\<^sub>\<E> C r) \<subseteq> d E ` (\<K>\<^sub>\<E> C r)" 
  proof (standard, standard)
    fix 
      r :: 'r and 
      x :: ereal
    assume 
      el: "x \<in> d ?E' ` (\<phi> g) ` (\<K>\<^sub>\<E> C r)"
    then obtain F where "F \<in> (\<phi> g) ` \<K>\<^sub>\<E> C r" and dist: "d ?E' F = x"
      by blast
    then obtain F' where cons': "F' \<in> \<K>\<^sub>\<E> C r" and img: "\<phi> g F' = F"
      by blast
    hence el_X': "F' \<in> X"
      using contains_cons_els
      by blast
    moreover have el_X: "F \<in> X"
      using img grp_el grp_act el_X' grp_act.element_image 
      by blast 
    ultimately have "\<phi> (inv\<^bsub>G\<^esub> g) F = F'"
      using grp_act.orbit_sym_aux grp_el img 
      by blast
    hence "(F, F') \<in> (rel_induced_by_action (carrier G) \<phi> X)"
      using grp_el_inv el_X el_X'
      unfolding rel_induced_by_action_def
      by blast
    hence "d E F' = x"
      using inv_d dist img inv_d el_X' el_x grp_el 
            rewrite_invariant_dist[of d X "carrier G" \<phi>]
      by blast
    thus "x \<in> d E ` (\<K>\<^sub>\<E> C r)"
      using cons'
      by blast
  qed
  moreover have "\<forall> r. d ?E' ` (\<phi> g) ` (\<K>\<^sub>\<E> C r) \<supseteq> d E ` (\<K>\<^sub>\<E> C r)" 
  proof (standard, standard)
    fix 
      r :: 'r and 
      x :: ereal
    assume 
      "x \<in> d E ` (\<K>\<^sub>\<E> C r)"
    then obtain F' where cons': "F' \<in> \<K>\<^sub>\<E> C r" and dist: "d E F' = x"
      by blast
    then obtain F where cons_img: "F \<in> (\<phi> g) ` (\<K>\<^sub>\<E> C r)" and img: "\<phi> g F' = F"
      by blast
    have el_X': "F' \<in> X"
      using cons' contains_cons_els
      by blast
    hence el_X: "F \<in> X"
      using img grp_el grp_act grp_act.element_image 
      by blast
    hence "(F',F) \<in> (rel_induced_by_action (carrier G) \<phi> X)"
      using img el_X' grp_el
      unfolding rel_induced_by_action_def
      by blast
    hence "d ?E' F = x"
      using dist inv_d grp_el el_x el_X' img
            rewrite_invariant_dist[of d X "carrier G" \<phi>]
      by auto
    thus "x \<in> d ?E' ` (\<phi> g) ` (\<K>\<^sub>\<E> C r)"
      using cons_img
      by blast
  qed
  ultimately have "\<forall> r. Inf (d ?E' ` (\<K>\<^sub>\<E> C (\<psi> g r))) = Inf (d E ` (\<K>\<^sub>\<E> C r))"
    by (metis subset_antisym)
  hence eq_scores: "\<forall> r. score d C ?E' (\<psi> g r) = score d C E r"
    unfolding score.simps
    by blast
  have "\<forall> X. arg_min_set (score d C ?E') ((\<psi> g) ` X) = 
                (\<psi> g) ` (arg_min_set (score d C E) X)"
  proof (safe)
    fix 
      X :: "'r set" and 
      x :: 'r
    let ?inv_x = "\<psi> (inv\<^bsub>G\<^esub> g) x"
    assume el_img: "x \<in> arg_min_set (score d C ?E') (\<psi> g ` X)"
    hence "\<forall> x' \<in> (\<psi> g ` X). score d C ?E' x \<le> score d C ?E' x'"
      unfolding arg_min_set.simps
      by (simp add: is_arg_min_linorder)
    hence "\<forall> y \<in> X. score d C ?E' x \<le> score d C ?E' (\<psi> g y)"
      by blast
    hence "\<forall> y \<in> X. score d C ?E' x \<le> score d C E y"
      by (metis eq_scores)
    hence "\<forall> y \<in> X. score d C E ?inv_x \<le> score d C E y"
      using grp_el_inv grp_el eq_scores
      by (metis UNIV_I grp_act_results.orbit_sym_aux)
    moreover have "?inv_x \<in> X"
      using grp_el_inv grp_act_results el_img
      by (metis UNIV_I arg_min_subset grp_act_results.orbit_sym_aux grp_el image_iff subsetD)
    ultimately have "?inv_x \<in> (arg_min_set (score d C E) X)"
      unfolding arg_min_set.simps
      by (simp add: is_arg_min_linorder)
    moreover have "x = \<psi> g ?inv_x"
      using grp_act_results grp_el grp_el_inv
      by (metis UNIV_I grp_act_results.orbit_sym_aux)
    ultimately show "x \<in> (\<psi> g) ` (arg_min_set (score d C E) X)"
      by blast
  next
    fix 
      X :: "'r set" and 
      x :: 'r
    assume el_min: "x \<in> arg_min_set (score d C E) X"
    hence "\<forall> x' \<in> X. score d C E x \<le> score d C E x'"
      unfolding arg_min_set.simps
      by (simp add: is_arg_min_linorder)
    hence "\<forall> x' \<in> X. score d C ?E' (\<psi> g x) \<le> score d C ?E' (\<psi> g x')"
      using eq_scores
      by presburger
    hence "\<forall> y \<in> (\<psi> g ` X). score d C ?E' (\<psi> g x) \<le> score d C ?E' y"
      by blast
    moreover have "(\<psi> g x) \<in> (\<psi> g ` X)"
      using el_min
      unfolding arg_min_set.simps
      by (meson arg_min_subset el_min image_eqI subsetD)
    ultimately show "\<psi> g x \<in> arg_min_set (score d C ?E') (\<psi> g ` X)"
      unfolding arg_min_set.simps
      by (metis is_arg_min_linorder mem_Collect_eq)
  qed
  moreover have res_rel: "limit_set (alts_\<E> ?E') UNIV = (\<psi> g) ` (limit_set (alts_\<E> E) UNIV)"
    using results_equivariant grp_el el_x img_x 
    unfolding equivariant_def
    by blast
  ultimately have win_rel: "\<R>\<^sub>\<W> d C (votrs_\<E> ?E') (alts_\<E> ?E') (prof_\<E> ?E') = 
          (\<psi> g) ` (\<R>\<^sub>\<W> d C (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E))"
    by simp
  hence "limit_set (alts_\<E> ?E') UNIV - (\<R>\<^sub>\<W> d C (votrs_\<E> ?E') (alts_\<E> ?E') (prof_\<E> ?E'))
          = (\<psi> g) ` ((limit_set (alts_\<E> E) UNIV) - (\<R>\<^sub>\<W> d C (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E)))"
    using res_rel win_rel
    by (simp add: grp_act_results.inj_prop image_set_diff grp_el)
  then show "distance_\<R> d C (votrs_\<E> ?E') (alts_\<E> ?E') (prof_\<E> ?E') =
              apply_to_res (\<psi> g) (distance_\<R> d C (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E))"
    unfolding distance_\<R>.simps
    using win_rel 
    by auto
qed

end
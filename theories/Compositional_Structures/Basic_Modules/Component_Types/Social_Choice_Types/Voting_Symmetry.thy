section \<open>Symmetry Properties of Voting Rules\<close>

theory Voting_Symmetry
  imports Symmetry_Of_Functions
          Profile
          Result_Interpretations
begin

subsection \<open>Definitions\<close>

fun (in result) results_closed_under_rel :: "('a, 'v) Election rel \<Rightarrow> bool" where
  "results_closed_under_rel r = 
    (\<forall> (E, E') \<in> r. limit_set (alts_\<E> E) UNIV = limit_set (alts_\<E> E') UNIV)"

fun result_action :: "('x, 'r) binary_fun \<Rightarrow> ('x, 'r Result) binary_fun" where
  "result_action \<psi> x = (\<lambda>r. (\<psi> x ` elect_r r, \<psi> x ` reject_r r, \<psi> x ` defer_r r))"

subsubsection \<open>Anonymity\<close>

definition anonymity\<^sub>\<G> :: "('v \<Rightarrow> 'v) monoid" where
  "anonymity\<^sub>\<G> = BijGroup (UNIV::'v set)"

fun \<phi>_anon :: "('v \<Rightarrow> 'v) \<Rightarrow> (('a, 'v) Election \<Rightarrow> ('a, 'v) Election)" where
  "\<phi>_anon \<pi> = extensional_continuation (rename \<pi>) valid_elections"

fun anonymity\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "anonymity\<^sub>\<R> X = rel_induced_by_action (carrier anonymity\<^sub>\<G>) X \<phi>_anon"

subsubsection \<open>Neutrality\<close>

fun rel_rename :: "('a \<Rightarrow> 'a, 'a Preference_Relation) binary_fun" where
  "rel_rename \<pi> r = {(\<pi> a, \<pi> b) | a b. (a,b) \<in> r}"

fun alts_rename :: "('a \<Rightarrow> 'a, ('a, 'v) Election) binary_fun" where
  "alts_rename \<pi> E = (\<pi> ` (alts_\<E> E), votrs_\<E> E, (rel_rename \<pi>) \<circ> (prof_\<E> E))"

definition neutrality\<^sub>\<G> :: "('a \<Rightarrow> 'a) monoid" where
  "neutrality\<^sub>\<G> = BijGroup (UNIV::'a set)"

fun \<phi>_neutr :: "('a \<Rightarrow> 'a, ('a, 'v) Election) binary_fun" where
  "\<phi>_neutr \<pi> = extensional_continuation (alts_rename \<pi>) valid_elections"

fun neutrality\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "neutrality\<^sub>\<R> X = rel_induced_by_action (carrier neutrality\<^sub>\<G>) X \<phi>_neutr"

fun \<psi>_neutr\<^sub>\<c> :: "('a \<Rightarrow> 'a, 'a) binary_fun" where
  "\<psi>_neutr\<^sub>\<c> \<pi> r = \<pi> r"

fun \<psi>_neutr\<^sub>\<w> :: "('a \<Rightarrow> 'a, 'a rel) binary_fun" where
  "\<psi>_neutr\<^sub>\<w> \<pi> r = rel_rename \<pi> r"

subsubsection \<open>Ordered Homogeneity\<close>

fun shift_by_prod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "shift_by_prod n m x = x + n*m"

fun shift :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
  "shift X n = (shift_by_prod n (Max X + 1)) ` X"

fun copy_nat_set :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
  "copy_nat_set X n = (if X = {} then {} else \<Union> {(shift X m) | m. m \<in> {0..<n}})"

fun modulo :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "modulo m n = n mod m"

fun preimg_copy :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "preimg_copy n m new = (if (new div (m + 1) < n) then (new mod (m + 1)) else new)"

definition homogeneity\<^sub>\<M> :: "nat monoid" where
  "homogeneity\<^sub>\<M> = \<lparr>carrier = UNIV, monoid.mult = (*), one = 1\<rparr>"

fun \<phi>_homogeneity :: "(nat, ('a, nat) Election) binary_fun" where
  "\<phi>_homogeneity n E = 
    (alts_\<E> E, copy_nat_set (votrs_\<E> E) n, (prof_\<E> E) \<circ> preimg_copy n (Max (votrs_\<E> E)))"

fun homogeneity\<^sub>\<R> :: "('a, nat) Election set \<Rightarrow> ('a, nat) Election rel" where
  "homogeneity\<^sub>\<R> X = 
    rel_induced_by_action (carrier homogeneity\<^sub>\<M>) X \<phi>_homogeneity"

subsubsection \<open>Reversal Symmetry\<close>

fun rev_rel :: "'a rel \<Rightarrow> 'a rel" where
  "rev_rel r = {(a,b). (b,a) \<in> r}"

definition reversal\<^sub>\<G> :: "('a rel \<Rightarrow> 'a rel) monoid" where
  "reversal\<^sub>\<G> = \<lparr>carrier = {rev_rel, id}, monoid.mult = comp, one = id\<rparr>"

fun \<phi>_rev :: "('a rel \<Rightarrow> 'a rel, ('a, 'v) Election) binary_fun" where
  "\<phi>_rev \<phi> = 
    extensional_continuation (\<lambda>E. (alts_\<E> E, votrs_\<E> E, \<phi> \<circ> (prof_\<E> E))) valid_elections"

fun \<psi>_rev :: "('a rel \<Rightarrow> 'a rel, 'a rel) binary_fun" where
  "\<psi>_rev \<phi> r = \<phi> r"

definition reversal\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow>  ('a, 'v) Election rel" where
  "reversal\<^sub>\<R> X = rel_induced_by_action (carrier reversal\<^sub>\<G>) X \<phi>_rev"

subsection \<open>Auxiliary Lemmas\<close>

lemma bij_betw_ext:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    X :: "'x set" and
    Y :: "'y set" 
  assumes
    "bij_betw f X Y"
  shows
    "bij_betw (extensional_continuation f X) X Y"
proof -
  have "\<forall>x \<in> X. extensional_continuation f X x = f x"
    by simp
  thus ?thesis
    using assms
    by (metis bij_betw_cong)
qed

subsection \<open>Anonymity Lemmas\<close>

lemma rename_comp:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v" and \<pi>' :: "'v \<Rightarrow> 'v"
  assumes
    "bij \<pi>" and "bij \<pi>'"
  shows
    "rename \<pi> \<circ> rename \<pi>' = rename (\<pi> \<circ> \<pi>')"
proof
  fix
    E :: "('a, 'v) Election"
  have "rename \<pi>' E = (alts_\<E> E, \<pi>' ` (votrs_\<E> E), (prof_\<E> E) \<circ> (the_inv \<pi>'))"
    by (metis prod.collapse rename.simps)
  hence 
    "(rename \<pi> \<circ> rename \<pi>') E = rename \<pi> (alts_\<E> E, \<pi>' ` (votrs_\<E> E), (prof_\<E> E) \<circ> (the_inv \<pi>'))"
    unfolding comp_def
    by simp
  also have "rename \<pi> (alts_\<E> E, \<pi>' ` (votrs_\<E> E), (prof_\<E> E) \<circ> (the_inv \<pi>'))
    = (alts_\<E> E, \<pi> ` \<pi>' ` (votrs_\<E> E), (prof_\<E> E) \<circ> (the_inv \<pi>') \<circ> (the_inv \<pi>))"
    by simp
  also have "\<pi> ` \<pi>' ` (votrs_\<E> E) = (\<pi> \<circ> \<pi>') ` (votrs_\<E> E)"
    unfolding comp_def
    by auto
  also have "(prof_\<E> E) \<circ> (the_inv \<pi>') \<circ> (the_inv \<pi>) = (prof_\<E> E) \<circ> the_inv (\<pi> \<circ> \<pi>')"
    using assms the_inv_comp[of \<pi> UNIV UNIV  \<pi>' UNIV]
    by auto
  also have 
    "(alts_\<E> E, (\<pi> \<circ> \<pi>') ` (votrs_\<E> E), (prof_\<E> E) \<circ> (the_inv (\<pi> \<circ> \<pi>'))) = rename (\<pi> \<circ> \<pi>') E"
    by (metis prod.collapse rename.simps)
  finally show "(rename \<pi> \<circ> rename \<pi>') E = rename (\<pi> \<circ> \<pi>') E"
    by simp
qed

interpretation anon_grp_act:
  group_action anonymity\<^sub>\<G> valid_elections \<phi>_anon
proof (unfold group_action_def group_hom_def anonymity\<^sub>\<G>_def group_hom_axioms_def hom_def, 
        safe, (rule group_BijGroup)+)
  {
    fix
      \<pi> :: "'v \<Rightarrow> 'v"
    assume
      "\<pi> \<in> carrier (BijGroup UNIV)"
    hence bij: "bij \<pi>"
      using rewrite_carrier
      by blast
    hence "rename \<pi> ` valid_elections = valid_elections"
      using rename_surj bij
      by blast
    moreover have "inj_on (rename \<pi>) valid_elections"
      using rename_inj bij subset_inj_on 
      by blast
    ultimately have "bij_betw (rename \<pi>) valid_elections valid_elections"
      unfolding bij_betw_def
      by blast
    hence "bij_betw (\<phi>_anon \<pi>) valid_elections valid_elections"
      unfolding \<phi>_anon.simps extensional_continuation.simps
      using bij_betw_ext
      by simp
    moreover have "\<phi>_anon \<pi> \<in> extensional valid_elections"
      unfolding extensional_def
      by force
    ultimately show "\<phi>_anon \<pi> \<in> carrier (BijGroup valid_elections)"
      unfolding BijGroup_def Bij_def
      by simp
  }
  note bij_car_el =
    \<open>\<And>\<pi>. \<pi> \<in> carrier (BijGroup UNIV) \<Longrightarrow> \<phi>_anon \<pi> \<in> carrier (BijGroup valid_elections)\<close>
  fix
    \<pi> :: "'v \<Rightarrow> 'v" and \<pi>' :: "'v \<Rightarrow> 'v"
  assume
    bij: "\<pi> \<in> carrier (BijGroup UNIV)" and bij': "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence car_els: "\<phi>_anon \<pi> \<in> carrier (BijGroup valid_elections) \<and> 
                    \<phi>_anon \<pi>' \<in> carrier (BijGroup valid_elections)"
    using bij_car_el
    by metis
  hence "bij_betw (\<phi>_anon \<pi>') valid_elections valid_elections"
    unfolding BijGroup_def Bij_def extensional_def
    by auto
  hence valid_closed': "\<phi>_anon \<pi>' ` valid_elections \<subseteq> valid_elections"
    using bij_betw_imp_surj_on 
    by blast
  from car_els have
    "\<phi>_anon \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_anon \<pi>' =
      extensional_continuation (\<phi>_anon \<pi> \<circ> \<phi>_anon \<pi>') valid_elections"
    using rewrite_mult
    by blast
  moreover have
    "\<forall>E. E \<in> valid_elections \<longrightarrow> 
      extensional_continuation (\<phi>_anon \<pi> \<circ> \<phi>_anon \<pi>') valid_elections E = 
        (\<phi>_anon \<pi> \<circ> \<phi>_anon \<pi>') E"
    by simp
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> (\<phi>_anon \<pi> \<circ> \<phi>_anon \<pi>') E = rename \<pi> (rename \<pi>' E)"
    unfolding \<phi>_anon.simps
    using valid_closed'
    by auto
  moreover have "\<forall>E. E \<in> valid_elections \<longrightarrow> rename \<pi> (rename \<pi>' E) = rename (\<pi> \<circ> \<pi>') E"
    using rename_comp bij bij' Symmetry_Of_Functions.bij_car_el comp_apply
    by metis
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> rename (\<pi> \<circ> \<pi>') E = \<phi>_anon (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E"
    using rewrite_mult_univ bij bij'
    unfolding \<phi>_anon.simps
    by force
  moreover have 
    "\<forall>E. E \<notin> valid_elections \<longrightarrow> 
      extensional_continuation (\<phi>_anon \<pi> \<circ> \<phi>_anon \<pi>') valid_elections E = undefined"
    by simp
  moreover have 
    "\<forall>E. E \<notin> valid_elections \<longrightarrow> \<phi>_anon (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E = undefined"
    by simp
  ultimately have 
    "\<forall>E. \<phi>_anon (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E = (\<phi>_anon \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_anon \<pi>') E"
    by metis
  thus
    "\<phi>_anon (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') = \<phi>_anon \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_anon \<pi>'"
    by blast
qed

lemma (in result) well_formed_res_anon:
  "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance (anonymity\<^sub>\<R> valid_elections))"
proof (unfold anonymity\<^sub>\<R>.simps, simp, safe) qed

subsubsection \<open>Neutrality Lemmas\<close>

lemma rel_rename_helper:
  fixes
    r :: "'a rel" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    a :: 'a and b :: 'a
  assumes
    "bij \<pi>"
  shows
    "(\<pi> a, \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> r} \<longleftrightarrow> (a, b) \<in> {(x, y) | x y. (x, y) \<in> r}"
proof (safe, simp)
  fix
    x :: 'a and y :: 'a
  assume 
    "(x, y) \<in> r" and "\<pi> a = \<pi> x" and "\<pi> b = \<pi> y"
  hence "a = x \<and> b = y"
    using \<open>bij \<pi>\<close>
    by (metis bij_is_inj the_inv_f_f)
  thus "(a, b) \<in> r"
    using \<open>(x, y) \<in> r\<close>
    by simp
next
  fix
    x :: 'a and y :: 'a
  assume
    "(a, b) \<in> r"
  thus "\<exists>x y. (\<pi> a, \<pi> b) = (\<pi> x, \<pi> y) \<and> (x, y) \<in> r"
    by auto
qed

lemma rel_rename_comp:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    \<pi>' :: "'a \<Rightarrow> 'a" 
  shows "rel_rename (\<pi> \<circ> \<pi>') = rel_rename \<pi> \<circ> rel_rename \<pi>'"
proof
  fix 
    r :: "'a rel"
  have "rel_rename (\<pi> \<circ> \<pi>') r = {(\<pi> (\<pi>' a), \<pi> (\<pi>' b)) | a b. (a, b) \<in> r}"
    by auto
  also have
    "{(\<pi> (\<pi>' a), \<pi> (\<pi>' b)) | a b. (a, b) \<in> r} = {(\<pi> a, \<pi> b) | a b. (a, b) \<in> rel_rename \<pi>' r}"
    unfolding rel_rename.simps
    by blast
  also have
    "{(\<pi> a, \<pi> b) | a b. (a, b) \<in> rel_rename \<pi>' r} = (rel_rename \<pi> \<circ> rel_rename \<pi>') r"
    unfolding comp_def
    by simp
  finally show "rel_rename (\<pi> \<circ> \<pi>') r = (rel_rename \<pi> \<circ> rel_rename \<pi>') r"
    by simp
qed

lemma rel_rename_sound:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    r :: "'a rel" and
    A :: "'a set"
  assumes
    "bij \<pi>"
  shows
    "refl_on A r \<longrightarrow> refl_on (\<pi> ` A) (rel_rename \<pi> r)" and
    "antisym r \<longrightarrow> antisym (rel_rename \<pi> r)" and
    "total_on A r \<longrightarrow> total_on (\<pi> ` A) (rel_rename \<pi> r)" and
    "Relation.trans r \<longrightarrow> Relation.trans (rel_rename \<pi> r)"
proof (unfold antisym_def total_on_def Relation.trans_def, safe)
  assume
    "refl_on A r"
  hence "r \<subseteq> A \<times> A \<and> (\<forall>a \<in> A. (a, a) \<in> r)"
    unfolding refl_on_def
    by simp
  hence "rel_rename \<pi> r \<subseteq> (\<pi> ` A) \<times> (\<pi> ` A) \<and> (\<forall>a \<in> A. (\<pi> a, \<pi> a) \<in> rel_rename \<pi> r)"
    unfolding rel_rename.simps
    by blast
  hence "rel_rename \<pi> r \<subseteq> (\<pi> ` A) \<times> (\<pi> ` A) \<and> (\<forall>a \<in> \<pi> ` A. (a, a) \<in> rel_rename \<pi> r)"
    by fastforce
  thus "refl_on (\<pi> ` A) (rel_rename \<pi> r)"
    unfolding refl_on_def
    by simp
next
  fix
    a :: 'a and b :: 'a
  assume 
    antisym: "\<forall>a b. (a, b) \<in> r \<longrightarrow> (b, a) \<in> r \<longrightarrow> a = b" and
    "(a, b) \<in> rel_rename \<pi> r" and "(b, a) \<in> rel_rename \<pi> r"
  then obtain c :: 'a and d :: 'a and c' :: 'a and d' :: 'a where 
    "(c, d) \<in> r" and "(d', c') \<in> r" and 
    "\<pi> c = a" and "\<pi> c' = a" and "\<pi> d = b" and "\<pi> d' = b"
    unfolding rel_rename.simps
    by auto
  hence "c = c' \<and> d = d'"
    using \<open>bij \<pi>\<close>
    by (metis UNIV_I bij_betw_iff_bijections)
  hence "c = d"
    using antisym \<open>(d', c') \<in> r\<close> \<open>(c, d) \<in> r\<close>
    by simp
  thus "a = b"
    using \<open>\<pi> c = a\<close> \<open>\<pi> d = b\<close>
    by simp
next
  fix
    a :: 'a and b :: 'a
  assume
    total: "\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r" and
    "a \<in> A" and "b \<in> A" and "\<pi> a \<noteq> \<pi> b" and "(\<pi> b, \<pi> a) \<notin> rel_rename \<pi> r"
  hence "(b, a) \<notin> r \<and> a \<noteq> b"
    unfolding rel_rename.simps
    by blast
  hence "(a, b) \<in> r"
    using \<open>a \<in> A\<close> \<open>b \<in> A\<close> total
    by blast
  thus "(\<pi> a, \<pi> b) \<in> rel_rename \<pi> r"
    unfolding rel_rename.simps
    by blast
next
  fix
    a :: 'a and b :: 'a and c :: 'a
  assume
    trans: "\<forall>x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r" and
    "(a, b) \<in> rel_rename \<pi> r" and "(b, c) \<in> rel_rename \<pi> r"
  then obtain d :: 'a and e :: 'a and s :: 'a and t :: 'a where
    "(d, e) \<in> r" and "(s, t) \<in> r" and 
    "\<pi> d = a" and "\<pi> s = b" and "\<pi> t = c" and "\<pi> e = b"
    using rel_rename.simps
    by auto
  hence "s = e"
    using \<open>bij \<pi>\<close>
    by (metis bij_is_inj rangeI range_ex1_eq)
  hence "(d, e) \<in> r \<and> (e, t) \<in> r"
    using \<open>(d, e) \<in> r\<close> \<open>(s, t) \<in> r\<close> 
    by simp
  hence "(d, t) \<in> r"
    using trans
    by blast
  thus "(a, c) \<in> rel_rename \<pi> r"
    unfolding rel_rename.simps
    using \<open>\<pi> d = a\<close> \<open>\<pi> t = c\<close> 
    by blast
qed

lemma rel_rename_bij:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a"
  assumes
    "bij \<pi>"
  shows
    "bij (rel_rename \<pi>)"
proof (unfold bij_def inj_def surj_def, safe)
  {
    fix
      r :: "'a rel" and s :: "'a rel" and a :: 'a and b :: 'a
    assume
      "rel_rename \<pi> r = rel_rename \<pi> s" and "(a, b) \<in> r"
    hence "(\<pi> a, \<pi> b) \<in> {(\<pi> a, \<pi> b) | a b. (a,b) \<in> s}"
      unfolding rel_rename.simps
      by blast
    hence "\<exists>c d. (c, d) \<in> s \<and> \<pi> c = \<pi> a \<and> \<pi> d = \<pi> b"
      by fastforce
    moreover have "\<forall>c d. \<pi> c = \<pi> d \<longrightarrow> c = d"
      using \<open>bij \<pi>\<close>
      by (metis bij_pointE)
    ultimately show "(a, b) \<in> s"
      by blast
  }
  note subset =
    \<open>\<And>r s a b. rel_rename \<pi> r = rel_rename \<pi> s \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> (a, b) \<in> s\<close>
  fix
    r :: "'a rel" and s :: "'a rel" and a :: 'a and b :: 'a
  assume
    "rel_rename \<pi> r = rel_rename \<pi> s" and "(a, b) \<in> s"
  thus
    "(a, b) \<in> r"
    using subset
    by presburger
next
  fix
    r :: "'a rel"
  have 
    "rel_rename (the_inv \<pi>) r = {((the_inv \<pi>) a, (the_inv \<pi>) b) | a b. (a,b) \<in> r}"
    by simp
  also have "rel_rename \<pi> {((the_inv \<pi>) a, (the_inv \<pi>) b) | a b. (a,b) \<in> r} =
    {(\<pi> ((the_inv \<pi>) a), \<pi> ((the_inv \<pi>) b)) | a b. (a,b) \<in> r}"
    by auto
  also have "{(\<pi> ((the_inv \<pi>) a), \<pi> ((the_inv \<pi>) b)) | a b. (a,b) \<in> r} =
    {(a, b) | a b. (a,b) \<in> r}"
    using the_inv_f_f \<open>bij \<pi>\<close>
    by (simp add: f_the_inv_into_f_bij_betw)
  also have "{(a, b) | a b. (a,b) \<in> r} = r"
    by simp
  finally have "rel_rename \<pi> (rel_rename (the_inv \<pi>) r) = r"
    by simp
  thus "\<exists>s. r = rel_rename \<pi> s"
    by blast
qed
    
lemma alts_rename_comp:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and \<pi>' :: "'a \<Rightarrow> 'a"
  assumes
    "bij \<pi>" and "bij \<pi>'"
  shows
    "alts_rename \<pi> \<circ> alts_rename \<pi>' = alts_rename (\<pi> \<circ> \<pi>')"
proof
  fix
    E :: "('a, 'v) Election"
  have "(alts_rename \<pi> \<circ> alts_rename \<pi>') E = alts_rename \<pi> (alts_rename \<pi>' E)"
    by simp
  also have "alts_rename \<pi> (alts_rename \<pi>' E) = 
    alts_rename \<pi> (\<pi>' ` (alts_\<E> E), votrs_\<E> E, (rel_rename \<pi>') \<circ> (prof_\<E> E))"
    by simp
  also have "alts_rename \<pi> (\<pi>' ` (alts_\<E> E), votrs_\<E> E, (rel_rename \<pi>') \<circ> (prof_\<E> E))
    = (\<pi> ` \<pi>' ` (alts_\<E> E), votrs_\<E> E, (rel_rename \<pi>) \<circ> (rel_rename \<pi>') \<circ> (prof_\<E> E))"
    by (simp add: fun.map_comp)
  also have 
    "(\<pi> ` \<pi>' ` (alts_\<E> E), votrs_\<E> E, (rel_rename \<pi>) \<circ> (rel_rename \<pi>') \<circ> (prof_\<E> E)) = 
      ((\<pi> \<circ> \<pi>') ` (alts_\<E> E), votrs_\<E> E, (rel_rename (\<pi> \<circ> \<pi>')) \<circ> (prof_\<E> E))"
    using rel_rename_comp image_comp
    by metis
  also have 
    "((\<pi> \<circ> \<pi>') ` (alts_\<E> E), votrs_\<E> E, (rel_rename (\<pi> \<circ> \<pi>')) \<circ> (prof_\<E> E)) = 
      alts_rename (\<pi> \<circ> \<pi>') E"
    by simp
  finally show "(alts_rename \<pi> \<circ> alts_rename \<pi>') E = alts_rename (\<pi> \<circ> \<pi>') E"
    by blast
qed

lemma alts_rename_bij:
  fixes
    \<pi> :: "('a \<Rightarrow> 'a)"
  assumes 
    "bij \<pi>"
  shows 
    "bij_betw (alts_rename \<pi>) valid_elections valid_elections"
proof (unfold bij_betw_def, safe, intro inj_onI, clarsimp)
  fix
    A :: "'a set" and A' :: "'a set" and V :: "'v set" and
    p :: "('a, 'v) Profile" and p' :: "('a, 'v) Profile"
  assume
    "(A, V, p) \<in> valid_elections" and "(A', V, p') \<in> valid_elections" and
    "\<pi> ` A = \<pi> ` A'" and eq: "rel_rename \<pi> \<circ> p = rel_rename \<pi> \<circ> p'"
  hence "(the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> \<circ> p = 
    (the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> \<circ> p'"
    by (metis fun.map_comp)
  also have "(the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> = id"
    using \<open>bij \<pi>\<close> rel_rename_bij
    by (metis (no_types, opaque_lifting) bij_betw_def inv_o_cancel surj_imp_inv_eq the_inv_f_f)
  finally have "p = p'"
    by simp
  moreover have "A = A'"
    using \<open>bij \<pi>\<close> \<open>\<pi> ` A = \<pi> ` A'\<close>
    by (simp add: bij_betw_imp_inj_on inj_image_eq_iff)
  ultimately show "A = A' \<and> p = p'"
    by blast
next
  {
    fix
      A :: "'a set" and A' :: "'a set" and 
      V :: "'v set" and V' :: "'v set" and
      p :: "('a, 'v) Profile" and p' :: "('a, 'v) Profile" and
      \<pi> :: "'a \<Rightarrow> 'a"
    assume
      prof: "(A, V, p) \<in> valid_elections" and "bij \<pi>" and
      renamed: "(A', V', p') = alts_rename \<pi> (A, V, p)"
    hence rewr: "V = V' \<and> A' = \<pi> ` A"
      by simp
    hence "\<forall>v \<in> V'. linear_order_on A (p v)"
      using prof
      unfolding valid_elections_def profile_def
      by simp
    moreover have "\<forall>v \<in> V'. p' v = rel_rename \<pi> (p v)"
      using renamed
      by simp
    ultimately have "\<forall>v \<in> V'. linear_order_on A' (p' v)"
      unfolding linear_order_on_def partial_order_on_def preorder_on_def
      using rewr rel_rename_sound[of \<pi>] \<open>bij \<pi>\<close> 
      by auto
    hence "(A', V', p') \<in> valid_elections"
      unfolding valid_elections_def profile_def
      by simp
  }
  note valid_els_closed =
    \<open>\<And> A A' V V' p p' \<pi>. (A, V, p) \<in> valid_elections \<Longrightarrow> 
      bij \<pi> \<Longrightarrow> (A', V', p') = alts_rename \<pi> (A, V, p) \<Longrightarrow>
        (A', V', p') \<in> valid_elections\<close>
  thus "\<And>a aa b ab ac ba.
          (a, aa, b) = alts_rename \<pi> (ab, ac, ba) \<Longrightarrow>
            (ab, ac, ba) \<in> valid_elections \<Longrightarrow> (a, aa, b) \<in> valid_elections"
    using \<open>bij \<pi>\<close>
    by blast
  fix
    A :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile"
  assume
    prof: "(A, V, p) \<in> valid_elections"
  have 
    "alts_rename (the_inv \<pi>) (A, V, p) = ((the_inv \<pi>) ` A, V, rel_rename (the_inv \<pi>) \<circ> p)"
    by simp
  also have 
    "alts_rename \<pi> ((the_inv \<pi>) ` A, V, rel_rename (the_inv \<pi>) \<circ> p) =
      (\<pi> ` (the_inv \<pi>) ` A, V, rel_rename \<pi> \<circ> rel_rename (the_inv \<pi>) \<circ> p)"
    by auto
  also have
    "(\<pi> ` (the_inv \<pi>) ` A, V, rel_rename \<pi> \<circ> rel_rename (the_inv \<pi>) \<circ> p) 
      = (A, V, rel_rename (\<pi> \<circ> the_inv \<pi>) \<circ> p)"
    using \<open>bij \<pi>\<close> rel_rename_comp[of \<pi> "the_inv \<pi>"] the_inv_f_f
    by (simp add: bij_betw_imp_surj_on bij_is_inj f_the_inv_into_f image_comp)
  also have "(A, V, rel_rename (\<pi> \<circ> the_inv \<pi>) \<circ> p) = (A, V, rel_rename id \<circ> p)"
    by (metis UNIV_I assms comp_apply f_the_inv_into_f_bij_betw id_apply)
  also have "rel_rename id \<circ> p = p"
    unfolding rel_rename.simps
    by auto
  finally have "alts_rename \<pi> (alts_rename (the_inv \<pi>) (A, V, p)) = (A, V, p)"
    by simp
  moreover have "alts_rename (the_inv \<pi>) (A, V, p) \<in> valid_elections"
    using valid_els_closed[of A V p "the_inv \<pi>"] \<open>bij \<pi>\<close>
    by (simp add: bij_betw_the_inv_into prof)
  ultimately show "(A, V, p) \<in> alts_rename \<pi> ` valid_elections"
    by (metis image_eqI)
qed

interpretation \<phi>_neutr_act: 
  group_action neutrality\<^sub>\<G> valid_elections \<phi>_neutr
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def neutrality\<^sub>\<G>_def, 
        safe, (rule group_BijGroup)+)
  {
    fix
      \<pi> :: "'a \<Rightarrow> 'a"
    assume
      "\<pi> \<in> carrier (BijGroup UNIV)"
    hence "bij \<pi>"
      using bij_car_el 
      by blast
    hence "bij_betw (alts_rename \<pi>) valid_elections valid_elections"
      using alts_rename_bij
      by blast
    hence "bij_betw (\<phi>_neutr \<pi>) valid_elections valid_elections"
      unfolding \<phi>_neutr.simps 
      using bij_betw_ext 
      by blast
    thus "\<phi>_neutr \<pi> \<in> carrier (BijGroup valid_elections)"
      unfolding \<phi>_neutr.simps BijGroup_def Bij_def extensional_def
      by simp
  }
  note bij_car_el =
    \<open>\<And>\<pi>. \<pi> \<in> carrier (BijGroup UNIV) \<Longrightarrow> \<phi>_neutr \<pi> \<in> carrier (BijGroup valid_elections)\<close>
  fix
      \<pi> :: "'a \<Rightarrow> 'a" and \<pi>' :: "'a \<Rightarrow> 'a"
  assume
    bij: "\<pi> \<in> carrier (BijGroup UNIV)" and bij': "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence car_els: "\<phi>_neutr \<pi> \<in> carrier (BijGroup valid_elections) \<and> 
                    \<phi>_neutr \<pi>' \<in> carrier (BijGroup valid_elections)"
    using bij_car_el
    by metis
  hence "bij_betw (\<phi>_neutr \<pi>') valid_elections valid_elections"
    unfolding BijGroup_def Bij_def extensional_def
    by auto
  hence valid_closed': "\<phi>_neutr \<pi>' ` valid_elections \<subseteq> valid_elections"
    using bij_betw_imp_surj_on 
    by blast
  from car_els have "\<phi>_neutr \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr \<pi>' = 
    extensional_continuation (\<phi>_neutr \<pi> \<circ> \<phi>_neutr \<pi>') valid_elections"
    using rewrite_mult
    by auto
  moreover have
    "\<forall>E. E \<in> valid_elections \<longrightarrow> 
      extensional_continuation (\<phi>_neutr \<pi> \<circ> \<phi>_neutr \<pi>') valid_elections E = 
        (\<phi>_neutr \<pi> \<circ> \<phi>_neutr \<pi>') E"
    by simp
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> (\<phi>_neutr \<pi> \<circ> \<phi>_neutr \<pi>') E = alts_rename \<pi> (alts_rename \<pi>' E)"
    unfolding \<phi>_neutr.simps
    using valid_closed'
    by auto
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> alts_rename \<pi> (alts_rename \<pi>' E) = alts_rename (\<pi> \<circ> \<pi>') E"
    using alts_rename_comp bij bij' Symmetry_Of_Functions.bij_car_el comp_apply
    by metis
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> alts_rename (\<pi> \<circ> \<pi>') E = \<phi>_neutr (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E"
    using rewrite_mult_univ bij bij'
    unfolding \<phi>_anon.simps
    by force
  moreover have 
    "\<forall>E. E \<notin> valid_elections \<longrightarrow> 
      extensional_continuation (\<phi>_neutr \<pi> \<circ> \<phi>_neutr \<pi>') valid_elections E = undefined"
    by simp
  moreover have 
    "\<forall>E. E \<notin> valid_elections \<longrightarrow> \<phi>_neutr (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E = undefined"
    by simp
  ultimately have 
    "\<forall>E. \<phi>_neutr (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E = (\<phi>_neutr \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr \<pi>') E"
    by metis
  thus
    "\<phi>_neutr (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') = \<phi>_neutr \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr \<pi>'"
    by blast
qed

interpretation \<psi>_neutr\<^sub>\<c>_act:
  group_action neutrality\<^sub>\<G> UNIV \<psi>_neutr\<^sub>\<c>
proof (unfold group_action_def group_hom_def hom_def neutrality\<^sub>\<G>_def group_hom_axioms_def, 
        safe, (rule group_BijGroup)+)
  {
    fix
      \<pi> :: "'a \<Rightarrow> 'a"
    assume
      "\<pi> \<in> carrier (BijGroup UNIV)"
    hence "bij \<pi>"
      unfolding BijGroup_def Bij_def
      by simp
    hence "bij (\<psi>_neutr\<^sub>\<c> \<pi>)"
      unfolding \<psi>_neutr\<^sub>\<c>.simps
      by simp
    thus "\<psi>_neutr\<^sub>\<c> \<pi> \<in> carrier (BijGroup UNIV)"
      using rewrite_carrier
      by blast
  }
  fix
    \<pi> :: "'a \<Rightarrow> 'a" and \<pi>' :: "'a \<Rightarrow> 'a"
  assume
    "\<pi> \<in> carrier (BijGroup UNIV)" and "\<pi>' \<in> carrier (BijGroup UNIV)"
  show "\<psi>_neutr\<^sub>\<c> (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') =
           \<psi>_neutr\<^sub>\<c> \<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<psi>_neutr\<^sub>\<c> \<pi>'"
    unfolding \<psi>_neutr\<^sub>\<c>.simps
    by simp
qed

interpretation \<psi>_neutr\<^sub>\<w>_act:
  group_action neutrality\<^sub>\<G> UNIV \<psi>_neutr\<^sub>\<w>
proof (unfold group_action_def group_hom_def hom_def neutrality\<^sub>\<G>_def group_hom_axioms_def, 
        safe, (rule group_BijGroup)+)
  {
    fix
      \<pi> :: "'a \<Rightarrow> 'a"
    assume
      "\<pi> \<in> carrier (BijGroup UNIV)"
    hence "bij \<pi>"
      unfolding neutrality\<^sub>\<G>_def BijGroup_def Bij_def
      by simp
    hence "bij (\<psi>_neutr\<^sub>\<w> \<pi>)"
      unfolding \<psi>_neutr\<^sub>\<w>.simps
      using rel_rename_bij
      by blast
    thus "\<psi>_neutr\<^sub>\<w> \<pi> \<in> carrier (BijGroup UNIV)"
      using rewrite_carrier
      by blast
  }
  note grp_el =
    \<open>\<And>\<pi>. \<pi> \<in> carrier (BijGroup UNIV) \<Longrightarrow> \<psi>_neutr\<^sub>\<w> \<pi> \<in> carrier (BijGroup UNIV)\<close>
  fix
    \<pi> :: "'a \<Rightarrow> 'a" and \<pi>' :: "'a \<Rightarrow> 'a"
  assume
    bij: "\<pi> \<in> carrier (BijGroup UNIV)" and bij': "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence "\<psi>_neutr\<^sub>\<w> \<pi> \<in> carrier (BijGroup UNIV) \<and>
          \<psi>_neutr\<^sub>\<w> \<pi>' \<in> carrier (BijGroup UNIV)"
    using grp_el
    by blast
  thus "\<psi>_neutr\<^sub>\<w> (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') =
           \<psi>_neutr\<^sub>\<w> \<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<psi>_neutr\<^sub>\<w> \<pi>'"
    unfolding \<psi>_neutr\<^sub>\<w>.simps
    using rel_rename_comp[of \<pi> \<pi>'] rewrite_mult_univ bij bij'
    by metis
qed

lemma wf_res_neutr_soc_choice:
  "satisfies (\<lambda>E. limit_set_soc_choice (alts_\<E> E) UNIV) 
            (equivar_ind_by_act (carrier neutrality\<^sub>\<G>) valid_elections 
                                \<phi>_neutr (set_action \<psi>_neutr\<^sub>\<c>))"
proof (simp del: limit_set_soc_choice.simps \<phi>_neutr.simps \<psi>_neutr\<^sub>\<w>.simps 
            add: rewrite_equivar_ind_by_act, safe, auto) qed

lemma wf_res_neutr_soc_welfare:
  "satisfies (\<lambda>E. limit_set_welfare (alts_\<E> E) UNIV) 
            (equivar_ind_by_act (carrier neutrality\<^sub>\<G>) valid_elections 
                                \<phi>_neutr (set_action \<psi>_neutr\<^sub>\<w>))"
proof (simp del: limit_set_welfare.simps \<phi>_neutr.simps \<psi>_neutr\<^sub>\<w>.simps 
            add: rewrite_equivar_ind_by_act, safe)
  {
    fix
      \<pi> :: "'a \<Rightarrow> 'a" and
      A :: "'a set" and
      V :: "'v set" and
      p :: "('a, 'v) Profile" and
      r :: "'a rel"
    let ?r_inv = "\<psi>_neutr\<^sub>\<w> (the_inv \<pi>) r"
    assume  
      "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
      prof: "(A, V, p) \<in> valid_elections" and
      "\<phi>_neutr \<pi> (A, V, p) \<in> valid_elections" and
      lim_el: "r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr \<pi> (A, V, p))) UNIV"
    hence "the_inv \<pi> \<in> carrier neutrality\<^sub>\<G>"
      unfolding neutrality\<^sub>\<G>_def
      by (simp add: bij_betw_the_inv_into rewrite_carrier)
    moreover have "the_inv \<pi> \<circ> \<pi> = id"
      using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close> bij_car_el[of \<pi>] bij_is_inj the_inv_f_f 
      unfolding neutrality\<^sub>\<G>_def
      by fastforce
    moreover have "\<one>\<^bsub>neutrality\<^sub>\<G>\<^esub> = id"
      unfolding neutrality\<^sub>\<G>_def BijGroup_def
      by auto
    ultimately have "the_inv \<pi> \<otimes>\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> = \<one>\<^bsub>neutrality\<^sub>\<G>\<^esub>"
      using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close>
      unfolding neutrality\<^sub>\<G>_def
      using rewrite_mult_univ[of "the_inv \<pi>" \<pi>]
      by metis
    hence "inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> = the_inv \<pi>"
      using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close> \<open>the_inv \<pi> \<in> carrier neutrality\<^sub>\<G>\<close>
            \<psi>_neutr\<^sub>\<c>_act.group_hom group.inv_closed group.inv_solve_right 
            group.l_inv group_BijGroup group_hom.hom_one group_hom.one_closed neutrality\<^sub>\<G>_def
      by metis
    have "r \<in> limit_set_welfare (\<pi> ` A) UNIV"
      unfolding \<phi>_neutr.simps
      using prof lim_el
      by simp
    hence lin: "linear_order_on (\<pi> ` A) r"
      by auto
    have bij_inv: "bij (the_inv \<pi>)"
      using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close> bij_betw_the_inv_into bij_car_el
      unfolding neutrality\<^sub>\<G>_def
      by blast
    hence "(the_inv \<pi>) ` \<pi> ` A = A"
      using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close>
      unfolding neutrality\<^sub>\<G>_def
      by (metis UNIV_I bij_betw_imp_surj bij_car_el
                f_the_inv_into_f_bij_betw image_f_inv_f surj_imp_inv_eq)
    hence lin_inv: "linear_order_on A ?r_inv"
      using rel_rename_sound[of "the_inv \<pi>"] bij_inv lin
      unfolding \<psi>_neutr\<^sub>\<w>.simps linear_order_on_def preorder_on_def partial_order_on_def
      by metis
    hence "\<forall>a b. (a, b) \<in> ?r_inv \<longrightarrow> a \<in> A \<and> b \<in> A"
      using linear_order_on_def partial_order_onD(1) refl_on_def 
      by blast
    hence "limit A ?r_inv = {(a, b). (a, b) \<in> ?r_inv}"
      by auto
    also have "{(a, b). (a, b) \<in> ?r_inv} = ?r_inv"
      by blast
    finally have "?r_inv = limit A ?r_inv"
      by blast
    hence "?r_inv \<in> limit_set_welfare (alts_\<E> (A, V, p)) UNIV"
      unfolding limit_set_welfare.simps 
      using lin_inv
      by (metis (mono_tags, lifting) UNIV_I fst_conv mem_Collect_eq)
    moreover have "r = \<psi>_neutr\<^sub>\<w> \<pi> ?r_inv"
      using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close> \<open>inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> = the_inv \<pi>\<close> 
            \<open>the_inv \<pi> \<in> carrier neutrality\<^sub>\<G>\<close> iso_tuple_UNIV_I
            \<psi>_neutr\<^sub>\<w>_act.orbit_sym_aux
      by metis
    ultimately show
      "r \<in> \<psi>_neutr\<^sub>\<w> \<pi> ` limit_set_welfare (alts_\<E> (A, V, p)) UNIV"
      by blast
  }
  note lim_el_\<pi> =
    \<open>\<And>\<pi> A V p r. \<pi> \<in> carrier neutrality\<^sub>\<G> \<Longrightarrow> (A, V, p) \<in> valid_elections \<Longrightarrow>
        \<phi>_neutr \<pi> (A, V, p) \<in> valid_elections \<Longrightarrow>
        r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr \<pi> (A, V, p))) UNIV \<Longrightarrow>
        r \<in> \<psi>_neutr\<^sub>\<w> \<pi> ` limit_set_welfare (alts_\<E> (A, V, p)) UNIV\<close>
  fix
    \<pi> :: "'a \<Rightarrow> 'a" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    r :: "'a rel"
  let ?r_inv = "\<psi>_neutr\<^sub>\<w> (the_inv \<pi>) r"
  assume  
    "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    prof: "(A, V, p) \<in> valid_elections" and
    prof_\<pi>: "\<phi>_neutr \<pi> (A, V, p) \<in> valid_elections" and
    "r \<in> limit_set_welfare (alts_\<E> (A, V, p)) UNIV"
  hence 
    "r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr (inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>) (\<phi>_neutr \<pi> (A, V, p)))) UNIV"
    by (metis \<phi>_neutr_act.orbit_sym_aux)
  moreover have inv_grp_el: "inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> \<in> carrier neutrality\<^sub>\<G>"
    using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close> \<psi>_neutr\<^sub>\<c>_act.group_hom 
          group.inv_closed group_hom_def
    by meson
  moreover have "\<phi>_neutr (inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>) (\<phi>_neutr \<pi> (A, V, p)) \<in> valid_elections"
    using prof \<phi>_neutr_act.element_image inv_grp_el prof_\<pi> 
    by blast
  ultimately have
    "r \<in> \<psi>_neutr\<^sub>\<w> (inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>) ` 
            limit_set_welfare (alts_\<E> (\<phi>_neutr \<pi> (A, V, p))) UNIV"
    using prof_\<pi> lim_el_\<pi>
    by (metis prod.collapse)
  thus
    "\<psi>_neutr\<^sub>\<w> \<pi> r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr \<pi> (A, V, p))) UNIV"
    using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close> \<psi>_neutr\<^sub>\<w>_act.group_action_axioms 
          \<psi>_neutr\<^sub>\<w>_act.inj_prop group_action.orbit_sym_aux 
          inj_image_mem_iff inv_grp_el iso_tuple_UNIV_I
    by (metis (no_types, lifting))
qed

subsection \<open>Homogeneity Lemmas\<close>

lemma copy_nat_set_card:
  fixes
    n :: nat and
    X :: "nat set"
  assumes
    "finite X"
  shows
    "card (copy_nat_set X n) = n * (card X)"
proof (cases "X = {}")
  case True
  hence "copy_nat_set X n = {}"
    by simp
  thus ?thesis
    by (simp add: True)
next
  case False
  have "\<And>a b. a > b \<Longrightarrow> (shift X a \<inter> shift X b = {})"
  proof (unfold shift.simps, safe)
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
    unfolding copy_nat_set.simps shift_def
    using assms(1)
    by (simp add: setcompr_eq_image)
  moreover have "\<forall>a \<in> {(shift X m) | m. m \<in> {0..<n}}. card a = card X"
    sorry
  moreover have "copy_nat_set X n = \<Union> {(shift X m) | m. m \<in> {0..<n}}"
    using False
    by simp
  ultimately have eq: "card X * card {(shift X m) | m. m \<in> {0..<n}} = card (copy_nat_set X n)"
    using card_partition[of "{(shift X m) | m. m \<in> {0..<n}}" "card X"]
    unfolding copy_nat_set.simps
    by auto 
  also have "card {(shift X m) | m. m \<in> {0..<n}} = n"
    sorry
  finally have "card X * n = card (copy_nat_set X n)"
    by simp
  thus "card (copy_nat_set X n) = n * card X"
    by (simp add: mult.commute)   
qed

lemma refl_homogeneity\<^sub>\<R>:
  "refl_on finite_elections (homogeneity\<^sub>\<R> finite_elections)"
proof (unfold refl_on_def finite_elections_def valid_elections_def homogeneity\<^sub>\<R>.simps 
              rel_induced_by_action.simps, safe)
  fix
    A :: "'a set" and
    V :: "nat set" and
    p :: "('a, nat) Profile"
  assume
    fin_V: "finite (votrs_\<E> (A, V, p)) " and
    "profile (votrs_\<E> (A, V, p)) (alts_\<E> (A, V, p)) (prof_\<E> (A, V, p))"
  have "\<forall>n \<in> V. modulo (Max (votrs_\<E> (A, V, p)) + 1) n = n"
    unfolding modulo.simps
    using fin_V less_Suc_eq_le
    by auto
  moreover have "\<forall>n. n \<notin> V \<longrightarrow> preimg_copy 1 (Max V) n = n"
    unfolding preimg_copy.simps
    by (simp add: mod_eq_self_iff_div_eq_0)
  ultimately have 
    "\<forall>n. (prof_\<E> (A, V, p) \<circ> preimg_copy 1 (Max (votrs_\<E> (A, V, p)))) n = p n"
    by (metis comp_apply less_one mod_eq_self_iff_div_eq_0 preimg_copy.simps snd_conv)
  moreover have "copy_nat_set (votrs_\<E> (A, V, p)) 1 = V"
    by simp
  ultimately have "\<phi>_homogeneity 1 (A, V, p) = (A, V, p)"
    unfolding \<phi>_homogeneity.simps
    by auto
  moreover have "1 \<in> carrier homogeneity\<^sub>\<M>"
    by (simp add: homogeneity\<^sub>\<M>_def)
  ultimately show "\<exists>x\<in>carrier homogeneity\<^sub>\<M>. \<phi>_homogeneity x (A, V, p) = (A, V, p)"
    by blast
qed

lemma (in result) well_formed_res_homogeneity: 
  "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance (homogeneity\<^sub>\<R> finite_elections))"
  unfolding homogeneity\<^sub>\<R>.simps
  using rewrite_invar_ind_by_act
  by simp

subsubsection \<open>Reversal Symmetry Lemmas\<close>

subsubsection \<open>Auxiliary Lemmas\<close>

lemma rev_rev_id:
  "rev_rel \<circ> rev_rel = id"
  by auto

lemma bij_rev:
  "bij rev_rel"
  unfolding bij_def inj_def
  by auto

interpretation reversal\<^sub>\<G>_group: group reversal\<^sub>\<G>
proof
  show "\<one>\<^bsub>reversal\<^sub>\<G>\<^esub> \<in> carrier reversal\<^sub>\<G>"
    unfolding reversal\<^sub>\<G>_def
    by simp
next
  show "carrier reversal\<^sub>\<G> \<subseteq> Units reversal\<^sub>\<G>"
    unfolding reversal\<^sub>\<G>_def Units_def
    using rev_rev_id
    by auto
next
  fix
    x :: "'a rel \<Rightarrow> 'a rel"
  assume
    x_el: "x \<in> carrier reversal\<^sub>\<G>"
  thus
    "\<one>\<^bsub>reversal\<^sub>\<G>\<^esub> \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> x = x"
    unfolding reversal\<^sub>\<G>_def
    by auto
  show 
    "x \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> \<one>\<^bsub>reversal\<^sub>\<G>\<^esub> = x"
    unfolding reversal\<^sub>\<G>_def
    by auto
  fix
    y :: "'a rel \<Rightarrow> 'a rel"
  assume
    y_el: "y \<in> carrier reversal\<^sub>\<G>"
  thus "x \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> y \<in> carrier reversal\<^sub>\<G>"
    using x_el rev_rev_id
    unfolding reversal\<^sub>\<G>_def
    by auto
  fix
    z :: "'a rel \<Rightarrow> 'a rel"
  assume
    z_el: "z \<in> carrier reversal\<^sub>\<G>"
  thus 
    "x \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> y \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> z = x \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> (y \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> z)"
    using x_el y_el
    unfolding reversal\<^sub>\<G>_def
    by auto
qed

lemma \<phi>_rev_\<phi>_rev_id:
  "\<And>x. x \<in> carrier reversal\<^sub>\<G> \<Longrightarrow> 
    (\<phi>_rev x) \<circ> (\<phi>_rev x) = extensional_continuation id valid_elections"
  sorry

interpretation \<phi>_rev_act:
  group_action reversal\<^sub>\<G> valid_elections \<phi>_rev
  sorry

interpretation \<psi>_rev_act: 
  group_action reversal\<^sub>\<G> UNIV \<psi>_rev
  sorry

lemma \<phi>_\<psi>_rev_well_formed:
  defines "equivar_prop_global_set_valued \<equiv> 
    equivar_ind_by_act (carrier reversal\<^sub>\<G>) valid_elections \<phi>_rev (\<lambda>g. image (\<psi>_rev g))"
  shows 
    "satisfies (\<lambda>E. limit_set_welfare (alts_\<E> E) UNIV) equivar_prop_global_set_valued"
  sorry

end
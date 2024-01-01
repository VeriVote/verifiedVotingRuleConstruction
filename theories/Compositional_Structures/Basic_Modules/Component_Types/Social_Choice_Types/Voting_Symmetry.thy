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

fun \<phi>_anon :: 
  "('a, 'v) Election set \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> (('a, 'v) Election \<Rightarrow> ('a, 'v) Election)" where
  "\<phi>_anon X \<pi> = extensional_continuation (rename \<pi>) X"

fun anonymity\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "anonymity\<^sub>\<R> X = rel_induced_by_action (carrier anonymity\<^sub>\<G>) X (\<phi>_anon X)"

subsubsection \<open>Neutrality\<close>

fun rel_rename :: "('a \<Rightarrow> 'a, 'a Preference_Relation) binary_fun" where
  "rel_rename \<pi> r = {(\<pi> a, \<pi> b) | a b. (a,b) \<in> r}"

fun alts_rename :: "('a \<Rightarrow> 'a, ('a, 'v) Election) binary_fun" where
  "alts_rename \<pi> E = (\<pi> ` (alts_\<E> E), votrs_\<E> E, (rel_rename \<pi>) \<circ> (prof_\<E> E))"

definition neutrality\<^sub>\<G> :: "('a \<Rightarrow> 'a) monoid" where
  "neutrality\<^sub>\<G> = BijGroup (UNIV::'a set)"

fun \<phi>_neutr :: "('a, 'v) Election set \<Rightarrow> ('a \<Rightarrow> 'a, ('a, 'v) Election) binary_fun" where
  "\<phi>_neutr X \<pi> = extensional_continuation (alts_rename \<pi>) X"

fun neutrality\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "neutrality\<^sub>\<R> X = rel_induced_by_action (carrier neutrality\<^sub>\<G>) X (\<phi>_neutr X)"

fun \<psi>_neutr\<^sub>\<c> :: "('a \<Rightarrow> 'a, 'a) binary_fun" where
  "\<psi>_neutr\<^sub>\<c> \<pi> r = \<pi> r"

fun \<psi>_neutr\<^sub>\<w> :: "('a \<Rightarrow> 'a, 'a rel) binary_fun" where
  "\<psi>_neutr\<^sub>\<w> \<pi> r = rel_rename \<pi> r"

subsubsection \<open>Homogeneity\<close>

fun homogeneity\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "homogeneity\<^sub>\<R> X = 
    {(E, E') \<in> X \<times> X. 
        alts_\<E> E = alts_\<E> E' \<and> finite (votrs_\<E> E) \<and> finite (votrs_\<E> E') \<and> 
        (\<exists>n > 0. \<forall>r::('a Preference_Relation). vote_count r E = n * (vote_count r E'))}"

fun copy_list :: "nat \<Rightarrow> 'x list \<Rightarrow> 'x list" where
  "copy_list 0 l = []" |
  "copy_list (Suc n) l = copy_list n l @ l"

fun homogeneity\<^sub>\<R>' :: "('a, 'v::linorder) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "homogeneity\<^sub>\<R>' X = 
    {(E, E') \<in> X \<times> X. alts_\<E> E = alts_\<E> E' \<and> finite (votrs_\<E> E) \<and> finite (votrs_\<E> E') \<and>
      (\<exists>n > 0. to_list (votrs_\<E> E') (prof_\<E> E') = copy_list n (to_list (votrs_\<E> E) (prof_\<E> E)))}"

subsubsection \<open>Reversal Symmetry\<close>

fun rev_rel :: "'a rel \<Rightarrow> 'a rel" where
  "rev_rel r = {(a,b). (b,a) \<in> r}"

fun rel_app :: "('a rel \<Rightarrow> 'a rel) \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "rel_app f (A, V, p) = (A, V, f \<circ> p)"

definition reversal\<^sub>\<G> :: "('a rel \<Rightarrow> 'a rel) monoid" where
  "reversal\<^sub>\<G> = \<lparr>carrier = {rev_rel, id}, monoid.mult = comp, one = id\<rparr>"

fun \<phi>_rev :: "('a, 'v) Election set \<Rightarrow> ('a rel \<Rightarrow> 'a rel, ('a, 'v) Election) binary_fun" where
  "\<phi>_rev X \<phi> = 
    extensional_continuation (rel_app \<phi>) X"

fun \<psi>_rev :: "('a rel \<Rightarrow> 'a rel, 'a rel) binary_fun" where
  "\<psi>_rev \<phi> r = \<phi> r"

definition reversal\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow>  ('a, 'v) Election rel" where
  "reversal\<^sub>\<R> X = rel_induced_by_action (carrier reversal\<^sub>\<G>) X (\<phi>_rev X)"

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

lemma anon_rel_vote_count:
  fixes
    X :: "('a, 'v) Election set" and
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election"
  assumes
    "finite (votrs_\<E> E)" and
    "(E, E') \<in> anonymity\<^sub>\<R> X"
  shows
    "alts_\<E> E = alts_\<E> E' \<and> (E, E') \<in> X \<times> X \<and> (\<forall>p. vote_count p E = vote_count p E')"
proof -
  from assms have rel': "(E, E') \<in> X \<times> X"
    unfolding anonymity\<^sub>\<R>.simps rel_induced_by_action.simps
    by blast
  hence "E \<in> X"
    by simp
  with assms obtain \<pi> :: "'v \<Rightarrow> 'v" where "bij \<pi>" and 
    renamed: "E' = rename \<pi> E"
    unfolding anonymity\<^sub>\<R>.simps rel_induced_by_action.simps anonymity\<^sub>\<G>_def \<phi>_anon.simps
              extensional_continuation.simps
    using bij_car_el 
    by auto
  hence eq_alts: "alts_\<E> E' = alts_\<E> E"
    by (metis eq_fst_iff rename.simps)
  from renamed have 
    "\<forall>v \<in> (votrs_\<E> E'). (prof_\<E> E') v = (prof_\<E> E) (the_inv \<pi> v)"
    using rename.simps
    by (metis (no_types, lifting) comp_apply prod.collapse snd_conv)
  hence rewrite:
    "\<forall>p. {v \<in> (votrs_\<E> E'). (prof_\<E> E') v = p} = {v \<in> (votrs_\<E> E'). (prof_\<E> E) (the_inv \<pi> v) = p}"
    by blast
  from renamed have 
    "\<forall>v \<in> votrs_\<E> E'. the_inv \<pi> v \<in> votrs_\<E> E"
    using UNIV_I \<open>bij \<pi>\<close> bij_betw_imp_surj bij_is_inj f_the_inv_into_f 
          fst_conv inj_image_mem_iff prod.collapse rename.simps snd_conv
    by (metis (mono_tags, lifting))
  hence
    "\<forall>p. \<forall>v \<in> votrs_\<E> E'. (prof_\<E> E) (the_inv \<pi> v) = p \<longrightarrow> 
      v \<in> \<pi> ` {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p}"
    using \<open>bij \<pi>\<close> f_the_inv_into_f_bij_betw image_iff 
    by fastforce
  hence subset:
    "\<forall>p. {v \<in> (votrs_\<E> E'). (prof_\<E> E) (the_inv \<pi> v) = p} \<subseteq>
          \<pi> ` {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p}"
    by blast
  from renamed have 
    "\<forall>v \<in> votrs_\<E> E. \<pi> v \<in> votrs_\<E> E'"
    using  \<open>bij \<pi>\<close> bij_is_inj fst_conv inj_image_mem_iff prod.collapse rename.simps snd_conv
    by (metis (mono_tags, lifting))
  hence 
    "\<forall>p. \<pi> ` {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p} \<subseteq> 
      {v \<in> (votrs_\<E> E'). (prof_\<E> E) (the_inv \<pi> v) = p}"
    using \<open>bij \<pi>\<close> bij_is_inj the_inv_f_f 
    by fastforce
  with subset rewrite have
    "\<forall>p. {v \<in> (votrs_\<E> E'). (prof_\<E> E') v = p} = \<pi> ` {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p}"
    by (simp add: subset_antisym)
  moreover have 
    "\<forall>p. card (\<pi> ` {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p}) = card {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p}"
    by (metis (no_types, lifting) \<open>bij \<pi>\<close> bij_betw_same_card bij_betw_subset top_greatest)
  ultimately have "\<forall>p. vote_count p E = vote_count p E'"
    unfolding vote_count.simps
    by presburger
  thus  
    "alts_\<E> E = alts_\<E> E' \<and> (E, E') \<in> X \<times> X \<and> (\<forall>p. vote_count p E = vote_count p E')"
    using eq_alts assms
    by simp
qed

lemma vote_count_anon_rel:
  fixes
    X :: "('a, 'v) Election set" and
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election"
  assumes
    "finite (votrs_\<E> E)" and
    "finite (votrs_\<E> E')" and
    eq: "alts_\<E> E = alts_\<E> E' \<and> (E, E') \<in> X \<times> X \<and> (\<forall>p. vote_count p E = vote_count p E')"
  shows "(E, E') \<in> anonymity\<^sub>\<R> X"
proof -
  from eq have 
    "\<forall>p. card {v \<in> votrs_\<E> E. prof_\<E> E v = p} = card {v \<in> votrs_\<E> E'. prof_\<E> E' v = p}"
    unfolding vote_count.simps
    by blast
  moreover have 
    "\<forall>p. finite {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<and> finite {v \<in> votrs_\<E> E'. prof_\<E> E' v = p}"
    using assms
    by simp
  ultimately have
    "\<forall>p. \<exists>\<pi>_p. bij_betw \<pi>_p {v \<in> votrs_\<E> E. prof_\<E> E v = p} {v \<in> votrs_\<E> E'. prof_\<E> E' v = p}"
    using bij_betw_iff_card 
    by blast
  then obtain \<pi> :: "'a Preference_Relation \<Rightarrow> ('v \<Rightarrow> 'v)" where
    bij: "\<forall>p. bij_betw (\<pi> p) {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p} 
                             {v \<in> (votrs_\<E> E'). (prof_\<E> E') v = p}"
    by (metis (no_types))
  hence bij_inv: 
    "\<forall>p. bij_betw (the_inv_into {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p} (\<pi> p)) 
                    {v \<in> (votrs_\<E> E'). (prof_\<E> E') v = p}
                    {v \<in> (votrs_\<E> E). (prof_\<E> E) v = p}"
    using bij_betw_the_inv_into 
    by blast
  let ?\<pi> = 
    "\<lambda>v. (if v \<in> votrs_\<E> E then \<pi> ((prof_\<E> E) v) v else
         (if v \<in> votrs_\<E> E' then the_inv_into {v \<in> (votrs_\<E> E). (prof_\<E> E) v = prof_\<E> E' v} 
                                                (\<pi> ((prof_\<E> E') v)) v 
                            else v))"
  have "bij ?\<pi>"
  proof (unfold bij_betw_def inj_def, safe)
    fix
      x :: 'v and
      y :: 'v
    assume eq_img:
      "?\<pi> x = ?\<pi> y"
    thus "x = y" \<comment> \<open>case distinction\<close>
      sorry
  next
    fix
      v :: 'v
    show 
      "?\<pi> v \<in> UNIV"
      by simp
  next
    fix
      v :: 'v
    have 
      "range ?\<pi> = ?\<pi> ` (votrs_\<E> E) \<union> ?\<pi> ` (votrs_\<E> E' - votrs_\<E> E) \<union> 
                  ?\<pi> ` (UNIV - votrs_\<E> E' - votrs_\<E> E)"
      by blast
    moreover have "?\<pi> ` (votrs_\<E> E' - votrs_\<E> E) = votrs_\<E> E - votrs_\<E> E'"
      sorry
    moreover have "?\<pi> ` (votrs_\<E> E) = votrs_\<E> E'"
      sorry
    moreover have "?\<pi> ` (UNIV - votrs_\<E> E' - votrs_\<E> E) = UNIV - votrs_\<E> E' - votrs_\<E> E"
      by simp
    ultimately have "range ?\<pi> = UNIV"
      by auto
    thus "v \<in> range ?\<pi>"
      by simp
  qed
  moreover have "?\<pi> ` (votrs_\<E> E) = votrs_\<E> E'"
  proof (safe)
    fix
      v :: 'v
    assume
      "v \<in> votrs_\<E> E"
    then obtain p :: "'a Preference_Relation" where
      "v \<in> {v \<in> votrs_\<E> E. prof_\<E> E v = p}"
      by blast
    thus
      "?\<pi> v \<in> votrs_\<E> E'"
      using bij bij_betwE 
      by fastforce
  next
    fix
      v :: 'v
    assume
      "v \<in> votrs_\<E> E'"
    thus 
      "v \<in> ?\<pi> ` votrs_\<E> E"
      sorry
  qed
  moreover have "prof_\<E> E' = prof_\<E> E \<circ> (the_inv ?\<pi>)"
    sorry
  ultimately have "rename ?\<pi> E = E'"
    using eq rename.simps
    by (metis (no_types, lifting) prod.collapse)
  moreover have "E \<in> X"
    using eq assms
    by blast
  ultimately show
    "(E, E') \<in> anonymity\<^sub>\<R> X"
    unfolding anonymity\<^sub>\<R>.simps rel_induced_by_action.simps \<phi>_anon.simps
              extensional_continuation.simps anonymity\<^sub>\<G>_def BijGroup_def Bij_def
    using \<open>bij ?\<pi>\<close> eq 
    by auto
qed

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
  group_action anonymity\<^sub>\<G> valid_elections "\<phi>_anon valid_elections"
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
    hence "bij_betw (\<phi>_anon valid_elections \<pi>) valid_elections valid_elections"
      unfolding \<phi>_anon.simps extensional_continuation.simps
      using bij_betw_ext
      by simp
    moreover have "\<phi>_anon valid_elections \<pi> \<in> extensional valid_elections"
      unfolding extensional_def
      by force
    ultimately show "\<phi>_anon valid_elections \<pi> \<in> carrier (BijGroup valid_elections)"
      unfolding BijGroup_def Bij_def
      by simp
  }
  note bij_car_el =
    \<open>\<And>\<pi>. \<pi> \<in> carrier (BijGroup UNIV) \<Longrightarrow> 
          \<phi>_anon valid_elections \<pi> \<in> carrier (BijGroup valid_elections)\<close>
  fix
    \<pi> :: "'v \<Rightarrow> 'v" and \<pi>' :: "'v \<Rightarrow> 'v"
  assume
    bij: "\<pi> \<in> carrier (BijGroup UNIV)" and bij': "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence car_els: "\<phi>_anon valid_elections \<pi> \<in> carrier (BijGroup valid_elections) \<and> 
                    \<phi>_anon valid_elections \<pi>' \<in> carrier (BijGroup valid_elections)"
    using bij_car_el
    by metis
  hence "bij_betw (\<phi>_anon valid_elections \<pi>') valid_elections valid_elections"
    unfolding BijGroup_def Bij_def extensional_def
    by auto
  hence valid_closed': "\<phi>_anon valid_elections \<pi>' ` valid_elections \<subseteq> valid_elections"
    using bij_betw_imp_surj_on 
    by blast
  from car_els have
    "\<phi>_anon valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> (\<phi>_anon valid_elections) \<pi>' =
      extensional_continuation 
        (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') valid_elections"
    using rewrite_mult
    by blast
  moreover have
    "\<forall>E. E \<in> valid_elections \<longrightarrow> 
      extensional_continuation 
        (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') valid_elections E = 
        (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') E"
    by simp
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> 
          (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') E = rename \<pi> (rename \<pi>' E)"
    unfolding \<phi>_anon.simps
    using valid_closed'
    by auto
  moreover have "\<forall>E. E \<in> valid_elections \<longrightarrow> rename \<pi> (rename \<pi>' E) = rename (\<pi> \<circ> \<pi>') E"
    using rename_comp bij bij' Symmetry_Of_Functions.bij_car_el comp_apply
    by metis
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> 
          rename (\<pi> \<circ> \<pi>') E = \<phi>_anon valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E"
    using rewrite_mult_univ bij bij'
    unfolding \<phi>_anon.simps
    by force
  moreover have 
    "\<forall>E. E \<notin> valid_elections \<longrightarrow> 
      extensional_continuation 
        (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') valid_elections E = undefined"
    by simp
  moreover have 
    "\<forall>E. E \<notin> valid_elections \<longrightarrow> \<phi>_anon valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E = undefined"
    by simp
  ultimately have 
    "\<forall>E. \<phi>_anon valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E = 
          (\<phi>_anon valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_anon valid_elections \<pi>') E"
    by metis
  thus
    "\<phi>_anon valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') = 
      \<phi>_anon valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_anon valid_elections \<pi>'"
    by blast
qed

lemma (in result) well_formed_res_anon:
  "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance (anonymity\<^sub>\<R> valid_elections))"
proof (unfold anonymity\<^sub>\<R>.simps, simp, safe) qed

subsection \<open>Neutrality Lemmas\<close>

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
  group_action neutrality\<^sub>\<G> valid_elections "\<phi>_neutr valid_elections"
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
    hence "bij_betw (\<phi>_neutr valid_elections \<pi>) valid_elections valid_elections"
      unfolding \<phi>_neutr.simps 
      using bij_betw_ext 
      by blast
    thus "\<phi>_neutr valid_elections \<pi> \<in> carrier (BijGroup valid_elections)"
      unfolding \<phi>_neutr.simps BijGroup_def Bij_def extensional_def
      by simp
  }
  note bij_car_el =
    \<open>\<And>\<pi>. \<pi> \<in> carrier (BijGroup UNIV) \<Longrightarrow> \<phi>_neutr valid_elections \<pi> \<in> carrier (BijGroup valid_elections)\<close>
  fix
      \<pi> :: "'a \<Rightarrow> 'a" and \<pi>' :: "'a \<Rightarrow> 'a"
  assume
    bij: "\<pi> \<in> carrier (BijGroup UNIV)" and bij': "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence car_els: "\<phi>_neutr valid_elections \<pi> \<in> carrier (BijGroup valid_elections) \<and> 
                    \<phi>_neutr valid_elections \<pi>' \<in> carrier (BijGroup valid_elections)"
    using bij_car_el
    by metis
  hence "bij_betw (\<phi>_neutr valid_elections \<pi>') valid_elections valid_elections"
    unfolding BijGroup_def Bij_def extensional_def
    by auto
  hence valid_closed': "\<phi>_neutr valid_elections \<pi>' ` valid_elections \<subseteq> valid_elections"
    using bij_betw_imp_surj_on 
    by blast
  from car_els have 
    "\<phi>_neutr valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr valid_elections \<pi>' = 
      extensional_continuation 
        (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') valid_elections"
    using rewrite_mult
    by auto
  moreover have
    "\<forall>E. E \<in> valid_elections \<longrightarrow> 
      extensional_continuation 
        (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') valid_elections E = 
          (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') E"
    by simp
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') E = alts_rename \<pi> (alts_rename \<pi>' E)"
    unfolding \<phi>_neutr.simps
    using valid_closed'
    by auto
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> alts_rename \<pi> (alts_rename \<pi>' E) = alts_rename (\<pi> \<circ> \<pi>') E"
    using alts_rename_comp bij bij' Symmetry_Of_Functions.bij_car_el comp_apply
    by metis
  moreover have 
    "\<forall>E. E \<in> valid_elections \<longrightarrow> alts_rename (\<pi> \<circ> \<pi>') E = \<phi>_neutr valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E"
    using rewrite_mult_univ bij bij'
    unfolding \<phi>_anon.simps
    by force
  moreover have 
    "\<forall>E. E \<notin> valid_elections \<longrightarrow> 
      extensional_continuation 
        (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') valid_elections E = undefined"
    by simp
  moreover have 
    "\<forall>E. E \<notin> valid_elections \<longrightarrow> \<phi>_neutr valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E = undefined"
    by simp
  ultimately have 
    "\<forall>E. \<phi>_neutr valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E = 
      (\<phi>_neutr valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr valid_elections \<pi>') E"
    by metis
  thus
    "\<phi>_neutr valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') = 
      \<phi>_neutr valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr valid_elections \<pi>'"
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
                                (\<phi>_neutr valid_elections) (set_action \<psi>_neutr\<^sub>\<c>))"
proof (simp del: limit_set_soc_choice.simps \<phi>_neutr.simps \<psi>_neutr\<^sub>\<w>.simps 
            add: rewrite_equivar_ind_by_act, safe, auto) qed

lemma wf_res_neutr_soc_welfare:
  "satisfies (\<lambda>E. limit_set_welfare (alts_\<E> E) UNIV) 
            (equivar_ind_by_act (carrier neutrality\<^sub>\<G>) valid_elections 
                                (\<phi>_neutr valid_elections) (set_action \<psi>_neutr\<^sub>\<w>))"
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
      "\<phi>_neutr valid_elections \<pi> (A, V, p) \<in> valid_elections" and
      lim_el: "r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections \<pi> (A, V, p))) UNIV"
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
        \<phi>_neutr valid_elections \<pi> (A, V, p) \<in> valid_elections \<Longrightarrow>
        r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections \<pi> (A, V, p))) UNIV \<Longrightarrow>
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
    prof_\<pi>: "\<phi>_neutr valid_elections \<pi> (A, V, p) \<in> valid_elections" and
    "r \<in> limit_set_welfare (alts_\<E> (A, V, p)) UNIV"
  hence 
    "r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections (inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>) 
                              (\<phi>_neutr valid_elections \<pi> (A, V, p)))) UNIV"
    by (metis \<phi>_neutr_act.orbit_sym_aux)
  moreover have inv_grp_el: "inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> \<in> carrier neutrality\<^sub>\<G>"
    using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close> \<psi>_neutr\<^sub>\<c>_act.group_hom 
          group.inv_closed group_hom_def
    by meson
  moreover have 
    "\<phi>_neutr valid_elections (inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>) 
      (\<phi>_neutr valid_elections \<pi> (A, V, p)) \<in> valid_elections"
    using prof \<phi>_neutr_act.element_image inv_grp_el prof_\<pi> 
    by blast
  ultimately have
    "r \<in> \<psi>_neutr\<^sub>\<w> (inv\<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>) ` 
            limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections \<pi> (A, V, p))) UNIV"
    using prof_\<pi> lim_el_\<pi>
    by (metis prod.collapse)
  thus
    "\<psi>_neutr\<^sub>\<w> \<pi> r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections \<pi> (A, V, p))) UNIV"
    using \<open>\<pi> \<in> carrier neutrality\<^sub>\<G>\<close> \<psi>_neutr\<^sub>\<w>_act.group_action_axioms 
          \<psi>_neutr\<^sub>\<w>_act.inj_prop group_action.orbit_sym_aux 
          inj_image_mem_iff inv_grp_el iso_tuple_UNIV_I
    by (metis (no_types, lifting))
qed

subsection \<open>Homogeneity Lemmas\<close>

lemma refl_homogeneity\<^sub>\<R>:
  fixes
    X :: "('a, 'v) Election set"
  assumes
    "X \<subseteq> finite_voter_elections"
  shows
    "refl_on X (homogeneity\<^sub>\<R> X)" 
  using assms
  unfolding refl_on_def finite_voter_elections_def homogeneity\<^sub>\<R>.simps
  by auto

lemma (in result) well_formed_res_homogeneity:
  "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance (homogeneity\<^sub>\<R> UNIV))"
  unfolding satisfies.simps homogeneity\<^sub>\<R>.simps
  by simp

lemma refl_homogeneity\<^sub>\<R>':
  fixes
    X :: "('a, 'v::linorder) Election set"
  assumes
    "X \<subseteq> finite_voter_elections"
  shows
    "refl_on X (homogeneity\<^sub>\<R>' X)" 
  using assms
  unfolding homogeneity\<^sub>\<R>'.simps refl_on_def finite_voter_elections_def
  by auto

lemma (in result) well_formed_res_homogeneity':
  "satisfies (\<lambda>E. limit_set (alts_\<E> E) UNIV) (Invariance (homogeneity\<^sub>\<R>' UNIV))"
  unfolding satisfies.simps homogeneity\<^sub>\<R>.simps
  by simp

subsection \<open>Reversal Symmetry Lemmas\<close>

subsubsection \<open>Auxiliary Lemmas\<close>

lemma rev_rev_id:
  "rev_rel \<circ> rev_rel = id"
  by auto

lemma rev_rel_limit:
  fixes
    A :: "'a set" and
    r :: "'a rel"
  shows
    "rev_rel (limit A r) = limit A (rev_rel r)"
  unfolding rev_rel.simps limit.simps
  by auto

lemma rev_rel_lin_ord:
  fixes
    A :: "'a set" and
    r :: "'a rel"
  assumes
    "linear_order_on A r"
  shows
    "linear_order_on A (rev_rel r)"
  using assms
  unfolding rev_rel.simps linear_order_on_def partial_order_on_def 
            total_on_def antisym_def preorder_on_def refl_on_def trans_def
  by blast

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

interpretation \<phi>_rev_act:
  group_action reversal\<^sub>\<G> valid_elections "\<phi>_rev valid_elections"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, 
        safe, rule group_BijGroup)
  {
    fix
      \<pi> :: "'a rel \<Rightarrow> 'a rel"
    assume
      "\<pi> \<in> carrier reversal\<^sub>\<G>"
    hence \<pi>_cases: "\<pi> \<in> {id, rev_rel}"
      unfolding reversal\<^sub>\<G>_def
      by auto
    hence "rel_app \<pi> \<circ> rel_app \<pi> = id"
      using rev_rev_id
      by fastforce
    hence id: "\<forall>E. rel_app \<pi> (rel_app \<pi> E) = E"
      unfolding comp_def
      \<comment> \<open>Weirdly doesn't seem to work without adding the previous equation like this.\<close>
      by (simp add: \<open>rel_app \<pi> \<circ> rel_app \<pi> = id\<close> pointfree_idE)
    have
      "\<forall>E \<in> valid_elections. rel_app \<pi> E \<in> valid_elections"
      unfolding valid_elections_def profile_def
      using \<pi>_cases rev_rel_lin_ord rel_app.simps fun.map_id 
      by fastforce  
    hence "rel_app \<pi> ` valid_elections \<subseteq> valid_elections"
      by blast
    with id have
      "bij_betw (rel_app \<pi>) valid_elections valid_elections"
      using bij_betw_byWitness[of valid_elections "rel_app \<pi>" "rel_app \<pi>" valid_elections]
      by blast
    hence 
      "bij_betw (\<phi>_rev valid_elections \<pi>) valid_elections valid_elections"
      unfolding \<phi>_rev.simps 
      using bij_betw_ext 
      by blast
    moreover have "\<phi>_rev valid_elections \<pi> \<in> extensional valid_elections"
      unfolding extensional_def
      by simp
    ultimately show "\<phi>_rev valid_elections \<pi> \<in> carrier (BijGroup valid_elections)"
      unfolding BijGroup_def Bij_def
      by simp
  }
  note car_el = 
    \<open>\<And>\<pi>. \<pi> \<in> carrier reversal\<^sub>\<G> \<Longrightarrow> \<phi>_rev valid_elections \<pi> \<in> carrier (BijGroup valid_elections)\<close>
  fix
    \<pi> :: "'a rel \<Rightarrow> 'a rel" and
    \<pi>' :: "'a rel \<Rightarrow> 'a rel"
  assume
    rev: "\<pi> \<in> carrier reversal\<^sub>\<G>" and
    rev': "\<pi>' \<in> carrier reversal\<^sub>\<G>"
  hence "\<pi> \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>' = \<pi> \<circ> \<pi>'"
    unfolding reversal\<^sub>\<G>_def
    by simp
  hence
    "\<phi>_rev valid_elections (\<pi> \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') =
      extensional_continuation (rel_app (\<pi> \<circ> \<pi>')) valid_elections"
    by simp
  also have
    "rel_app (\<pi> \<circ> \<pi>') = rel_app \<pi> \<circ> rel_app \<pi>'"
    using rel_app.simps
    by fastforce
  finally have rewrite:
    "\<phi>_rev valid_elections (\<pi> \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') = 
      extensional_continuation (rel_app \<pi> \<circ> rel_app \<pi>') valid_elections"
    by blast
  have "bij_betw (\<phi>_rev valid_elections \<pi>') valid_elections valid_elections"
    using car_el rev'
    unfolding BijGroup_def Bij_def
    by auto
  hence "\<forall>E \<in> valid_elections. \<phi>_rev valid_elections \<pi>' E \<in> valid_elections"
    unfolding bij_betw_def
    by blast
  hence
    "extensional_continuation 
      (\<phi>_rev valid_elections \<pi> \<circ> \<phi>_rev valid_elections \<pi>') valid_elections =
      extensional_continuation (rel_app \<pi> \<circ> rel_app \<pi>') valid_elections"
    unfolding extensional_continuation.simps \<phi>_rev.simps
    by fastforce
  also have
    "extensional_continuation (\<phi>_rev valid_elections \<pi> \<circ> \<phi>_rev valid_elections \<pi>') valid_elections
      = \<phi>_rev valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_rev valid_elections \<pi>'"
    using car_el rewrite_mult rev rev'
    by metis
  finally show
    "\<phi>_rev valid_elections (\<pi> \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') =
     \<phi>_rev valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_rev valid_elections \<pi>'"
    using rewrite
    by metis
qed

interpretation \<psi>_rev_act: 
  group_action reversal\<^sub>\<G> UNIV \<psi>_rev
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def \<psi>_rev.simps, 
        safe, rule group_BijGroup)
  {
    fix
      \<pi> :: "'a rel \<Rightarrow> 'a rel"
    assume
      "\<pi> \<in> carrier reversal\<^sub>\<G>"
    hence "\<pi> \<in> {id, rev_rel}"
      unfolding reversal\<^sub>\<G>_def
      by auto
    hence "bij \<pi>"
      using rev_rev_id
      by (metis bij_id insertE o_bij singleton_iff)
    thus "\<pi> \<in> carrier (BijGroup UNIV)"
      using rewrite_carrier
      by blast
  }
  note bij = 
    \<open>\<And>\<pi>. \<pi> \<in> carrier reversal\<^sub>\<G> \<Longrightarrow> \<pi> \<in> carrier (BijGroup UNIV)\<close>
  fix
    \<pi> :: "'a rel \<Rightarrow> 'a rel" and
    \<pi>' :: "'a rel \<Rightarrow> 'a rel"
  assume
    rev: "\<pi> \<in> carrier reversal\<^sub>\<G>" and
    rev': "\<pi>' \<in> carrier reversal\<^sub>\<G>"
  hence "\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>' = \<pi> \<circ> \<pi>'"
    using bij rewrite_mult_univ
    by blast
  also have "\<pi> \<circ> \<pi>' = \<pi> \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>'"
    unfolding reversal\<^sub>\<G>_def
    using rev rev'
    by simp
  finally show
    "\<pi> \<otimes>\<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>' = \<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>'"
    by simp
qed

lemma \<phi>_\<psi>_rev_well_formed:
  shows 
    "satisfies (\<lambda>E. limit_set_welfare (alts_\<E> E) UNIV) 
               (equivar_ind_by_act (carrier reversal\<^sub>\<G>) valid_elections 
                                    (\<phi>_rev valid_elections) (set_action \<psi>_rev))"
proof (simp only: rewrite_equivar_ind_by_act, clarify)
  fix
    \<pi> :: "'a rel \<Rightarrow> 'a rel" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume
    rev: "\<pi> \<in> carrier reversal\<^sub>\<G>" and
    valid: "(A, V, p) \<in> valid_elections"
  hence cases: "\<pi> \<in> {id, rev_rel}"
    unfolding reversal\<^sub>\<G>_def
    by auto
  have eq_A: "alts_\<E> (\<phi>_rev valid_elections \<pi> (A, V, p)) = A"
    using rev valid
    by simp
  have
    "\<forall>r \<in> {limit A r |r. r \<in> UNIV \<and> linear_order_on A (limit A r)}. \<exists>r' \<in> UNIV. 
      rev_rel r = limit A (rev_rel r') \<and> 
        rev_rel r' \<in> UNIV \<and> linear_order_on A (limit A (rev_rel r'))"
    using rev_rel_limit[of A] rev_rel_lin_ord[of A]
    by force
  hence
    "\<forall>r \<in> {limit A r |r. r \<in> UNIV \<and> linear_order_on A (limit A r)}.
      rev_rel r \<in> 
        {limit A (rev_rel r') |r'. rev_rel r' \<in> UNIV \<and> linear_order_on A (limit A (rev_rel r'))}"
    by blast
  moreover have
    "{limit A (rev_rel r') |r'. rev_rel r' \<in> UNIV \<and> linear_order_on A (limit A (rev_rel r'))} \<subseteq>
      {limit A r |r. r \<in> UNIV \<and> linear_order_on A (limit A r)}"
    by blast
  ultimately have "\<forall>r \<in> limit_set_welfare A UNIV. rev_rel r \<in> limit_set_welfare A UNIV"
    unfolding limit_set_welfare.simps
    by blast
  hence subset: "\<forall>r \<in> limit_set_welfare A UNIV. \<pi> r \<in> limit_set_welfare A UNIV"
    using cases
    by fastforce
  hence "\<forall>r \<in> limit_set_welfare A UNIV. r \<in> \<pi> ` limit_set_welfare A UNIV"
    using rev_rev_id
    by (metis comp_apply empty_iff id_apply image_eqI insert_iff local.cases)
  with subset have "\<pi> ` limit_set_welfare A UNIV = limit_set_welfare A UNIV"
    by blast
  hence
    "set_action \<psi>_rev \<pi> (limit_set_welfare A UNIV) = limit_set_welfare A UNIV"
    unfolding set_action.simps \<psi>_rev.simps
    by blast
  also have
    "limit_set_welfare A UNIV = 
      limit_set_welfare (alts_\<E> (\<phi>_rev valid_elections \<pi> (A, V, p))) UNIV"
    using eq_A
    by simp
  finally show
    "limit_set_welfare (alts_\<E> (\<phi>_rev valid_elections \<pi> (A, V, p))) UNIV =
       set_action \<psi>_rev \<pi> (limit_set_welfare (alts_\<E> (A, V, p)) UNIV)"
    by simp
qed

end

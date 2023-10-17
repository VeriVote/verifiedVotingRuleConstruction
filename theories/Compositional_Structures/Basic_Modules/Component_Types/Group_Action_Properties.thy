section \<open>Symmetry Properties\<close>

theory Group_Action_Properties
  imports Electoral_Module
          Distance_Rationalization
begin

subsection \<open>Invariance and Equivariance\<close>

definition invariant :: "'x monoid \<Rightarrow> ('x \<Rightarrow> 'y \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> ('y \<Rightarrow> 'z) \<Rightarrow> bool" 
  where "invariant G \<phi> E f = (\<forall> x \<in> E. \<forall> g \<in> carrier G. f x = f (\<phi> g x))"

definition equivariant :: 
"'x monoid \<Rightarrow> ('x \<Rightarrow> 'y \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> ('x \<Rightarrow> 'z \<Rightarrow> 'z) \<Rightarrow> 'z set \<Rightarrow> ('y \<Rightarrow> 'z) \<Rightarrow> bool" where 
  "equivariant G \<phi> E \<pi> F f = (\<forall> x \<in> E. \<forall> g \<in> carrier G. f (\<phi> g x) = \<pi> g (f x))"

subsubsection \<open>General Results\<close>

subsubsection \<open>Anonymity\<close>

text \<open>
  Anonymity is invariance under the natural action of the voter permutation group on elections.
\<close>

interpretation rename_action:
  group_action  "BijGroup (UNIV::'v set)" 
                "{el :: ('a, 'v) Election. finite_profile (votrs_\<E> el) (alts_\<E> el) (prof_\<E> el)}" 
                "rename"
  sorry

lemma (in result) anon_equiv_inv_under_voter_rename:
  "anonymity m = (electoral_module m \<and> 
    invariant (BijGroup (UNIV::'v set)) 
              rename 
              {el :: ('a, 'v) Election. finite_profile (votrs_\<E> el) (alts_\<E> el) (prof_\<E> el)} 
              (\<lambda> E. m (votrs_\<E> E) (alts_\<E> E) (prof_\<E> E)))"
proof (unfold anonymity_def invariant_def, safe)
  fix 
    m :: "('a, 'v, ('r Result)) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    g :: "'v \<Rightarrow> 'v"
  assume
    anon: "\<forall>A V p \<pi>.
       bij \<pi> \<longrightarrow>
       (let (A', V', q) = rename \<pi> (A, V, p)
        in finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> m V A p = m V' A' q)" and
    mod: "electoral_module m" and
    bij: "g \<in> carrier (BijGroup UNIV)" and
    fin_V: "finite (alts_\<E> (A, V, p))" and
    fin_A: "finite (votrs_\<E> (A, V, p))" and
    prof: "profile (votrs_\<E> (A, V, p)) (alts_\<E> (A, V, p)) (prof_\<E> (A, V, p))"
  hence "finite_profile (votrs_\<E> (A, V, p)) (alts_\<E> (A, V, p)) (prof_\<E> (A, V, p))"
    by simp
  moreover have "finite_profile (votrs_\<E> (rename g (A, V, p))) 
                                (alts_\<E> (rename g (A, V, p))) 
                                (prof_\<E> (rename g (A, V, p)))"
    using bij fin_A fin_V prof mem_Collect_eq rename_action.element_image
    by (metis (no_types, lifting))
  moreover have "((alts_\<E> (rename g (A, V, p))), votrs_\<E> (rename g (A, V, p)), 
                  (prof_\<E> (rename g (A, V, p)))) = rename g (A, V, p)"
    by simp
  moreover have "bij g" 
    using bij
    unfolding BijGroup_def Bij_def bij_def
    by auto
  ultimately show 
    "m (votrs_\<E> (A, V, p)) (alts_\<E> (A, V, p)) (prof_\<E> (A, V, p)) =
     m (votrs_\<E> (rename g (A, V, p))) 
       (alts_\<E> (rename g (A, V, p))) 
       (prof_\<E> (rename g (A, V, p)))"
    using anon bij
    by auto
next
  fix 
    m :: "('a, 'v, ('r Result)) Electoral_Module" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume
    mod: "electoral_module m" and
    inv: "\<forall>x\<in>{el. finite_profile (votrs_\<E> el) (alts_\<E> el) (prof_\<E> el)}.
          \<forall>g\<in>carrier (BijGroup UNIV).
             m (votrs_\<E> x) (alts_\<E> x) (prof_\<E> x) =
             m (votrs_\<E> (rename g x)) (alts_\<E> (rename g x)) (prof_\<E> (rename g x))" and
    bij: "bij \<pi>"
  show "let (A', V', q) = rename \<pi> (A, V, p)
       in finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> m V A p = m V' A' q"
  proof (unfold Let_def, safe)
    fix 
      A' :: "'a set" and
      V' :: "'v set" and
      p' :: "('a, 'v) Profile"
    assume
      renamed: "rename \<pi> (A, V, p) = (A', V', p')" and
      fin_A: "finite A" and
      fin_V: "finite V" and
      prof: "profile V A p"
    have "(A, V, p) \<in> {el. finite_profile (votrs_\<E> el) (alts_\<E> el) (prof_\<E> el)}"
      using fin_A fin_V prof
      by simp
    moreover have "\<pi> \<in> (carrier (BijGroup UNIV))"
      using bij
      unfolding BijGroup_def Bij_def
      by simp
    ultimately show "m V A p = m V' A' p'"
      using renamed bij inv
      by simp
  qed
qed

subsubsection \<open>Neutrality\<close>

text \<open>
  Neutrality is equivariance under the natural action of the candidate 
  permutation group on elections.
\<close>

definition pref_rename :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
  "pref_rename \<pi> r = {(\<pi> a, \<pi> b) | a b. (a,b) \<in> r}"
  
end
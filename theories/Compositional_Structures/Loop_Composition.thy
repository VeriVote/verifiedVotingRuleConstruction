(*  File:       Loop_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Loop Composition\<close>

theory Loop_Composition
  imports "Basic_Modules/Component_Types/Termination_Condition"
          "Basic_Modules/Defer_Module"
          Sequential_Composition
begin

text
\<open>The loop composition uses the same module in sequence,
combined with a termination condition, until either
  (1) the termination condition is met or
  (2) no new decisions are made (i.e., a fixed point is reached).\<close>

subsection \<open>Definition\<close>

lemma loop_termination_helper:
  assumes
    not_term: "\<not>t (acc A p)" and
    subset: "defer (acc \<triangleright> m) A p \<subset> defer acc A p" and
    not_inf: "\<not>infinite (defer acc A p)"
  shows
    "((acc \<triangleright> m, m, t, A, p), (acc, m, t, A, p)) \<in>
        measure (\<lambda>(acc, m, t, A, p). card (defer acc A p))"
  using assms psubset_card_mono
  by auto

(*
   This function handles the accumulator for the following loop composition
   function.
*)
function loop_comp_helper ::
    "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Termination_Condition \<Rightarrow> 'a Electoral_Module" where
  "t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
    infinite (defer acc A p) \<Longrightarrow>
      loop_comp_helper acc m t A p = acc A p" |
  "\<not>(t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
    infinite (defer acc A p)) \<Longrightarrow>
      loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
proof -
  fix
    P :: bool and
    x :: "('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
          ('a Termination_Condition) \<times> 'a set \<times> 'a Profile"
  assume
    a1: "\<And>t acc A p m.
          \<lbrakk>t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
              infinite (defer acc A p);
            x = (acc, m, t, A, p)\<rbrakk> \<Longrightarrow> P" and
    a2: "\<And>t acc A p m.
          \<lbrakk>\<not> (t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
              infinite (defer acc A p));
            x = (acc, m, t, A, p)\<rbrakk> \<Longrightarrow> P"
  have "\<exists>f A p rs fa. (fa, f, p, A, rs) = x"
    using prod_cases5
    by metis
  then show P
    using a2 a1
    by (metis (no_types))
next
  show
    "\<And>t acc A p m ta acca Aa pa ma.
       t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
        infinite (defer acc A p) \<Longrightarrow>
          ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
          infinite (defer acca Aa pa) \<Longrightarrow>
           (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
              acc A p = acca Aa pa"
    by fastforce
next
  show
    "\<And>t acc A p m ta acca Aa pa ma.
       t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
        infinite (defer acc A p) \<Longrightarrow>
          \<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
          infinite (defer acca Aa pa)) \<Longrightarrow>
           (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
              acc A p = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
  proof -
    fix
      t :: "'a Termination_Condition" and
      acc :: "'a Electoral_Module" and
      A :: "'a set" and
      p :: "'a Profile" and
      m :: "'a Electoral_Module" and
      ta :: "'a Termination_Condition" and
      acca :: "'a Electoral_Module" and
      Aa :: "'a set" and
      pa :: "'a Profile" and
      ma :: "'a Electoral_Module"
    assume
      a1: "t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
            infinite (defer acc A p)" and
      a2: "\<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
            infinite (defer acca Aa pa))" and
      "(acc, m, t, A, p) = (acca, ma, ta, Aa, pa)"
    hence False
      using a2 a1
      by force
  thus "acc A p = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
    by auto
qed
next
  show
    "\<And>t acc A p m ta acca Aa pa ma.
       \<not> (t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
          infinite (defer acc A p)) \<Longrightarrow>
           \<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
            infinite (defer acca Aa pa)) \<Longrightarrow>
             (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
                loop_comp_helper_sumC (acc \<triangleright> m, m, t, A, p) =
                  loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
    by force
qed
termination
proof -
  have f0:
    "\<exists>r. wf r \<and>
        (\<forall>p f A rs fa.
          p (f (A::'a set) rs) \<or>
          \<not> defer (f \<triangleright> fa) A rs \<subset> defer f A rs \<or>
          infinite (defer f A rs) \<or>
          ((f \<triangleright> fa, fa, p, A, rs), (f, fa, p, A, rs)) \<in> r)"
    using loop_termination_helper wf_measure "termination"
    by (metis (no_types))
  hence
    "\<forall>r p.
      Ex ((\<lambda>ra. \<forall>f A rs pa fa. \<exists>ra pb rb pc pd fb Aa rsa fc pe.
        \<not> wf r \<or>
          loop_comp_helper_dom
            (p::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
              (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
          infinite (defer f (A::'a set) rs) \<or>
          pa (f A rs) \<and>
            wf
              (ra::((
                ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
                ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times> _) set) \<and>
            \<not> loop_comp_helper_dom (pb::
                ('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
          wf rb \<and> \<not> defer (f \<triangleright> fa) A rs \<subset> defer f A rs \<and>
            \<not> loop_comp_helper_dom
                (pc::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                  (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
            ((f \<triangleright> fa, fa, pa, A, rs), f, fa, pa, A, rs) \<in> rb \<and> wf rb \<and>
            \<not> loop_comp_helper_dom
                (pd::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                  (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
            finite (defer fb (Aa::'a set) rsa) \<and>
            defer (fb \<triangleright> fc) Aa rsa \<subset> defer fb Aa rsa \<and>
            \<not> pe (fb Aa rsa) \<and>
            ((fb \<triangleright> fc, fc, pe, Aa, rsa), fb, fc, pe, Aa, rsa) \<notin> r)::
          ((('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
            ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times>
            ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
            ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) set \<Rightarrow> bool)"
    by metis
  obtain
    rr ::  "((('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
             ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times>
             ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
             ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) set" where
      "wf rr \<and>
        (\<forall>p f A rs fa. p (f A rs) \<or>
          \<not> defer (f \<triangleright> fa) A rs \<subset> defer f A rs \<or>
          infinite (defer f A rs) \<or>
          ((f \<triangleright> fa, fa, p, A, rs), f, fa, p, A, rs) \<in> rr)"
    using f0
    by presburger
  thus ?thesis
    using "termination"
    by metis
qed

lemma loop_comp_code_helper[code]:
  "loop_comp_helper acc m t A p =
    (if (t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
      infinite (defer acc A p))
    then (acc A p) else (loop_comp_helper (acc \<triangleright> m) m t A p))"
  by simp

function loop_composition ::
    "'a Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow>
        'a Electoral_Module" where
  "t ({}, {}, A) \<Longrightarrow>
    loop_composition m t A p = defer_module A p" |
  "\<not>(t ({}, {}, A)) \<Longrightarrow>
    loop_composition m t A p = (loop_comp_helper m m t) A p"
  by (fastforce, simp_all)
termination
  using  "termination" wf_empty
  by blast

abbreviation loop ::
  "'a Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow> 'a Electoral_Module"
    ("_ \<circlearrowleft>\<^sub>_" 50) where
  "m \<circlearrowleft>\<^sub>t \<equiv> loop_composition m t"

lemma loop_comp_code[code]:
  "loop_composition m t A p =
    (if (t ({},{},A))
    then (defer_module A p) else (loop_comp_helper m m t) A p)"
  by simp

lemma loop_comp_helper_imp_partit:
  assumes
    module_m: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "electoral_module acc \<and> (n = card (defer acc A p)) \<Longrightarrow>
        well_formed A (loop_comp_helper acc m t A p)"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  thus ?case
    using electoral_module_def loop_comp_helper.simps(1)
          loop_comp_helper.simps(2) module_m profile
          psubset_card_mono seq_comp_sound
    by (smt (verit))
qed

subsection \<open>Soundness\<close>

theorem loop_comp_sound:
  assumes m_module: "electoral_module m"
  shows "electoral_module (m \<circlearrowleft>\<^sub>t)"
  using def_mod_sound electoral_module_def loop_composition.simps(1)
        loop_composition.simps(2) loop_comp_helper_imp_partit m_module
  by metis

lemma loop_comp_helper_imp_no_def_incr:
  assumes
    module_m: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "(electoral_module acc \<and> n = card (defer acc A p)) \<Longrightarrow>
        defer (loop_comp_helper acc m t) A p \<subseteq> defer acc A p"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  thus ?case
    using dual_order.trans eq_iff less_imp_le loop_comp_helper.simps(1)
          loop_comp_helper.simps(2) module_m psubset_card_mono
          seq_comp_sound
    by (smt (verit, ccfv_SIG))
qed

subsection \<open>Lemmata\<close>

lemma loop_comp_helper_def_lift_inv_helper:
  assumes
    monotone_m: "defer_lift_invariance m" and
    f_prof: "finite_profile A p"
  shows
    "(defer_lift_invariance acc \<and> n = card (defer acc A p)) \<longrightarrow>
        (\<forall>q a.
          (a \<in> (defer (loop_comp_helper acc m t) A p) \<and>
            lifted A p q a) \<longrightarrow>
                (loop_comp_helper acc m t) A p =
                  (loop_comp_helper acc m t) A q)"
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have defer_card_comp:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc \<triangleright> m) A p) = card (defer (acc \<triangleright> m) A q))"
    using monotone_m def_lift_inv_seq_comp_help
    by metis
  have defer_card_acc:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc) A p) = card (defer (acc) A q))"
    by (simp add: defer_lift_invariance_def)
  hence defer_card_acc_2:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc) A p) = card (defer (acc) A q))"
    using monotone_m f_prof defer_lift_invariance_def seq_comp_def_set_trans
    by metis
  thus ?case
  proof cases
    assume card_unchanged: "card (defer (acc \<triangleright> m) A p) = card (defer acc A p)"
    with defer_card_comp defer_card_acc monotone_m
    have
      "defer_lift_invariance (acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (acc) A p) \<and> lifted A p q a) \<longrightarrow>
              (loop_comp_helper acc m t) A q = acc A q)"
      using card_subset_eq defer_in_alts less_irrefl
            loop_comp_helper.simps(1) f_prof psubset_card_mono
            sequential_composition.simps def_presv_fin_prof snd_conv
            defer_lift_invariance_def seq_comp_def_set_bounded
            loop_comp_code_helper
      by (smt (verit))
    moreover from card_unchanged have
      "(loop_comp_helper acc m t) A p = acc A p"
      using loop_comp_helper.simps(1) order.strict_iff_order
            psubset_card_mono
      by metis
    ultimately have
      "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (loop_comp_helper acc m t) A p) \<and>
              lifted A p q a) \<longrightarrow>
                  (loop_comp_helper acc m t) A p =
                    (loop_comp_helper acc m t) A q)"
      using defer_lift_invariance_def
      by metis
    thus ?thesis
      using monotone_m seq_comp_presv_def_lift_inv
      by blast
  next
    assume card_changed:
      "\<not> (card (defer (acc \<triangleright> m) A p) = card (defer acc A p))"
    with f_prof seq_comp_def_card_bounded have card_smaller_for_p:
      "electoral_module (acc) \<longrightarrow>
          (card (defer (acc \<triangleright> m) A p) < card (defer acc A p))"
      using monotone_m order.not_eq_order_implies_strict
            defer_lift_invariance_def
      by (metis (full_types))
    with defer_card_acc_2 defer_card_comp have card_changed_for_q:
      "defer_lift_invariance (acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
              (card (defer (acc \<triangleright> m) A q) < card (defer acc A q)))"
      using defer_lift_invariance_def
      by (metis (no_types, lifting))
    thus ?thesis
    proof cases
      assume t_not_satisfied_for_p: "\<not> t (acc A p)"
      hence t_not_satisfied_for_q:
        "defer_lift_invariance (acc) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                \<not> t (acc A q))"
        using monotone_m f_prof defer_lift_invariance_def seq_comp_def_set_trans
        by metis
      from card_changed defer_card_comp defer_card_acc
      have f0:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> Profile.lifted A p q a) \<longrightarrow>
                card (defer (acc \<triangleright> m) A q) \<noteq> (card (defer acc A q)))"
      proof -
        have
          "\<forall>f. (defer_lift_invariance f \<or>
            (\<exists>A rs rsa a. f A rs \<noteq> f A rsa \<and>
              Profile.lifted A rs rsa (a::'a) \<and>
              a \<in> defer f A rs) \<or> \<not> electoral_module f) \<and>
              ((\<forall>A rs rsa a. f A rs = f A rsa \<or> \<not> Profile.lifted A rs rsa a \<or>
                  a \<notin> defer f A rs) \<and> electoral_module f \<or> \<not> defer_lift_invariance f)"
          using defer_lift_invariance_def
          by blast
        thus ?thesis
          using card_changed monotone_m f_prof seq_comp_def_set_trans
          by (metis (no_types, hide_lams))
      qed
      hence
        "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                defer (acc \<triangleright> m) A q \<subset> defer acc A q)"
      proof -
        {
          fix
            aa :: 'a and
            rrs :: "('a \<times> 'a) set list"
          have
            "(\<not> defer_lift_invariance (acc \<triangleright> m) \<or> \<not> defer_lift_invariance acc) \<or>
              (aa \<notin> defer (acc \<triangleright> m) A p \<or> \<not> Profile.lifted A p rrs aa) \<or>
              defer (acc \<triangleright> m) A rrs \<subset> defer acc A rrs"
            using Profile.lifted_def f0 defer_lift_invariance_def
                  monotone_m psubsetI seq_comp_def_set_bounded
            by (metis (no_types))
        }
        thus ?thesis
          by metis
      qed
      with t_not_satisfied_for_p have rec_step_q:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                loop_comp_helper acc m t A q =
                  loop_comp_helper (acc \<triangleright> m) m t A q)"
        using defer_in_alts loop_comp_helper.simps(2) monotone_m subsetCE
              prod.sel(2) f_prof sequential_composition.simps card_eq_0_iff
              def_presv_fin_prof defer_lift_invariance_def card_changed_for_q
              gr_implies_not0 t_not_satisfied_for_q
        by (smt (verit, ccfv_SIG))
      have rec_step_p:
        "electoral_module acc \<longrightarrow>
            loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
        using card_changed defer_in_alts loop_comp_helper.simps(2)
              monotone_m prod.sel(2) f_prof psubsetI def_presv_fin_prof
              sequential_composition.simps defer_lift_invariance_def
              t_not_satisfied_for_p seq_comp_def_set_bounded
        by (smt (verit, best))
      thus ?thesis
        using card_smaller_for_p less.hyps
              loop_comp_helper_imp_no_def_incr monotone_m
              seq_comp_presv_def_lift_inv f_prof rec_step_q
              defer_lift_invariance_def subsetCE subset_eq
        by (smt (verit, ccfv_threshold))
    next
      assume t_satisfied_for_p: "\<not> \<not>t (acc A p)"
      thus ?thesis
        using loop_comp_helper.simps(1) defer_lift_invariance_def
        by metis
    qed
  qed
qed

lemma loop_comp_helper_def_lift_inv:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc" and
    profile: "finite_profile A p"
  shows
    "\<forall>q a. (lifted A p q a \<and> a \<in> (defer (loop_comp_helper acc m t) A p)) \<longrightarrow>
        (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q"
  using loop_comp_helper_def_lift_inv_helper
        monotone_m monotone_acc profile
  by blast

lemma loop_comp_helper_def_lift_inv2:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc"
  shows
    "\<forall>A p q a. (finite_profile A p \<and>
        lifted A p q a \<and>
        a \<in> (defer (loop_comp_helper acc m t) A p)) \<longrightarrow>
            (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q"
  using loop_comp_helper_def_lift_inv monotone_acc monotone_m
  by blast

lemma lifted_imp_fin_prof:
  assumes "lifted A p q a"
  shows "finite_profile A p"
  using assms Profile.lifted_def
  by fastforce

lemma loop_comp_helper_presv_def_lift_inv:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc"
  shows "defer_lift_invariance (loop_comp_helper acc m t)"
proof -
  have
    "\<forall>f. (defer_lift_invariance f \<or>
         (\<exists>A rs rsa a. f A rs \<noteq> f A rsa \<and>
              Profile.lifted A rs rsa (a::'a) \<and>
              a \<in> defer f A rs) \<or>
         \<not> electoral_module f) \<and>
      ((\<forall>A rs rsa a. f A rs = f A rsa \<or> \<not> Profile.lifted A rs rsa a \<or>
          a \<notin> defer f A rs) \<and>
      electoral_module f \<or> \<not> defer_lift_invariance f)"
    using defer_lift_invariance_def
    by blast
  thus ?thesis
    using electoral_module_def lifted_imp_fin_prof
          loop_comp_helper_def_lift_inv loop_comp_helper_imp_partit
          monotone_acc monotone_m
    by (metis (full_types))
qed

lemma loop_comp_presv_non_electing_helper:
  assumes
    non_electing_m: "non_electing m" and
    f_prof: "finite_profile A p"
  shows
    "(n = card (defer acc A p) \<and> non_electing acc) \<Longrightarrow>
        elect (loop_comp_helper acc m t) A p = {}"
proof (induct n arbitrary: acc rule: less_induct)
  case(less n)
  thus ?case
    using loop_comp_helper.simps(1) loop_comp_helper.simps(2)
          non_electing_def non_electing_m f_prof psubset_card_mono
          seq_comp_presv_non_electing
    by (smt (verit, ccfv_threshold))
qed

lemma loop_comp_helper_iter_elim_def_n_helper:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p"
  shows
    "(n = card (defer acc A p) \<and> n \<ge> x \<and> card (defer acc A p) > 1 \<and>
      non_electing acc) \<longrightarrow>
          card (defer (loop_comp_helper acc m t) A p) = x"
proof (induct n arbitrary: acc rule: less_induct)
  case(less n)
  have subset:
    "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> electoral_module acc) \<longrightarrow>
        defer (acc \<triangleright> m) A p \<subset> defer acc A p"
    using seq_comp_elim_one_red_def_set single_elimination
    by blast
  hence step_reduces_defer_set:
    "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> non_electing acc) \<longrightarrow>
        defer (acc \<triangleright> m) A p \<subset> defer acc A p"
    using non_electing_def
    by auto
  thus ?case
  proof cases
    assume term_satisfied: "t (acc A p)"
    have "card (defer_r (loop_comp_helper acc m t A p)) = x"
      using loop_comp_helper.simps(1) term_satisfied terminate_if_n_left
      by metis
    thus ?case
      by blast
  next
    assume term_not_satisfied: "\<not>(t (acc A p))"
    hence card_not_eq_x: "card (defer acc A p) \<noteq> x"
      by (simp add: terminate_if_n_left)
    have rec_step:
      "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> non_electing acc) \<longrightarrow>
          loop_comp_helper acc m t A p =
              loop_comp_helper (acc \<triangleright> m) m t A p" (*needed for step*)
      using loop_comp_helper.simps(2) non_electing_def def_presv_fin_prof
            step_reduces_defer_set term_not_satisfied
      by metis
    thus ?case
    proof cases
      assume card_too_small: "card (defer acc A p) < x"
      thus ?thesis
        using not_le
        by blast
    next
      assume old_card_at_least_x: "\<not>(card (defer acc A p) < x)"
      obtain i where i_is_new_card: "i = card (defer (acc \<triangleright> m) A p)"
        by blast
      with card_not_eq_x have card_too_big:
        "card (defer acc A p) > x"
        using nat_neq_iff old_card_at_least_x
        by blast
      hence enough_leftover: "card (defer acc A p) > 1"
        using x_greater_zero
        by auto
      have "electoral_module acc \<longrightarrow> (defer acc A p) \<subseteq> A"
        by (simp add: defer_in_alts f_prof)
      hence step_profile:
        "electoral_module acc \<longrightarrow>
            finite_profile (defer acc A p)
              (limit_profile (defer acc A p) p)"
        using f_prof limit_profile_sound
        by auto
      hence
        "electoral_module acc \<longrightarrow>
            card (defer m (defer acc A p)
              (limit_profile (defer acc A p) p)) =
                card (defer acc A p) - 1"
        using non_electing_m single_elimination
              single_elim_decr_def_card2 enough_leftover
        by blast
      hence "electoral_module acc \<longrightarrow> i = card (defer acc A p) - 1"
        using sequential_composition.simps snd_conv i_is_new_card
        by metis
      hence "electoral_module acc \<longrightarrow> i \<ge> x"
        using card_too_big
        by linarith
      hence new_card_still_big_enough: "electoral_module acc \<longrightarrow> x \<le> i"
        by blast
      have
        "electoral_module acc \<and> electoral_module m \<longrightarrow>
            defer (acc \<triangleright> m) A p \<subseteq> defer acc A p"
        using enough_leftover f_prof subset
        by blast
      hence
        "electoral_module acc \<and> electoral_module m \<longrightarrow>
            i \<le> card (defer acc A p)"
        using card_mono i_is_new_card step_profile
        by blast
      hence i_geq_x:
        "electoral_module acc \<and> electoral_module m \<longrightarrow> (i = x \<or> i > x)"
        using nat_less_le new_card_still_big_enough
        by blast
      thus ?thesis
      proof cases
        assume new_card_greater_x: "electoral_module acc \<longrightarrow> i > x"
        hence "electoral_module acc \<longrightarrow> 1 < card (defer (acc \<triangleright> m) A p)"
          using x_greater_zero i_is_new_card
          by linarith
        moreover have new_card_still_big_enough2:
          "electoral_module acc \<longrightarrow> x \<le> i" (* Needed for step *)
          using i_is_new_card new_card_still_big_enough
          by blast
        moreover have
          "n = card (defer acc A p) \<longrightarrow>
              (electoral_module acc \<longrightarrow> i < n)" (* Needed for step *)
          using subset step_profile enough_leftover f_prof psubset_card_mono
                i_is_new_card
          by blast
        moreover have
          "electoral_module acc \<longrightarrow>
              electoral_module (acc \<triangleright> m)" (* Needed for step *)
          using non_electing_def non_electing_m seq_comp_sound
          by blast
        moreover have non_electing_new:
          "non_electing acc \<longrightarrow> non_electing (acc \<triangleright> m)"
          by (simp add: non_electing_m)
        ultimately have
          "(n = card (defer acc A p) \<and> non_electing acc \<and>
              electoral_module acc) \<longrightarrow>
                  card (defer (loop_comp_helper (acc \<triangleright> m) m t) A p) = x"
          using less.hyps i_is_new_card new_card_greater_x
          by blast
        thus ?thesis
          using f_prof rec_step non_electing_def
          by metis
      next
        assume i_not_gt_x: "\<not>(electoral_module acc \<longrightarrow> i > x)"
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> i = x"
          using i_geq_x
          by blast
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> t ((acc \<triangleright> m) A p)"
          using i_is_new_card terminate_if_n_left
          by blast
        hence
          "electoral_module acc \<and> electoral_module m \<longrightarrow>
              card (defer_r (loop_comp_helper (acc \<triangleright> m) m t A p)) = x"
          using loop_comp_helper.simps(1) terminate_if_n_left
          by metis
        thus ?thesis
          using i_not_gt_x dual_order.strict_iff_order i_is_new_card
                loop_comp_helper.simps(1) new_card_still_big_enough
                f_prof rec_step terminate_if_n_left
          by metis
      qed
    qed
  qed
qed

lemma loop_comp_helper_iter_elim_def_n:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    acc_defers_enough: "card (defer acc A p) \<ge> x" and
    non_electing_acc: "non_electing acc"
  shows "card (defer (loop_comp_helper acc m t) A p) = x"
  using acc_defers_enough gr_implies_not0 le_neq_implies_less
        less_one linorder_neqE_nat loop_comp_helper.simps(1)
        loop_comp_helper_iter_elim_def_n_helper non_electing_acc
        non_electing_m f_prof single_elimination nat_neq_iff
        terminate_if_n_left x_greater_zero less_le
  by (metis (no_types, lifting))

lemma iter_elim_def_n_helper:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
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
      using enough_alternatives not_le
      by blast
  next
    assume "\<not>card A < x"
    hence card_big_enough_A: "card A > x"
      using card_not_x
      by linarith
    hence card_m: "card (defer m A p) = card A - 1"
      using non_electing_m f_prof single_elimination
            single_elim_decr_def_card2 x_greater_zero
      by fastforce
    hence card_big_enough_m: "card (defer m A p) \<ge> x"
      using card_big_enough_A
      by linarith
    hence "(m \<circlearrowleft>\<^sub>t) A p = (loop_comp_helper m m t) A p"
      by (simp add: card_not_x terminate_if_n_left)
    thus ?thesis
      using card_big_enough_m non_electing_m f_prof single_elimination
            terminate_if_n_left x_greater_zero loop_comp_helper_iter_elim_def_n
      by metis
  qed
qed

subsection \<open>Composition Rules\<close>

(*The loop composition preserves defer-lift-invariance.*)
theorem loop_comp_presv_def_lift_inv[simp]:
  assumes monotone_m: "defer_lift_invariance m"
  shows "defer_lift_invariance (m \<circlearrowleft>\<^sub>t)"
proof -
  fix
    A :: "'a set"
  have
    "\<forall> p q a. (a \<in> (defer (m \<circlearrowleft>\<^sub>t) A p) \<and> lifted A p q a) \<longrightarrow>
        (m \<circlearrowleft>\<^sub>t) A p = (m \<circlearrowleft>\<^sub>t) A q"
    using defer_module.simps monotone_m lifted_imp_fin_prof
          loop_composition.simps(1) loop_composition.simps(2)
          loop_comp_helper_def_lift_inv2
    by (metis (full_types))
  thus ?thesis
    using def_mod_def_lift_inv monotone_m loop_composition.simps(1)
          loop_composition.simps(2) defer_lift_invariance_def
          loop_comp_sound loop_comp_helper_def_lift_inv2
          lifted_imp_fin_prof
    by (smt (verit, best))
qed

(*The loop composition preserves the property non-electing.*)
theorem loop_comp_presv_non_electing[simp]:
  assumes non_electing_m: "non_electing m"
  shows "non_electing (m \<circlearrowleft>\<^sub>t)"
  unfolding non_electing_def
proof (safe, simp_all)
  show "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound non_electing_def non_electing_m
    by metis
next
    fix
      A :: "'a set" and
      p :: "'a Profile" and
      x :: "'a"
    assume
      fin_A: "finite A" and
      prof_A: "profile A p" and
      x_elect: "x \<in> elect (m \<circlearrowleft>\<^sub>t) A p"
    show "False"
  using def_mod_non_electing loop_comp_presv_non_electing_helper
        non_electing_m empty_iff fin_A loop_comp_code
        non_electing_def prof_A x_elect
  by metis
qed

theorem iter_elim_def_n[simp]:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = n))" and
    x_greater_zero: "n > 0"
  shows "defers n (m \<circlearrowleft>\<^sub>t)"
proof -
  have
    "\<forall> A p. finite_profile A p \<and> card A \<ge> n \<longrightarrow>
        card (defer (m \<circlearrowleft>\<^sub>t) A p) = n"
    using iter_elim_def_n_helper non_electing_m single_elimination
          terminate_if_n_left x_greater_zero
    by blast
  moreover have "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound eliminates_def single_elimination
    by blast
  thus ?thesis
    by (simp add: calculation defers_def)
qed

end

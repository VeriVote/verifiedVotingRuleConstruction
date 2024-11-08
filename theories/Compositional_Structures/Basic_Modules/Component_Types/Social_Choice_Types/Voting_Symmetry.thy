(*  File:       Voting_Symmetry.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Symmetry Properties of Voting Rules\<close>

theory Voting_Symmetry
  imports Symmetry_Of_Functions
          Social_Choice_Result
          Social_Welfare_Result
          Profile
begin

subsection \<open>Definitions\<close>

fun (in result) closed_elections :: "('a, 'v) Election rel \<Rightarrow> bool" where
  "closed_elections r =
    (\<forall> (e, e') \<in> r.
      limit (alternatives_\<E> e) UNIV = limit (alternatives_\<E> e') UNIV)"

fun result_action :: "('x, 'r) binary_fun \<Rightarrow> ('x, 'r Result) binary_fun" where
  "result_action \<psi> x = (\<lambda> r. (\<psi> x ` elect_r r, \<psi> x ` reject_r r, \<psi> x ` defer_r r))"

subsubsection \<open>Anonymity\<close>

definition anonymity\<^sub>\<G> :: "('v \<Rightarrow> 'v) monoid" where
  "anonymity\<^sub>\<G> = BijGroup (UNIV::'v set)"

fun \<phi>_anon :: "('a, 'v) Election set \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow>
        (('a, 'v) Election \<Rightarrow> ('a, 'v) Election)" where
  "\<phi>_anon \<E> \<pi> = extensional_continuation (rename \<pi>) \<E>"

fun anonymity\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "anonymity\<^sub>\<R> \<E> = action_induced_rel (carrier anonymity\<^sub>\<G>) \<E> (\<phi>_anon \<E>)"

subsubsection \<open>Neutrality\<close>

fun rel_rename :: "('a \<Rightarrow> 'a, 'a Preference_Relation) binary_fun" where
  "rel_rename \<pi> r = {(\<pi> a, \<pi> b) | a b. (a, b) \<in> r}"

fun alternatives_rename :: "('a \<Rightarrow> 'a, ('a, 'v) Election) binary_fun" where
  "alternatives_rename \<pi> \<E> =
      (\<pi> ` (alternatives_\<E> \<E>), voters_\<E> \<E>, (rel_rename \<pi>) \<circ> (profile_\<E> \<E>))"

definition neutrality\<^sub>\<G> :: "('a \<Rightarrow> 'a) monoid" where
  "neutrality\<^sub>\<G> = BijGroup (UNIV::'a set)"

fun \<phi>_neutral :: "('a, 'v) Election set \<Rightarrow> ('a \<Rightarrow> 'a, ('a, 'v) Election) binary_fun" where
  "\<phi>_neutral \<E> \<pi> = extensional_continuation (alternatives_rename \<pi>) \<E>"

fun neutrality\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "neutrality\<^sub>\<R> \<E> = action_induced_rel (carrier neutrality\<^sub>\<G>) \<E> (\<phi>_neutral \<E>)"

fun \<psi>_neutral\<^sub>\<c> :: "('a \<Rightarrow> 'a, 'a) binary_fun" where
  "\<psi>_neutral\<^sub>\<c> \<pi> r = \<pi> r"

fun \<psi>_neutral\<^sub>\<w> :: "('a \<Rightarrow> 'a, 'a rel) binary_fun" where
  "\<psi>_neutral\<^sub>\<w> \<pi> r = rel_rename \<pi> r"

subsubsection \<open>Homogeneity\<close>

fun homogeneity\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "homogeneity\<^sub>\<R> \<E> =
      {(E, E'). E \<in> \<E>
        \<and>  alternatives_\<E> E = alternatives_\<E> E'
        \<and> finite (voters_\<E> E) \<and> finite (voters_\<E> E')
        \<and> (\<exists> n > 0. \<forall> r::('a Preference_Relation).
              vote_count r E = n * (vote_count r E'))}"

fun copy_list :: "nat \<Rightarrow> 'x list \<Rightarrow> 'x list" where
  "copy_list 0 l = []" |
  "copy_list (Suc n) l = copy_list n l @ l"

fun homogeneity\<^sub>\<R>' :: "('a, 'v::linorder) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "homogeneity\<^sub>\<R>' \<E> =
      {(E, E'). E \<in> \<E>
        \<and>  alternatives_\<E> E = alternatives_\<E> E'
        \<and> finite (voters_\<E> E) \<and> finite (voters_\<E> E')
        \<and> (\<exists> n > 0.
            to_list (voters_\<E> E') (profile_\<E> E') =
              copy_list n (to_list (voters_\<E> E) (profile_\<E> E)))}"

subsubsection \<open>Reversal Symmetry\<close>

fun reverse_rel :: "'a rel \<Rightarrow> 'a rel" where
  "reverse_rel r = {(a, b). (b, a) \<in> r}"

fun rel_app :: "('a rel \<Rightarrow> 'a rel) \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "rel_app f (A, V, p) = (A, V, f \<circ> p)"

definition reversal\<^sub>\<G> :: "('a rel \<Rightarrow> 'a rel) monoid" where
  "reversal\<^sub>\<G> = \<lparr>carrier = {reverse_rel, id}, monoid.mult = comp, one = id\<rparr>"

fun \<phi>_reverse :: "('a, 'v) Election set
                \<Rightarrow> ('a rel \<Rightarrow> 'a rel, ('a, 'v) Election) binary_fun" where
  "\<phi>_reverse \<E> \<phi> = extensional_continuation (rel_app \<phi>) \<E>"

fun \<psi>_reverse :: "('a rel \<Rightarrow> 'a rel, 'a rel) binary_fun" where
  "\<psi>_reverse \<phi> r = \<phi> r"

fun reversal\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow>  ('a, 'v) Election rel" where
  "reversal\<^sub>\<R> \<E> = action_induced_rel (carrier reversal\<^sub>\<G>) \<E> (\<phi>_reverse \<E>)"

subsection \<open>Auxiliary Lemmas\<close>

fun n_app :: "nat \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> ('x \<Rightarrow> 'x)" where
  "n_app 0 f = id" |
  "n_app (Suc n) f = f \<circ> n_app n f"

lemma n_app_rewrite:
  fixes
    f :: "'x \<Rightarrow> 'x" and
    n :: "nat" and
    x :: "'x"
  shows "(f \<circ> n_app n f) x = (n_app n f \<circ> f) x"
proof (unfold comp_def, induction n f arbitrary: x rule: n_app.induct)
  case (1 f)
  fix
    f :: "'x \<Rightarrow> 'x" and
    x :: "'x"
  show "f (n_app 0 f x) = n_app 0 f (f x)"
    by simp
next
  case (2 n f)
  fix
    f :: "'x \<Rightarrow> 'x" and
    n :: "nat" and
    x :: "'x"
  assume "\<And> y. f (n_app n f y) = n_app n f (f y)"
  thus "f (n_app (Suc n) f x) = n_app (Suc n) f (f x)"
    by simp
qed

lemma n_app_leaves_set:
  fixes
    A B :: "'x set" and
    f :: "'x \<Rightarrow> 'x" and
    x :: "'x"
  assumes
    fin_A: "finite A" and
    fin_B: "finite B" and
    x_el: "x \<in> A - B" and
    bij: "bij_betw f A B"
  obtains n :: "nat" where
    "n > 0" and
    "n_app n f x \<in> B - A" and
    "\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A \<inter> B"
proof -
  have n_app_f_x_in_A: "n_app 0 f x \<in> A"
    using x_el
    by simp
  moreover have ex_A:
    "\<exists> n > 0. n_app n f x \<in> B - A \<and> (\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A)"
  proof (rule ccontr,
         unfold Diff_iff conj_assoc not_ex de_Morgan_conj not_gr_zero
                simp_thms not_all not_imp disj_not1 imp_disj2)
    assume nex:
      "\<forall> n. n_app n f x \<in> B
          \<longrightarrow> n = 0 \<or> n_app n f x \<in> A \<or> (\<exists> m > 0. m < n \<and> n_app m f x \<notin> A)"
    hence "\<forall> n > 0. n_app n f x \<in> B
            \<longrightarrow> n_app n f x \<in> A \<or> (\<exists> m > 0. m < n \<and> n_app m f x \<notin> A)"
      by blast
    moreover have "\<not> (\<forall> n > 0. n_app n f x \<in> B \<longrightarrow> n_app n f x \<in> A)"
    proof (safe)
      assume in_A: "\<forall> n > 0. n_app n f x \<in> B \<longrightarrow> n_app n f x \<in> A"
      hence "\<forall> n > 0. n_app n f x \<in> A \<longrightarrow> n_app (Suc n) f x \<in> A"
        using n_app.simps bij
        unfolding bij_betw_def
        by force
      hence in_AB_imp_in_AB:
        "\<forall> n > 0. n_app n f x \<in> A \<inter> B \<longrightarrow> n_app (Suc n) f x \<in> A \<inter> B"
        using n_app.simps bij
        unfolding bij_betw_def
        by auto
      have in_int: "\<forall> n > 0. n_app n f x \<in> A \<inter> B"
      proof (clarify)
        fix n :: "nat"
        assume "n > 0"
        thus "n_app n f x \<in> A \<inter> B"
        proof (induction n)
          case 0
          thus ?case
            by safe
        next
          case (Suc n)
          assume "0 < n \<Longrightarrow> n_app n f x \<in> A \<inter> B"
          moreover have "n = 0 \<longrightarrow> n_app (Suc n) f x = f x"
            by simp
          ultimately show "n_app (Suc n) f x \<in> A \<inter> B"
            using x_el bij in_A in_AB_imp_in_AB
            unfolding bij_betw_def
            by blast
        qed
      qed
      hence "{n_app n f x | n. n > 0} \<subseteq> A \<inter> B"
        by blast
      hence "finite {n_app n f x | n. n > 0}"
        using fin_A fin_B rev_finite_subset
        by blast
      moreover have
        "inj_on (\<lambda> n. n_app n f x) {n. n > 0}
          \<longrightarrow> infinite ((\<lambda> n. n_app n f x) ` {n. n > 0})"
        using diff_is_0_eq' finite_imageD finite_nat_set_iff_bounded lessI
              less_imp_diff_less mem_Collect_eq nless_le
        by metis
      moreover have "(\<lambda> n. n_app n f x) ` {n. n > 0} = {n_app n f x | n. n > 0}"
        by auto
      ultimately have "\<not> inj_on (\<lambda> n. n_app n f x) {n. n > 0}"
        by metis
      hence "\<exists> n > 0 . \<exists> m > n. n_app n f x = n_app m f x"
        using linorder_inj_onI' mem_Collect_eq
        by metis
      hence "\<exists> n_min > 0.
          (\<exists> m > n_min. n_app n_min f x = n_app m f x)
        \<and> (\<forall> n < n_min. \<not> (0 < n \<and> (\<exists> m > n. n_app n f x = n_app m f x)))"
        using exists_least_iff[of
                "\<lambda> n. n > 0 \<and> (\<exists> m > n. n_app n f x = n_app m f x)"]
        by presburger
      then obtain n_min :: "nat" where
        n_min_pos: "n_min > 0" and
        "\<exists> m > n_min. n_app n_min f x = n_app m f x" and
        neq: "\<forall> n < n_min. \<not> (n > 0 \<and> (\<exists> m > n. n_app n f x = n_app m f x))"
        by blast
      then obtain m :: "nat" where
        m_gt_n_min: "m > n_min" and
        "n_app n_min f x = f (n_app (m - 1) f x)"
        using comp_apply diff_Suc_1 less_nat_zero_code n_app.elims
        by (metis (mono_tags, lifting))
      moreover have "n_app n_min f x = f (n_app (n_min - 1) f x)"
        using Suc_pred' n_min_pos comp_eq_id_dest id_comp diff_Suc_1
              less_nat_zero_code n_app.elims
        by (metis (mono_tags, opaque_lifting))
      moreover have "n_app (m - 1) f x \<in> A \<and> n_app (n_min - 1) f x \<in> A"
        using in_int x_el n_min_pos m_gt_n_min Diff_iff IntD1 diff_le_self id_apply
              nless_le cancel_comm_monoid_add_class.diff_cancel n_app.simps(1)
        by metis
      ultimately have eq: "n_app (m - 1) f x = n_app (n_min - 1) f x"
        using bij
        unfolding bij_betw_def inj_def inj_on_def
        by simp
      moreover have "m - 1 > n_min - 1"
        using m_gt_n_min n_min_pos
        by simp
      ultimately have case_greater_0: "n_min - 1 > 0 \<longrightarrow> False"
        using neq n_min_pos diff_less zero_less_one
        by metis
      have "n_app (m - 1) f x \<in> B"
        using in_int m_gt_n_min n_min_pos
        by simp
      thus False
        using x_el eq case_greater_0
        by simp
    qed
    ultimately have "\<exists> n > 0. \<exists> m > 0. m < n \<and> n_app m f x \<notin> A"
      by blast
    hence "\<exists> n > 0. n_app n f x \<notin> A \<and> (\<forall> m < n. \<not> (m > 0 \<and> n_app m f x \<notin> A))"
      using exists_least_iff[of "\<lambda> n. n > 0 \<and> n_app n f x \<notin> A"]
      by blast
    then obtain n :: "nat" where
      n_pos: "n > 0" and
      not_in_A: "n_app n f x \<notin> A" and
      less_in_A: "\<forall> m. (0 < m \<and> m < n) \<longrightarrow> n_app m f x \<in> A"
      by blast
    moreover have "n_app 0 f x \<in> A"
      using x_el
      by simp
    ultimately have "n_app (n - 1) f x \<in> A"
      using bot_nat_0.not_eq_extremum diff_less less_numeral_extra(1)
      by metis
    moreover have "n_app n f x = f (n_app (n - 1) f x)"
      using n_app.simps(2) Suc_pred' n_pos comp_eq_id_dest fun.map_id
      by (metis (mono_tags, opaque_lifting))
    ultimately show False
      using bij nex not_in_A n_pos less_in_A
      unfolding bij_betw_def
      by blast
  qed
  ultimately have
    "\<forall> n. (\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A)
            \<longrightarrow> (\<forall> m > 0. m < n \<longrightarrow> n_app (m - 1) f x \<in> A)"
    using bot_nat_0.not_eq_extremum less_imp_diff_less
    by metis
  moreover have "\<forall> m > 0. n_app m f x = f (n_app (m - 1) f x)"
    using bot_nat_0.not_eq_extremum comp_apply diff_Suc_1 n_app.elims
    by (metis (mono_tags, lifting))
  ultimately have
    "\<forall> n. (\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A)
            \<longrightarrow> (\<forall> m > 0. m \<le> n \<longrightarrow> n_app m f x \<in> B)"
    using bij n_app.simps(1) n_app_f_x_in_A diff_Suc_1 gr0_conv_Suc imageI
          linorder_not_le nless_le not_less_eq_eq
    unfolding bij_betw_def
    by metis
  hence "\<exists> n > 0. n_app n f x \<in> B - A
              \<and> (\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A \<inter> B)"
    using IntI nless_le ex_A
    by metis
  thus ?thesis
    using that
    by blast
qed

lemma n_app_rev:
  fixes
    A B :: "'x set" and
    f :: "'x \<Rightarrow> 'x" and
    m n :: "nat" and
    x y :: "'x"
  assumes
    x_in_A: "x \<in> A" and
    y_in_A: "y \<in> A" and
    n_geq_m: "n \<ge> m" and
    n_app_eq_m_n: "n_app n f x = n_app m f y" and
    n_app_x_in_A: "\<forall> n' < n. n_app n' f x \<in> A" and
    n_app_y_in_A: "\<forall> m' < m. n_app m' f y \<in> A" and
    fin_A: "finite A" and
    fin_B: "finite B" and
    bij_f_A_B: "bij_betw f A B"
  shows "n_app (n - m) f x = y"
  using assms
proof (induction n f arbitrary: m x y rule: n_app.induct)
  case (1 f)
  fix
    f :: "'x \<Rightarrow> 'x" and
    m :: "nat" and
    x y :: "'x"
  assume
    "m \<le> 0" and
    "n_app 0 f x = n_app m f y"
  thus "n_app (0 - m) f x = y"
    by simp
next
  case (2 n f)
  fix
    f :: "'x \<Rightarrow> 'x" and
    m n :: "nat" and
    x y :: "'x"
  assume
    bij: "bij_betw f A B" and
    x_in_A: "x \<in> A" and
    y_in_A: "y \<in> A" and
    m_leq_suc_n: "m \<le> Suc n" and
    x_dom: "\<forall> n' < Suc n. n_app n' f x \<in> A" and
    y_dom: "\<forall> m' < m. n_app m' f y \<in> A" and
    eq: "n_app (Suc n) f x = n_app m f y" and
    hyp:
      "\<And> m x y.
           x \<in> A \<Longrightarrow>
           y \<in> A \<Longrightarrow>
           m \<le> n \<Longrightarrow>
           n_app n f x = n_app m f y \<Longrightarrow>
           \<forall> n' < n. n_app n' f x \<in> A \<Longrightarrow>
           \<forall> m' < m. n_app m' f y \<in> A \<Longrightarrow>
           finite A \<Longrightarrow> finite B \<Longrightarrow> bij_betw f A B \<Longrightarrow> n_app (n - m) f x = y"
  hence "m > 0 \<longrightarrow> f (n_app n f x) = f (n_app (m - 1) f y)"
    using Suc_pred' comp_apply n_app.simps(2)
    by (metis (mono_tags, opaque_lifting))
  moreover have "n_app n f x \<in> A"
    using x_in_A x_dom
    by blast
  moreover have "m > 0 \<longrightarrow> n_app (m - 1) f y \<in> A"
    using y_dom
    by simp
  ultimately have "m > 0 \<longrightarrow> n_app n f x = n_app (m - 1) f y"
    using bij
    unfolding bij_betw_def inj_on_def
    by blast
  moreover have "m - 1 \<le> n"
    using m_leq_suc_n
    by simp
  hence "m > 0 \<longrightarrow> n_app (n - (m - 1)) f x = y"
    using hyp x_in_A y_in_A x_dom y_dom Suc_pred fin_A fin_B
          bij calculation less_SucI
    unfolding One_nat_def
    by metis
  hence "m > 0 \<longrightarrow> n_app (Suc n - m) f x = y"
    using Suc_diff_eq_diff_pred
    by presburger
  moreover have "m = 0 \<longrightarrow> n_app (Suc n - m) f x = y"
    using eq
    by simp
  ultimately show "n_app (Suc n - m) f x = y"
    by blast
qed

lemma n_app_inv:
  fixes
    A B :: "'x set" and
    f :: "'x \<Rightarrow> 'x" and
    n :: "nat" and
    x :: "'x"
  assumes
    "x \<in> B" and
    "\<forall> m \<ge> 0. m < n \<longrightarrow> n_app m (the_inv_into A f) x \<in> B" and
    "bij_betw f A B"
  shows "n_app n f (n_app n (the_inv_into A f) x) = x"
  using assms
proof (induction n f arbitrary: x rule: n_app.induct)
  case (1 f)
  fix f :: "'x \<Rightarrow> 'x"
  show ?case
    by simp
next
  case (2 n f)
  fix
    n :: "nat" and
    f :: "'x \<Rightarrow> 'x" and
    x :: "'x"
  assume
    x_in_B: "x \<in> B" and
    bij: "bij_betw f A B" and
    stays_in_B: "\<forall> m \<ge> 0. m < Suc n \<longrightarrow> n_app m (the_inv_into A f) x \<in> B" and
    hyp: "\<And> x. x \<in> B \<Longrightarrow>
             \<forall> m \<ge> 0. m < n \<longrightarrow> n_app m (the_inv_into A f) x \<in> B \<Longrightarrow>
             bij_betw f A B \<Longrightarrow> n_app n f (n_app n (the_inv_into A f) x) = x"
  have "n_app (Suc n) f (n_app (Suc n) (the_inv_into A f) x) =
    n_app n f (f (n_app (Suc n) (the_inv_into A f) x))"
    using n_app_rewrite
    by simp
  also have "\<dots> = n_app n f (n_app n (the_inv_into A f) x)"
    using stays_in_B bij
    by (simp add: f_the_inv_into_f_bij_betw)
  finally show "n_app (Suc n) f (n_app (Suc n) (the_inv_into A f) x) = x"
    using hyp bij stays_in_B x_in_B
    by simp
qed

lemma bij_betw_finite_ind_global_bij:
  fixes
    A B :: "'x set" and
    f :: "'x \<Rightarrow> 'x"
  assumes
    fin_A: "finite A" and
    fin_B: "finite B" and
    bij: "bij_betw f A B"
  obtains g :: "'x \<Rightarrow> 'x" where
    "bij g" and
    "\<forall> a \<in> A. g a = f a" and
    "\<forall> b \<in> B - A. g b \<in> A - B \<and> (\<exists> n > 0. n_app n f (g b) = b)" and
    "\<forall> x \<in> UNIV - A - B. g x = x"
proof -
  assume existence_witness:
    "\<And> g. bij g \<Longrightarrow>
          \<forall> a \<in> A. g a = f a \<Longrightarrow>
          \<forall> b \<in> B - A. g b \<in> A - B \<and> (\<exists> n > 0. n_app n f (g b) = b) \<Longrightarrow>
          \<forall> x \<in> UNIV - A - B. g x = x \<Longrightarrow> ?thesis"
  have bij_inv: "bij_betw (the_inv_into A f) B A"
    using bij bij_betw_the_inv_into
    by blast
  then obtain g' :: "'x \<Rightarrow> nat" where
    greater_0: "\<forall> x \<in> B - A. g' x > 0" and
    in_set_diff: "\<forall> x \<in> B - A. n_app (g' x) (the_inv_into A f) x \<in> A - B" and
    minimal: "\<forall> x \<in> B - A. \<forall> n > 0.
                  n < g' x \<longrightarrow> n_app n (the_inv_into A f) x \<in> B \<inter> A"
    using n_app_leaves_set fin_A fin_B
    by metis
  obtain g :: "'x \<Rightarrow> 'x" where
    def_g:
      "g = (\<lambda> x. if x \<in> A then f x else
                (if x \<in> B - A then n_app (g' x) (the_inv_into A f) x else x))"
    by simp
  hence coincide: "\<forall> a \<in> A. g a = f a"
    by simp
  have id: "\<forall> x \<in> UNIV - A - B. g x = x"
    using def_g
    by simp
  have "\<forall> x \<in> B - A. n_app 0 (the_inv_into A f) x \<in> B"
    by simp
  moreover have
    "\<forall> x \<in> B - A. \<forall> n > 0.
        n < g' x \<longrightarrow> n_app n (the_inv_into A f) x \<in> B"
    using minimal
    by blast
  ultimately have
    "\<forall> x \<in> B - A. n_app (g' x) f (n_app (g' x) (the_inv_into A f) x) = x"
    using n_app_inv bij DiffD1 antisym_conv2
    by metis
  hence "\<forall> x \<in> B - A. n_app (g' x) f (g x) = x"
    using def_g
    by simp
  with greater_0 in_set_diff
  have reverse: "\<forall> x \<in> B - A. g x \<in> A - B \<and> (\<exists> n > 0. n_app n f (g x) = x)"
    using def_g
    by auto
  have "\<forall> x \<in> UNIV - A - B. g x = id x"
    using def_g
    by simp
  hence "g ` (UNIV - A - B) = UNIV - A - B"
    by simp
  moreover have "g ` A = B"
    using def_g bij
    unfolding bij_betw_def
    by simp
  moreover have "A \<union> (UNIV - A - B) = UNIV - (B - A)
                \<and> B \<union> (UNIV - A - B) = UNIV - (A - B)"
    by blast
  ultimately have surj_cases_13: "g ` (UNIV - (B - A)) = UNIV - (A - B)"
    using image_Un
    by metis
  have "inj_on g A \<and> inj_on g (UNIV - A - B)"
    using def_g bij
    unfolding bij_betw_def inj_on_def
    by simp
  hence inj_cases_13: "inj_on g (UNIV - (B - A))"
    unfolding inj_on_def
    using DiffD2 DiffI bij bij_betwE def_g
    by (metis (no_types, lifting))
  have "card A = card B"
    using fin_A fin_B bij bij_betw_same_card
    by blast
  with fin_A fin_B
  have "finite (B - A) \<and> finite (A - B) \<and> card (B - A) = card (A - B)"
    using card_le_sym_Diff finite_Diff2 nle_le
    by metis
  moreover have "(\<lambda> x. n_app (g' x) (the_inv_into A f) x) ` (B - A) \<subseteq> A - B"
    using in_set_diff
    by blast
  moreover have "inj_on (\<lambda> x. n_app (g' x) (the_inv_into A f) x) (B - A)"
    proof (unfold inj_on_def, safe)
    fix x y :: "'x"
    assume
      x_in_B: "x \<in> B" and
      x_not_in_A: "x \<notin> A" and
      y_in_B: "y \<in> B" and
      y_not_in_A: "y \<notin> A" and
      "n_app (g' x) (the_inv_into A f) x = n_app (g' y) (the_inv_into A f) y"
    moreover from this have
      "\<forall> n < g' x. n_app n (the_inv_into A f) x \<in> B" and
      "\<forall> n < g' y. n_app n (the_inv_into A f) y \<in> B"
      using minimal Diff_iff Int_iff bot_nat_0.not_eq_extremum eq_id_iff n_app.simps(1)
      by (metis, metis)
    ultimately have x_to_y:
      "n_app (g' x - g' y) (the_inv_into A f) x = y
        \<or> n_app (g' y - g' x) (the_inv_into A f) y = x"
      using x_in_B y_in_B bij_inv fin_A fin_B
            n_app_rev[of "x"] n_app_rev[of "y" "B" "x" "g' x" "g' y"]
      by fastforce
    hence "g' x \<noteq> g' y \<longrightarrow>
      ((\<exists> n > 0. n < g' x \<and> n_app n (the_inv_into A f) x \<in> B - A) \<or>
      (\<exists> n > 0. n < g' y \<and> n_app n (the_inv_into A f) y \<in> B - A))"
      using greater_0 x_in_B x_not_in_A y_in_B y_not_in_A Diff_iff diff_less_mono2
            diff_zero id_apply less_Suc_eq_0_disj n_app.elims
      by (metis (full_types))
    thus "x = y"
      using minimal x_in_B x_not_in_A y_in_B y_not_in_A x_to_y
      by force
  qed
  ultimately have
    "bij_betw (\<lambda> x. n_app (g' x) (the_inv_into A f) x) (B - A) (A - B)"
    unfolding bij_betw_def
    by (simp add: card_image card_subset_eq)
  hence bij_case2: "bij_betw g (B - A) (A - B)"
    using def_g
    unfolding bij_betw_def inj_on_def
    by simp
  hence "g ` UNIV = UNIV"
    using surj_cases_13 Un_Diff_cancel2 image_Un sup_top_left
    unfolding bij_betw_def
    by metis
  moreover have "inj g"
    using inj_cases_13 bij_case2 DiffD2 DiffI imageI surj_cases_13
    unfolding bij_betw_def inj_def inj_on_def
    by metis
  ultimately have "bij g"
    unfolding bij_def
    by safe
  thus ?thesis
    using coincide id reverse existence_witness
    by blast
qed

lemma bij_betw_ext:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    X :: "'x set" and
    Y :: "'y set"
  assumes "bij_betw f X Y"
  shows "bij_betw (extensional_continuation f X) X Y"
proof -
  have "\<forall> x \<in> X. extensional_continuation f X x = f x"
    by simp
  thus ?thesis
    using assms bij_betw_cong
    by metis
qed

subsection \<open>Anonymity Lemmas\<close>

lemma anon_rel_vote_count:
  fixes
    \<E> :: "('a, 'v) Election set" and
    E E' :: "('a, 'v) Election"
  assumes
    "finite (voters_\<E> E)" and
    "(E, E') \<in> anonymity\<^sub>\<R> \<E>"
  shows "alternatives_\<E> E = alternatives_\<E> E' \<and> E \<in> \<E>
          \<and> (\<forall> p. vote_count p E = vote_count p E')"
proof -
  have "E \<in> \<E>"
    using assms
    unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps
    by safe
  with assms
  obtain \<pi> :: "'v \<Rightarrow> 'v" where
    bijection_\<pi>: "bij \<pi>" and
    renamed: "E' = rename \<pi> E"
    unfolding anonymity\<^sub>\<R>.simps anonymity\<^sub>\<G>_def
    using universal_set_carrier_imp_bij_group
    by auto
  have eq_alts: "alternatives_\<E> E' = alternatives_\<E> E"
    using eq_fst_iff rename.simps alternatives_\<E>.elims renamed
    by (metis (no_types))
  have "\<forall> v \<in> voters_\<E> E'. (profile_\<E> E') v = (profile_\<E> E) (the_inv \<pi> v)"
    unfolding profile_\<E>.simps
    using renamed rename.simps comp_apply prod.collapse snd_conv
    by (metis (no_types, lifting))
  hence rewrite:
    "\<forall> p. {v \<in> (voters_\<E> E'). (profile_\<E> E') v = p} =
            {v \<in> (voters_\<E> E'). (profile_\<E> E) (the_inv \<pi> v) = p}"
    by blast
  have "\<forall> v \<in> voters_\<E> E'. the_inv \<pi> v \<in> voters_\<E> E"
    unfolding voters_\<E>.simps
    using renamed UNIV_I bijection_\<pi> bij_betw_imp_surj bij_is_inj f_the_inv_into_f
          prod.sel inj_image_mem_iff prod.collapse rename.simps
    by (metis (no_types, lifting))
  hence
    "\<forall> p. \<forall> v \<in> voters_\<E> E'. (profile_\<E> E) (the_inv \<pi> v) = p
          \<longrightarrow> v \<in> \<pi> ` {v \<in> voters_\<E> E. (profile_\<E> E) v = p}"
    using bijection_\<pi> f_the_inv_into_f_bij_betw image_iff
    by fastforce
  hence subset:
    "\<forall> p. {v \<in> voters_\<E> E'. (profile_\<E> E) (the_inv \<pi> v) = p} \<subseteq>
            \<pi> ` {v \<in> voters_\<E> E. (profile_\<E> E) v = p}"
    by blast
  from renamed have "\<forall> v \<in> voters_\<E> E. \<pi> v \<in> voters_\<E> E'"
    unfolding voters_\<E>.simps
    using bijection_\<pi> bij_is_inj prod.sel inj_image_mem_iff prod.collapse rename.simps
    by (metis (mono_tags, lifting))
  hence
    "\<forall> p. \<pi> ` {v \<in> voters_\<E> E. (profile_\<E> E) v = p} \<subseteq>
            {v \<in> voters_\<E> E'. (profile_\<E> E) (the_inv \<pi> v) = p}"
    using bijection_\<pi> bij_is_inj the_inv_f_f
    by fastforce
  hence
    "\<forall> p. {v \<in> voters_\<E> E'. (profile_\<E> E') v = p} =
            \<pi> ` {v \<in> voters_\<E> E. (profile_\<E> E) v = p}"
    using subset rewrite
    by (simp add: subset_antisym)
  moreover have
    "\<forall> p. card (\<pi> ` {v \<in> voters_\<E> E. (profile_\<E> E) v = p}) =
            card {v \<in> voters_\<E> E. (profile_\<E> E) v = p}"
    using bijection_\<pi> bij_betw_same_card bij_betw_subset top_greatest
    by (metis (no_types, lifting))
  ultimately show
    "alternatives_\<E> E =
        alternatives_\<E> E' \<and> E \<in> \<E> \<and> (\<forall> p. vote_count p E = vote_count p E')"
    using eq_alts assms

    by simp
qed

lemma vote_count_anon_rel:
  fixes
    \<E> :: "('a, 'v) Election set" and
    E E' :: "('a, 'v) Election"
  assumes
    fin_voters_E: "finite (voters_\<E> E)" and
    fin_voters_E': "finite (voters_\<E> E')" and
    default_non_v: "\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {}" and
    default_non_v': "\<forall> v. v \<notin> voters_\<E> E' \<longrightarrow> profile_\<E> E' v = {}" and
    eq: "alternatives_\<E> E = alternatives_\<E> E' \<and> (E, E') \<in> \<E> \<times> \<E>
          \<and> (\<forall> p. vote_count p E = vote_count p E')"
  shows "(E, E') \<in> anonymity\<^sub>\<R> \<E>"
proof -
  have "\<forall> p. card {v \<in> voters_\<E> E. profile_\<E> E v = p} =
                card {v \<in> voters_\<E> E'. profile_\<E> E' v = p}"
    using eq
    unfolding vote_count.simps
    by blast
  moreover have
    "\<forall> p. finite {v \<in> voters_\<E> E. profile_\<E> E v = p}
          \<and> finite {v \<in> voters_\<E> E'. profile_\<E> E' v = p}"
    using assms
    by simp
  ultimately have
    "\<forall> p. \<exists> \<pi>\<^sub>p. bij_betw \<pi>\<^sub>p
        {v \<in> voters_\<E> E. profile_\<E> E v = p}
          {v \<in> voters_\<E> E'. profile_\<E> E' v = p}"
    using bij_betw_iff_card
    by blast
  then obtain \<pi> :: "'a Preference_Relation \<Rightarrow> ('v \<Rightarrow> 'v)" where
    bij: "\<forall> p. bij_betw (\<pi> p) {v \<in> voters_\<E> E. profile_\<E> E v = p}
                              {v \<in> voters_\<E> E'. profile_\<E> E' v = p}"
    by (metis (no_types))
  obtain \<pi>' :: "'v \<Rightarrow> 'v" where
    \<pi>'_def: "\<forall> v \<in> voters_\<E> E. \<pi>' v = \<pi> (profile_\<E> E v) v"
    by fastforce
  hence "\<forall> v \<in> voters_\<E> E. \<forall> v' \<in> voters_\<E> E.
            \<pi>' v = \<pi>' v' \<longrightarrow> \<pi> (profile_\<E> E v) v = \<pi> (profile_\<E> E v') v'"
    by simp
  moreover have
    "\<forall> w \<in> voters_\<E> E. \<forall> w' \<in> voters_\<E> E.
        \<pi> (profile_\<E> E w) w = \<pi> (profile_\<E> E w') w'
      \<longrightarrow> {v \<in> voters_\<E> E'. profile_\<E> E' v = profile_\<E> E w}
          \<inter> {v \<in> voters_\<E> E'. profile_\<E> E' v = profile_\<E> E w'} \<noteq> {}"
    using bij
    unfolding bij_betw_def
    by blast
  moreover have
    "\<forall> w w'.
    {v \<in> voters_\<E> E'. profile_\<E> E' v = profile_\<E> E w}
      \<inter> {v \<in> voters_\<E> E'. profile_\<E> E' v = profile_\<E> E w'} \<noteq> {}
        \<longrightarrow> profile_\<E> E w = profile_\<E> E w'"
    by blast
  ultimately have eq_prof:
    "\<forall> v \<in> voters_\<E> E. \<forall> v' \<in> voters_\<E> E.
        \<pi>' v = \<pi>' v' \<longrightarrow> profile_\<E> E v = profile_\<E> E v'"
    by blast
  hence "\<forall> v \<in> voters_\<E> E. \<forall> v' \<in> voters_\<E> E.
            \<pi>' v = \<pi>' v' \<longrightarrow> \<pi> (profile_\<E> E v) v = \<pi> (profile_\<E> E v) v'"
    using \<pi>'_def
    by metis
  hence "\<forall> v \<in> voters_\<E> E. \<forall> v' \<in> voters_\<E> E. \<pi>' v = \<pi>' v' \<longrightarrow> v = v'"
    using bij eq_prof mem_Collect_eq
    unfolding bij_betw_def inj_on_def
    by (metis (mono_tags, lifting))
  hence inj: "inj_on \<pi>' (voters_\<E> E)"
    unfolding inj_on_def
    by simp
  have "\<pi>' ` voters_\<E> E = {\<pi> (profile_\<E> E v) v | v. v \<in> voters_\<E> E}"
    using \<pi>'_def
    unfolding Setcompr_eq_image
    by simp
  also have
    "\<dots> = \<Union> {\<pi> p ` {v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    unfolding Union_eq
    by blast
  also have
    "\<dots> = \<Union> {{v \<in> voters_\<E> E'. profile_\<E> E' v = p} | p. p \<in> UNIV}"
    using bij
    unfolding bij_betw_def
    by (metis (mono_tags, lifting))
  finally have "\<pi>' ` voters_\<E> E = voters_\<E> E'"
    by blast
  with inj have bij': "bij_betw \<pi>' (voters_\<E> E) (voters_\<E> E')"
    using bij
    unfolding bij_betw_def
    by blast
  then obtain \<pi>_global :: "'v \<Rightarrow> 'v" where
    bijection_\<pi>\<^sub>g: "bij \<pi>_global" and
    \<pi>_global_eq_\<pi>': "\<forall> v \<in> voters_\<E> E. \<pi>_global v = \<pi>' v" and
    \<pi>_global_eq_n_app_\<pi>':
      "\<forall> v \<in> voters_\<E> E' - voters_\<E> E.
        \<pi>_global v \<in> voters_\<E> E - voters_\<E> E' \<and>
        (\<exists> n > 0. n_app n \<pi>' (\<pi>_global v) = v)" and
    \<pi>_global_non_voters: "\<forall> v \<in> UNIV - voters_\<E> E - voters_\<E> E'. \<pi>_global v = v"
    using fin_voters_E fin_voters_E' bij_betw_finite_ind_global_bij
    by blast
  hence inv: "\<forall> v v'. (\<pi>_global v' = v) = (v' = the_inv \<pi>_global v)"
    using UNIV_I bij_betw_imp_inj_on bij_betw_imp_surj_on f_the_inv_into_f the_inv_f_f
    by metis
  moreover have
    "\<forall> v \<in> UNIV - (voters_\<E> E' - voters_\<E> E).
        \<pi>_global v \<in> UNIV - (voters_\<E> E - voters_\<E> E')"
    using \<pi>_global_eq_\<pi>' \<pi>_global_non_voters bij' bijection_\<pi>\<^sub>g
          DiffD1 DiffD2 DiffI bij_betwE
    by (metis (no_types, lifting))
  ultimately have
    "\<forall> v \<in> voters_\<E> E - voters_\<E> E'.
        the_inv \<pi>_global v \<in> voters_\<E> E' - voters_\<E> E"
    using bijection_\<pi>\<^sub>g \<pi>_global_eq_n_app_\<pi>' DiffD2 DiffI UNIV_I
    by metis
  hence "\<forall> v \<in> voters_\<E> E - voters_\<E> E'. \<forall> n > 0.
              profile_\<E> E (the_inv \<pi>_global v) = {}"
    using default_non_v
    by simp
  moreover have "\<forall> v \<in> voters_\<E> E - voters_\<E> E'. profile_\<E> E' v = {}"
    using default_non_v'
    by simp
  ultimately have case_1:
    "\<forall> v \<in> voters_\<E> E - voters_\<E> E'.
        profile_\<E> E' v = (profile_\<E> E \<circ> the_inv \<pi>_global) v"
    by auto
  have "\<forall> v \<in> voters_\<E> E'. \<exists> v' \<in> voters_\<E> E. \<pi>_global v' = v \<and> \<pi>' v' = v"
    using bij' imageE \<pi>_global_eq_\<pi>'
    unfolding bij_betw_def
    by (metis (mono_tags, opaque_lifting))
  hence "\<forall> v \<in> voters_\<E> E'. \<exists> v' \<in> voters_\<E> E. v' = the_inv \<pi>_global v \<and> \<pi>' v' = v"
    using inv
    by metis
  hence "\<forall> v \<in> voters_\<E> E'.
      the_inv \<pi>_global v \<in> voters_\<E> E \<and> \<pi>' (the_inv \<pi>_global v) = v"
    by blast
  moreover have "\<forall> v' \<in> voters_\<E> E. profile_\<E> E' (\<pi>' v') = profile_\<E> E v'"
    using \<pi>'_def bij bij_betwE mem_Collect_eq
    by fastforce
  ultimately have case_2:
    "\<forall> v \<in> voters_\<E> E'. profile_\<E> E' v = (profile_\<E> E \<circ> the_inv \<pi>_global) v"
    unfolding comp_def
    by metis
  have "\<forall> v \<in> UNIV - voters_\<E> E - voters_\<E> E'.
          profile_\<E> E' v = (profile_\<E> E \<circ> the_inv \<pi>_global) v"
    using \<pi>_global_non_voters default_non_v default_non_v' inv
    by simp
  hence "profile_\<E> E' = profile_\<E> E \<circ> the_inv \<pi>_global"
    using case_1 case_2
    by blast
  moreover have "\<pi>_global ` (voters_\<E> E) = voters_\<E> E'"
    using \<pi>_global_eq_\<pi>' bij' bij_betw_imp_surj_on
    by fastforce
  ultimately have "E' = rename \<pi>_global E"
    using rename.simps eq prod.collapse
    unfolding voters_\<E>.simps profile_\<E>.simps alternatives_\<E>.simps
    by metis
  thus ?thesis
    unfolding extensional_continuation.simps anonymity\<^sub>\<R>.simps
              action_induced_rel.simps \<phi>_anon.simps anonymity\<^sub>\<G>_def
    using eq bijection_\<pi>\<^sub>g case_prodI rewrite_carrier
    by auto
qed

lemma rename_comp:
  fixes \<pi> \<pi>' :: "'v \<Rightarrow> 'v"
  assumes
    "bij \<pi>" and
    "bij \<pi>'"
  shows "rename \<pi> \<circ> rename \<pi>' = rename (\<pi> \<circ> \<pi>')"
proof
  fix E :: "('a, 'v) Election"
  have "rename \<pi>' E =
      (alternatives_\<E> E, \<pi>' ` (voters_\<E> E), (profile_\<E> E) \<circ> (the_inv \<pi>'))"
    unfolding alternatives_\<E>.simps voters_\<E>.simps profile_\<E>.simps
    using prod.collapse rename.simps
    by metis
  hence
    "(rename \<pi> \<circ> rename \<pi>') E =
        rename \<pi> (alternatives_\<E> E, \<pi>' ` (voters_\<E> E), (profile_\<E> E) \<circ> (the_inv \<pi>'))"
    unfolding comp_def
    by presburger
  also have
    "\<dots> = (alternatives_\<E> E, \<pi> ` \<pi>' ` (voters_\<E> E),
            (profile_\<E> E) \<circ> (the_inv \<pi>') \<circ> (the_inv \<pi>))"
    by simp
  also have
    "\<dots> = (alternatives_\<E> E, (\<pi> \<circ> \<pi>') ` (voters_\<E> E),
            (profile_\<E> E) \<circ> the_inv (\<pi> \<circ> \<pi>'))"
    using assms the_inv_comp[of \<pi> _ _ \<pi>']
    unfolding comp_def image_image
    by simp
  finally show "(rename \<pi> \<circ> rename \<pi>') E = rename (\<pi> \<circ> \<pi>') E"
    unfolding alternatives_\<E>.simps voters_\<E>.simps profile_\<E>.simps
    using prod.collapse rename.simps
    by metis
qed

interpretation anonymous_group_action:
  "group_action" "anonymity\<^sub>\<G>" "well_formed_elections" "\<phi>_anon well_formed_elections"
proof (unfold group_action_def group_hom_def anonymity\<^sub>\<G>_def
        group_hom_axioms_def hom_def, intro conjI group_BijGroup, safe)
  fix \<pi> :: "'v \<Rightarrow> 'v"
  assume bij_carrier: "\<pi> \<in> carrier (BijGroup UNIV)"
  hence bij: "bij \<pi>"
    using rewrite_carrier
    by blast
  hence "rename \<pi> ` well_formed_elections = well_formed_elections"
    using rename_surj bij
    by blast
  moreover have "inj_on (rename \<pi>) well_formed_elections"
    using rename_inj bij subset_inj_on
    by blast
  ultimately have "bij_betw (rename \<pi>) well_formed_elections well_formed_elections"
    unfolding bij_betw_def
    by blast
  hence "bij_betw (\<phi>_anon well_formed_elections \<pi>) well_formed_elections well_formed_elections"
    unfolding \<phi>_anon.simps extensional_continuation.simps
    using bij_betw_ext
    by simp
  moreover have "\<phi>_anon well_formed_elections \<pi> \<in> extensional well_formed_elections"
    unfolding extensional_def
    by force
  ultimately show bij_car_elect:
    "\<phi>_anon well_formed_elections \<pi> \<in> carrier (BijGroup well_formed_elections)"
    unfolding BijGroup_def Bij_def
    by simp
  fix \<pi>' :: "'v \<Rightarrow> 'v"
  assume bij_carrier: "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence bij': "bij \<pi>'"
    using rewrite_carrier
    by blast
  hence "rename \<pi>' ` well_formed_elections = well_formed_elections"
    using rename_surj bij
    by blast
  moreover have "inj_on (rename \<pi>') well_formed_elections"
    using rename_inj bij' subset_inj_on
    by blast
  ultimately have "bij_betw (rename \<pi>') well_formed_elections well_formed_elections"
    unfolding bij_betw_def
    by blast
  hence "bij_betw (\<phi>_anon well_formed_elections \<pi>') well_formed_elections well_formed_elections"
    unfolding \<phi>_anon.simps extensional_continuation.simps
    using bij_betw_ext
    by simp
  moreover from this have wf_closed':
    "\<phi>_anon well_formed_elections \<pi>' ` well_formed_elections \<subseteq> well_formed_elections"
    using bij_betw_imp_surj_on
    by blast
  moreover have "\<phi>_anon well_formed_elections \<pi>' \<in> extensional well_formed_elections"
    unfolding extensional_def
    by force
  ultimately have bij_car_elect':
    "\<phi>_anon well_formed_elections \<pi>' \<in> carrier (BijGroup well_formed_elections)"
    unfolding BijGroup_def Bij_def
    by simp
  have
    "\<phi>_anon well_formed_elections \<pi>
        \<otimes> \<^bsub>BijGroup well_formed_elections\<^esub> (\<phi>_anon well_formed_elections) \<pi>' =
      extensional_continuation
        (\<phi>_anon well_formed_elections \<pi> \<circ> \<phi>_anon well_formed_elections \<pi>') well_formed_elections"
    using rewrite_mult bij_car_elect bij_car_elect'
    by blast
  moreover have
    "\<forall> E \<in> well_formed_elections.
      extensional_continuation
        (\<phi>_anon well_formed_elections \<pi> \<circ> \<phi>_anon well_formed_elections \<pi>')
          well_formed_elections E =
        (\<phi>_anon well_formed_elections \<pi> \<circ> \<phi>_anon well_formed_elections \<pi>') E"
    by simp
  moreover have
    "\<forall> E \<in> well_formed_elections.
          (\<phi>_anon well_formed_elections \<pi> \<circ> \<phi>_anon well_formed_elections \<pi>') E =
          rename \<pi> (rename \<pi>' E)"
    unfolding \<phi>_anon.simps
    using wf_closed'
    by auto
  moreover have
    "\<forall> E \<in> well_formed_elections. rename \<pi> (rename \<pi>' E) = rename (\<pi> \<circ> \<pi>') E"
    using rename_comp bij bij' comp_apply
    by metis
  moreover have
    "\<forall> E \<in> well_formed_elections. rename (\<pi> \<circ> \<pi>') E =
          \<phi>_anon well_formed_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') E"
    unfolding \<phi>_anon.simps
    using rewrite_mult_univ bij bij' rewrite_carrier mem_Collect_eq
    by fastforce
  moreover have
    "\<forall> E. E \<notin> well_formed_elections
        \<longrightarrow> extensional_continuation
              (\<phi>_anon well_formed_elections \<pi>
                \<circ> \<phi>_anon well_formed_elections \<pi>') well_formed_elections E =
          undefined"
    by simp
  moreover have
    "\<forall> E. E \<notin> well_formed_elections
            \<longrightarrow> \<phi>_anon well_formed_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') E =
                  undefined"
    by simp
  ultimately have
    "\<forall> E. \<phi>_anon well_formed_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') E =
          (\<phi>_anon well_formed_elections \<pi>
            \<otimes> \<^bsub>BijGroup well_formed_elections\<^esub> \<phi>_anon well_formed_elections \<pi>') E"
    by metis
  thus "\<phi>_anon well_formed_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') =
      \<phi>_anon well_formed_elections \<pi>
        \<otimes> \<^bsub>BijGroup well_formed_elections\<^esub> \<phi>_anon well_formed_elections \<pi>'"
    by blast
qed

lemma (in result) anonymity:
  "is_symmetry (\<lambda> E. limit (alternatives_\<E> E) UNIV)
          (Invariance (anonymity\<^sub>\<R> well_formed_elections))"
  unfolding anonymity\<^sub>\<R>.simps
  by clarsimp

subsection \<open>Neutrality Lemmas\<close>

lemma rel_rename_helper:
  fixes
    r :: "'a rel" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    a b :: "'a"
  assumes "bij \<pi>"
  shows "(\<pi> a, \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> r}
            \<longleftrightarrow> (a, b) \<in> {(x, y) | x y. (x, y) \<in> r}"
proof (safe)
  fix x y :: "'a"
  assume
    "(x, y) \<in> r" and
    "\<pi> a = \<pi> x" and
    "\<pi> b = \<pi> y"
  thus "\<exists> x y. (a, b) = (x, y) \<and> (x, y) \<in> r"
    using assms bij_is_inj the_inv_f_f
    by metis
next
  fix x y :: "'a"
  assume "(a, b) \<in> r"
  thus "\<exists> x y. (\<pi> a, \<pi> b) = (\<pi> x, \<pi> y) \<and> (x, y) \<in> r"
    by metis
qed

lemma rel_rename_comp:
  fixes \<pi> \<pi>' :: "'a \<Rightarrow> 'a"
  shows "rel_rename (\<pi> \<circ> \<pi>') = rel_rename \<pi> \<circ> rel_rename \<pi>'"
proof
  fix r :: "'a rel"
  have "rel_rename (\<pi> \<circ> \<pi>') r = {(\<pi> (\<pi>' a), \<pi> (\<pi>' b)) | a b. (a, b) \<in> r}"
    by simp
  also have "\<dots> = {(\<pi> a, \<pi> b) | a b. (a, b) \<in> rel_rename \<pi>' r}"
    unfolding rel_rename.simps
    by blast
  finally show "rel_rename (\<pi> \<circ> \<pi>') r = (rel_rename \<pi> \<circ> rel_rename \<pi>') r"
    unfolding comp_def
    by simp
qed

lemma rel_rename_sound:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    r :: "'a rel" and
    A :: "'a set"
  assumes "inj \<pi>"
  shows
    "refl_on A r \<longrightarrow> refl_on (\<pi> ` A) (rel_rename \<pi> r)" and
    "antisym r \<longrightarrow> antisym (rel_rename \<pi> r)" and
    "total_on A r \<longrightarrow> total_on (\<pi> ` A) (rel_rename \<pi> r)" and
    "Relation.trans r \<longrightarrow> Relation.trans (rel_rename \<pi> r)"
proof (unfold antisym_def total_on_def Relation.trans_def, safe)
  assume "refl_on A r"
  thus "refl_on (\<pi> ` A) (rel_rename \<pi> r)"
    unfolding refl_on_def rel_rename.simps
    by blast
next
  fix a b :: "'a"
  assume
    "(a, b) \<in> rel_rename \<pi> r" and
    "(b, a) \<in> rel_rename \<pi> r"
  then obtain
    c c' d d' :: "'a" where
      c_rel_d: "(c, d) \<in> r" and
      d'_rel_c': "(d', c') \<in> r" and
      \<pi>\<^sub>c_eq_a: "\<pi> c = a" and
      \<pi>\<^sub>c'_eq_a: "\<pi> c' = a" and
      \<pi>\<^sub>d_eq_b: "\<pi> d = b" and
      \<pi>\<^sub>d'_eq_b: "\<pi> d' = b"
    unfolding rel_rename.simps
    by auto
  hence "c = c' \<and> d = d'"
    using assms
    unfolding inj_def
    by presburger
  moreover assume "\<forall> a b. (a, b) \<in> r \<longrightarrow> (b, a) \<in> r \<longrightarrow> a = b"
  ultimately have "c = d"
    using d'_rel_c' c_rel_d
    by simp
  thus "a = b"
    using \<pi>\<^sub>c_eq_a \<pi>\<^sub>d_eq_b
    by simp
next
  fix a b :: "'a"
  assume
    total: "\<forall> x \<in> A. \<forall> y \<in> A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    \<pi>\<^sub>a_neq_\<pi>\<^sub>b: "\<pi> a \<noteq> \<pi> b" and
    \<pi>\<^sub>b_not_rel_\<pi>\<^sub>a: "(\<pi> b, \<pi> a) \<notin> rel_rename \<pi> r"
  hence "(b, a) \<notin> r \<and> a \<noteq> b"
    unfolding rel_rename.simps
    by blast
  hence "(a, b) \<in> r"
    using a_in_A b_in_A total
    by blast
  thus "(\<pi> a, \<pi> b) \<in> rel_rename \<pi> r"
    unfolding rel_rename.simps
    by blast
next
  fix a b c :: "'a"
  assume
    "(a, b) \<in> rel_rename \<pi> r" and
    "(b, c) \<in> rel_rename \<pi> r"
  then obtain
    d e s t :: "'a" where
      d_rel_e: "(d, e) \<in> r" and
      s_rel_t: "(s, t) \<in> r" and
      \<pi>\<^sub>d_eq_a: "\<pi> d = a" and
      \<pi>\<^sub>s_eq_b: "\<pi> s = b" and
      \<pi>\<^sub>t_eq_c: "\<pi> t = c" and
      \<pi>\<^sub>e_eq_b: "\<pi> e = b"
    unfolding alternatives_\<E>.simps voters_\<E>.simps profile_\<E>.simps
    using rel_rename.simps Pair_inject mem_Collect_eq
    by auto
  hence "s = e"
    using assms rangeI range_ex1_eq
    by metis
  hence "(d, e) \<in> r \<and> (e, t) \<in> r"
    using d_rel_e s_rel_t
    by simp
  moreover assume "\<forall> x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
  ultimately have "(d, t) \<in> r"
    by blast
  thus "(a, c) \<in> rel_rename \<pi> r"
    unfolding rel_rename.simps
    using \<pi>\<^sub>d_eq_a \<pi>\<^sub>t_eq_c
    by blast
qed

lemma rename_subset:
  fixes
    r s :: "'a rel" and
    a b :: "'a" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assumes
    bij_\<pi>: "bij \<pi>"and
    "rel_rename \<pi> r = rel_rename \<pi> s" and
    "(a, b) \<in> r"
  shows "(a, b) \<in> s"
proof -
  have "(\<pi> a, \<pi> b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> s}"
    using assms
    unfolding rel_rename.simps
    by blast
  hence "\<exists> c d. (c, d) \<in> s \<and> \<pi> c = \<pi> a \<and> \<pi> d = \<pi> b"
    by fastforce
  moreover have "\<forall> c d. \<pi> c = \<pi> d \<longrightarrow> c = d"
    using bij_\<pi> bij_pointE
    by metis
  ultimately show "(a, b) \<in> s"
    by blast
qed

lemma rel_rename_bij:
  fixes \<pi> :: "'a \<Rightarrow> 'a"
  assumes bij_\<pi>: "bij \<pi>"
  shows "bij (rel_rename \<pi>)"
proof (unfold bij_def inj_def surj_def, safe)
  fix
    r s :: "'a rel" and
    a b :: "'a"
  assume rename: "rel_rename \<pi> r = rel_rename \<pi> s"
  {
    moreover assume "(a, b) \<in> r"
    ultimately have "(\<pi> a, \<pi> b) \<in> {(\<pi> a, \<pi> b) | a b. (a, b) \<in> s}"
      unfolding rel_rename.simps
      by blast
    hence "\<exists> c d. (c, d) \<in> s \<and> \<pi> c = \<pi> a \<and> \<pi> d = \<pi> b"
      by fastforce
    moreover have "\<forall> c d. \<pi> c = \<pi> d \<longrightarrow> c = d"
      using bij_\<pi> bij_pointE
      by metis
    ultimately show subset: "(a, b) \<in> s"
      by blast
  }
  moreover assume "(a, b) \<in> s"
  ultimately show "(a, b) \<in> r"
    using rename rename_subset bij_\<pi>
    by (metis (no_types))
next
  fix r :: "'a rel"
  have "rel_rename \<pi> {((the_inv \<pi>) a, (the_inv \<pi>) b) | a b. (a, b) \<in> r} =
          {(\<pi> ((the_inv \<pi>) a), \<pi> ((the_inv \<pi>) b)) | a b. (a, b) \<in> r}"
    by auto
  also have "\<dots> = {(a, b) | a b. (a, b) \<in> r}"
    using the_inv_f_f bij_\<pi>
    by (simp add: f_the_inv_into_f_bij_betw)
  finally have "rel_rename \<pi> (rel_rename (the_inv \<pi>) r) = r"
    by simp
  thus "\<exists> s. r = rel_rename \<pi> s"
    by blast
qed

lemma alternatives_rename_comp:
  fixes \<pi> \<pi>' :: "'a \<Rightarrow> 'a"
  shows "alternatives_rename \<pi> \<circ> alternatives_rename \<pi>' = alternatives_rename (\<pi> \<circ> \<pi>')"
proof
  fix \<E> :: "('a, 'v) Election"
  have "(alternatives_rename \<pi> \<circ> alternatives_rename \<pi>') \<E> =
      (\<pi> ` \<pi>' ` (alternatives_\<E> \<E>), voters_\<E> \<E>,
        (rel_rename \<pi>) \<circ> (rel_rename \<pi>') \<circ> (profile_\<E> \<E>))"
    by (simp add: fun.map_comp)
  also have
    "\<dots> = ((\<pi> \<circ> \<pi>') ` (alternatives_\<E> \<E>), voters_\<E> \<E>,
              (rel_rename (\<pi> \<circ> \<pi>')) \<circ> (profile_\<E> \<E>))"
    using rel_rename_comp image_comp
    by metis
  also have "\<dots> = alternatives_rename (\<pi> \<circ> \<pi>') \<E>"
    by simp
  finally show
    "(alternatives_rename \<pi> \<circ> alternatives_rename \<pi>') \<E> =
        alternatives_rename (\<pi> \<circ> \<pi>') \<E>"
    by blast
qed

lemma well_formed_elects_closed:
  fixes
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assumes
    bij_\<pi>: "bij \<pi>" and
    wf_elects: "(A, V, p) \<in> well_formed_elections" and
    renamed: "(A', V', p') = alternatives_rename \<pi> (A, V, p)"
  shows "(A', V', p') \<in> well_formed_elections"
proof -
  have
    "A' = \<pi> ` A" and
    "V = V'"
    using renamed
    by (simp, simp)
  moreover from this have "\<forall> v \<in> V'. linear_order_on A (p v)"
    using wf_elects
    unfolding well_formed_elections_def profile_def
    by simp
  moreover have "\<forall> v \<in> V'. p' v = rel_rename \<pi> (p v)"
    using renamed
    by simp
  ultimately have "\<forall> v \<in> V'. linear_order_on A' (p' v)"
    unfolding linear_order_on_def partial_order_on_def preorder_on_def
    using bij_\<pi> rel_rename_sound bij_is_inj
    by metis
  thus "(A', V', p') \<in> well_formed_elections"
    unfolding well_formed_elections_def profile_def
    by simp
qed

lemma alternatives_rename_bij:
  fixes \<pi> :: "('a \<Rightarrow> 'a)"
  assumes bij_\<pi>: "bij \<pi>"
  shows "bij_betw (alternatives_rename \<pi>) well_formed_elections well_formed_elections"
proof (unfold bij_betw_def, safe, intro inj_onI, clarify)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assume
    renamed: "alternatives_rename \<pi> (A, V, p) = alternatives_rename \<pi> (A', V', p')"
  hence
    \<pi>_eq_img_A_A': "\<pi> ` A = \<pi> ` A'" and
    rel_rename_eq: "rel_rename \<pi> \<circ> p = rel_rename \<pi> \<circ> p'"
    by (simp, simp)
  hence "(the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> \<circ> p =
            (the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> \<circ> p'"
    using fun.map_comp
    by metis
  also have "(the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> = id"
    using bij_\<pi> rel_rename_bij inv_o_cancel surj_imp_inv_eq the_inv_f_f
    unfolding bij_betw_def
    by (metis (no_types, opaque_lifting))
  finally have "p = p'"
    by simp
  hence
    "A = A'" and
    "p = p'"
    using bij_\<pi> \<pi>_eq_img_A_A' bij_betw_imp_inj_on inj_image_eq_iff
    by (metis, safe)
  thus "A = A' \<and> (V, p) = (V', p')"
    using renamed
    by simp
next
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assume renamed: "(A', V', p') = alternatives_rename \<pi> (A, V, p)"
  hence rewr: "V = V' \<and> A' = \<pi> ` A"
    by simp
  moreover assume "(A, V, p) \<in> well_formed_elections"
  ultimately have "\<forall> v \<in> V'. linear_order_on A (p v)"
    unfolding well_formed_elections_def profile_def
    by simp
  moreover have "\<forall> v \<in> V'. p' v = rel_rename \<pi> (p v)"
    using renamed
    by simp
  ultimately have "\<forall> v \<in> V'. linear_order_on A' (p' v)"
    unfolding linear_order_on_def partial_order_on_def preorder_on_def
    using rewr rel_rename_sound bij_is_inj assms
    by metis
  thus "(A', V', p') \<in> well_formed_elections"
    unfolding well_formed_elections_def profile_def
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume wf_elects: "(A, V, p) \<in> well_formed_elections"
  have rename_inv:
    "alternatives_rename (the_inv \<pi>) (A, V, p) =
        ((the_inv \<pi>) ` A, V, rel_rename (the_inv \<pi>) \<circ> p)"
    by simp
  also have
    "alternatives_rename \<pi> ((the_inv \<pi>) ` A, V, rel_rename (the_inv \<pi>) \<circ> p) =
      (\<pi> ` (the_inv \<pi>) ` A, V, rel_rename \<pi> \<circ> rel_rename (the_inv \<pi>) \<circ> p)"
    by auto
  also have "\<dots> = (A, V, rel_rename (\<pi> \<circ> the_inv \<pi>) \<circ> p)"
    using bij_\<pi> rel_rename_comp[of \<pi>] the_inv_f_f
    by (simp add: bij_betw_imp_surj_on bij_is_inj f_the_inv_into_f image_comp)
  also have "(A, V, rel_rename (\<pi> \<circ> the_inv \<pi>) \<circ> p) = (A, V, rel_rename id \<circ> p)"
    using UNIV_I assms comp_apply f_the_inv_into_f_bij_betw id_apply
    by metis
  finally have
    "alternatives_rename \<pi> (alternatives_rename (the_inv \<pi>) (A, V, p)) =
        (A, V, p)"
    unfolding rel_rename.simps
    by auto
  moreover have "alternatives_rename (the_inv \<pi>) (A, V, p) \<in> well_formed_elections"
    using rename_inv wf_elects well_formed_elects_closed bij_\<pi> bij_betw_the_inv_into
    by (metis (no_types))
  ultimately show "(A, V, p) \<in> alternatives_rename \<pi> ` well_formed_elections"
    using image_eqI
    by metis
qed

interpretation \<phi>_neutral_action:
  group_action "neutrality\<^sub>\<G>" "well_formed_elections" "\<phi>_neutral well_formed_elections"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def
              neutrality\<^sub>\<G>_def, intro conjI group_BijGroup, safe)
  fix \<pi> :: "'a \<Rightarrow> 'a"
  assume bij_carrier: "\<pi> \<in> carrier (BijGroup UNIV)"
  hence bij:
    "bij_betw (\<phi>_neutral well_formed_elections \<pi>) well_formed_elections well_formed_elections"
    using universal_set_carrier_imp_bij_group alternatives_rename_bij bij_betw_ext
    unfolding \<phi>_neutral.simps
    by metis
  thus bij_carrier_elect:
    "\<phi>_neutral well_formed_elections \<pi> \<in> carrier (BijGroup well_formed_elections)"
    unfolding \<phi>_neutral.simps BijGroup_def Bij_def extensional_def
    by simp
  fix \<pi>' :: "'a \<Rightarrow> 'a"
  assume bij_carrier': "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence bij':
    "bij_betw (\<phi>_neutral well_formed_elections \<pi>') well_formed_elections well_formed_elections"
    using universal_set_carrier_imp_bij_group alternatives_rename_bij bij_betw_ext
    unfolding \<phi>_neutral.simps
    by metis
  hence bij_carrier_elect':
    "\<phi>_neutral well_formed_elections \<pi>' \<in> carrier (BijGroup well_formed_elections)"
    unfolding \<phi>_neutral.simps BijGroup_def Bij_def extensional_def
    by simp
  hence carrier_elects:
    "\<phi>_neutral well_formed_elections \<pi> \<in> carrier (BijGroup well_formed_elections)
      \<and> \<phi>_neutral well_formed_elections \<pi>' \<in> carrier (BijGroup well_formed_elections)"
    using bij_carrier_elect
    by metis
  hence "bij_betw (\<phi>_neutral well_formed_elections \<pi>') well_formed_elections well_formed_elections"
    unfolding BijGroup_def Bij_def extensional_def
    by auto
  hence wf_closed':
    "\<phi>_neutral well_formed_elections \<pi>' ` well_formed_elections \<subseteq> well_formed_elections"
    using bij_betw_imp_surj_on
    by blast
  have "\<phi>_neutral well_formed_elections \<pi>
            \<otimes> \<^bsub>BijGroup well_formed_elections\<^esub> \<phi>_neutral well_formed_elections \<pi>' =
      extensional_continuation
        (\<phi>_neutral well_formed_elections \<pi> \<circ> \<phi>_neutral well_formed_elections \<pi>')
              well_formed_elections"
    using carrier_elects rewrite_mult
    by auto
  moreover have
    "\<forall> \<E> \<in> well_formed_elections. extensional_continuation
        (\<phi>_neutral well_formed_elections \<pi> \<circ> \<phi>_neutral well_formed_elections \<pi>')
            well_formed_elections \<E> =
          (\<phi>_neutral well_formed_elections \<pi> \<circ> \<phi>_neutral well_formed_elections \<pi>') \<E>"
    by simp
  moreover have
    "\<forall> \<E> \<in> well_formed_elections.
      (\<phi>_neutral well_formed_elections \<pi> \<circ> \<phi>_neutral well_formed_elections \<pi>') \<E> =
        alternatives_rename \<pi> (alternatives_rename \<pi>' \<E>)"
    unfolding \<phi>_neutral.simps
    using wf_closed'
    by auto
  moreover have
    "\<forall> \<E> \<in> well_formed_elections.
        alternatives_rename \<pi> (alternatives_rename \<pi>' \<E>) =
            alternatives_rename (\<pi> \<circ> \<pi>') \<E>"
    using alternatives_rename_comp comp_apply
    by metis
  moreover have
    "\<forall> \<E> \<in> well_formed_elections. alternatives_rename (\<pi> \<circ> \<pi>') \<E> =
        \<phi>_neutral well_formed_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') \<E>"
    using rewrite_mult_univ bij_carrier bij_carrier'
    unfolding \<phi>_anon.simps \<phi>_neutral.simps extensional_continuation.simps
    by metis
  moreover have
    "\<forall> \<E>. \<E> \<notin> well_formed_elections \<longrightarrow>
      extensional_continuation
        (\<phi>_neutral well_formed_elections \<pi> \<circ> \<phi>_neutral well_formed_elections \<pi>')
            well_formed_elections \<E> = undefined"
    by simp
  moreover have
    "\<forall> \<E>. \<E> \<notin> well_formed_elections
            \<longrightarrow> \<phi>_neutral well_formed_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') \<E> = undefined"
    by simp
  ultimately have
    "\<forall> \<E>. \<phi>_neutral well_formed_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') \<E> =
      (\<phi>_neutral well_formed_elections \<pi>
          \<otimes> \<^bsub>BijGroup well_formed_elections\<^esub> \<phi>_neutral well_formed_elections \<pi>') \<E>"
    by metis
  thus
    "\<phi>_neutral well_formed_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') =
      \<phi>_neutral well_formed_elections \<pi>
          \<otimes> \<^bsub>BijGroup well_formed_elections\<^esub> \<phi>_neutral well_formed_elections \<pi>'"
    by blast
qed

interpretation \<psi>_neutral\<^sub>\<c>_action: "group_action" "neutrality\<^sub>\<G>" "UNIV" "\<psi>_neutral\<^sub>\<c>"
proof (unfold group_action_def group_hom_def hom_def neutrality\<^sub>\<G>_def
              group_hom_axioms_def, intro conjI group_BijGroup, safe)
  fix \<pi> :: "'a \<Rightarrow> 'a"
  assume "\<pi> \<in> carrier (BijGroup UNIV)"
  hence "bij \<pi>"
    unfolding BijGroup_def Bij_def
    by simp
  thus "\<psi>_neutral\<^sub>\<c> \<pi> \<in> carrier (BijGroup UNIV)"
    unfolding \<psi>_neutral\<^sub>\<c>.simps
    using rewrite_carrier
    by blast
  fix \<pi>' :: "'a \<Rightarrow> 'a"
  show "\<psi>_neutral\<^sub>\<c> (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') =
           \<psi>_neutral\<^sub>\<c> \<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<psi>_neutral\<^sub>\<c> \<pi>'"
    unfolding \<psi>_neutral\<^sub>\<c>.simps
    by safe
qed

interpretation \<psi>_neutral\<^sub>\<w>_action: group_action "neutrality\<^sub>\<G>" "UNIV" "\<psi>_neutral\<^sub>\<w>"
proof (unfold group_action_def group_hom_def hom_def neutrality\<^sub>\<G>_def
              group_hom_axioms_def, intro conjI group_BijGroup, safe)
  fix \<pi> :: "'a \<Rightarrow> 'a"
  assume bij_carrier: "\<pi> \<in> carrier (BijGroup UNIV)"
  hence "bij \<pi>"
    unfolding neutrality\<^sub>\<G>_def BijGroup_def Bij_def
    by simp
  hence "bij (\<psi>_neutral\<^sub>\<w> \<pi>)"
    unfolding neutrality\<^sub>\<G>_def BijGroup_def Bij_def \<psi>_neutral\<^sub>\<w>.simps
    using rel_rename_bij
    by blast
  thus group_elem: "\<psi>_neutral\<^sub>\<w> \<pi> \<in> carrier (BijGroup UNIV)"
    using rewrite_carrier
    by blast
  moreover fix \<pi>' :: "'a \<Rightarrow> 'a"
  assume bij_carrier': "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence "bij \<pi>'"
    unfolding neutrality\<^sub>\<G>_def BijGroup_def Bij_def
    by simp
  hence "bij (\<psi>_neutral\<^sub>\<w> \<pi>')"
    unfolding neutrality\<^sub>\<G>_def BijGroup_def Bij_def \<psi>_neutral\<^sub>\<w>.simps
    using rel_rename_bij
    by blast
  hence group_elem': "\<psi>_neutral\<^sub>\<w> \<pi>' \<in> carrier (BijGroup UNIV)"
    using rewrite_carrier
    by blast
  moreover have "\<psi>_neutral\<^sub>\<w> (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') = \<psi>_neutral\<^sub>\<w> (\<pi> \<circ> \<pi>')"
    using bij_carrier bij_carrier' rewrite_mult_univ
    by metis
  ultimately show
    "\<psi>_neutral\<^sub>\<w> (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') =
          \<psi>_neutral\<^sub>\<w> \<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<psi>_neutral\<^sub>\<w> \<pi>'"
    using rewrite_mult_univ
    by fastforce
qed

lemma neutrality_\<S>\<C>\<F>:
  "is_symmetry (\<lambda> \<E>. limit_\<S>\<C>\<F> (alternatives_\<E> \<E>) UNIV)
            (action_induced_equivariance (carrier neutrality\<^sub>\<G>) well_formed_elections
                                (\<phi>_neutral well_formed_elections) (set_action \<psi>_neutral\<^sub>\<c>))"
proof (unfold rewrite_equivariance, safe)
  fix
    \<pi> :: "'a \<Rightarrow> 'a" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "'v \<Rightarrow> ('a \<times> 'a) set" and
    r :: "'a"
  assume
    carrier_\<pi>: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    prof: "(A, V, p) \<in> well_formed_elections"
  {
    moreover assume
      "r \<in> limit_\<S>\<C>\<F> (alternatives_\<E> (\<phi>_neutral well_formed_elections \<pi> (A, V, p))) UNIV"
    ultimately show
      "r \<in> set_action \<psi>_neutral\<^sub>\<c> \<pi> (limit_\<S>\<C>\<F> (alternatives_\<E> (A, V, p)) UNIV)"
      by auto
  }
  {
    moreover assume
      "r \<in> set_action \<psi>_neutral\<^sub>\<c> \<pi> (limit_\<S>\<C>\<F> (alternatives_\<E> (A, V, p)) UNIV)"
    ultimately show
      "r \<in> limit_\<S>\<C>\<F> (alternatives_\<E> (\<phi>_neutral well_formed_elections \<pi> (A, V, p))) UNIV"
      using prof
      by simp
  }
qed

lemma neutrality_\<S>\<W>\<F>:
  "is_symmetry (\<lambda> \<E>. limit_\<S>\<W>\<F> (alternatives_\<E> \<E>) UNIV)
            (action_induced_equivariance (carrier neutrality\<^sub>\<G>) well_formed_elections
                                (\<phi>_neutral well_formed_elections) (set_action \<psi>_neutral\<^sub>\<w>))"
proof (unfold rewrite_equivariance voters_\<E>.simps profile_\<E>.simps set_action.simps,
        safe)
  show "\<And> \<pi> A V p r.
          \<pi> \<in> carrier neutrality\<^sub>\<G> \<Longrightarrow> (A, V, p) \<in> well_formed_elections
        \<Longrightarrow> r \<in> limit_\<S>\<W>\<F>
          (alternatives_\<E> (\<phi>_neutral well_formed_elections \<pi> (A, V , p))) UNIV
        \<Longrightarrow> r \<in> \<psi>_neutral\<^sub>\<w> \<pi> ` limit_\<S>\<W>\<F> (alternatives_\<E> (A, V, p)) UNIV"
  proof -
    fix
      \<pi> :: "'c \<Rightarrow> 'c" and
      A :: "'c set" and
      V :: "'v set" and
      p :: "('c, 'v) Profile" and
      r :: "'c rel"
    let ?r_inv = "\<psi>_neutral\<^sub>\<w> (the_inv \<pi>) r"
    assume
      carrier_\<pi>: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
      prof: "(A, V, p) \<in> well_formed_elections"
    have inv_carrier: "the_inv \<pi> \<in> carrier neutrality\<^sub>\<G>"
      using carrier_\<pi> bij_betw_the_inv_into
      unfolding neutrality\<^sub>\<G>_def rewrite_carrier
      by simp
    moreover have "the_inv \<pi> \<circ> \<pi> = id"
      using carrier_\<pi> universal_set_carrier_imp_bij_group bij_is_inj the_inv_f_f
      unfolding neutrality\<^sub>\<G>_def
      by fastforce
    moreover have "\<one> \<^bsub>neutrality\<^sub>\<G>\<^esub> = id"
      unfolding neutrality\<^sub>\<G>_def BijGroup_def
      by auto
    ultimately have "the_inv \<pi> \<otimes> \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> = \<one> \<^bsub>neutrality\<^sub>\<G>\<^esub>"
      using carrier_\<pi> rewrite_mult_univ
      unfolding neutrality\<^sub>\<G>_def
      by metis
    hence "inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> = the_inv \<pi>"
      using carrier_\<pi> inv_carrier \<psi>_neutral\<^sub>\<c>_action.group_hom group.inv_closed
            group.inv_solve_right group.l_inv group_BijGroup group_hom.hom_one
            group_hom.one_closed
      unfolding neutrality\<^sub>\<G>_def
      by metis
    hence neutral_r: "r = \<psi>_neutral\<^sub>\<w> \<pi> ?r_inv"
      using carrier_\<pi> inv_carrier iso_tuple_UNIV_I \<psi>_neutral\<^sub>\<w>_action.orbit_sym_aux
      by metis
    have bij_inv: "bij (the_inv \<pi>)"
      using carrier_\<pi> bij_betw_the_inv_into universal_set_carrier_imp_bij_group
      unfolding neutrality\<^sub>\<G>_def
      by blast
    hence the_inv_\<pi>: "(the_inv \<pi>) ` \<pi> ` A = A"
      using carrier_\<pi> UNIV_I bij_betw_imp_surj universal_set_carrier_imp_bij_group
            f_the_inv_into_f_bij_betw image_f_inv_f surj_imp_inv_eq
      unfolding neutrality\<^sub>\<G>_def
      by metis
    assume
      "r \<in> limit_\<S>\<W>\<F> (alternatives_\<E> (\<phi>_neutral well_formed_elections \<pi> (A, V, p))) UNIV"
    hence "r \<in> limit_\<S>\<W>\<F> (\<pi> ` A) UNIV"
      unfolding \<phi>_neutral.simps
      using prof
      by simp
    hence lin: "linear_order_on (\<pi> ` A) r"
      by auto
    hence lin_inv: "linear_order_on A ?r_inv"
      using rel_rename_sound bij_inv bij_is_inj the_inv_\<pi>
      unfolding \<psi>_neutral\<^sub>\<w>.simps linear_order_on_def preorder_on_def partial_order_on_def
      by metis
    hence "\<forall> (a, b) \<in> ?r_inv. a \<in> A \<and> b \<in> A"
      using linear_order_on_def partial_order_onD(1) refl_on_def
      by blast
    hence "limit A ?r_inv = {(a, b). (a, b) \<in> ?r_inv}"
      by auto
    also have "\<dots> = ?r_inv"
      by blast
    finally have "\<dots> = limit A ?r_inv"
      by blast
    hence "?r_inv \<in> limit_\<S>\<W>\<F> (alternatives_\<E> (A, V, p)) UNIV"
      unfolding limit_\<S>\<W>\<F>.simps alternatives_\<E>.simps
      using lin_inv UNIV_I fst_conv mem_Collect_eq iso_tuple_UNIV_I CollectI
      by (metis (mono_tags, lifting))
    thus lim_el_\<pi>:
      "r \<in> \<psi>_neutral\<^sub>\<w> \<pi> ` limit_\<S>\<W>\<F> (alternatives_\<E> (A, V, p)) UNIV"
      using neutral_r
      by blast
  qed
  moreover fix
    \<pi> :: "'a \<Rightarrow> 'a" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    r :: "'a rel"
  assume
    carrier_\<pi>: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    prof: "(A, V, p) \<in> well_formed_elections"
  hence prof_\<pi>: 
    "\<phi>_neutral well_formed_elections \<pi> (A, V, p) \<in> well_formed_elections"
    using \<phi>_neutral_action.element_image
    by blast
  moreover have inv_group_elem: "inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> \<in> carrier neutrality\<^sub>\<G>"
    using carrier_\<pi> \<psi>_neutral\<^sub>\<c>_action.group_hom group.inv_closed
    unfolding group_hom_def
    by metis
  moreover have "\<phi>_neutral well_formed_elections (inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>)
        (\<phi>_neutral well_formed_elections \<pi> (A, V, p)) \<in> well_formed_elections"
    using prof \<phi>_neutral_action.element_image inv_group_elem prof_\<pi>
    by metis
  moreover assume "r \<in> limit_\<S>\<W>\<F> (alternatives_\<E> (A, V, p)) UNIV"
  hence "r \<in> limit_\<S>\<W>\<F>
      (alternatives_\<E> (\<phi>_neutral well_formed_elections (inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>)
        (\<phi>_neutral well_formed_elections \<pi> (A, V, p)))) UNIV"
    using \<phi>_neutral_action.orbit_sym_aux carrier_\<pi> prof
    by metis
  ultimately have
    "r \<in> \<psi>_neutral\<^sub>\<w> (inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>) `
      limit_\<S>\<W>\<F>
        (alternatives_\<E> (\<phi>_neutral well_formed_elections \<pi> (A, V, p))) UNIV"
    using prod.collapse
    by metis
  thus "\<psi>_neutral\<^sub>\<w> \<pi> r \<in> limit_\<S>\<W>\<F>
            (alternatives_\<E> (\<phi>_neutral well_formed_elections \<pi> (A, V, p))) UNIV"
    using carrier_\<pi> \<psi>_neutral\<^sub>\<w>_action.group_action_axioms
          \<psi>_neutral\<^sub>\<w>_action.inj_prop group_action.orbit_sym_aux
          inj_image_mem_iff inv_group_elem iso_tuple_UNIV_I
    by (metis (no_types, lifting))
qed

subsection \<open>Homogeneity Lemmas\<close>

definition reflp_on' :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
    "reflp_on' A r \<longleftrightarrow> reflp_on A (\<lambda> x y. (x, y) \<in> r)"

lemma refl_homogeneity\<^sub>\<R>:
  fixes \<E> :: "('a, 'v) Election set"
  assumes "\<E> \<subseteq> finite_elections_\<V>"
  shows "reflp_on' \<E> (homogeneity\<^sub>\<R> \<E>)"
  using assms
  unfolding reflp_on'_def reflp_on_def finite_elections_\<V>_def
  by auto

lemma (in result) homogeneity:
  "is_symmetry (\<lambda> \<E>. limit (alternatives_\<E> \<E>) UNIV)
        (Invariance (homogeneity\<^sub>\<R> UNIV))"
  by simp

lemma refl_homogeneity\<^sub>\<R>':
  fixes \<E> :: "('a, 'v::linorder) Election set"
  assumes "\<E> \<subseteq> finite_elections_\<V>"
  shows "reflp_on' \<E> (homogeneity\<^sub>\<R>' \<E>)"
  using assms
  unfolding homogeneity\<^sub>\<R>'.simps reflp_on'_def reflp_on_def finite_elections_\<V>_def
  by auto

lemma (in result) homogeneity':
  "is_symmetry (\<lambda> \<E>. limit (alternatives_\<E> \<E>) UNIV)
        (Invariance (homogeneity\<^sub>\<R>' UNIV))"
  by simp

subsection \<open>Reversal Symmetry Lemmas\<close>

lemma reverse_reverse_id: "reverse_rel \<circ> reverse_rel = id"
  by auto

lemma reverse_rel_limit:
  fixes
    A :: "'a set" and
    r :: "'a rel"
  shows "reverse_rel (limit A r) = limit A (reverse_rel r)"
  unfolding reverse_rel.simps limit.simps
  by blast

lemma reverse_rel_lin_ord:
  fixes
    A :: "'a set" and
    r :: "'a rel"
  assumes "linear_order_on A r"
  shows "linear_order_on A (reverse_rel r)"
  using assms
  unfolding reverse_rel.simps linear_order_on_def partial_order_on_def
            total_on_def antisym_def preorder_on_def refl_on_def trans_def
  by blast

interpretation reversal\<^sub>\<G>_group: "group" "reversal\<^sub>\<G>"
proof
  show "\<one> \<^bsub>reversal\<^sub>\<G>\<^esub> \<in> carrier reversal\<^sub>\<G>"
    unfolding reversal\<^sub>\<G>_def
    by simp
next
  show "carrier reversal\<^sub>\<G> \<subseteq> Units reversal\<^sub>\<G>"
    unfolding reversal\<^sub>\<G>_def Units_def
    using reverse_reverse_id
    by auto
next
  fix \<alpha> :: "'a rel \<Rightarrow> 'a rel"
  show "\<alpha> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<one> \<^bsub>reversal\<^sub>\<G>\<^esub> = \<alpha>"
    unfolding reversal\<^sub>\<G>_def
    by auto
  assume \<alpha>_elem: "\<alpha> \<in> carrier reversal\<^sub>\<G>"
  thus "\<one> \<^bsub>reversal\<^sub>\<G>\<^esub> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<alpha> = \<alpha>"
    unfolding reversal\<^sub>\<G>_def
    by auto
  fix \<alpha>' :: "'a rel \<Rightarrow> 'a rel"
  assume \<alpha>'_elem: "\<alpha>' \<in> carrier reversal\<^sub>\<G>"
  thus "\<alpha> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<alpha>' \<in> carrier reversal\<^sub>\<G>"
    using \<alpha>_elem reverse_reverse_id
    unfolding reversal\<^sub>\<G>_def
    by auto
  fix z :: "'a rel \<Rightarrow> 'a rel"
  assume "z \<in> carrier reversal\<^sub>\<G>"
  thus "\<alpha> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<alpha>' \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> z = \<alpha> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> (\<alpha>' \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> z)"
    using \<alpha>_elem \<alpha>'_elem
    unfolding reversal\<^sub>\<G>_def
    by auto
qed

interpretation \<phi>_reverse_action:
  group_action "reversal\<^sub>\<G>" "well_formed_elections" "\<phi>_reverse well_formed_elections"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def,
       intro conjI group_BijGroup CollectI ballI funcsetI)
  show "Group.group reversal\<^sub>\<G>"
    by safe
next
  show carrier_elect_gen:
    "\<And> \<pi>. \<pi> \<in> carrier reversal\<^sub>\<G>
        \<Longrightarrow> \<phi>_reverse well_formed_elections \<pi> \<in> carrier (BijGroup well_formed_elections)"
  proof -
    fix \<pi> :: "'c rel \<Rightarrow> 'c rel"
    assume "\<pi> \<in> carrier reversal\<^sub>\<G>"
    hence \<pi>_cases: "\<pi> \<in> {id, reverse_rel}"
      unfolding reversal\<^sub>\<G>_def
      by auto
    hence [simp]: "rel_app \<pi> \<circ> rel_app \<pi> = id"
      using reverse_reverse_id
      by fastforce
    have "\<forall> \<E>. rel_app \<pi> (rel_app \<pi> \<E>) = \<E>"
      by (simp add: pointfree_idE)
    moreover have "\<forall> \<E> \<in> well_formed_elections. rel_app \<pi> \<E> \<in> well_formed_elections"
      unfolding well_formed_elections_def profile_def
      using \<pi>_cases reverse_rel_lin_ord rel_app.simps fun.map_id
      by fastforce
    hence "rel_app \<pi> ` well_formed_elections \<subseteq> well_formed_elections"
      by blast
    ultimately have "bij_betw (rel_app \<pi>) well_formed_elections well_formed_elections"
      using bij_betw_byWitness[of "well_formed_elections"]
      by blast
    hence "bij_betw (\<phi>_reverse well_formed_elections \<pi>)
              well_formed_elections well_formed_elections"
      unfolding \<phi>_reverse.simps
      using bij_betw_ext
      by blast
    moreover have "\<phi>_reverse well_formed_elections \<pi> \<in> extensional well_formed_elections"
      unfolding extensional_def
      by simp
    ultimately show
      "\<phi>_reverse well_formed_elections \<pi> \<in> carrier (BijGroup well_formed_elections)"
      unfolding BijGroup_def Bij_def
      by simp
  qed
  moreover fix \<pi> \<pi>' :: "'a rel \<Rightarrow> 'a rel"
  assume
    rev: "\<pi> \<in> carrier reversal\<^sub>\<G>" and
    rev': "\<pi>' \<in> carrier reversal\<^sub>\<G>"
  ultimately have carrier_elect:
    "\<phi>_reverse well_formed_elections \<pi> \<in> carrier (BijGroup well_formed_elections)"
    by blast
  have "\<phi>_reverse well_formed_elections (\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') =
          extensional_continuation (rel_app (\<pi> \<circ> \<pi>')) well_formed_elections"
    unfolding reversal\<^sub>\<G>_def
    by simp
  moreover have "rel_app (\<pi> \<circ> \<pi>') = rel_app \<pi> \<circ> rel_app \<pi>'"
    using rel_app.simps
    by fastforce
  ultimately have
    "\<phi>_reverse well_formed_elections (\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') =
      extensional_continuation (rel_app \<pi> \<circ> rel_app \<pi>') well_formed_elections"
    by metis
  moreover have
    "\<forall> A V p. \<forall> v \<in> V. linear_order_on A (p v) \<longrightarrow> linear_order_on A (\<pi>' (p v))"
    using empty_iff id_apply insert_iff rev' reverse_rel_lin_ord
    unfolding partial_object.simps reversal\<^sub>\<G>_def
    by metis
  hence "extensional_continuation
      (\<phi>_reverse well_formed_elections \<pi> \<circ> \<phi>_reverse well_formed_elections \<pi>')
          well_formed_elections =
            extensional_continuation (rel_app \<pi> \<circ> rel_app \<pi>') well_formed_elections"
    unfolding well_formed_elections_def profile_def
    by fastforce
  moreover have "extensional_continuation
      (\<phi>_reverse well_formed_elections \<pi> \<circ> \<phi>_reverse well_formed_elections \<pi>')
          well_formed_elections =
        \<phi>_reverse well_formed_elections \<pi>
            \<otimes> \<^bsub>BijGroup well_formed_elections\<^esub> \<phi>_reverse well_formed_elections \<pi>'"
    using carrier_elect_gen carrier_elect rev' rewrite_mult
    by metis
  ultimately show
    "\<phi>_reverse well_formed_elections (\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') =
        \<phi>_reverse well_formed_elections \<pi>
            \<otimes> \<^bsub>BijGroup well_formed_elections\<^esub> \<phi>_reverse well_formed_elections \<pi>'"
    by metis
qed

interpretation \<psi>_reverse_action: "group_action" "reversal\<^sub>\<G>" "UNIV" "\<psi>_reverse"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def \<psi>_reverse.simps,
       intro conjI group_BijGroup CollectI ballI funcsetI)
  show "Group.group reversal\<^sub>\<G>"
    by safe
next
  fix \<pi> :: "'a rel \<Rightarrow> 'a rel"
  assume "\<pi> \<in> carrier reversal\<^sub>\<G>"
  hence "\<pi> \<in> {id, reverse_rel}"
    unfolding reversal\<^sub>\<G>_def
    by force
  hence "bij \<pi>"
    using reverse_reverse_id bij_id insertE o_bij singleton_iff
    by metis
  thus "\<pi> \<in> carrier (BijGroup UNIV)"
    using rewrite_carrier
    by blast
next
  fix \<pi> \<pi>' :: "'a rel \<Rightarrow> 'a rel"
  assume
    "\<pi> \<in> carrier reversal\<^sub>\<G>" and
    "\<pi>' \<in> carrier reversal\<^sub>\<G>"
  hence "bij \<pi>' \<and> bij \<pi>"
    using singleton_iff comp_apply id_apply involuntory_imp_bij reverse_reverse_id
    unfolding bij_id insert_iff reversal\<^sub>\<G>_def partial_object.select_convs
    by (metis (mono_tags, opaque_lifting))
  hence "\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>' = \<pi> \<circ> \<pi>'"
    using rewrite_carrier rewrite_mult_univ
    by blast
  also have "\<dots> = \<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>'"
    unfolding reversal\<^sub>\<G>_def
    by force
  finally show "\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>' = \<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>'"
    by presburger
qed

lemma reversal_symmetry:
  shows "is_symmetry (\<lambda> \<E>. limit_\<S>\<W>\<F> (alternatives_\<E> \<E>) UNIV)
               (action_induced_equivariance (carrier reversal\<^sub>\<G>) well_formed_elections
                    (\<phi>_reverse well_formed_elections) (set_action \<psi>_reverse))"
proof (unfold rewrite_equivariance, clarify)
  fix
    \<pi> :: "'a rel \<Rightarrow> 'a rel" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume "\<pi> \<in> carrier reversal\<^sub>\<G>"
  hence cases: "\<pi> \<in> {id, reverse_rel}"
    unfolding reversal\<^sub>\<G>_def
    by force
  assume "(A, V, p) \<in> well_formed_elections"
  hence eq_A:
    "alternatives_\<E> (\<phi>_reverse well_formed_elections \<pi> (A, V, p)) = A"
    by simp
  have
    "\<forall> r \<in> {limit A r | r. r \<in> UNIV \<and> linear_order_on A (limit A r)}.
      \<exists> r' \<in> UNIV. reverse_rel r = limit A (reverse_rel r')
                \<and> reverse_rel r' \<in> UNIV \<and> linear_order_on A (limit A (reverse_rel r'))"
    using reverse_rel_limit[of A] reverse_rel_lin_ord
    by force
  hence
    "\<forall> r \<in> {limit A r | r. r \<in> UNIV \<and> linear_order_on A (limit A r)}.
      reverse_rel r \<in> {limit A (reverse_rel r')
              | r'. reverse_rel r' \<in> UNIV
                  \<and> linear_order_on A (limit A (reverse_rel r'))}"
    by blast
  moreover have
    "{limit A (reverse_rel r') |
        r'. reverse_rel r' \<in> UNIV \<and> linear_order_on A (limit A (reverse_rel r'))}
      \<subseteq> {limit A r | r. r \<in> UNIV \<and> linear_order_on A (limit A r)}"
    by blast
  ultimately have
    "\<forall> r \<in> limit_\<S>\<W>\<F> A UNIV. reverse_rel r \<in> limit_\<S>\<W>\<F> A UNIV"
    unfolding limit_\<S>\<W>\<F>.simps
    by blast
  hence subset:
    "\<forall> r \<in> limit_\<S>\<W>\<F> A UNIV. \<pi> r \<in> limit_\<S>\<W>\<F> A UNIV"
    using cases
    by fastforce
  hence "\<forall> r \<in> limit_\<S>\<W>\<F> A UNIV. r \<in> \<pi> ` limit_\<S>\<W>\<F> A UNIV"
    using reverse_reverse_id comp_apply empty_iff id_apply image_eqI insert_iff cases
    by metis
  hence "\<pi> ` limit_\<S>\<W>\<F> A UNIV = limit_\<S>\<W>\<F> A UNIV"
    using subset
    by blast
  hence "set_action \<psi>_reverse \<pi> (limit_\<S>\<W>\<F> A UNIV) = limit_\<S>\<W>\<F> A UNIV"
    unfolding set_action.simps
    by simp
  also have
    "\<dots> = limit_\<S>\<W>\<F> (alternatives_\<E> (\<phi>_reverse well_formed_elections \<pi> (A, V, p))) UNIV"
    using eq_A
    by simp
  finally show
    "limit_\<S>\<W>\<F> (alternatives_\<E> (\<phi>_reverse well_formed_elections \<pi> (A, V, p))) UNIV =
       set_action \<psi>_reverse \<pi> (limit_\<S>\<W>\<F> (alternatives_\<E> (A, V, p)) UNIV)"
    by simp
qed

end
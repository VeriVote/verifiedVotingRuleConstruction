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
  "result_action \<psi> x = (\<lambda> r. (\<psi> x ` elect_r r, \<psi> x ` reject_r r, \<psi> x ` defer_r r))"

subsubsection \<open>Anonymity\<close>

definition anonymity\<^sub>\<G> :: "('v \<Rightarrow> 'v) monoid" where
  "anonymity\<^sub>\<G> = BijGroup (UNIV::'v set)"

fun \<phi>_anon :: "('a, 'v) Election set \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> (('a, 'v) Election
                \<Rightarrow> ('a, 'v) Election)" where
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
        (\<exists> n > 0. \<forall> r::('a Preference_Relation). vote_count r E = n * (vote_count r E'))}"

fun copy_list :: "nat \<Rightarrow> 'x list \<Rightarrow> 'x list" where
  "copy_list 0 l = []" |
  "copy_list (Suc n) l = copy_list n l @ l"

fun homogeneity\<^sub>\<R>' :: "('a, 'v::linorder) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "homogeneity\<^sub>\<R>' X =
    {(E, E') \<in> X \<times> X. alts_\<E> E = alts_\<E> E' \<and> finite (votrs_\<E> E) \<and> finite (votrs_\<E> E') \<and>
      (\<exists> n > 0. to_list (votrs_\<E> E') (prof_\<E> E') = copy_list n (to_list (votrs_\<E> E) (prof_\<E> E)))}"

subsubsection \<open>Reversal Symmetry\<close>

fun rev_rel :: "'a rel \<Rightarrow> 'a rel" where
  "rev_rel r = {(a,b). (b,a) \<in> r}"

fun rel_app :: "('a rel \<Rightarrow> 'a rel) \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "rel_app f (A, V, p) = (A, V, f \<circ> p)"

definition reversal\<^sub>\<G> :: "('a rel \<Rightarrow> 'a rel) monoid" where
  "reversal\<^sub>\<G> = \<lparr>carrier = {rev_rel, id}, monoid.mult = comp, one = id\<rparr>"

fun \<phi>_rev :: "('a, 'v) Election set \<Rightarrow> ('a rel \<Rightarrow> 'a rel, ('a, 'v) Election) binary_fun" where
  "\<phi>_rev X \<phi> = extensional_continuation (rel_app \<phi>) X"

fun \<psi>_rev :: "('a rel \<Rightarrow> 'a rel, 'a rel) binary_fun" where
  "\<psi>_rev \<phi> r = \<phi> r"

fun reversal\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow>  ('a, 'v) Election rel" where
  "reversal\<^sub>\<R> X = rel_induced_by_action (carrier reversal\<^sub>\<G>) X (\<phi>_rev X)"

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
proof (simp, induction n f arbitrary: x rule: n_app.induct)
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
  assume hyp: "\<And> x. f (n_app n f x) = n_app n f (f x)"
  have "f (n_app (Suc n) f x) = f (f (n_app n f x))"
    by simp
  also have "... = f ((n_app n f \<circ> f) x)"
    using hyp
    by simp
  also have "... = f (n_app n f (f x))"
    by simp
  also have "... = n_app (Suc n) f (f x)"
    by simp
  finally show "f (n_app (Suc n) f x) = n_app (Suc n) f (f x)"
    by simp
qed

lemma n_app_leaves_set:
  fixes
    A :: "'x set" and
    B :: "'x set" and
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
  assume existence_witness:
    "\<And> n. 0 < n \<Longrightarrow> n_app n f x \<in> B - A \<Longrightarrow> \<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A \<inter> B \<Longrightarrow> ?thesis"
  have ex_A: "\<exists> n > 0. n_app n f x \<in> B - A \<and> (\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A)"
  proof (rule ccontr, clarsimp)
    assume nex:
      "\<forall> n. n_app n f x \<in> B \<longrightarrow> n = 0 \<or> n_app n f x \<in> A \<or> (\<exists> m > 0. m < n \<and> n_app m f x \<notin> A)"
    hence "\<forall> n > 0. n_app n f x \<in> B \<longrightarrow> n_app n f x \<in> A \<or> (\<exists> m > 0. m < n \<and> n_app m f x \<notin> A)"
      by blast
    moreover have "(\<forall> n > 0. n_app n f x \<in> B \<longrightarrow> n_app n f x \<in> A) \<longrightarrow> False"
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
          have "False"
            using "0"
            by blast
          thus ?case
            by simp
        next
          case (Suc n)
          assume hyp: "0 < n \<Longrightarrow> n_app n f x \<in> A \<inter> B"
          have "n = 0 \<longrightarrow> n_app (Suc n) f x = f x"
            by auto
          hence "n = 0 \<longrightarrow> n_app (Suc n) f x \<in> A \<inter> B"
            using x_el bij in_A
            unfolding bij_betw_def
            by blast
          moreover have "n > 0 \<longrightarrow> n_app (Suc n) f x \<in> A \<inter> B"
            using hyp in_AB_imp_in_AB
            by blast
          ultimately show "n_app (Suc n) f x \<in> A \<inter> B"
            by blast
        qed
      qed
      hence "{n_app n f x | n. n > 0} \<subseteq> A \<inter> B"
        by blast
      moreover have "finite (A \<inter> B)"
        using fin_A fin_B
        by blast
      ultimately have "finite {n_app n f x | n. n > 0}"
        using rev_finite_subset
        by blast
      moreover have
        "inj_on (\<lambda> n. n_app n f x) {n. n > 0} \<longrightarrow> infinite ((\<lambda> n. n_app n f x) ` {n. n > 0})"
        using diff_is_0_eq' finite_imageD finite_nat_set_iff_bounded lessI
              less_imp_diff_less mem_Collect_eq nless_le
        by metis
      moreover have "(\<lambda> n. n_app n f x) ` {n. n > 0} = {n_app n f x | n. n > 0}"
        by auto
      ultimately have "\<not> inj_on (\<lambda> n. n_app n f x) {n. n > 0}"
        by metis
      hence "\<exists> n. n > 0 \<and> (\<exists> m > n. n_app n f x = n_app m f x)"
        using linorder_inj_onI' mem_Collect_eq
        by metis
      hence "\<exists> n_min. 0 < n_min \<and> (\<exists> m > n_min. n_app n_min f x = n_app m f x) \<and>
              (\<forall> n < n_min. \<not> (0 < n \<and> (\<exists> m > n. n_app n f x = n_app m f x)))"
        using exists_least_iff[of "\<lambda> n. n > 0 \<and> (\<exists> m > n. n_app n f x = n_app m f x)"]
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
        using in_int x_el n_min_pos m_gt_n_min Diff_iff IntD1 diff_le_self id_apply nless_le
              cancel_comm_monoid_add_class.diff_cancel n_app.simps(1)
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
      moreover have "n_min - 1 = 0 \<longrightarrow> n_app (n_min - 1) f x \<notin> B"
        using x_el
        by simp
      ultimately have "n_min - 1 = 0 \<longrightarrow> False"
        using eq
        by auto
      thus "False"
        using case_greater_0
        by blast
    qed
    ultimately have "\<exists> n > 0. \<exists> m > 0. m < n \<and> n_app m f x \<notin> A"
      by blast
    hence "\<exists> n. n > 0 \<and> n_app n f x \<notin> A"
      by blast
    hence "\<exists> n. n > 0 \<and> n_app n f x \<notin> A \<and> (\<forall> m < n. \<not> (m > 0 \<and> n_app m f x \<notin> A))"
      using exists_least_iff[of "\<lambda> n. n > 0 \<and> n_app n f x \<notin> A"]
      by presburger
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
    ultimately have "n_app n f x \<in> B"
      using bij n_app.simps
      unfolding bij_betw_def
      by blast
    thus "False"
      using nex not_in_A n_pos less_in_A
      by blast
  qed
  moreover have n_app_f_x_in_A: "n_app 0 f x \<in> A"
    using x_el
    by simp
  ultimately have
    "\<forall> n. (\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A) \<longrightarrow> (\<forall> m > 0. m < n \<longrightarrow> n_app (m - 1) f x \<in> A)"
    using bot_nat_0.not_eq_extremum less_imp_diff_less
    by metis
  moreover have "\<forall> m > 0. n_app m f x = f (n_app (m - 1) f x)"
    using bot_nat_0.not_eq_extremum comp_apply diff_Suc_1 n_app.elims
    by (metis (mono_tags, lifting))
  ultimately have
    "\<forall> n. (\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A) \<longrightarrow> (\<forall> m > 0. m \<le> n \<longrightarrow> n_app m f x \<in> B)"
    using bij n_app.simps(1) n_app_f_x_in_A diff_Suc_1 gr0_conv_Suc imageI
          linorder_not_le nless_le not_less_eq_eq
    unfolding bij_betw_def
    by metis
  hence "\<exists> n > 0. n_app n f x \<in> B - A \<and> (\<forall> m > 0. m < n \<longrightarrow> n_app m f x \<in> A \<inter> B)"
    using IntI nless_le ex_A
    by metis
  thus ?thesis
    using existence_witness
    by blast
qed

lemma n_app_rev:
  fixes
    A :: "'x set" and
    B :: "'x set" and
    f :: "'x \<Rightarrow> 'x" and
    n :: "nat" and
    m :: "nat" and
    x :: "'x" and
    y :: "'x"
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
    x :: "'x" and
    y :: "'x"
  assume
    "m \<le> 0" and
    "n_app 0 f x = n_app m f y"
  thus "n_app (0 - m) f x = y"
    by simp
next
  case (2 n f)
  fix
    f :: "'x \<Rightarrow> 'x" and
    n :: "nat" and
    m :: "nat" and
    x :: "'x" and
    y :: "'x"
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
    A :: "'x set" and
    B :: "'x set" and
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
  also have "... = n_app n f (f (the_inv_into A f (n_app n (the_inv_into A f) x)))"
    by simp
  also have "f (the_inv_into A f (n_app n (the_inv_into A f) x)) = n_app n (the_inv_into A f) x"
    using stays_in_B bij
    by (simp add: f_the_inv_into_f_bij_betw)
  finally have
    "n_app (Suc n) f (n_app (Suc n) (the_inv_into A f) x) =
      n_app n f (n_app n (the_inv_into A f) x)"
    by simp
  thus "n_app (Suc n) f (n_app (Suc n) (the_inv_into A f) x) = x"
    using hyp bij stays_in_B x_in_B
    by simp
qed

lemma bij_betw_finite_ind_global_bij:
  fixes
    A :: "'x set" and
    B :: "'x set" and
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
    minimal: "\<forall> x \<in> B - A. \<forall> n > 0. n < g' x \<longrightarrow> n_app n (the_inv_into A f) x \<in> B \<inter> A"
    using n_app_leaves_set[of B A _ "the_inv_into A f" "False"] fin_A fin_B
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
  moreover have "\<forall> x \<in> B - A. \<forall> n > 0. n < g' x \<longrightarrow> n_app n (the_inv_into A f) x \<in> B"
    using minimal
    by blast
  ultimately have "\<forall> x \<in> B - A. n_app (g' x) f (n_app (g' x) (the_inv_into A f) x) = x"
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
  hence "g ` (UNIV - A - B) = id ` (UNIV - A - B)"
    by simp
  hence "g ` (UNIV - A - B) = UNIV - A - B"
    by simp
  moreover have "g ` A = B"
    using def_g bij
    unfolding bij_betw_def
    by simp
  moreover have "A \<union> (UNIV - A - B) = UNIV - (B - A) \<and> B \<union> (UNIV - A - B) = UNIV - (A - B)"
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
    fix
      x :: "'x" and
      y :: "'x"
    assume
      x_in_B: "x \<in> B" and
      x_not_in_A: "x \<notin> A" and
      y_in_B: "y \<in> B" and
      y_not_in_A: "y \<notin> A" and
      "n_app (g' x) (the_inv_into A f) x = n_app (g' y) (the_inv_into A f) y"
    moreover have "\<forall> n < g' x. n_app n (the_inv_into A f) x \<in> B"
      using x_in_B x_not_in_A minimal Diff_iff Int_iff bot_nat_0.not_eq_extremum
            eq_id_iff n_app.simps(1)
      by metis
    moreover have "\<forall> n < g' y. n_app n (the_inv_into A f) y \<in> B"
      using y_in_B y_not_in_A minimal Diff_iff Int_iff bot_nat_0.not_eq_extremum
            eq_id_iff n_app.simps(1)
      by metis
    ultimately have x_to_y:
      "n_app (g' x - g' y) (the_inv_into A f) x = y \<or>
        n_app (g' y - g' x) (the_inv_into A f) y = x"
      using x_in_B y_in_B bij_inv fin_A fin_B
            n_app_rev[of "x"] n_app_rev[of "y" "B" "x" "g' x" "g' y"]
      by fastforce
    hence "g' x \<noteq> g' y \<longrightarrow>
      ((\<exists> n > 0. n < g' x \<and> n_app n (the_inv_into A f) x \<in> B - A) \<or>
      (\<exists> n > 0. n < g' y \<and> n_app n (the_inv_into A f) y \<in> B - A))"
      using greater_0 x_in_B x_not_in_A y_in_B y_not_in_A Diff_iff diff_less_mono2
            diff_zero id_apply less_Suc_eq_0_disj n_app.elims
      by (metis (full_types))
    hence "g' x = g' y"
      using minimal x_in_B x_not_in_A y_in_B y_not_in_A
      by blast
    thus "x = y"
      using x_to_y
      by force
  qed
  ultimately have "bij_betw (\<lambda> x. n_app (g' x) (the_inv_into A f) x) (B - A) (A - B)"
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
    by blast
  with coincide id reverse
  have "\<exists> g. bij g \<and> (\<forall> a \<in> A. g a = f a) \<and>
          (\<forall> b \<in> B - A. g b \<in> A - B \<and> (\<exists> n > 0. n_app n f (g b) = b)) \<and>
          (\<forall> x \<in> UNIV - A - B. g x = x)"
    by blast
  thus ?thesis
    using existence_witness
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
    X :: "('a, 'v) Election set" and
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election"
  assumes
    "finite (votrs_\<E> E)" and
    "(E, E') \<in> anonymity\<^sub>\<R> X"
  shows "alts_\<E> E = alts_\<E> E' \<and> (E, E') \<in> X \<times> X \<and> (\<forall> p. vote_count p E = vote_count p E')"
proof -
  from assms have rel': "(E, E') \<in> X \<times> X"
    unfolding anonymity\<^sub>\<R>.simps rel_induced_by_action.simps
    by blast
  hence "E \<in> X"
    by simp
  with assms
  obtain \<pi> :: "'v \<Rightarrow> 'v" where
    bijection_\<pi>: "bij \<pi>" and 
    renamed: "E' = rename \<pi> E"
    unfolding anonymity\<^sub>\<R>.simps anonymity\<^sub>\<G>_def
    using universal_set_carrier_imp_bij_group
    by auto
  hence eq_alts: "alts_\<E> E' = alts_\<E> E"
    using eq_fst_iff rename.simps
    by metis
  from renamed
  have "\<forall> v \<in> votrs_\<E> E'. (prof_\<E> E') v = (prof_\<E> E) (the_inv \<pi> v)"
    using rename.simps comp_apply prod.collapse snd_conv
    by (metis (no_types, lifting))
  hence rewrite:
    "\<forall> p. {v \<in> (votrs_\<E> E'). (prof_\<E> E') v = p} = {v \<in> (votrs_\<E> E'). (prof_\<E> E) (the_inv \<pi> v) = p}"
    by blast
  from renamed have "\<forall> v \<in> votrs_\<E> E'. the_inv \<pi> v \<in> votrs_\<E> E"
    using UNIV_I bijection_\<pi> bij_betw_imp_surj bij_is_inj f_the_inv_into_f
          fst_conv inj_image_mem_iff prod.collapse rename.simps snd_conv
    by (metis (mono_tags, lifting))
  hence
    "\<forall> p. \<forall> v \<in> votrs_\<E> E'. (prof_\<E> E) (the_inv \<pi> v) = p \<longrightarrow>
      v \<in> \<pi> ` {v \<in> votrs_\<E> E. (prof_\<E> E) v = p}"
    using bijection_\<pi> f_the_inv_into_f_bij_betw image_iff
    by fastforce
  hence subset:
    "\<forall> p. {v \<in> votrs_\<E> E'. (prof_\<E> E) (the_inv \<pi> v) = p} \<subseteq>
          \<pi> ` {v \<in> votrs_\<E> E. (prof_\<E> E) v = p}"
    by blast
  from renamed have "\<forall> v \<in> votrs_\<E> E. \<pi> v \<in> votrs_\<E> E'"
    using bijection_\<pi> bij_is_inj fst_conv inj_image_mem_iff prod.collapse rename.simps snd_conv
    by (metis (mono_tags, lifting))
  hence
    "\<forall> p. \<pi> ` {v \<in> votrs_\<E> E. (prof_\<E> E) v = p} \<subseteq>
      {v \<in> votrs_\<E> E'. (prof_\<E> E) (the_inv \<pi> v) = p}"
    using bijection_\<pi> bij_is_inj the_inv_f_f
    by fastforce
  with subset rewrite
    have "\<forall> p. {v \<in> votrs_\<E> E'. (prof_\<E> E') v = p} = \<pi> ` {v \<in> votrs_\<E> E. (prof_\<E> E) v = p}"
    by (simp add: subset_antisym)
  moreover have
    "\<forall> p. card (\<pi> ` {v \<in> votrs_\<E> E. (prof_\<E> E) v = p}) = card {v \<in> votrs_\<E> E. (prof_\<E> E) v = p}"
    using bijection_\<pi> bij_betw_same_card bij_betw_subset top_greatest
    by (metis (no_types, lifting))
  ultimately have "\<forall> p. vote_count p E = vote_count p E'"
    unfolding vote_count.simps
    by presburger
  thus "alts_\<E> E = alts_\<E> E' \<and> (E, E') \<in> X \<times> X \<and> (\<forall> p. vote_count p E = vote_count p E')"
    using eq_alts assms
    by simp
qed

lemma vote_count_anon_rel:
  fixes
    X :: "('a, 'v) Election set" and
    E :: "('a, 'v) Election" and
    E' :: "('a, 'v) Election"
  assumes
    fin_voters_E: "finite (votrs_\<E> E)" and
    fin_voters_E': "finite (votrs_\<E> E')" and
    default_non_v: "\<forall> v. v \<notin> votrs_\<E> E \<longrightarrow> prof_\<E> E v = {}" and
    default_non_v': "\<forall> v. v \<notin> votrs_\<E> E' \<longrightarrow> prof_\<E> E' v = {}" and
    eq: "alts_\<E> E = alts_\<E> E' \<and> (E, E') \<in> X \<times> X \<and> (\<forall> p. vote_count p E = vote_count p E')"
  shows "(E, E') \<in> anonymity\<^sub>\<R> X"
proof -
  from eq
  have "\<forall> p. card {v \<in> votrs_\<E> E. prof_\<E> E v = p} = card {v \<in> votrs_\<E> E'. prof_\<E> E' v = p}"
    unfolding vote_count.simps
    by blast
  moreover have
    "\<forall> p. finite {v \<in> votrs_\<E> E. prof_\<E> E v = p} \<and> finite {v \<in> votrs_\<E> E'. prof_\<E> E' v = p}"
    using assms
    by simp
  ultimately have
    "\<forall> p. \<exists> \<pi>\<^sub>p. bij_betw \<pi>\<^sub>p {v \<in> votrs_\<E> E. prof_\<E> E v = p} {v \<in> votrs_\<E> E'. prof_\<E> E' v = p}"
    using bij_betw_iff_card
    by blast
  then obtain \<pi> :: "'a Preference_Relation \<Rightarrow> ('v \<Rightarrow> 'v)" where
    bij: "\<forall> p. bij_betw (\<pi> p) {v \<in> votrs_\<E> E. prof_\<E> E v = p}
                              {v \<in> votrs_\<E> E'. prof_\<E> E' v = p}"
    by (metis (no_types))
  obtain \<pi>' :: "'v \<Rightarrow> 'v" where
    \<pi>'_def: "\<forall> v \<in> votrs_\<E> E. \<pi>' v = \<pi> (prof_\<E> E v) v"
    by fastforce
  hence "\<forall> v v'. v \<in> votrs_\<E> E \<and> v' \<in> votrs_\<E> E \<longrightarrow>
    \<pi>' v = \<pi>' v' \<longrightarrow> \<pi> (prof_\<E> E v) v = \<pi> (prof_\<E> E v') v'"
    by simp
  moreover have
    "\<forall> w w'. w \<in> votrs_\<E> E \<and> w' \<in> votrs_\<E> E \<longrightarrow> \<pi> (prof_\<E> E w) w = \<pi> (prof_\<E> E w') w' \<longrightarrow>
    {v \<in> votrs_\<E> E'. prof_\<E> E' v = prof_\<E> E w} \<inter> {v \<in> votrs_\<E> E'. prof_\<E> E' v = prof_\<E> E w'} \<noteq> {}"
    using bij
    unfolding bij_betw_def
    by blast
  moreover have
    "\<forall> w w'.
    {v \<in> votrs_\<E> E'. prof_\<E> E' v = prof_\<E> E w} \<inter> {v \<in> votrs_\<E> E'. prof_\<E> E' v = prof_\<E> E w'} \<noteq> {}
        \<longrightarrow> prof_\<E> E w = prof_\<E> E w'"
    by blast
  ultimately have eq_prof:
    "\<forall> v v'. v \<in> votrs_\<E> E \<and> v' \<in> votrs_\<E> E \<longrightarrow> \<pi>' v = \<pi>' v' \<longrightarrow> prof_\<E> E v = prof_\<E> E v'"
    by presburger
  hence "\<forall> v v'. v \<in> votrs_\<E> E \<and> v' \<in> votrs_\<E> E \<longrightarrow> \<pi>' v = \<pi>' v' \<longrightarrow>
          \<pi> (prof_\<E> E v) v = \<pi> (prof_\<E> E v) v'"
    using \<pi>'_def
    by metis
  hence "\<forall> v v'. v \<in> votrs_\<E> E \<and> v' \<in> votrs_\<E> E \<longrightarrow> \<pi>' v = \<pi>' v' \<longrightarrow> v = v'"
    using bij eq_prof
    unfolding bij_betw_def inj_on_def
    by simp
  hence inj: "inj_on \<pi>' (votrs_\<E> E)"
    unfolding inj_on_def
    by simp
  have "\<pi>' ` votrs_\<E> E = {\<pi> (prof_\<E> E v) v | v. v \<in> votrs_\<E> E}"
    using \<pi>'_def
    unfolding Setcompr_eq_image
    by simp
  also have
    "{\<pi> (prof_\<E> E v) v | v. v \<in> votrs_\<E> E} = {\<pi> p v | p v. v \<in> {v \<in> votrs_\<E> E. prof_\<E> E v = p}}"
    by blast
  also have
    "{\<pi> p v | p v. v \<in> {v \<in> votrs_\<E> E. prof_\<E> E v = p}} =
      {x | p x. p \<in> UNIV \<and> x \<in> \<pi> p ` {v \<in> votrs_\<E> E. prof_\<E> E v = p}}"
    by blast
  also have
    "{x | p x. p \<in> UNIV \<and> x \<in> \<pi> p ` {v \<in> votrs_\<E> E. prof_\<E> E v = p}} =
      {x | x. \<exists> p \<in> UNIV. x \<in> \<pi> p ` {v \<in> votrs_\<E> E. prof_\<E> E v = p}}"
    by blast
  also have
    "{x | x. \<exists> p \<in> UNIV. x \<in> \<pi> p ` {v \<in> votrs_\<E> E. prof_\<E> E v = p}} =
      {x | x. \<exists> A \<in> {\<pi> p ` {v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}. x \<in> A}"
    by auto
  also have
    "{x | x. \<exists> A \<in> {\<pi> p ` {v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}. x \<in> A} =
      \<Union> {\<pi> p ` {v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV}"
    unfolding Union_eq
    by simp
  also have
    "\<Union> {\<pi> p ` {v \<in> votrs_\<E> E. prof_\<E> E v = p} | p. p \<in> UNIV} =
      \<Union> {{v \<in> votrs_\<E> E'. prof_\<E> E' v = p} | p. p \<in> UNIV}"
    using bij
    unfolding bij_betw_def
    by (metis (mono_tags, lifting))
  also have "\<Union> {{v \<in> votrs_\<E> E'. prof_\<E> E' v = p} | p. p \<in> UNIV} = votrs_\<E> E'"
    by blast
  finally have "\<pi>' ` votrs_\<E> E = votrs_\<E> E'"
    by simp
  with inj have bij': "bij_betw \<pi>' (votrs_\<E> E) (votrs_\<E> E')"
    using bij
    unfolding bij_betw_def
    by blast
  then obtain \<pi>_global :: "'v \<Rightarrow> 'v" where
    bijection_\<pi>\<^sub>g: "bij \<pi>_global" and
    \<pi>_global_def: "\<forall> v \<in> votrs_\<E> E. \<pi>_global v = \<pi>' v" and
    \<pi>_global_def':
      "\<forall> v \<in> votrs_\<E> E' - votrs_\<E> E.
        \<pi>_global v \<in> votrs_\<E> E - votrs_\<E> E' \<and>
        (\<exists> n > 0. n_app n \<pi>' (\<pi>_global v) = v)" and
    \<pi>_global_non_voters: "\<forall> v \<in> UNIV - votrs_\<E> E - votrs_\<E> E'. \<pi>_global v = v"
    using fin_voters_E fin_voters_E' bij_betw_finite_ind_global_bij
    by blast
  hence inv: "\<forall> v v'. (\<pi>_global v' = v) = (v' = the_inv \<pi>_global v)"
    using UNIV_I bij_betw_imp_inj_on bij_betw_imp_surj_on f_the_inv_into_f the_inv_f_f
    by metis
  have "\<forall> v \<in> UNIV - (votrs_\<E> E' - votrs_\<E> E). \<pi>_global v \<in> UNIV - (votrs_\<E> E - votrs_\<E> E')"
    using \<pi>_global_def \<pi>_global_non_voters bij' bijection_\<pi>\<^sub>g DiffD1 DiffD2 DiffI bij_betwE
    by (metis (no_types, lifting))
  hence "\<forall> v \<in> votrs_\<E> E - votrs_\<E> E'. \<exists> v' \<in> votrs_\<E> E' - votrs_\<E> E.
      \<pi>_global v' = v \<and> (\<exists> n > 0. n_app n \<pi>' v = v')"
    using bijection_\<pi>\<^sub>g \<pi>_global_def' DiffD2 DiffI UNIV_I local.inv
    by metis
  with inv
    have "\<forall> v \<in> votrs_\<E> E - votrs_\<E> E'. the_inv \<pi>_global v \<in> votrs_\<E> E' - votrs_\<E> E"
    by simp
  hence "\<forall> v \<in> votrs_\<E> E - votrs_\<E> E'. \<forall> n > 0. prof_\<E> E (the_inv \<pi>_global v) = {}"
    using default_non_v
    by simp
  moreover have "\<forall> v \<in> votrs_\<E> E - votrs_\<E> E'. prof_\<E> E' v = {}"
    using default_non_v'
    by simp
  ultimately have case_1:
    "\<forall> v \<in> votrs_\<E> E - votrs_\<E> E'. prof_\<E> E' v = (prof_\<E> E \<circ> the_inv \<pi>_global) v"
    by auto
  have "\<forall> v \<in> votrs_\<E> E'. \<exists> v' \<in> votrs_\<E> E. \<pi>_global v' = v \<and> \<pi>' v' = v"
    using bij' imageE \<pi>_global_def
    unfolding bij_betw_def
    by (metis (mono_tags, opaque_lifting))
  with inv
  have "\<forall> v \<in> votrs_\<E> E'. \<exists> v' \<in> votrs_\<E> E. v' = the_inv \<pi>_global v \<and> \<pi>' v' = v"
    by presburger
  hence "\<forall> v \<in> votrs_\<E> E'. the_inv \<pi>_global v \<in> votrs_\<E> E \<and> \<pi>' (the_inv \<pi>_global v) = v"
    by blast
  moreover have "\<forall> v' \<in> votrs_\<E> E. prof_\<E> E' (\<pi>' v') = prof_\<E> E v'"
    using \<pi>'_def bij bij_betwE mem_Collect_eq
    by fastforce
  ultimately have case_2: "\<forall> v \<in> votrs_\<E> E'. prof_\<E> E' v = (prof_\<E> E \<circ> the_inv \<pi>_global) v"
    unfolding comp_def
    by metis
  from \<pi>_global_non_voters
  have "\<forall> v \<in> UNIV - votrs_\<E> E - votrs_\<E> E'. prof_\<E> E' v = (prof_\<E> E \<circ> the_inv \<pi>_global) v"
    using default_non_v default_non_v' inv
    by auto
  with case_1 case_2
  have "prof_\<E> E' = prof_\<E> E \<circ> the_inv \<pi>_global"
    by blast
  moreover have "\<pi>_global ` (votrs_\<E> E) = votrs_\<E> E'"
    using \<pi>_global_def bij' bij_betw_imp_surj_on
    by fastforce
  ultimately have "E' = rename \<pi>_global E"
    using rename.simps eq prod.collapse
    by metis
  thus ?thesis
    unfolding extensional_continuation.simps anonymity\<^sub>\<R>.simps
              rel_induced_by_action.simps \<phi>_anon.simps anonymity\<^sub>\<G>_def
    using eq bijection_\<pi>\<^sub>g case_prodI rewrite_carrier
    by auto
qed

lemma rename_comp:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v" and
    \<pi>' :: "'v \<Rightarrow> 'v"
  assumes
    "bij \<pi>" and
    "bij \<pi>'"
  shows "rename \<pi> \<circ> rename \<pi>' = rename (\<pi> \<circ> \<pi>')"
proof
  fix E :: "('a, 'v) Election"
  have "rename \<pi>' E = (alts_\<E> E, \<pi>' ` (votrs_\<E> E), (prof_\<E> E) \<circ> (the_inv \<pi>'))"
    using prod.collapse rename.simps
    by metis
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
    using assms the_inv_comp[of \<pi> UNIV UNIV \<pi>']
    by auto
  also have
    "(alts_\<E> E, (\<pi> \<circ> \<pi>') ` (votrs_\<E> E), (prof_\<E> E) \<circ> (the_inv (\<pi> \<circ> \<pi>'))) = rename (\<pi> \<circ> \<pi>') E"
    using prod.collapse rename.simps
    by metis
  finally show "(rename \<pi> \<circ> rename \<pi>') E = rename (\<pi> \<circ> \<pi>') E"
    by simp
qed

interpretation anon_grp_act:
  "group_action" "anonymity\<^sub>\<G>" "valid_elections" "\<phi>_anon valid_elections"
proof (unfold group_action_def group_hom_def anonymity\<^sub>\<G>_def group_hom_axioms_def hom_def, 
        safe, (rule group_BijGroup)+)
  {
    fix \<pi> :: "'v \<Rightarrow> 'v"
    assume "\<pi> \<in> carrier (BijGroup UNIV)"
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
    \<open>\<And> \<pi>. \<pi> \<in> carrier (BijGroup UNIV) \<Longrightarrow>
          \<phi>_anon valid_elections \<pi> \<in> carrier (BijGroup valid_elections)\<close>
  fix
    \<pi> :: "'v \<Rightarrow> 'v" and
    \<pi>' :: "'v \<Rightarrow> 'v"
  assume
    bij: "\<pi> \<in> carrier (BijGroup UNIV)" and
    bij': "\<pi>' \<in> carrier (BijGroup UNIV)"
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
  from car_els
  have "\<phi>_anon valid_elections \<pi> \<otimes> \<^bsub>BijGroup valid_elections\<^esub> (\<phi>_anon valid_elections) \<pi>' =
      extensional_continuation
        (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') valid_elections"
    using rewrite_mult
    by blast
  moreover have
    "\<forall> E. E \<in> valid_elections \<longrightarrow>
      extensional_continuation
        (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') valid_elections E =
        (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') E"
    by simp
  moreover have
    "\<forall> E. E \<in> valid_elections \<longrightarrow>
          (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') E = rename \<pi> (rename \<pi>' E)"
    unfolding \<phi>_anon.simps
    using valid_closed'
    by auto
  moreover have "\<forall> E. E \<in> valid_elections \<longrightarrow> rename \<pi> (rename \<pi>' E) = rename (\<pi> \<circ> \<pi>') E"
    using rename_comp bij bij' universal_set_carrier_imp_bij_group comp_apply
    by metis
  moreover have
    "\<forall> E. E \<in> valid_elections \<longrightarrow>
          rename (\<pi> \<circ> \<pi>') E = \<phi>_anon valid_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') E"
    using rewrite_mult_univ bij bij'
    unfolding \<phi>_anon.simps
    by force
  moreover have
    "\<forall> E. E \<notin> valid_elections \<longrightarrow>
      extensional_continuation
        (\<phi>_anon valid_elections \<pi> \<circ> \<phi>_anon valid_elections \<pi>') valid_elections E = undefined"
    by simp
  moreover have
    "\<forall> E. E \<notin> valid_elections \<longrightarrow> \<phi>_anon valid_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') E = undefined"
    by simp
  ultimately have
    "\<forall> E. \<phi>_anon valid_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') E =
          (\<phi>_anon valid_elections \<pi> \<otimes> \<^bsub>BijGroup valid_elections\<^esub> \<phi>_anon valid_elections \<pi>') E"
    by metis
  thus
    "\<phi>_anon valid_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') =
      \<phi>_anon valid_elections \<pi> \<otimes> \<^bsub>BijGroup valid_elections\<^esub> \<phi>_anon valid_elections \<pi>'"
    by blast
qed

lemma (in result) well_formed_res_anon:
  "satisfies (\<lambda> E. limit_set (alts_\<E> E) UNIV) (Invariance (anonymity\<^sub>\<R> valid_elections))"
proof (unfold anonymity\<^sub>\<R>.simps, simp, safe) qed

subsection \<open>Neutrality Lemmas\<close>

lemma rel_rename_helper:
  fixes
    r :: "'a rel" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    a :: "'a" and
    b :: "'a"
  assumes "bij \<pi>"
  shows "(\<pi> a, \<pi> b) \<in> {(\<pi> x, \<pi> y) | x y. (x, y) \<in> r} \<longleftrightarrow> (a, b) \<in> {(x, y) | x y. (x, y) \<in> r}"
proof (safe, simp)
  fix
    x :: "'a" and
    y :: "'a"
  assume
    x_rel_y: "(x, y) \<in> r" and
    "\<pi> a = \<pi> x" and
    "\<pi> b = \<pi> y"
  hence "a = x \<and> b = y"
    using assms bij_is_inj the_inv_f_f
    by metis
  thus "(a, b) \<in> r"
    using x_rel_y
    by simp
next
  fix
    x :: "'a" and
    y :: "'a"
  assume "(a, b) \<in> r"
  thus "\<exists> x y. (\<pi> a, \<pi> b) = (\<pi> x, \<pi> y) \<and> (x, y) \<in> r"
    by auto
qed

lemma rel_rename_comp:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    \<pi>' :: "'a \<Rightarrow> 'a"
  shows "rel_rename (\<pi> \<circ> \<pi>') = rel_rename \<pi> \<circ> rel_rename \<pi>'"
proof
  fix r :: "'a rel"
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
  assumes "inj \<pi>"
  shows
    "refl_on A r \<longrightarrow> refl_on (\<pi> ` A) (rel_rename \<pi> r)" and
    "antisym r \<longrightarrow> antisym (rel_rename \<pi> r)" and
    "total_on A r \<longrightarrow> total_on (\<pi> ` A) (rel_rename \<pi> r)" and
    "Relation.trans r \<longrightarrow> Relation.trans (rel_rename \<pi> r)"
proof (unfold antisym_def total_on_def Relation.trans_def, safe)
  assume "refl_on A r"
  hence "r \<subseteq> A \<times> A \<and> (\<forall> a \<in> A. (a, a) \<in> r)"
    unfolding refl_on_def
    by simp
  hence "rel_rename \<pi> r \<subseteq> (\<pi> ` A) \<times> (\<pi> ` A) \<and> (\<forall> a \<in> A. (\<pi> a, \<pi> a) \<in> rel_rename \<pi> r)"
    unfolding rel_rename.simps
    by blast
  hence "rel_rename \<pi> r \<subseteq> (\<pi> ` A) \<times> (\<pi> ` A) \<and> (\<forall> a \<in> \<pi> ` A. (a, a) \<in> rel_rename \<pi> r)"
    by fastforce
  thus "refl_on (\<pi> ` A) (rel_rename \<pi> r)"
    unfolding refl_on_def
    by simp
next
  fix
    a :: "'a" and
    b :: "'a"
  assume 
    antisym: "\<forall> a b. (a, b) \<in> r \<longrightarrow> (b, a) \<in> r \<longrightarrow> a = b" and
    "(a, b) \<in> rel_rename \<pi> r" and
    "(b, a) \<in> rel_rename \<pi> r"
  then obtain
    c :: "'a" and
    d :: "'a" and
    c' :: "'a" and
    d' :: "'a" where 
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
  hence "c = d"
    using antisym d'_rel_c' c_rel_d
    by simp
  thus "a = b"
    using \<pi>\<^sub>c_eq_a \<pi>\<^sub>d_eq_b
    by simp
next
  fix
    a :: "'a" and
    b :: "'a"
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
  fix
    a :: "'a" and
    b :: "'a" and
    c :: "'a"
  assume
    trans: "\<forall> x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r" and
    "(a, b) \<in> rel_rename \<pi> r" and
    "(b, c) \<in> rel_rename \<pi> r"
  then obtain
    d :: "'a" and
    e :: "'a" and
    s :: "'a" and
    t :: "'a" where
      d_rel_e: "(d, e) \<in> r" and
      s_rel_t: "(s, t) \<in> r" and
      \<pi>\<^sub>d_eq_a: "\<pi> d = a" and
      \<pi>\<^sub>s_eq_b: "\<pi> s = b" and
      \<pi>\<^sub>t_eq_c: "\<pi> t = c" and
      \<pi>\<^sub>e_eq_b: "\<pi> e = b"
    using rel_rename.simps
    by auto
  hence "s = e"
    using assms rangeI range_ex1_eq
    by metis
  hence "(d, e) \<in> r \<and> (e, t) \<in> r"
    using d_rel_e s_rel_t
    by simp
  hence "(d, t) \<in> r"
    using trans
    by blast
  thus "(a, c) \<in> rel_rename \<pi> r"
    unfolding rel_rename.simps
    using \<pi>\<^sub>d_eq_a \<pi>\<^sub>t_eq_c
    by blast
qed

lemma rel_rename_bij:
  fixes \<pi> :: "'a \<Rightarrow> 'a"
  assumes bij_\<pi>: "bij \<pi>"
  shows "bij (rel_rename \<pi>)"
proof (unfold bij_def inj_def surj_def, safe)
  {
    fix
      r :: "'a rel" and
      s :: "'a rel" and
      a :: "'a" and
      b :: "'a"
    assume
      "rel_rename \<pi> r = rel_rename \<pi> s" and
      "(a, b) \<in> r"
    hence "(\<pi> a, \<pi> b) \<in> {(\<pi> a, \<pi> b) | a b. (a,b) \<in> s}"
      unfolding rel_rename.simps
      by blast
    hence "\<exists> c d. (c, d) \<in> s \<and> \<pi> c = \<pi> a \<and> \<pi> d = \<pi> b"
      by fastforce
    moreover have "\<forall> c d. \<pi> c = \<pi> d \<longrightarrow> c = d"
      using bij_\<pi> bij_pointE
      by metis
    ultimately show "(a, b) \<in> s"
      by blast
  }
  note subset =
    \<open>\<And> r s a b. rel_rename \<pi> r = rel_rename \<pi> s \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> (a, b) \<in> s\<close>
  fix
    r :: "'a rel" and
    s :: "'a rel" and
    a :: "'a" and
    b :: "'a"
  assume
    "rel_rename \<pi> r = rel_rename \<pi> s" and
    "(a, b) \<in> s"
  thus "(a, b) \<in> r"
    using subset
    by presburger
next
  fix r :: "'a rel"
  have "rel_rename (the_inv \<pi>) r = {((the_inv \<pi>) a, (the_inv \<pi>) b) | a b. (a,b) \<in> r}"
    by simp
  also have "rel_rename \<pi> {((the_inv \<pi>) a, (the_inv \<pi>) b) | a b. (a,b) \<in> r} =
    {(\<pi> ((the_inv \<pi>) a), \<pi> ((the_inv \<pi>) b)) | a b. (a,b) \<in> r}"
    by auto
  also have "{(\<pi> ((the_inv \<pi>) a), \<pi> ((the_inv \<pi>) b)) | a b. (a,b) \<in> r} =
    {(a, b) | a b. (a,b) \<in> r}"
    using the_inv_f_f bij_\<pi>
    by (simp add: f_the_inv_into_f_bij_betw)
  also have "{(a, b) | a b. (a,b) \<in> r} = r"
    by simp
  finally have "rel_rename \<pi> (rel_rename (the_inv \<pi>) r) = r"
    by simp
  thus "\<exists> s. r = rel_rename \<pi> s"
    by blast
qed
    
lemma alts_rename_comp:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    \<pi>' :: "'a \<Rightarrow> 'a"
  shows "alts_rename \<pi> \<circ> alts_rename \<pi>' = alts_rename (\<pi> \<circ> \<pi>')"
proof
  fix E :: "('a, 'v) Election"
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
  fixes \<pi> :: "('a \<Rightarrow> 'a)"
  assumes bij_\<pi>: "bij \<pi>"
  shows "bij_betw (alts_rename \<pi>) valid_elections valid_elections"
proof (unfold bij_betw_def, safe, intro inj_onI, clarsimp)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    p' :: "('a, 'v) Profile"
  assume
    "(A, V, p) \<in> valid_elections" and
    "(A', V, p') \<in> valid_elections" and
    \<pi>_eq_img_A_A': "\<pi> ` A = \<pi> ` A'" and
    eq: "rel_rename \<pi> \<circ> p = rel_rename \<pi> \<circ> p'"
  hence "(the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> \<circ> p =
    (the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> \<circ> p'"
    using fun.map_comp
    by metis
  also have "(the_inv (rel_rename \<pi>)) \<circ> rel_rename \<pi> = id"
    using bij_\<pi> rel_rename_bij bij_betw_def inv_o_cancel surj_imp_inv_eq the_inv_f_f
    by (metis (no_types, opaque_lifting))
  finally have "p = p'"
    by simp
  moreover have "A = A'"
    using bij_\<pi> \<pi>_eq_img_A_A'
    by (simp add: bij_betw_imp_inj_on inj_image_eq_iff)
  ultimately show "A = A' \<and> p = p'"
    by blast
next
  {
    fix
      A :: "'a set" and
      A' :: "'a set" and 
      V :: "'v set" and
      V' :: "'v set" and
      p :: "('a, 'v) Profile" and
      p' :: "('a, 'v) Profile" and
      \<pi> :: "'a \<Rightarrow> 'a"
    assume
      prof: "(A, V, p) \<in> valid_elections" and
      bij_\<pi>: "bij \<pi>" and
      renamed: "(A', V', p') = alts_rename \<pi> (A, V, p)"
    hence rewr: "V = V' \<and> A' = \<pi> ` A"
      by simp
    hence "\<forall> v \<in> V'. linear_order_on A (p v)"
      using prof
      unfolding valid_elections_def profile_def
      by simp
    moreover have "\<forall> v \<in> V'. p' v = rel_rename \<pi> (p v)"
      using renamed
      by simp
    ultimately have "\<forall> v \<in> V'. linear_order_on A' (p' v)"
      unfolding linear_order_on_def partial_order_on_def preorder_on_def
      using rewr rel_rename_sound bij_\<pi> bij_is_inj
      by metis
    hence "(A', V', p') \<in> valid_elections"
      unfolding valid_elections_def profile_def
      by simp
  }
  note valid_els_closed =
    \<open>\<And> A A' V V' p p' \<pi>. (A, V, p) \<in> valid_elections \<Longrightarrow>
      bij \<pi> \<Longrightarrow> (A', V', p') = alts_rename \<pi> (A, V, p) \<Longrightarrow>
        (A', V', p') \<in> valid_elections\<close>
  thus "\<And> a aa b ab ac ba.
          (a, aa, b) = alts_rename \<pi> (ab, ac, ba) \<Longrightarrow>
            (ab, ac, ba) \<in> valid_elections \<Longrightarrow> (a, aa, b) \<in> valid_elections"
    using bij_\<pi>
    by blast
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assume prof: "(A, V, p) \<in> valid_elections"
  have "alts_rename (the_inv \<pi>) (A, V, p) = ((the_inv \<pi>) ` A, V, rel_rename (the_inv \<pi>) \<circ> p)"
    by simp
  also have
    "alts_rename \<pi> ((the_inv \<pi>) ` A, V, rel_rename (the_inv \<pi>) \<circ> p) =
      (\<pi> ` (the_inv \<pi>) ` A, V, rel_rename \<pi> \<circ> rel_rename (the_inv \<pi>) \<circ> p)"
    by auto
  also have
    "(\<pi> ` (the_inv \<pi>) ` A, V, rel_rename \<pi> \<circ> rel_rename (the_inv \<pi>) \<circ> p)
      = (A, V, rel_rename (\<pi> \<circ> the_inv \<pi>) \<circ> p)"
    using bij_\<pi> rel_rename_comp[of \<pi>] the_inv_f_f
    by (simp add: bij_betw_imp_surj_on bij_is_inj f_the_inv_into_f image_comp)
  also have "(A, V, rel_rename (\<pi> \<circ> the_inv \<pi>) \<circ> p) = (A, V, rel_rename id \<circ> p)"
    using UNIV_I assms comp_apply f_the_inv_into_f_bij_betw id_apply
    by metis
  also have "rel_rename id \<circ> p = p"
    unfolding rel_rename.simps
    by auto
  finally have "alts_rename \<pi> (alts_rename (the_inv \<pi>) (A, V, p)) = (A, V, p)"
    by simp
  moreover have "alts_rename (the_inv \<pi>) (A, V, p) \<in> valid_elections"
    using valid_els_closed[of A V] bij_\<pi>
    by (simp add: bij_betw_the_inv_into prof)
  ultimately show "(A, V, p) \<in> alts_rename \<pi> ` valid_elections"
    using image_eqI
    by metis
qed

interpretation \<phi>_neutr_act:
  "group_action" "neutrality\<^sub>\<G>" "valid_elections" "\<phi>_neutr valid_elections"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def neutrality\<^sub>\<G>_def,
        safe, (rule group_BijGroup)+)
  {
    fix \<pi> :: "'a \<Rightarrow> 'a"
    assume "\<pi> \<in> carrier (BijGroup UNIV)"
    hence "bij \<pi>"
      using universal_set_carrier_imp_bij_group
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
    \<open>\<And> \<pi>. \<pi> \<in> carrier (BijGroup UNIV) \<Longrightarrow>
      \<phi>_neutr valid_elections \<pi> \<in> carrier (BijGroup valid_elections)\<close>
  fix
    \<pi> :: "'a \<Rightarrow> 'a" and
    \<pi>' :: "'a \<Rightarrow> 'a"
  assume
    bij: "\<pi> \<in> carrier (BijGroup UNIV)" and
    bij': "\<pi>' \<in> carrier (BijGroup UNIV)"
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
  have "\<phi>_neutr valid_elections \<pi> \<otimes> \<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr valid_elections \<pi>' =
      extensional_continuation
        (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') valid_elections"
    using car_els rewrite_mult
    by auto
  moreover have
    "\<forall> E. E \<in> valid_elections \<longrightarrow>
      extensional_continuation
        (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') valid_elections E =
          (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') E"
    by simp
  moreover have
    "\<forall> E. E \<in> valid_elections \<longrightarrow>
      (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') E =
        alts_rename \<pi> (alts_rename \<pi>' E)"
    unfolding \<phi>_neutr.simps
    using valid_closed'
    by auto
  moreover have
    "\<forall> E. E \<in> valid_elections \<longrightarrow> alts_rename \<pi> (alts_rename \<pi>' E) = alts_rename (\<pi> \<circ> \<pi>') E"
    using alts_rename_comp bij bij' comp_apply
    by metis
  moreover have
    "\<forall> E. E \<in> valid_elections \<longrightarrow> alts_rename (\<pi> \<circ> \<pi>') E =
        \<phi>_neutr valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E"
    using rewrite_mult_univ bij bij'
    unfolding \<phi>_anon.simps
    by force
  moreover have
    "\<forall> E. E \<notin> valid_elections \<longrightarrow>
      extensional_continuation
        (\<phi>_neutr valid_elections \<pi> \<circ> \<phi>_neutr valid_elections \<pi>') valid_elections E = undefined"
    by simp
  moreover have
    "\<forall> E. E \<notin> valid_elections \<longrightarrow> \<phi>_neutr valid_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') E = undefined"
    by simp
  ultimately have
    "\<forall> E. \<phi>_neutr valid_elections (\<pi> \<otimes>\<^bsub>BijGroup UNIV\<^esub> \<pi>') E =
      (\<phi>_neutr valid_elections \<pi> \<otimes>\<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr valid_elections \<pi>') E"
    by metis
  thus
    "\<phi>_neutr valid_elections (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') =
      \<phi>_neutr valid_elections \<pi> \<otimes> \<^bsub>BijGroup valid_elections\<^esub> \<phi>_neutr valid_elections \<pi>'"
    by blast
qed

interpretation \<psi>_neutr\<^sub>\<c>_act: "group_action" "neutrality\<^sub>\<G>" "UNIV" "\<psi>_neutr\<^sub>\<c>"
proof (unfold group_action_def group_hom_def hom_def neutrality\<^sub>\<G>_def group_hom_axioms_def, 
        safe, (rule group_BijGroup)+)
  {
    fix \<pi> :: "'a \<Rightarrow> 'a"
    assume "\<pi> \<in> carrier (BijGroup UNIV)"
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
    \<pi> :: "'a \<Rightarrow> 'a" and
    \<pi>' :: "'a \<Rightarrow> 'a"
  assume
    "\<pi> \<in> carrier (BijGroup UNIV)" and
    "\<pi>' \<in> carrier (BijGroup UNIV)"
  show "\<psi>_neutr\<^sub>\<c> (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') =
           \<psi>_neutr\<^sub>\<c> \<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<psi>_neutr\<^sub>\<c> \<pi>'"
    unfolding \<psi>_neutr\<^sub>\<c>.simps
    by simp
qed

interpretation \<psi>_neutr\<^sub>\<w>_act: "group_action" "neutrality\<^sub>\<G>" "UNIV" "\<psi>_neutr\<^sub>\<w>"
proof (unfold group_action_def group_hom_def hom_def neutrality\<^sub>\<G>_def group_hom_axioms_def, 
        safe, (rule group_BijGroup)+)
  {
    fix \<pi> :: "'a \<Rightarrow> 'a"
    assume "\<pi> \<in> carrier (BijGroup UNIV)"
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
    \<open>\<And> \<pi>. \<pi> \<in> carrier (BijGroup UNIV) \<Longrightarrow> \<psi>_neutr\<^sub>\<w> \<pi> \<in> carrier (BijGroup UNIV)\<close>
  fix
    \<pi> :: "'a \<Rightarrow> 'a" and
    \<pi>' :: "'a \<Rightarrow> 'a"
  assume
    bij: "\<pi> \<in> carrier (BijGroup UNIV)" and
    bij': "\<pi>' \<in> carrier (BijGroup UNIV)"
  hence "\<psi>_neutr\<^sub>\<w> \<pi> \<in> carrier (BijGroup UNIV) \<and> \<psi>_neutr\<^sub>\<w> \<pi>' \<in> carrier (BijGroup UNIV)"
    using grp_el
    by blast
  thus "\<psi>_neutr\<^sub>\<w> (\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>') = \<psi>_neutr\<^sub>\<w> \<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<psi>_neutr\<^sub>\<w> \<pi>'"
    unfolding \<psi>_neutr\<^sub>\<w>.simps
    using rel_rename_comp rewrite_mult_univ bij bij'
    by metis
qed

lemma wf_res_neutr_soc_choice:
  "satisfies (\<lambda> E. limit_set_soc_choice (alts_\<E> E) UNIV)
            (equivar_ind_by_act (carrier neutrality\<^sub>\<G>) valid_elections
                                (\<phi>_neutr valid_elections) (set_action \<psi>_neutr\<^sub>\<c>))"
proof (unfold rewrite_equivar_ind_by_act, safe, auto) qed

lemma wf_res_neutr_soc_welfare:
  "satisfies (\<lambda> E. limit_set_welfare (alts_\<E> E) UNIV)
            (equivar_ind_by_act (carrier neutrality\<^sub>\<G>) valid_elections
                                (\<phi>_neutr valid_elections) (set_action \<psi>_neutr\<^sub>\<w>))"
proof (simp del: limit_set_welfare.simps \<phi>_neutr.simps
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
      carrier_\<pi>: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
      prof: "(A, V, p) \<in> valid_elections" and
      "\<phi>_neutr valid_elections \<pi> (A, V, p) \<in> valid_elections" and
      lim_el: "r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections \<pi> (A, V, p))) UNIV"
    hence inv_carrier: "the_inv \<pi> \<in> carrier neutrality\<^sub>\<G>"
      unfolding neutrality\<^sub>\<G>_def rewrite_carrier
      using bij_betw_the_inv_into
      by simp
    moreover have "the_inv \<pi> \<circ> \<pi> = id"
      using carrier_\<pi> universal_set_carrier_imp_bij_group bij_is_inj the_inv_f_f
      unfolding neutrality\<^sub>\<G>_def
      by fastforce
    moreover have "\<one> \<^bsub>neutrality\<^sub>\<G>\<^esub> = id"
      unfolding neutrality\<^sub>\<G>_def BijGroup_def
      by auto
    ultimately have "the_inv \<pi> \<otimes> \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> = \<one> \<^bsub>neutrality\<^sub>\<G>\<^esub>"
      using carrier_\<pi>
      unfolding neutrality\<^sub>\<G>_def
      using rewrite_mult_univ
      by metis
    hence inv_eq: "inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> = the_inv \<pi>"
      using carrier_\<pi> inv_carrier \<psi>_neutr\<^sub>\<c>_act.group_hom group.inv_closed group.inv_solve_right
            group.l_inv group_BijGroup group_hom.hom_one group_hom.one_closed
      unfolding neutrality\<^sub>\<G>_def
      by metis
    have "r \<in> limit_set_welfare (\<pi> ` A) UNIV"
      unfolding \<phi>_neutr.simps
      using prof lim_el
      by simp
    hence lin: "linear_order_on (\<pi> ` A) r"
      by auto
    have bij_inv: "bij (the_inv \<pi>)"
      using carrier_\<pi> bij_betw_the_inv_into universal_set_carrier_imp_bij_group
      unfolding neutrality\<^sub>\<G>_def
      by blast
    hence "(the_inv \<pi>) ` \<pi> ` A = A"
      using carrier_\<pi> UNIV_I bij_betw_imp_surj universal_set_carrier_imp_bij_group
            f_the_inv_into_f_bij_betw image_f_inv_f surj_imp_inv_eq
      unfolding neutrality\<^sub>\<G>_def
      by metis
    hence lin_inv: "linear_order_on A ?r_inv"
      using rel_rename_sound bij_inv lin bij_is_inj
      unfolding \<psi>_neutr\<^sub>\<w>.simps linear_order_on_def preorder_on_def partial_order_on_def
      by metis
    hence "\<forall> a b. (a, b) \<in> ?r_inv \<longrightarrow> a \<in> A \<and> b \<in> A"
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
      using lin_inv UNIV_I fst_conv mem_Collect_eq
      by (metis (mono_tags, lifting))
    moreover have "r = \<psi>_neutr\<^sub>\<w> \<pi> ?r_inv"
      using carrier_\<pi> inv_eq inv_carrier iso_tuple_UNIV_I \<psi>_neutr\<^sub>\<w>_act.orbit_sym_aux
      by metis
    ultimately show "r \<in> \<psi>_neutr\<^sub>\<w> \<pi> ` limit_set_welfare (alts_\<E> (A, V, p)) UNIV"
      by blast
  }
  note lim_el_\<pi> =
    \<open>\<And> \<pi> A V p r. \<pi> \<in> carrier neutrality\<^sub>\<G> \<Longrightarrow> (A, V, p) \<in> valid_elections \<Longrightarrow>
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
    carrier_\<pi>: "\<pi> \<in> carrier neutrality\<^sub>\<G>" and
    prof: "(A, V, p) \<in> valid_elections" and
    prof_\<pi>: "\<phi>_neutr valid_elections \<pi> (A, V, p) \<in> valid_elections" and
    "r \<in> limit_set_welfare (alts_\<E> (A, V, p)) UNIV"
  hence
    "r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections (inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>)
                              (\<phi>_neutr valid_elections \<pi> (A, V, p)))) UNIV"
    using \<phi>_neutr_act.orbit_sym_aux
    by metis
  moreover have inv_grp_el: "inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi> \<in> carrier neutrality\<^sub>\<G>"
    using carrier_\<pi> \<psi>_neutr\<^sub>\<c>_act.group_hom
          group.inv_closed group_hom_def
    by metis
  moreover have
    "\<phi>_neutr valid_elections (inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>)
      (\<phi>_neutr valid_elections \<pi> (A, V, p)) \<in> valid_elections"
    using prof \<phi>_neutr_act.element_image inv_grp_el prof_\<pi>
    by metis
  ultimately have
    "r \<in> \<psi>_neutr\<^sub>\<w> (inv \<^bsub>neutrality\<^sub>\<G>\<^esub> \<pi>) `
            limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections \<pi> (A, V, p))) UNIV"
    using prof_\<pi> lim_el_\<pi> prod.collapse
    by metis
  thus "\<psi>_neutr\<^sub>\<w> \<pi> r \<in> limit_set_welfare (alts_\<E> (\<phi>_neutr valid_elections \<pi> (A, V, p))) UNIV"
    using carrier_\<pi> \<psi>_neutr\<^sub>\<w>_act.group_action_axioms
          \<psi>_neutr\<^sub>\<w>_act.inj_prop group_action.orbit_sym_aux
          inj_image_mem_iff inv_grp_el iso_tuple_UNIV_I
    by (metis (no_types, lifting))
qed

subsection \<open>Homogeneity Lemmas\<close>

lemma refl_homogeneity\<^sub>\<R>:
  fixes X :: "('a, 'v) Election set"
  assumes "X \<subseteq> finite_voter_elections"
  shows "refl_on X (homogeneity\<^sub>\<R> X)"
  using assms
  unfolding refl_on_def finite_voter_elections_def
  by auto

lemma (in result) well_formed_res_homogeneity:
  "satisfies (\<lambda> E. limit_set (alts_\<E> E) UNIV) (Invariance (homogeneity\<^sub>\<R> UNIV))"
  by simp

lemma refl_homogeneity\<^sub>\<R>':
  fixes X :: "('a, 'v::linorder) Election set"
  assumes "X \<subseteq> finite_voter_elections"
  shows "refl_on X (homogeneity\<^sub>\<R>' X)"
  using assms
  unfolding homogeneity\<^sub>\<R>'.simps refl_on_def finite_voter_elections_def
  by auto

lemma (in result) well_formed_res_homogeneity':
  "satisfies (\<lambda> E. limit_set (alts_\<E> E) UNIV) (Invariance (homogeneity\<^sub>\<R>' UNIV))"
  by simp

subsection \<open>Reversal Symmetry Lemmas\<close>

lemma rev_rev_id: "rev_rel \<circ> rev_rel = id"
  by auto

lemma rev_rel_limit:
  fixes
    A :: "'a set" and
    r :: "'a rel"
  shows "rev_rel (limit A r) = limit A (rev_rel r)"
  unfolding rev_rel.simps limit.simps
  by auto

lemma rev_rel_lin_ord:
  fixes
    A :: "'a set" and
    r :: "'a rel"
  assumes "linear_order_on A r"
  shows "linear_order_on A (rev_rel r)"
  using assms
  unfolding rev_rel.simps linear_order_on_def partial_order_on_def
            total_on_def antisym_def preorder_on_def refl_on_def trans_def
  by blast

interpretation reversal\<^sub>\<G>_group: group reversal\<^sub>\<G>
proof
  show "\<one> \<^bsub>reversal\<^sub>\<G>\<^esub> \<in> carrier reversal\<^sub>\<G>"
    unfolding reversal\<^sub>\<G>_def
    by simp
next
  show "carrier reversal\<^sub>\<G> \<subseteq> Units reversal\<^sub>\<G>"
    unfolding reversal\<^sub>\<G>_def Units_def
    using rev_rev_id
    by auto
next
  fix x :: "'a rel \<Rightarrow> 'a rel"
  assume x_el: "x \<in> carrier reversal\<^sub>\<G>"
  thus "\<one> \<^bsub>reversal\<^sub>\<G>\<^esub> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> x = x"
    unfolding reversal\<^sub>\<G>_def
    by auto
  show "x \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<one> \<^bsub>reversal\<^sub>\<G>\<^esub> = x"
    unfolding reversal\<^sub>\<G>_def
    by auto
  fix y :: "'a rel \<Rightarrow> 'a rel"
  assume y_el: "y \<in> carrier reversal\<^sub>\<G>"
  thus "x \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> y \<in> carrier reversal\<^sub>\<G>"
    using x_el rev_rev_id
    unfolding reversal\<^sub>\<G>_def
    by auto
  fix z :: "'a rel \<Rightarrow> 'a rel"
  assume z_el: "z \<in> carrier reversal\<^sub>\<G>"
  thus "x \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> y \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> z = x \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> (y \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> z)"
    using x_el y_el
    unfolding reversal\<^sub>\<G>_def
    by auto
qed

interpretation \<phi>_rev_act: group_action "reversal\<^sub>\<G>" "valid_elections" "\<phi>_rev valid_elections"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def,
        safe, rule group_BijGroup)
  {
    fix \<pi> :: "'a rel \<Rightarrow> 'a rel"
    assume "\<pi> \<in> carrier reversal\<^sub>\<G>"
    hence \<pi>_cases: "\<pi> \<in> {id, rev_rel}"
      unfolding reversal\<^sub>\<G>_def
      by auto
    hence inv_rel_app: "rel_app \<pi> \<circ> rel_app \<pi> = id"
      using rev_rev_id
      by fastforce
    have id: "\<forall> E. rel_app \<pi> (rel_app \<pi> E) = E"
      by (simp add: inv_rel_app pointfree_idE)
    have "\<forall> E \<in> valid_elections. rel_app \<pi> E \<in> valid_elections"
      unfolding valid_elections_def profile_def
      using \<pi>_cases rev_rel_lin_ord rel_app.simps fun.map_id
      by fastforce
    hence "rel_app \<pi> ` valid_elections \<subseteq> valid_elections"
      by blast
    with id have "bij_betw (rel_app \<pi>) valid_elections valid_elections"
      using id bij_betw_byWitness[of "valid_elections"]
      by blast
    hence "bij_betw (\<phi>_rev valid_elections \<pi>) valid_elections valid_elections"
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
    \<open>\<And> \<pi>. \<pi> \<in> carrier reversal\<^sub>\<G> \<Longrightarrow> \<phi>_rev valid_elections \<pi> \<in> carrier (BijGroup valid_elections)\<close>
  fix
    \<pi> :: "'a rel \<Rightarrow> 'a rel" and
    \<pi>' :: "'a rel \<Rightarrow> 'a rel"
  assume
    rev: "\<pi> \<in> carrier reversal\<^sub>\<G>" and
    rev': "\<pi>' \<in> carrier reversal\<^sub>\<G>"
  hence "\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>' = \<pi> \<circ> \<pi>'"
    unfolding reversal\<^sub>\<G>_def
    by simp
  hence "\<phi>_rev valid_elections (\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') =
          extensional_continuation (rel_app (\<pi> \<circ> \<pi>')) valid_elections"
    by simp
  also have "rel_app (\<pi> \<circ> \<pi>') = rel_app \<pi> \<circ> rel_app \<pi>'"
    using rel_app.simps
    by fastforce
  finally have rewrite:
    "\<phi>_rev valid_elections (\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') =
      extensional_continuation (rel_app \<pi> \<circ> rel_app \<pi>') valid_elections"
    by blast
  have "bij_betw (\<phi>_rev valid_elections \<pi>') valid_elections valid_elections"
    using car_el rev'
    unfolding BijGroup_def Bij_def
    by auto
  hence "\<forall> E \<in> valid_elections. \<phi>_rev valid_elections \<pi>' E \<in> valid_elections"
    unfolding bij_betw_def
    by blast
  hence "extensional_continuation
      (\<phi>_rev valid_elections \<pi> \<circ> \<phi>_rev valid_elections \<pi>') valid_elections =
      extensional_continuation (rel_app \<pi> \<circ> rel_app \<pi>') valid_elections"
    unfolding extensional_continuation.simps \<phi>_rev.simps
    by fastforce
  also have
    "extensional_continuation (\<phi>_rev valid_elections \<pi> \<circ> \<phi>_rev valid_elections \<pi>') valid_elections
      = \<phi>_rev valid_elections \<pi> \<otimes> \<^bsub>BijGroup valid_elections\<^esub> \<phi>_rev valid_elections \<pi>'"
    using car_el rewrite_mult rev rev'
    by metis
  finally show
    "\<phi>_rev valid_elections (\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>') =
     \<phi>_rev valid_elections \<pi> \<otimes> \<^bsub>BijGroup valid_elections\<^esub> \<phi>_rev valid_elections \<pi>'"
    using rewrite
    by metis
qed

interpretation \<psi>_rev_act: "group_action" "reversal\<^sub>\<G>" "UNIV" "\<psi>_rev"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def \<psi>_rev.simps,
        safe, rule group_BijGroup)
  {
    fix \<pi> :: "'a rel \<Rightarrow> 'a rel"
    assume "\<pi> \<in> carrier reversal\<^sub>\<G>"
    hence "\<pi> \<in> {id, rev_rel}"
      unfolding reversal\<^sub>\<G>_def
      by auto
    hence "bij \<pi>"
      using rev_rev_id bij_id insertE o_bij singleton_iff
      by metis
    thus "\<pi> \<in> carrier (BijGroup UNIV)"
      using rewrite_carrier
      by blast
  }
  note bij = \<open>\<And> \<pi>. \<pi> \<in> carrier reversal\<^sub>\<G> \<Longrightarrow> \<pi> \<in> carrier (BijGroup UNIV)\<close>
  fix
    \<pi> :: "'a rel \<Rightarrow> 'a rel" and
    \<pi>' :: "'a rel \<Rightarrow> 'a rel"
  assume
    rev: "\<pi> \<in> carrier reversal\<^sub>\<G>" and
    rev': "\<pi>' \<in> carrier reversal\<^sub>\<G>"
  hence "\<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>' = \<pi> \<circ> \<pi>'"
    using bij rewrite_mult_univ
    by blast
  also have "\<pi> \<circ> \<pi>' = \<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>'"
    unfolding reversal\<^sub>\<G>_def
    using rev rev'
    by simp
  finally show "\<pi> \<otimes> \<^bsub>reversal\<^sub>\<G>\<^esub> \<pi>' = \<pi> \<otimes> \<^bsub>BijGroup UNIV\<^esub> \<pi>'"
    by simp
qed

lemma \<phi>_\<psi>_rev_well_formed:
  shows
    "satisfies (\<lambda> E. limit_set_welfare (alts_\<E> E) UNIV)
               (equivar_ind_by_act (carrier reversal\<^sub>\<G>) valid_elections
                                    (\<phi>_rev valid_elections) (set_action \<psi>_rev))"
proof (unfold rewrite_equivar_ind_by_act, clarify)
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
    "\<forall> r \<in> {limit A r | r. r \<in> UNIV \<and> linear_order_on A (limit A r)}. \<exists> r' \<in> UNIV.
      rev_rel r = limit A (rev_rel r') \<and>
        rev_rel r' \<in> UNIV \<and> linear_order_on A (limit A (rev_rel r'))"
    using rev_rel_limit[of A] rev_rel_lin_ord[of A]
    by force
  hence
    "\<forall> r \<in> {limit A r | r. r \<in> UNIV \<and> linear_order_on A (limit A r)}.
      rev_rel r \<in>
        {limit A (rev_rel r') | r'. rev_rel r' \<in> UNIV \<and> linear_order_on A (limit A (rev_rel r'))}"
    by blast
  moreover have
    "{limit A (rev_rel r') | r'. rev_rel r' \<in> UNIV \<and> linear_order_on A (limit A (rev_rel r'))} \<subseteq>
      {limit A r | r. r \<in> UNIV \<and> linear_order_on A (limit A r)}"
    by blast
  ultimately have "\<forall> r \<in> limit_set_welfare A UNIV. rev_rel r \<in> limit_set_welfare A UNIV"
    unfolding limit_set_welfare.simps
    by blast
  hence subset: "\<forall> r \<in> limit_set_welfare A UNIV. \<pi> r \<in> limit_set_welfare A UNIV"
    using cases
    by fastforce
  hence "\<forall> r \<in> limit_set_welfare A UNIV. r \<in> \<pi> ` limit_set_welfare A UNIV"
    using rev_rev_id comp_apply empty_iff id_apply image_eqI insert_iff local.cases
    by metis
  hence "\<pi> ` limit_set_welfare A UNIV = limit_set_welfare A UNIV"
    using subset
    by blast
  hence "set_action \<psi>_rev \<pi> (limit_set_welfare A UNIV) = limit_set_welfare A UNIV"
    unfolding set_action.simps
    by simp
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
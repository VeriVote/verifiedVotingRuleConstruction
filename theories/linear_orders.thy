theory linear_orders
imports Main

begin

abbreviation smaller :: "'a \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<preceq>\<^sub>_ _" [50, 1000, 51] 50) where
  "x \<preceq>\<^sub>r y == (x, y) \<in> r"

definition connex_on where
  "connex_on A r \<longleftrightarrow> r \<subseteq> A \<times> A \<and> (\<forall>x \<in> A. \<forall>y \<in> A. x \<preceq>\<^sub>r y \<or> y \<preceq>\<^sub>r x)"

lemma connex_impl_refl:
  assumes "connex_on A r"
  shows "refl_on A r"
  by (meson assms connex_on_def refl_on_def)

definition limited_to :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "limited_to A r \<equiv> r \<subseteq> A \<times> A"

lemma limited_intro[intro]:
  "(\<And>x y. \<lbrakk> x \<preceq>\<^sub>r y \<rbrakk> \<Longrightarrow>  x \<in> A \<and> y \<in> A) \<Longrightarrow> limited_to A r"
  unfolding limited_to_def
  by auto

lemma limited_dest:
  "(\<And>x y. \<lbrakk> x \<preceq>\<^sub>r y; limited_to A r \<rbrakk> \<Longrightarrow>  x \<in> A \<and> y \<in> A)"
  unfolding limited_to_def
  by auto

lemma linear_order_impl_connex:
  assumes "linear_order_on A r"
  shows "connex_on A r"
  by (smt assms connex_on_def linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      total_on_def)

lemma lin_imp_antisym:
  assumes "linear_order_on A r"
  shows "antisym r"
  using assms linear_order_on_def partial_order_on_def
  by auto

lemma lin_imp_trans:
  assumes "linear_order_on A r"
  shows "trans r"
  using assms order_on_defs
  by blast

lemma connex_antisym_trans_impl_lin_order:
  assumes "connex_on A r" and
          "antisym r" and
          "trans r"
  shows "linear_order_on A r"
  by (meson assms connex_impl_refl connex_on_def order_on_defs total_on_def)

fun limit_to :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "limit_to A r = {(a, b) \<in> r. a \<in> A \<and> b \<in> A}"

lemma limit_to_limits:
  shows "limited_to A (limit_to A r)"
  by (metis (no_types, lifting) CollectD case_prodD limit_to.simps limited_intro)

lemma limit_preserves_connectivity:
  assumes connex: "connex_on S r" and
          subset: "A \<subseteq> S"
  shows "connex_on A (limit_to A r)"
  by (smt CollectI Product_Type.Collect_case_prodD assms case_prod_conv connex_on_def fst_conv
      limit_to.simps mem_Sigma_iff snd_conv subrelI subset_eq)

lemma limit_preserves_antisymmetry:
  assumes antisymmetric: "antisym r" and
          subset:        "A \<subseteq> S"
  shows "antisym (limit_to A r)"
  using antisym_def antisymmetric
  by auto

lemma limit_preserves_transitivity:
  assumes transitive: "trans r" and
          subset:     "A \<subseteq> S"
  shows "trans (limit_to A r)"
  by (smt Product_Type.Collect_case_prodD case_prodI fst_conv limit_to.simps local.transitive
      mem_Collect_eq snd_conv trans_def)

lemma limit_preserves_linear_order:
  assumes "linear_order_on S r" and
          "A \<subseteq> S"
  shows "linear_order_on A (limit_to A r)"
  by (meson assms connex_antisym_trans_impl_lin_order limit_preserves_antisymmetry
      limit_preserves_connectivity limit_preserves_transitivity
      linear_order_impl_connex order_on_defs)

lemma limit_preserves_preferences1:
  assumes x_less_y: "x \<preceq>\<^sub>r y" and
          x_in_A:   "x \<in> A" and
          y_in_A:   "y \<in> A"
  shows "let s = limit_to A r in x \<preceq>\<^sub>s y"
  by (simp add: x_in_A x_less_y y_in_A)

lemma limit_preserves_preferences2:
  assumes x_less_y: "(x, y) \<in> limit_to A r"
  shows "x \<preceq>\<^sub>r y"
  by (metis (no_types, lifting) case_prodD limit_to.simps mem_Collect_eq x_less_y)

lemma limit_twice:
  assumes "B \<subseteq> A" and
          "C \<subseteq> B" and
          "linear_order_on A r"
  shows "limit_to C r = limit_to C (limit_to B r)"
  using assms
  by auto

(* needed? *)
fun rank_in :: "'a rel \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank_in r x = card (above r x)"

lemma rank_greater_zero:
  assumes refl: "x \<preceq>\<^sub>r x" and
          fin:  "finite r"
  shows "rank_in r x \<ge> 1"
proof -
  have "x \<in> {y \<in> Field r. (x, y) \<in> r}"
    using FieldI2 local.refl
    by fastforce
  hence "{y \<in> Field r. (x, y) \<in> r} \<noteq> {}"
    by blast
  hence "card{y \<in> Field r. (x, y) \<in> r} \<noteq> 0"
    by (simp add: fin finite_Field)
  moreover have "card{y \<in> Field r. (x, y) \<in> r} \<ge> 0"
    using fin
    by auto
  ultimately show ?thesis
    by (metis (no_types, lifting) Collect_cong FieldI2 above_def less_one not_le_imp_less
        rank_in.elims)
qed

lemma above_decr:
  assumes "trans r" and
          "(a, b) \<in> r"
  shows "above r b \<subseteq> above r a"
  by (metis (mono_tags, lifting) Collect_mono above_def assms transE)

lemma in_above:
  assumes "refl_on A r" and
          "a \<in> A"
  shows "a \<in> above r a"
  using above_def assms refl_onD
  by fastforce

lemma above_subset_geq_one:
  assumes "linear_order_on A r \<and> linear_order_on A s" and
          "above r a \<subseteq> above s a" and
          "above s a = {a}"
  shows "above r a = {a}"
  by (metis above_def assms connex_impl_refl in_above insert_absorb linear_order_impl_connex
      mem_Collect_eq refl_on_domain singletonI subset_singletonD)

definition lifted :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A r s a \<equiv> linear_order_on A r \<and> linear_order_on A s \<and> a \<in> A \<and>
    (\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a) \<and> (\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y)"

definition only_change :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool" where
  "only_change A r s a \<equiv> linear_order_on A r \<and> linear_order_on A s \<and> a \<in> A \<and>
    (\<forall>x \<in> A-{a}. \<forall>y \<in> A-{a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y)"

lemma trivial_only_change:
  assumes order: "linear_order_on A p"
  shows "\<forall>a \<in> A. only_change A p p a"
  by (simp add: only_change_def order)

lemma lifted_implies_only_change:
  assumes lifted: "lifted A r s a"
  shows "only_change A r s a"
proof -
  from lifted
  have "linear_order_on A r \<and> linear_order_on A s \<and> a \<in> A \<and>
      (\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y)"
    by (simp add: lifted_def)
  thus ?thesis
    by (simp add: only_change_def)
qed

lemma lifted_impl_not_worse:
  assumes lifted: "lifted A r s a"
  shows "\<forall>x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x)"
proof (rule ccontr)
  assume a_not: "\<not>(\<forall>x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x))"
  then obtain x::"'a" where x: "x \<in> A - {a} \<and> x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x"
    by blast
  from lifted obtain y::"'a" where y: "y \<in> A - {a} \<and> a \<preceq>\<^sub>r y \<and> y \<preceq>\<^sub>s a"
    by (meson lifted_def)
  from x
  have "a \<preceq>\<^sub>s x"
    by auto
  moreover from lifted x y
  have "x \<preceq>\<^sub>s y"
    by (meson lifted_def linear_order_on_def partial_order_on_def preorder_on_def transE)
  moreover from lifted
  have "trans s"
    by (simp add: lifted_def order_on_defs)
  ultimately have "a \<preceq>\<^sub>s y"
    by (meson transE)
  moreover from y
  have "y \<noteq> a \<and> y \<preceq>\<^sub>s a"
    by auto
  moreover from lifted
  have "antisym s"
    by (simp add: lifted_def linear_order_on_def partial_order_on_def)
  ultimately show "False"
    by (meson antisymD)
qed

lemma lifted_impl_not_worse2:
  assumes lifted: "lifted A r s a"
  shows "x \<preceq>\<^sub>r a \<longrightarrow> x \<preceq>\<^sub>s a"
proof -
  { assume "x \<noteq> a"
    moreover
      { assume "x \<in> A \<and> x \<noteq> a"
        moreover
          { assume "x \<in> A \<and> a \<preceq>\<^sub>s x \<and> x \<noteq> a"
            hence "x \<in> A - {a} \<and> a \<preceq>\<^sub>s x"
              by (meson Diff_iff singleton_iff)
            hence ?thesis
              by (meson lifted lifted_impl_not_worse)
          }
        ultimately have ?thesis
          by (metis lifted lifted_def linear_order_on_def total_on_def) }
      ultimately have ?thesis
        by (metis (full_types) lifted lifted_def linear_order_on_def order_on_defs(1)
            order_on_defs(2) refl_on_domain)
  }
  then show ?thesis
    by (metis (full_types) lifted lifted_def linear_order_on_def order_on_defs(1) order_on_defs(2)
        refl_onD)
qed

lemma lifted_above:
  assumes "lifted A r s a"
  shows "above s a \<subseteq> above r a"
proof -
  { have "\<not>(\<exists>x \<in> A. x \<in> above s a \<and> x \<notin> above r a)"
    proof -
      { fix aa :: 'a
          { assume "aa \<noteq> a"
            moreover
              { assume "aa \<preceq>\<^sub>r a \<and> aa \<noteq> a"
                hence "(a, aa) \<notin> s"
                  by (metis antisym_def assms lifted_def lifted_impl_not_worse2 linear_order_on_def
                      partial_order_on_def)
                hence "aa \<notin> A \<or> aa \<notin> above s a \<or> aa \<in> above r a"
                  by (simp add: above_def)
              }
            ultimately have "(aa \<notin> A \<or> aa \<notin> above s a \<or> aa \<in> above r a) \<or> a \<preceq>\<^sub>r aa"
              by (metis (no_types) assms lifted_def linear_order_on_def total_on_def)
          }
        hence "(aa \<notin> A \<or> aa \<notin> above s a \<or> aa \<in> above r a) \<or> a \<preceq>\<^sub>r aa"
          by (metis (no_types) assms lifted_def linear_order_on_def partial_order_on_def
              preorder_on_def refl_on_def)
        hence "aa \<notin> A \<or> aa \<notin> above s a \<or> aa \<in> above r a"
          using above_def
          by fastforce
      }
      then show ?thesis
        by (metis (lifting))
    qed }
  thus ?thesis
    by (metis CollectD above_def assms lifted_def order_on_defs(1) order_on_defs(2) order_on_defs(3)
        refl_on_domain subsetI)
qed

lemma lifted_above2:
  assumes "lifted A r s a"
  shows "\<forall>x. x \<in> A-{a} \<longrightarrow> above r x \<subseteq> above s x \<union> {a}"
proof
  { fix x show "x \<in> A-{a} \<longrightarrow> above r x \<subseteq> above s x \<union> {a}"
    proof
      assume "x \<in> A-{a}"
      hence "\<forall>y \<in> A-{a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
        by (meson assms lifted_def)
      hence "\<forall>y \<in> A-{a}. y \<in> above r x \<longleftrightarrow> y \<in> above s x"
        by (simp add: above_def)
      moreover have "a \<in> above r x \<longrightarrow> a \<in> above s x"
        by (metis CollectD CollectI above_def assms lifted_impl_not_worse2)
      moreover have "above r x \<subseteq> A \<and> above s x \<subseteq> A"
        by (metis CollectD above_def assms connex_impl_refl lifted_def linear_order_impl_connex
            refl_on_domain subsetI)
      ultimately show "above r x \<subseteq> above s x \<union> {a}"
        by blast
  qed }
qed

lemma limit_lifted_interaction:
  assumes lifted: "lifted S r s a" and
          subset: "A \<subseteq> S"
  shows "limit_to A r = limit_to A s \<or> lifted A (limit_to A r) (limit_to A s) a"
proof -
  from lifted
  have "\<forall>x \<in> S - {a}. \<forall>y \<in> S - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    by (simp add: lifted_def)
  from this subset
  have temp: "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    by auto
  hence eql_rs: "\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. (x, y) \<in> (limit_to A r) \<longleftrightarrow> (x, y) \<in> (limit_to A s)"
    by (metis DiffD1 limit_preserves_preferences1 limit_preserves_preferences2)
  { show ?thesis
    proof cases
      { assume a1: "a \<in> A"
        thus ?thesis
        proof cases
          (* (\<forall>x \<in> A - {a}. \<forall>y \<in> A - {a}. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y) *)
          { assume a1_1: "\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a" (* \<and> a1: "a \<in> A" *)
            from lifted subset
            have "linear_order_on A (limit_to A r) \<and> linear_order_on A (limit_to A s)"
              by (meson lifted_def limit_preserves_linear_order)
            moreover from a1 a1_1
            have keep_lift: "\<exists>x \<in> A - {a}. (a, x) \<in> (limit_to A r) \<and> (x, a) \<in> (limit_to A s)"
              by (meson DiffD1 limit_preserves_preferences1)
            ultimately show ?thesis
              by (simp add: a1 temp lifted_def)
          }
        next
          { assume "\<not>(\<exists>x \<in> A - {a}. a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)" (* \<and> a1: "a \<in> A" *)
            hence a1_2: "\<forall>x \<in> A - {a}. \<not>(a \<preceq>\<^sub>r x \<and> x \<preceq>\<^sub>s a)"
              by auto
            moreover from lifted subset
            have not_worse: "\<forall>x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x)"
              using lifted_impl_not_worse
              by fastforce
            moreover from lifted subset
            have connex: "connex_on A (limit_to A r) \<and> connex_on A (limit_to A s)"
              by (meson lifted_def limit_preserves_linear_order linear_order_impl_connex)
            ultimately have r_eq_s_on_A: "\<forall>x \<in> A - {a}. (a \<preceq>\<^sub>r x \<and> a \<preceq>\<^sub>s x) \<or> (x \<preceq>\<^sub>r a \<and> x \<preceq>\<^sub>s a)"
              by (smt DiffD1 a1 connex_on_def limit_preserves_preferences2)
            from this a1 a1_2 not_worse
            have "\<forall>x \<in> A - {a}. (a, x) \<in> (limit_to A r) \<longleftrightarrow> (a, x) \<in> (limit_to A s)"
              by (metis DiffD1 limit_preserves_preferences1 limit_preserves_preferences2)
            moreover from r_eq_s_on_A a1 a1_2 not_worse
            have "\<forall>x \<in> A - {a}. (x, a) \<in> (limit_to A r) \<longleftrightarrow> (x, a) \<in> (limit_to A s)"
              by (metis DiffD1 limit_preserves_preferences1 limit_preserves_preferences2)
            moreover from lifted a1
            have "(a, a) \<in> (limit_to A r) \<and> (a, a) \<in> (limit_to A s)"
              by (meson connex connex_impl_refl refl_onD)
            moreover have "limited_to A (limit_to A r) \<and> limited_to A (limit_to A s)"
              using limit_to_limits
              by blast
            ultimately have "\<forall>x y. (x, y) \<in> limit_to A r \<longleftrightarrow> (x, y) \<in> limit_to A s"
              by (smt eql_rs insertE insert_Diff limited_dest)
            thus ?thesis
              by (simp add: subset_antisym subset_iff)
          }
        qed }
    next
      { assume a2: "a \<notin> A"
        from this eql_rs
        have "\<forall>x \<in> A. \<forall>y \<in> A. (x, y) \<in> (limit_to A r) \<longleftrightarrow> (x, y) \<in> (limit_to A s)"
          by simp
        thus ?thesis
          by (meson limit_to_limits limited_dest subrelI subset_antisym)
      }
    qed }
qed

lemma remove_only_difference:
  assumes change: "only_change S r s a" and
          subset: "A \<subseteq> S" and
          notInA: "a \<notin> A"
  shows "limit_to A r = limit_to A s"
proof -
  have "A \<subseteq> S-{a}"
    by (simp add: notInA subset subset_Diff_insert)
  hence "\<forall>x \<in> A. \<forall>y \<in> A. x \<preceq>\<^sub>r y \<longleftrightarrow> x \<preceq>\<^sub>s y"
    by (meson change only_change_def subsetCE)
  thus ?thesis
    by auto
qed

lemma self_in_above:
  assumes "connex_on A r" and
          "a \<in> A"
  shows "a \<in> above r a"
  by (meson assms connex_impl_refl in_above)

lemma above_in_relation_equiv: "a \<preceq>\<^sub>r b \<longleftrightarrow> b \<in> above r a"
  by (simp add: above_def)

lemma not_lin_order_on_empty:
  assumes "r \<noteq> {}"
  shows "\<not>linear_order_on {} r"
  using assms connex_impl_refl linear_order_impl_connex refl_on_domain subrelI
  by fastforce

lemma only_lin_order_on_singleton: "\<forall>r. linear_order_on {a} r \<longrightarrow> r = {(a, a)}"
proof
  { fix r show "linear_order_on {a} r \<longrightarrow> r = {(a, a)}"
    proof
      { assume asm: "linear_order_on {a} r"
        hence "a \<preceq>\<^sub>r a"
          by (meson connex_on_def linear_order_impl_connex singletonI)
        moreover have "\<forall>(x, y) \<in> r. x = a \<and> y = a"
          using asm connex_impl_refl linear_order_impl_connex refl_on_domain split_beta
          by fastforce
        ultimately show "r = {(a, a)}"
          by blast
      }
    qed }
qed

lemma limit_preserves_above:
  assumes "b \<in> above r a" and
          (*"linear_order_on A r" and
          "B \<subseteq> A" and ??? *)
          "a \<in> B \<and> b \<in> B"
        shows "b \<in> above (limit_to B r) a"
  by (meson above_in_relation_equiv assms limit_preserves_preferences1)

lemma limit_preserves_above2:
  assumes "b \<in> above (limit_to B r) a" and
          "linear_order_on A r" and
          "B \<subseteq> A" and
          "a \<in> B" and
          "b \<in> B"
        shows "b \<in> above r a"
  by (metis above_def assms(1) limit_preserves_preferences2 mem_Collect_eq)

lemma linear_order_above_one_winner:
  assumes "linear_order_on A r" and
          "finite A \<and> A \<noteq> {}"
  shows "\<exists>a\<in>A. above r a = {a} \<and> (\<forall>x\<in>A. above r x = {x} \<longrightarrow> x = a)"
proof -
  obtain n::nat where n: "n+1 = card A"
    by (metis Suc_eq_plus1 antisym_conv2 assms(2) card_eq_0_iff gr0_implies_Suc le0)
    { have "(linear_order_on A r \<and> finite A \<and> A \<noteq> {} \<and> n+1 = card A) \<longrightarrow>
              (\<exists>a. a\<in>A \<and> above r a = {a})"
      proof (induction n arbitrary: A r)
        case 0
          { show ?case
            proof
              assume asm: "linear_order_on A r \<and> finite A \<and> A \<noteq> {} \<and> 0+1 = card A"
              then obtain a where
                  "{a} = A"
                using card_1_singletonE
                by auto
              hence "a \<in> A \<and> above r a = {a}"
                using above_def asm connex_impl_refl in_above linear_order_impl_connex
                      refl_on_domain
                by fastforce
              thus "\<exists>a. a\<in>A \<and> above r a = {a}"
                by auto
            qed }
        next
          case (Suc n)
          { show ?case
            proof
              { assume asm: "linear_order_on A r \<and> finite A \<and> A \<noteq> {} \<and> Suc n+1 = card A"
                then obtain B where B: "card B = n+1 \<and> B \<subseteq> A"
                  by (smt Suc_inject add_Suc card.insert_remove finite.cases insert_Diff_single
                      subset_insertI)
                then obtain a where a: "{a} = A - B"
                  by (metis Suc_eq_plus1 add_diff_cancel_left' asm card_1_singletonE
                      card_Diff_subset finite_subset)
                have "\<exists>b\<in>B. above (limit_to B r) b = {b}"
                  by (metis B One_nat_def Suc.IH add_diff_cancel_left' asm card_empty diff_le_self
                      finite_subset leD lessI limit_preserves_linear_order)
                then obtain b where b: "above (limit_to B r) b = {b}"
                  by blast
                show "\<exists>a. a \<in> A \<and> above r a = {a}"
                proof cases
                  { assume "a \<preceq>\<^sub>r b"
                    moreover have "\<forall>x \<in> B. b \<in> above r x"
                      using limit_preserves_above2
                      by (smt B above_in_relation_equiv asm b connex_impl_refl
                          limit_preserves_linear_order linear_order_impl_connex order_on_defs(3)
                          refl_on_domain singletonD singletonI total_on_def)
                    ultimately have b_wins: "\<forall>x \<in> A. b \<in> above r x"
                      using a above_in_relation_equiv
                      by fastforce
                    hence "\<forall>x \<in> A. x \<in> above r b \<longrightarrow> x = b"
                      by (metis CollectD above_def antisym_def asm lin_imp_antisym)
                    hence "\<forall>x \<in> A. x \<in> above r b \<longleftrightarrow> x = b"
                      using b_wins
                      by blast
                    moreover have above_b_in_A: "above r b \<subseteq> A"
                      using above_def asm connex_impl_refl linear_order_impl_connex mem_Collect_eq
                            refl_on_domain
                      by fastforce
                    ultimately have "above r b = {b}"
                      using above_def b
                      by fastforce
                    thus ?thesis
                      using above_b_in_A
                      by blast
                  }
                next
                  { assume "\<not>a \<preceq>\<^sub>r b"
                    hence b_smaller_a: "b \<preceq>\<^sub>r a"
                      by (metis B CollectD DiffE a above_def asm b limit_to_limits limited_dest
                          order_on_defs(3) singletonI subset_iff total_on_def)
                    have "\<forall>x \<in> B. b \<in> above r x"
                      using limit_preserves_above2
                      by (smt B above_in_relation_equiv asm b connex_impl_refl
                          limit_preserves_linear_order linear_order_impl_connex order_on_defs(3)
                          refl_on_domain singletonD singletonI total_on_def)
                    hence "\<forall>x \<in> B. x \<preceq>\<^sub>r b"
                      by (simp add: above_def)
                    hence "\<forall>x \<in> B. x \<preceq>\<^sub>r a"
                      using b_smaller_a lin_imp_trans
                      by (metis asm transE)
                    hence nothing_above_a: "\<forall>x \<in> A. x \<preceq>\<^sub>r a"
                      using a above_def asm linear_order_impl_connex self_in_above
                      by fastforce
                    have "\<forall>x \<in> A. x \<in> above r a \<longleftrightarrow> x = a"
                      using above_def antisym_def asm lin_imp_antisym nothing_above_a
                      by fastforce
                    moreover have above_a_in_A: "above r a \<subseteq> A"
                      using above_def asm connex_impl_refl linear_order_impl_connex mem_Collect_eq
                            refl_on_domain
                      by fastforce
                    ultimately have "above r a = {a}"
                      using above_def a
                      by fastforce
                    thus ?thesis
                      using above_a_in_A
                      by auto
                  }
                qed }
            qed }
      qed }
  hence "\<exists>a. a\<in>A \<and> above r a = {a}"
    using assms n
    by blast
  thus ?thesis
    by (smt Diff_eq_empty_iff above_decr assms(1) empty_Diff insertE insert_Diff_if insert_absorb
        insert_not_empty order_on_defs(1) order_on_defs(2) order_on_defs(3) total_on_def)
qed


lemma linear_order_above_one_winner2:
  assumes "linear_order_on A r" and
          "finite A \<and> A \<noteq> {}" and
          "above r a = {a} \<and> above r b = {b}"
  shows "a = b"
  by (metis (no_types, lifting) above_in_relation_equiv assms(1) assms(2) assms(3) connex_impl_refl
      insert_iff linear_order_above_one_winner linear_order_impl_connex  refl_on_domain subsetI
      subset_antisym)

lemma lifted_above_winner:
  assumes "lifted A r s a" and
          "above r x = {x}" and
          "finite A"
  shows "above s x = {x} \<or> above s a = {a}"
proof cases
  assume "x = a"
  thus ?thesis
    by (metis above_subset_geq_one assms(1) assms(2) lifted_above lifted_def)
  next
    { assume asm1: "x \<noteq> a"
      thus ?thesis
      proof cases
        { assume "above s x = {x}"
          thus ?thesis
            by simp
        }
      next
        assume asm2: "above s x \<noteq> {x}" (* \<and> asm1: x \<noteq> a *)
          { have "\<forall>y \<in> A. y \<preceq>\<^sub>r x"
            proof -
              { fix aa :: 'a
                have "x \<preceq>\<^sub>r aa \<longrightarrow> aa \<notin> A \<or> aa \<preceq>\<^sub>r x"
                  by (simp add: above_in_relation_equiv assms(2))
                hence "aa \<notin> A \<or> aa \<preceq>\<^sub>r x"
                  by (metis (no_types) above_in_relation_equiv assms(1) assms(2) connex_impl_refl
                      connex_on_def lifted_def linear_order_impl_connex refl_on_domain singleton_iff)
              }
              then show ?thesis
                by meson
            qed }
      moreover have "x \<in> A-{a}"
        by (metis asm1 assms(1) calculation connex_impl_refl lifted_def linear_order_impl_connex
            member_remove refl_on_domain remove_def)
      ultimately have "\<forall>y \<in> A-{a}. y \<preceq>\<^sub>s x"
        by (meson DiffD1 assms(1) lifted_def)
      hence not_others: "\<forall>y \<in> A-{a}. above s y \<noteq> {y}"
        by (metis asm2 above_def empty_iff insert_iff mem_Collect_eq)
      hence "above s a = {a}"
        by (metis Diff_iff all_not_in_conv assms(1) assms(3) lifted_def
            linear_order_above_one_winner singleton_iff)
      thus ?thesis
        by simp
      qed }
qed

lemma lifted_above_winner2:
  assumes "lifted A r s a" and
          "above r a = {a}" and
          "finite A"
  shows "above s a = {a}"
  by (meson assms lifted_above_winner)

lemma lifted_above_winner3:
  assumes "lifted A r s a" and
          "above s x = {x}" and
          "finite A" and
          "x \<noteq> a"
  shows "above r x = {x}"
proof (rule ccontr)
  assume asm: "above r x \<noteq> {x}"
  then obtain y where y: "above r y = {y}"
    by (metis assms(1) assms(3) insert_Diff insert_not_empty lifted_def
        linear_order_above_one_winner)
  hence "above s y = {y} \<or> above s a = {a}"
    by (meson assms(1) assms(3) lifted_above_winner)
  moreover have "\<forall>b. above s b = {b} \<longrightarrow> b = x"
    using linear_order_above_one_winner
    by (metis above_in_relation_equiv all_not_in_conv assms(1) assms(2) assms(3) connex_impl_refl
        insertI1 lifted_def linear_order_impl_connex refl_on_domain)
  ultimately have "y = x"
    using assms(4)
    by auto
  moreover have "y \<noteq> x"
    using asm y
    by blast
  ultimately show "False"
    by simp
qed

lemma limited_above_subset:
  assumes "linear_order r"
  shows "above (limit_to A r) x \<subseteq> A"
  by (metis CollectD above_def assms connex_impl_refl limit_preserves_connectivity
      linear_order_impl_connex refl_on_domain subset_UNIV subset_iff)

end

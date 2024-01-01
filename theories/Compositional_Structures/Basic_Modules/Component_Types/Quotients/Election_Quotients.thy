theory Election_Quotients
  imports Relation_Quotients
          "../Social_Choice_Types/Property_Interpretations"
          "HOL-Library.Extended_Real"
          "HOL-Analysis.Cartesian_Euclidean_Space"
          "HOL-Combinatorics.Multiset_Permutations"
begin
(*"HOL-Analysis.Simplex_Content" *)
subsection \<open>Auxiliary Definitions\<close>

fun fst_ind :: "'x list \<Rightarrow> 'x \<Rightarrow> int" where
  "fst_ind [] x = -1" |
  "fst_ind (y#xs) x = 
    (if (y = x) then 0 else 
      (let fst_ind' = fst_ind xs x in (if fst_ind' = -1 then -1 else 1 + fst_ind')))"

fun lin_ord_of_list :: "'x list \<Rightarrow> 'x rel" where
    "lin_ord_of_list l = {(x, y) \<in> set l \<times> set l. fst_ind l x \<le> fst_ind l y}"

subsection \<open>Auxiliary Lemmas\<close>

lemma fst_ind_is_fst_ind:
  fixes
    l :: "'x list" and
    x :: 'x and i :: int
  shows
    minus_one_no_el: "i = fst_ind l x \<longrightarrow> (i = -1 \<longleftrightarrow> x \<notin> set l)" and
    nonneg_fst_ind: "i = fst_ind l x \<longrightarrow> 
      (x \<in> set l \<longleftrightarrow> i \<ge> 0 \<and> l!(nat i) = x \<and> (\<forall>j < nat i. l!j \<noteq> x))"
proof (induction l arbitrary: i, simp, clarify)
  have "(0 \<le> fst_ind [] x) = False"
    by simp
  hence "False = 
    (0 \<le> fst_ind [] x \<and> [] ! nat (fst_ind [] x) = x \<and> (\<forall>j<nat (fst_ind [] x). [] ! j \<noteq> x))"
    by simp
  thus
    "(x \<in> set []) =
         (0 \<le> fst_ind [] x \<and> [] ! nat (fst_ind [] x) = x \<and> (\<forall>j<nat (fst_ind [] x). [] ! j \<noteq> x))"
    by simp
next
  fix
    a :: 'x and
    i :: int and
    l :: "'x list"
  assume
    "\<And>i. i = fst_ind l x \<longrightarrow> (i = - 1) = (x \<notin> set l)" and
    "\<And>i. i = fst_ind l x \<longrightarrow> (x \<in> set l) = (0 \<le> i \<and> l ! nat i = x \<and> (\<forall>j<nat i. l ! j \<noteq> x))"
  thus "i = fst_ind (a # l) x \<longrightarrow> (i = - 1) = (x \<notin> set (a # l))"
    sorry
next
  fix
    a :: 'x and
    i :: int and
    l :: "'x list"
  assume
    "\<And>i. i = fst_ind l x \<longrightarrow> (i = - 1) = (x \<notin> set l)" and
    "\<And>i. i = fst_ind l x \<longrightarrow> (x \<in> set l) = (0 \<le> i \<and> l ! nat i = x \<and> (\<forall>j<nat i. l ! j \<noteq> x))"
  thus
    "i = fst_ind (a # l) x \<longrightarrow>
       (x \<in> set (a # l)) = (0 \<le> i \<and> (a # l) ! nat i = x \<and> (\<forall>j<nat i. (a # l) ! j \<noteq> x))"
    sorry
qed

lemma fst_ind_inj:
  fixes
    l :: "'x list" and
    x :: 'x and y :: 'x
  assumes
    "x \<in> set l" and
    "y \<in> set l" and
    "x \<noteq> y"
  shows
    "fst_ind l x \<noteq> fst_ind l y"
proof (safe)
  assume
    "fst_ind l x = fst_ind l y"
  moreover have nonneg: "fst_ind l x \<ge> 0 \<and> fst_ind l y \<ge> 0"
    using nonneg_fst_ind assms nat_eq_iff2
    by metis
  ultimately have "l!(nat (fst_ind l x)) = l!(nat (fst_ind l y))"
    by simp
  moreover have "l!(nat (fst_ind l x)) = x \<and> l!(nat (fst_ind l y)) = y"
    using nonneg_fst_ind nonneg assms
    by metis
  ultimately show "False"
    using \<open>x \<noteq> y\<close>
    by simp
qed

lemma fst_ind_bij:
  fixes
    X :: "'x set" and
    l :: "'x list"
  assumes
    "finite X" and
    "set l = X" and
    "distinct l"  
  shows
    "bij_betw (fst_ind l) X {0..<length l}"
proof (unfold bij_betw_def, safe)
  show "inj_on (fst_ind l) X"
    using fst_ind_inj assms
    unfolding inj_on_def
    by meson
next
  fix
    x :: 'x
  assume
    "x \<in> X"
  hence "x \<in> set l" 
    using assms
    by simp
  hence is_index:
    "0 \<le> fst_ind l x \<and> l ! nat (fst_ind l x) = x \<and> (\<forall>j < nat (fst_ind l x). l ! j \<noteq> x)"
    using nonneg_fst_ind[of _ l x]
    by blast
  moreover from this have "nat (fst_ind l x) < length l"
    using \<open>x \<in> X\<close> assms(2) atLeast0LessThan 
          diff_diff_cancel in_set_conv_nth
          less_imp_diff_less linorder_not_le
          bot_nat_0.extremum
    by metis
  ultimately show "fst_ind l x \<in> {0..<int (length l)}"
    using is_index nat_less_iff 
    by force
next
  fix
    i :: int
  assume
    i_rng: "i \<in> {0..<int (length l)}"
  hence fst_ind_i:
    "0 \<le> fst_ind l (l!nat i) \<and> l!(nat (fst_ind l (l!nat i))) = l!(nat i) \<and> 
    (\<forall>j < nat (fst_ind l (l!nat i)). l!j \<noteq> l!(nat i))"
    using assms nonneg_fst_ind[of _ l "l!nat i"] int_eq_iff 
          atLeastLessThan_iff nat_less_iff nth_mem
    by meson
  hence ge: "nat i \<ge> nat (fst_ind l (l!nat i))"
    using linorder_le_less_linear 
    by blast
  have "\<forall>j < nat i. l!j \<noteq> l!(nat i)"
    using assms(3) i_rng nth_eq_iff_index_eq 
    by fastforce
  hence "nat i \<le> nat (fst_ind l (l!nat i))"
    using fst_ind_i linorder_le_less_linear 
    by blast
  hence "nat i = nat (fst_ind l (l!nat i))"
    using ge
    by simp
  hence "i = fst_ind l (l!nat i)"
    by (metis atLeastLessThan_iff fst_ind_i i_rng int_nat_eq)
  moreover from i_rng have "l!(nat i) \<in> X"
    using assms atLeastLessThan_iff nat_less_iff nth_mem
    by meson
  ultimately show "i \<in> fst_ind l ` X"
    by blast
qed

lemma lin_ord_of_list_bij_betw:
  fixes
    X :: "'x set"
  assumes
    "finite X"
  shows
    "bij_betw lin_ord_of_list (permutations_of_set X) {r :: 'x rel. linear_order_on X r}"
  sorry
(* proof (unfold bij_betw_def inj_on_def permutations_of_set_def, safe) *)

lemma fin_ordered:
  fixes
    X :: "'x set" 
  assumes
    "finite X"
  obtains ord :: "'x rel" where "linear_order_on X ord"
proof -
  assume
    ex: "\<And>ord. linear_order_on X ord \<Longrightarrow> thesis"
  obtain l :: "'x list" where "set l = X"
    using finite_list assms
    by blast
  let ?r = "lin_ord_of_list l"
  have "antisym ?r"
    using fst_ind_inj \<open>set l = X\<close>
    unfolding antisym_def
    by fastforce
  moreover have "refl_on X ?r"
    using \<open>set l = X\<close>
    unfolding refl_on_def lin_ord_of_list.simps
    by blast
  moreover have "trans ?r"
    unfolding trans_def
    by simp
  moreover have "total_on X ?r"
    using \<open>set l = X\<close>
    unfolding total_on_def
    by force
  ultimately have "linear_order_on X ?r"
    unfolding linear_order_on_def preorder_on_def partial_order_on_def
    by blast
  thus thesis
    using ex
    by blast
qed

lemma obtain_partition:
  fixes
    X :: "'x set" and
    N :: "'y \<Rightarrow> nat" and
    Y :: "'y set"
  assumes
    "finite X" and
    "finite Y" and
    "sum N Y = card X"
  shows
    "\<exists>\<X>. X = \<Union>{\<X> i |i. i \<in> Y} \<and> (\<forall>i \<in> Y. card (\<X> i) = N i) \<and> 
         (\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
  using assms
proof (induction "card Y" arbitrary: X Y)
  case 0
  fix
    X :: "'x set" and
    Y :: "'y set"
  assume
    fin_X: "finite X" and
    card_X: "sum N Y = card X" and
    fin_Y: "finite Y" and
    card_Y: "0 = card Y"
  let ?\<X> = "\<lambda>y. {}"
  have "Y = {}"
    using 0 fin_Y card_Y
    by simp
  hence "sum N Y = 0"
    by simp
  hence "X = {}"
    using fin_X card_X
    by simp
  hence "X = \<Union> {?\<X> i |i. i \<in> Y}"
    by blast
  moreover have 
    "\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> ?\<X> i \<inter> ?\<X> j = {}"
    by blast
  ultimately show
    "\<exists>\<X>. X = \<Union> {\<X> i |i. i \<in> Y} \<and>
                (\<forall>i\<in>Y. card (\<X> i) = N i) \<and> (\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"   
    by (simp add: \<open>Y = {}\<close>)
next
  case (Suc x)
  fix
    x :: nat and
    X :: "'x set" and
    Y :: "'y set"
  assume
    card_Y: "Suc x = card Y" and
    fin_Y: "finite Y" and
    fin_X: "finite X" and 
    card_X: "sum N Y = card X" and
    hyp: 
      "\<And>Y (X::'x set). 
         x = card Y \<Longrightarrow>
         finite X \<Longrightarrow>
         finite Y \<Longrightarrow>
         sum N Y = card X \<Longrightarrow>
         \<exists>\<X>. 
          X = \<Union> {\<X> i |i. i \<in> Y} \<and>
                  (\<forall>i\<in>Y. card (\<X> i) = N i) \<and> (\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
  then obtain Y' :: "'y set" and y :: 'y where 
    "Y = insert y Y'" and "card Y' = x" and "finite Y'" and "y \<notin> Y'"
    using card_Suc_eq_finite
    by (metis (no_types, lifting))
  hence "N y \<le> card X"
    using card_X card_Y fin_Y le_add1 n_not_Suc_n sum.insert
    by metis
  then obtain X' :: "'x set" where "X' \<subseteq> X" and "card X' = N y"
    using fin_X ex_card
    by meson
  hence "finite (X - X') \<and> card (X - X') = sum N Y'"
    using card_Y card_X fin_X fin_Y \<open>Y = insert y Y'\<close> \<open>card Y' = x\<close> \<open>finite Y'\<close> 
          Suc_n_not_n add_diff_cancel_left' card_Diff_subset card_insert_if 
          finite_Diff finite_subset sum.insert
    by metis
  then obtain \<X> :: "'y \<Rightarrow> 'x set" where
    part: "X - X' = \<Union>{\<X> i |i. i \<in> Y'}" and 
    disj: "\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y' \<and> j \<in> Y' \<longrightarrow> \<X> i \<inter> \<X> j = {}" and
    card: "\<forall>i \<in> Y'. card (\<X> i) = N i"
    using hyp[of Y' "X - X'"] \<open>finite Y'\<close> \<open>card Y' = x\<close>
    by auto
  then obtain \<X>' :: "'y \<Rightarrow> 'x set" where 
    map': "\<X>' = (\<lambda>z. if (z = y) then X' else \<X> z)"
    by simp
  hence eq_\<X>: "\<forall>i \<in> Y'. \<X>' i = \<X> i"
    using \<open>y \<notin> Y'\<close>
    by auto
  have "Y = {y} \<union> Y'"
    using \<open>Y = insert y Y'\<close>
    by fastforce
  hence "\<forall>f. {f i |i. i \<in> Y} = {f y} \<union> {f i |i. i \<in> Y'}"
    by auto
  hence "{\<X>' i |i. i \<in> Y} = {\<X>' y} \<union> {\<X>' i |i. i \<in> Y'}"
    by metis
  hence "\<Union>{\<X>' i |i. i \<in> Y} = \<X>' y \<union> \<Union>{\<X>' i |i. i \<in> Y'}"
    by simp
  also have "\<X>' y = X'"
    using map'
    by presburger
  also have "\<Union>{\<X>' i |i. i \<in> Y'} = \<Union>{\<X> i |i. i \<in> Y'}"
    using eq_\<X>
    by blast
  finally have part': "X = \<Union>{\<X>' i |i. i \<in> Y}"
    using part
    by (metis Diff_partition \<open>X' \<subseteq> X\<close>)
  have "\<forall>i \<in> Y'. \<X>' i \<subseteq> X - X'"
    using part eq_\<X>
    by (metis Setcompr_eq_image UN_upper)
  hence "\<forall>i \<in> Y'. \<X>' i \<inter> X' = {}"
    by blast
  hence "\<forall>i \<in> Y'. \<X>' i \<inter> \<X>' y = {}"
    using map'
    by simp
  hence "\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X>' i \<inter> \<X>' j = {}"
    using map' disj \<open>Y = insert y Y'\<close> inf.commute insertE
    by (metis (no_types, lifting))
  moreover have "\<forall>i \<in> Y. card (\<X>' i) = N i"
    using map' card \<open>card X' = N y\<close> \<open>Y = insert y Y'\<close>
    by simp
  ultimately show
    "\<exists>\<X>. X = \<Union> {\<X> i |i. i \<in> Y} \<and>
                (\<forall>i\<in>Y. card (\<X> i) = N i) \<and> (\<forall>i j. i \<noteq> j \<longrightarrow> i \<in> Y \<and> j \<in> Y \<longrightarrow> \<X> i \<inter> \<X> j = {})"
    using part'
    by blast
qed

lemma rel_ind_by_action_subset:
  fixes
    X :: "'x set" and
    Y :: "'y set" and
    Z :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun" and 
    \<phi>' :: "('x, 'y) binary_fun"
  assumes
    "Z \<subseteq> Y" and
    "\<forall>x \<in> X. \<forall>z \<in> Z. \<phi>' x z = \<phi> x z"
  shows
    "rel_induced_by_action X Z \<phi>' = Restr (rel_induced_by_action X Y \<phi>) Z"
proof (unfold rel_induced_by_action.simps)
  have 
    "{(y1, y2). (y1, y2) \<in> Z \<times> Z \<and> (\<exists>x\<in>X. \<phi>' x y1 = y2)} = 
      {(y1, y2). (y1, y2) \<in> Z \<times> Z \<and> (\<exists>x\<in>X. \<phi> x y1 = y2)}"
    using assms
    by auto
  also have 
    "... = Restr {(y1, y2). (y1, y2) \<in> Y \<times> Y \<and> (\<exists>x\<in>X. \<phi> x y1 = y2)} Z"
    using assms
    by blast
  finally show 
    "{(y1, y2). (y1, y2) \<in> Z \<times> Z \<and> (\<exists>x\<in>X. \<phi>' x y1 = y2)} =
      Restr {(y1, y2). (y1, y2) \<in> Y \<times> Y \<and> (\<exists>x\<in>X. \<phi> x y1 = y2)} Z"
    by simp
qed

subsection \<open>Definitions\<close>

(* fun isomorphic :: "'x set \<Rightarrow> 'y set \<Rightarrow> bool" where
  "isomorphic X Y = (\<exists>f :: 'x \<Rightarrow> 'y. bij_betw f X Y)" *)

typedef 'a Ordered_Preference = 
  "{p :: 'a::finite Preference_Relation. linear_order_on (UNIV::'a set) p}"
  morphisms ord2pref pref2ord
proof (simp)
  have "finite (UNIV::'a set)"
    by simp
  then obtain p :: "'a Preference_Relation" where
    "linear_order_on (UNIV::'a set) p"
    using fin_ordered[of UNIV False]
    by blast
  thus "\<exists>p::'a Preference_Relation. linear_order p"
    by blast
qed

instance Ordered_Preference :: (finite) finite
proof
  have 
    "(UNIV::'a Ordered_Preference set) = 
      pref2ord ` {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    using type_definition.card type_definition_Ordered_Preference type_definition.univ 
    by blast
  moreover have "finite {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    by simp
  ultimately show "finite (UNIV::'a Ordered_Preference set)"
    by (metis finite_imageI)
qed

lemma card_ord_pref:
"CARD ('a::finite Ordered_Preference) = fact (CARD ('a))"
proof -
  let ?n = "card (UNIV::'a set)" and
      ?perm = "permutations_of_set (UNIV :: 'a set)" and
      ?univ' = "{p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
  have "card ?perm = fact ?n"
    by simp
  moreover have "CARD ('a::finite Ordered_Preference) = 
    card {p :: 'a Preference_Relation. linear_order_on (UNIV::'a set) p}"
    using type_definition.card type_definition_Ordered_Preference 
    by blast
  moreover have "?n = CARD ('a)"
    by simp
  ultimately show ?thesis
    using bij_betw_same_card lin_ord_of_list_bij_betw[of "UNIV::'a set"] 
    by force
qed

subsection \<open>Anonymity Quotient - Grid\<close>

\<comment> \<open>The election equivalence classes of the anonymity equivalence relation.\<close>
fun anonymity\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anonymity\<^sub>\<Q> A = quotient (fixed_alt_elections A) (anonymity\<^sub>\<R> (fixed_alt_elections A))"

\<comment> \<open>Counts the occurrences of a ballot per election in a set of elections
    if the occurrences of the ballot per election coincide for all elections in the set.\<close>      
fun vote_count\<^sub>\<Q> :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election set \<Rightarrow> nat" where
  "vote_count\<^sub>\<Q> p = \<pi>\<^sub>\<Q> (vote_count p)"

fun anon_cls_to_vec :: 
  "('a::finite, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec" where
  "anon_cls_to_vec X = (\<chi> p. vote_count\<^sub>\<Q> (ord2pref p) X)"

text \<open>
  We assume all our elections to consist of a fixed finite alternative set of size n and
  finite subsets of an infinite voter universe. Profiles are linear orders on the alternatives.
  Then we can work on the natural-number-vectors of dimension n! instead of the equivalence 
  classes of the anonymity relation:
  Each dimension corresponds to one possible linear order on the alternative set, 
  i.e. the possible preferences.
  Each equivalence class of elections corresponds to a vector whose entries denote the amount 
  of voters per election in that class who vote the respective corresponding preference.
\<close>
theorem anonymity\<^sub>\<Q>_iso:
  assumes
    "infinite (UNIV::('v set))" 
    \<comment> \<open>Assume an infinite voter universe so that we can choose arbitrarily large voter sets.\<close>
  shows
    "bij_betw (anon_cls_to_vec::('a::finite, 'v) Election set \<Rightarrow> nat^('a Ordered_Preference)) 
              (anonymity\<^sub>\<Q> (UNIV::'a set)) (UNIV::(nat^('a Ordered_Preference)) set)"
proof (unfold bij_betw_def inj_on_def, standard, standard, standard, standard)
  fix
    X :: "('a, 'v) Election set" and
    Y :: "('a, 'v) Election set"
  assume
    cls_X: "X \<in> anonymity\<^sub>\<Q> UNIV" and
    cls_Y: "Y \<in> anonymity\<^sub>\<Q> UNIV" and
    eq_vec: "anon_cls_to_vec X = anon_cls_to_vec Y"
  have "\<forall>E \<in> fixed_alt_elections UNIV. finite (votrs_\<E> E)"
    by simp
  hence "\<forall>(E, E') \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV). finite (votrs_\<E> E)"
    unfolding anonymity\<^sub>\<R>.simps rel_induced_by_action.simps fixed_alt_elections.simps
    by force
  moreover have subset: "fixed_alt_elections UNIV \<subseteq> valid_elections"
    by simp
  ultimately have
    "\<forall>(E, E') \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV). \<forall>p. vote_count p E = vote_count p E'"
    using anon_rel_vote_count[of _ _ "fixed_alt_elections UNIV"]
    by blast
  hence vote_count_invar:
    "\<forall>p. (vote_count p) respects (anonymity\<^sub>\<R> (fixed_alt_elections UNIV))"
    unfolding congruent_def
    by blast  
  have 
    "equiv valid_elections (anonymity\<^sub>\<R> valid_elections)"
    using rel_ind_by_grp_act_equiv[of anonymity\<^sub>\<G> valid_elections "\<phi>_anon valid_elections"]
          rel_ind_by_action_subset[of "fixed_alt_elections UNIV" valid_elections
                                      "carrier anonymity\<^sub>\<G>" "\<phi>_anon valid_elections"]
    by (simp add: anon_grp_act.group_action_axioms)
  moreover have
    "\<forall>\<pi> \<in> carrier anonymity\<^sub>\<G>.
      \<forall>E\<in>fixed_alt_elections UNIV. 
        \<phi>_anon (fixed_alt_elections UNIV) \<pi> E = \<phi>_anon valid_elections \<pi> E"
    using subset
    unfolding \<phi>_anon.simps
    by simp
  ultimately have equiv_rel:
    "equiv (fixed_alt_elections UNIV) (anonymity\<^sub>\<R> (fixed_alt_elections UNIV))"
    using subset rel_ind_by_action_subset[of
            "fixed_alt_elections UNIV" valid_elections "carrier anonymity\<^sub>\<G>" 
            "\<phi>_anon (fixed_alt_elections UNIV)" "\<phi>_anon valid_elections"]
          equiv_rel_restr[
            of valid_elections "anonymity\<^sub>\<R> valid_elections" "fixed_alt_elections UNIV"]
    unfolding anonymity\<^sub>\<R>.simps
    by (metis (no_types))
  with vote_count_invar have quotient_count:
    "\<forall>X \<in> anonymity\<^sub>\<Q> UNIV. \<forall>p. \<forall>E \<in> X. vote_count\<^sub>\<Q> p X = vote_count p E"
    using pass_to_quotient[of 
            "anonymity\<^sub>\<R> (fixed_alt_elections UNIV)" "vote_count _" "fixed_alt_elections UNIV"]
    unfolding anonymity\<^sub>\<Q>.simps anonymity\<^sub>\<R>.simps vote_count\<^sub>\<Q>.simps
    by blast
  moreover from equiv_rel 
  obtain E :: "('a, 'v) Election" and E' :: "('a, 'v) Election" where 
    "E \<in> X" and "E' \<in> Y"
    using cls_X cls_Y equiv_Eps_in
    unfolding anonymity\<^sub>\<Q>.simps
    by blast
  ultimately have 
    "\<forall>p. vote_count\<^sub>\<Q> p X = vote_count p E \<and> vote_count\<^sub>\<Q> p Y = vote_count p E'"
    using cls_X cls_Y
    by blast
  moreover with eq_vec have 
    "\<forall>p. vote_count\<^sub>\<Q> (ord2pref p) X = vote_count\<^sub>\<Q> (ord2pref p) Y"
    unfolding anon_cls_to_vec.simps
    using UNIV_I vec_lambda_inverse
    by metis
  ultimately have
    "\<forall>p. vote_count (ord2pref p) E = vote_count (ord2pref p) E'"
    by simp
  hence eq:
    "\<forall>p \<in> {p. linear_order_on (UNIV::'a set) p}.
       vote_count p E = vote_count p E'"
    by (metis pref2ord_inverse)
  from equiv_rel cls_X cls_Y have subset_fixed_alts:
    "X \<subseteq> fixed_alt_elections UNIV \<and> Y \<subseteq> fixed_alt_elections UNIV"
    unfolding anonymity\<^sub>\<Q>.simps
    using in_quotient_imp_subset 
    by blast
  hence eq_alts:
    "alts_\<E> E = UNIV \<and> alts_\<E> E' = UNIV"
    using \<open>E \<in> X\<close> \<open>E' \<in> Y\<close>
    unfolding fixed_alt_elections.simps
    by blast
  with subset_fixed_alts have eq_complement:
    "\<forall>p \<in> UNIV - {p. linear_order_on (UNIV::'a set) p}. 
      {v \<in> votrs_\<E> E. prof_\<E> E v = p} = {} \<and> {v \<in> votrs_\<E> E'. prof_\<E> E' v = p} = {}"
    using \<open>E \<in> X\<close> \<open>E' \<in> Y\<close>
    unfolding fixed_alt_elections.simps valid_elections_def profile_def
    by auto
  hence 
    "\<forall>p \<in> UNIV - {p. linear_order_on (UNIV::'a set) p}. 
      vote_count p E = 0 \<and> vote_count p E' = 0"
    unfolding vote_count.simps
    by (simp add: card_eq_0_iff)
  with eq have eq_vote_count: 
    "\<forall>p. vote_count p E = vote_count p E'"
    by (metis DiffI UNIV_I)
  moreover from subset_fixed_alts \<open>E \<in> X\<close> \<open>E' \<in> Y\<close> have 
    "finite (votrs_\<E> E) \<and> finite (votrs_\<E> E')"
    unfolding fixed_alt_elections.simps
    by blast
  moreover from subset_fixed_alts \<open>E \<in> X\<close> \<open>E' \<in> Y\<close> have
    "(E, E') \<in> (fixed_alt_elections UNIV) \<times> (fixed_alt_elections UNIV)"
    by blast
  ultimately have
    "(E, E') \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV)"
    using eq_alts vote_count_anon_rel
    by metis
  hence 
    "anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {E} = anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {E'}"
    using equiv_rel
    by (metis equiv_class_eq)
  also have "anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {E} = X"
    using \<open>E \<in> X\<close> cls_X equiv_rel
    unfolding anonymity\<^sub>\<Q>.simps
    by (metis (no_types, lifting) Image_singleton_iff equiv_class_eq quotientE)
  also have "anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {E'} = Y"
    using \<open>E' \<in> Y\<close> cls_Y equiv_rel
    unfolding anonymity\<^sub>\<Q>.simps
    by (metis (no_types, lifting) Image_singleton_iff equiv_class_eq quotientE)
  finally show "X = Y"
    by simp
next
  have subset: "fixed_alt_elections UNIV \<subseteq> valid_elections"
      by simp
  have 
    "equiv valid_elections (anonymity\<^sub>\<R> valid_elections)"
    using rel_ind_by_grp_act_equiv[of anonymity\<^sub>\<G> valid_elections "\<phi>_anon valid_elections"]
          rel_ind_by_action_subset[of "fixed_alt_elections UNIV" valid_elections
                                      "carrier anonymity\<^sub>\<G>" "\<phi>_anon valid_elections"]
    by (simp add: anon_grp_act.group_action_axioms)
  \<comment> \<open>TODO: Remove this duplicate, already shown in the previous subgoal...\<close>
  moreover have
    "\<forall>\<pi> \<in> carrier anonymity\<^sub>\<G>.
      \<forall>E\<in>fixed_alt_elections UNIV. 
        \<phi>_anon (fixed_alt_elections UNIV) \<pi> E = \<phi>_anon valid_elections \<pi> E"
    using subset
    unfolding \<phi>_anon.simps
    by simp
  ultimately have equiv_rel:
    "equiv (fixed_alt_elections UNIV) (anonymity\<^sub>\<R> (fixed_alt_elections UNIV))"
    using subset rel_ind_by_action_subset[of
            "fixed_alt_elections UNIV" valid_elections "carrier anonymity\<^sub>\<G>" 
            "\<phi>_anon (fixed_alt_elections UNIV)" "\<phi>_anon valid_elections"]
          equiv_rel_restr[
            of valid_elections "anonymity\<^sub>\<R> valid_elections" "fixed_alt_elections UNIV"]
    unfolding anonymity\<^sub>\<R>.simps
    by (metis (no_types))
  have 
    "(UNIV::((nat, 'a Ordered_Preference) vec set)) \<subseteq> 
      (anon_cls_to_vec::('a, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec) ` 
      anonymity\<^sub>\<Q> UNIV"
  proof (unfold anon_cls_to_vec.simps, safe)
    fix
      x :: "(nat, 'a Ordered_Preference) vec"
    have "finite (UNIV::('a Ordered_Preference set))"
      by simp
    hence "finite {x$i |i. i \<in> UNIV}"
      using finite_Atleast_Atmost_nat 
      by blast
    hence "sum (\<lambda>i. x$i) UNIV < \<infinity>"
      using enat_ord_code(4) 
      by blast
    moreover have "0 \<le> sum (\<lambda>i. x$i) UNIV"
      by blast
    ultimately obtain V :: "'v set" where 
      "finite V" and "card V = sum (\<lambda>i. x$i) UNIV"
      using assms infinite_arbitrarily_large
      by meson
    then obtain X' :: "'a Ordered_Preference \<Rightarrow> 'v set" where
      card': "\<forall>i. card (X' i) = x$i" and
      partition': "V = \<Union>{X' i |i. i \<in> UNIV}" and
      disjoint': "\<forall>i j. i \<noteq> j \<longrightarrow> X' i \<inter> X' j = {}"
      using obtain_partition[of V UNIV "($) x"]
      by auto  
    obtain X :: "'a Preference_Relation \<Rightarrow> 'v set" where
      def_X: "X = (\<lambda>i. if (i \<in> {i. linear_order i}) then X' (pref2ord i) else {})"
      by simp
    hence "{X i |i. i \<notin> {i. linear_order i}} \<subseteq> {{}}"
      by auto
    moreover have 
      "{X i |i. i \<in> {i. linear_order i}} = {X' (pref2ord i) |i. i \<in> {i. linear_order i}}"
      using def_X
      by auto
    moreover have
      "{X i |i. i \<in> UNIV} = {X i |i. i \<in> {i. linear_order i}} \<union> 
                              {X i |i. i \<in> UNIV - {i. linear_order i}}"
      by blast
    ultimately have 
      "{X i |i. i \<in> UNIV} = {X' (pref2ord i) |i. i \<in> {i. linear_order i}} \<or> 
        {X i |i. i \<in> UNIV} = {X' (pref2ord i) |i. i \<in> {i. linear_order i}} \<union> {{}}"
      by auto
    also have 
      "{X' (pref2ord i) |i. i \<in> {i. linear_order i}} = {X' i |i. i \<in> UNIV}"
      by (metis iso_tuple_UNIV_I pref2ord_cases)
    finally have
      "{X i |i. i \<in> UNIV} = {X' i |i. i \<in> UNIV} \<or> 
        {X i |i. i \<in> UNIV} = {X' i |i. i \<in> UNIV} \<union> {{}}"
      by simp
    hence "\<Union>{X i |i. i \<in> UNIV} = \<Union>{X' i |i. i \<in> UNIV}"
      by (metis (no_types, lifting) Sup_union_distrib ccpo_Sup_singleton sup_bot.right_neutral)
    hence partition: "V = \<Union>{X i |i. i \<in> UNIV}"
      using partition'
      by simp
    moreover have "\<forall>i j. i \<noteq> j \<longrightarrow> X i \<inter> X j = {}"
      using disjoint' def_X pref2ord_inject
      by auto
    ultimately have "\<forall>v \<in> V. \<exists>!i. v \<in> X i"
      by auto
    then obtain p :: "'v \<Rightarrow> 'a Preference_Relation" where
      p_X: "\<forall>v \<in> V. v \<in> X (p v)" and p_disj: "\<forall>v \<in> V. \<forall>i. i \<noteq> p v \<longrightarrow> v \<notin> X i"
      by metis
    hence lin_ord: "\<forall>v \<in> V. linear_order (p v)"
      using def_X
      by fastforce
    hence valid:
      "(UNIV, V, p) \<in> fixed_alt_elections UNIV"
      using \<open>finite V\<close>
      unfolding fixed_alt_elections.simps valid_elections_def profile_def
      by auto
    hence
      "\<forall>i. \<forall>E \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}.
        vote_count i E = vote_count i (UNIV, V, p)"
      using anon_rel_vote_count[of "(UNIV, V, p)" _ "fixed_alt_elections UNIV" ]
            \<open>finite V\<close> subset
      by simp
    moreover have 
      "(UNIV, V, p) \<in> anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}"
      using equiv_rel valid
      unfolding Image_def equiv_def refl_on_def
      by blast
    ultimately have eq_vote_count:
      "\<forall>i. vote_count i ` (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = 
            {vote_count i (UNIV, V, p)}"
      by blast
    have "\<forall>i. \<forall>v \<in> V. p v = i \<longleftrightarrow> v \<in> X i"
      using p_X p_disj
      by blast
    hence "\<forall>i. {v \<in> V. p v = i} = {v \<in> V. v \<in> X i}"
      by blast
    moreover have "\<forall>i. X i \<subseteq> V"
      using partition
      by blast
    ultimately have rewr_preimg: "\<forall>i. {v \<in> V. p v = i} = X i"
      by auto
    hence "\<forall>i \<in> {i. linear_order i}. vote_count i (UNIV, V, p) = x$(pref2ord i)"
      unfolding vote_count.simps
      using def_X card'
      by auto
    hence
      "\<forall>i \<in> {i. linear_order i}.
       vote_count i ` (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = {x$(pref2ord i)}"
      using eq_vote_count
      by metis
    hence 
      "\<forall>i \<in> {i. linear_order i}. 
        vote_count\<^sub>\<Q> i (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = x$(pref2ord i)"
      unfolding vote_count\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
      using is_singleton_altdef singleton_set_def_if_card_one 
      by fastforce
    hence 
      "\<forall>i. vote_count\<^sub>\<Q> (ord2pref i) (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = x$i"
      by (metis ord2pref ord2pref_inverse)
    hence 
      "anon_cls_to_vec (anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)}) = x"
      by simp
    moreover have 
      "anonymity\<^sub>\<R> (fixed_alt_elections UNIV) `` {(UNIV, V, p)} \<in> anonymity\<^sub>\<Q> UNIV"
      using valid
      unfolding anonymity\<^sub>\<Q>.simps quotient_def
      by blast
    ultimately show 
      "x \<in> (\<lambda>X::(('a, 'v) Election set). \<chi> p. vote_count\<^sub>\<Q> (ord2pref p) X) ` anonymity\<^sub>\<Q> UNIV"
      using anon_cls_to_vec.elims 
      by blast
  qed
  thus
    "(anon_cls_to_vec::('a, 'v) Election set \<Rightarrow> (nat, 'a Ordered_Preference) vec) ` 
      anonymity\<^sub>\<Q> UNIV = (UNIV::((nat, 'a Ordered_Preference) vec set))"
    by blast
qed

subsection \<open>Homogeneity Quotient - Simplex\<close>

fun votes :: "('a, 'v) Election \<Rightarrow> 'a Preference_Relation set" where
  "votes E = (prof_\<E> E) ` (votrs_\<E> E)"

fun vote_fraction :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election \<Rightarrow> ereal" where
  "vote_fraction r E = 
    (if (finite (votrs_\<E> E)) then (vote_count r E/card (votrs_\<E> E)) else 0)"

fun anon_hom\<^sub>\<R> :: "('a, 'v) Election set \<Rightarrow> ('a, 'v) Election rel" where
  "anon_hom\<^sub>\<R> X = 
    {(E, E') |E E'. E \<in> X \<and> E' \<in> X \<and> 
                    (\<forall>r \<in> (votes E \<union> votes E'). vote_fraction r E = vote_fraction r E')}"

fun anon_hom\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v) Election set set" where
  "anon_hom\<^sub>\<Q> A = quotient (fixed_alt_elections A) (anon_hom\<^sub>\<R> (fixed_alt_elections A))"

lemma anon_hom_equiv_rel:
  fixes
    X :: "('a, 'v) Election set"
  assumes
    "\<forall>E \<in> X. finite (votrs_\<E> E)"
  shows
    "equiv X (anon_hom\<^sub>\<R> X)"
proof (unfold equiv_def refl_on_def trans_def sym_def, safe)

end
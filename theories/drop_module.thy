theory drop_module
imports electoral_modules pass_module

begin

(*******************************)
(*** Definition: Drop Module ***)
(*******************************)

(* This is a family of electoral modules. For a natural number n and a lexicon (linear order) r of
   all alternatives the affiliated drop module rejects the lexicographically first n alternatives
   (from A) and defers the rest. It is primarily used as counterpart of the pass module in a
   parallel composition, to devide alternatives into two groups.
*)
fun Drop_module :: "nat \<Rightarrow> 'a rel \<Rightarrow> 'a Electoral_module" where
  "Drop_module n r A p = ({},
                          {a \<in> A. card(above (limit_to A r) a) \<le> n},
                          {a \<in> A. card(above (limit_to A r) a) > n})"

(* For any natural number and any linear order the affiliated drop module satisfies the
   electoral_module predicate. This ensures it can be used as electoral module in compositions.
*)
lemma drop_module_sound[simp]:
  assumes order: "linear_order r"
  shows "electoral_module (Drop_module n r)"
proof -
  let ?mod = "Drop_module n r"
  have "\<forall>A p. finite_profile A p \<longrightarrow> (\<forall>a \<in> A. a \<in> {x \<in> A. card(above (limit_to A r) x) \<le> n} \<or>
                                              a \<in> {x \<in> A. card(above (limit_to A r) x) > n})"
    by auto
  hence "\<forall>A p. finite_profile A p \<longrightarrow> {a \<in> A. card(above (limit_to A r) a) \<le> n} \<union>
                                      {a \<in> A. card(above (limit_to A r) a) > n} = A"
    by blast
  hence 0: "\<forall>A p. finite_profile A p \<longrightarrow> unify_to A (Drop_module n r A p)"
    by simp
  have "\<forall>A p. finite_profile A p \<longrightarrow> (\<forall>a \<in> A. \<not>(a \<in> {x \<in> A. card(above (limit_to A r) x) \<le> n} \<and>
                                              a \<in> {x \<in> A. card(above (limit_to A r) x) > n}))"
    by auto
  hence "\<forall>A p. finite_profile A p \<longrightarrow> {a \<in> A. card(above (limit_to A r) a) \<le> n} \<inter>
                                      {a \<in> A. card(above (limit_to A r) a) > n} = {}"
    by blast
  hence 1: "\<forall>A p. finite_profile A p \<longrightarrow> disjoint3 (?mod A p)"
    by simp
  from 0 1
  have "\<forall>A p. finite_profile A p \<longrightarrow> partition_of A (?mod A p)"
    by (simp add: partition_of_def)
  hence "\<forall>A p. finite_profile A p \<longrightarrow> partition_of A (?mod A p)"
    by simp
  thus ?thesis
    by blast
qed

(*************************************)
(*** Properties of the Drop Module ***)
(*************************************)

(* For any natural number and any linear order the affiliated drop module is strict defer monotone.
*)
lemma drop_module_defer_lift_invariant[simp]:
  assumes order: "linear_order r"
  shows "defer_lift_invariant (Drop_module n r)"
  by (simp add: order defer_lift_invariant_def)

(* For any natural number and any linear order the affiliated drop module is non electing. *)
lemma drop_module_non_electing[simp]:
  assumes order: "linear_order r"
  shows "non_electing (Drop_module n r)"
  by (simp add: non_electing_def order)

(* For any natural number n and any linear order, the affiliated drop module rejects n alternatives
   (if there are n alternatives).
*)
(* The induction proof is still missing. Following is the proofs n=2. *)
lemma drop_2_module_rejects_2[simp]:
  assumes order: "linear_order r"
  shows "rejects 2 (Drop_module 2 r)"
proof -
  have "reject (Drop_module 2 r) = defer (Pass_module 2 r)"
    by simp
    { thus ?thesis
        using pass_2_module_defers_2
      proof - (*generated proof*)
        obtain
          AA :: "('a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set" and
          rrs :: "('a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow>
                    nat \<Rightarrow> ('a \<times> 'a) set list" where
            "\<forall>x0 x1. (\<exists>v2 v3. (x1 \<le> card v2 \<and> finite_profile v2 v3) \<and> card (reject x0 v2 v3) \<noteq> x1)
                = ((x1 \<le> card (AA x0 x1) \<and> finite_profile (AA x0 x1) (rrs x0 x1))
                    \<and> card (reject x0 (AA x0 x1) (rrs x0 x1)) \<noteq> x1)"
          by moura
        hence "\<forall>n f. (\<not> rejects n f \<or> electoral_module f
                \<and> (\<forall>A rs. (\<not> n \<le> card A \<or> infinite A \<or> \<not> profile_on A rs)
                    \<or> card (reject f A rs) = n))
              \<and> (rejects n f \<or> \<not> electoral_module f
                \<or> (n \<le> card (AA f n) \<and> finite_profile (AA f n) (rrs f n))
                    \<and> card (reject f (AA f n) (rrs f n)) \<noteq> n)"
          using rejects_def
          by force
        hence f1: "\<forall>n f. (\<not> rejects n f \<or> electoral_module f
                    \<and> (\<forall>A rs. \<not> n \<le> card A \<or> infinite A \<or> \<not> profile_on A rs
                        \<or> card (reject f A rs) = n))
                    \<and> (rejects n f \<or> \<not> electoral_module f \<or> n \<le> card (AA f n) \<and> finite (AA f n)
                      \<and> profile_on (AA f n) (rrs f n) \<and> card (reject f (AA f n) (rrs f n)) \<noteq> n)"
          by presburger
        have "\<not> 2 \<le> card (AA (Drop_module 2 r) 2) \<or> infinite (AA (Drop_module 2 r) 2)
          \<or> \<not> profile_on (AA (Drop_module 2 r) 2) (rrs (Drop_module 2 r) 2)
          \<or> card (reject (Drop_module 2 r) (AA (Drop_module 2 r) 2) (rrs (Drop_module 2 r) 2)) = 2"
          by (metis (no_types) \<open>reject (Drop_module 2 r) = defer (Pass_module 2 r)\<close> defers_def
              order pass_2_module_defers_2)
        then show ?thesis
          using f1 drop_module_sound order
          by blast
      qed }
qed

end
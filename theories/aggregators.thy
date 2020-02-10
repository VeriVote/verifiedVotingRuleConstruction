theory aggregators
imports electoral_modules

begin

(******************************)
(*** Definition: Aggregator ***)
(******************************)

type_synonym 'a Aggregator = "'a set \<Rightarrow> 'a Result \<Rightarrow> 'a Result \<Rightarrow> 'a Result"

(* Aggregators get two partitions (results of electoral modules) as input and output another
   partition. They are used to aggregate results of parallel composed electoral modules.
*)
definition aggregator :: "'a Aggregator \<Rightarrow> bool" where
  "aggregator agg \<equiv> \<forall>A e1 e2 d1 d2 r1 r2.
      (partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
      partition_of A (agg A (e1, r1, d1) (e2, r2, d2))"

(****************************)
(*** Property Definitions ***)
(****************************)

(* A commutative aggregator has the same output, no matter which input partition is passed first. *)
definition commutative_agg :: "'a Aggregator \<Rightarrow> bool" where
  "commutative_agg agg \<equiv> aggregator agg \<and> (\<forall>A e1 e2 d1 d2 r1 r2.
      agg A (e1, r1, d1) (e2, r2, d2) = agg A (e2, r2, d2) (e1, r1, d1))"

(* A conservative aggregator choses the decision from one of the inputs for every alternative. *)
definition conservative :: "'a Aggregator \<Rightarrow> bool" where
  "conservative agg \<equiv> aggregator agg \<and> (\<forall>A e1 e2 d1 d2 r1 r2.
    ((partition_of A (e1, r1, d1) \<and> partition_of A (e2, r2, d2)) \<longrightarrow>
    elect_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
    reject_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2) \<and>
    defer_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2)))"

end

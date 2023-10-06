(*  File:       Aggregator.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Aggregator\<close>

theory Aggregator
  imports "Social_Choice_Types/Result"
begin

text \<open>
  An aggregator gets two partitions (results of electoral modules) as input and
  output another partition. They are used to aggregate results of parallel
  composed electoral modules.
  They are commutative, i.e., the order of the aggregated modules does not
  affect the resulting aggregation. Moreover, they are conservative in the
  sense that the resulting decisions are subsets of the two given partitions'
  decisions.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Aggregator = "'a set \<Rightarrow> 'a Result \<Rightarrow> 'a Result \<Rightarrow> 'a Result"

definition aggregator :: "'a Aggregator \<Rightarrow> bool" where
  "aggregator agg \<equiv>
    \<forall> A e1 e2 d1 d2 r1 r2.
      (well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
      well_formed A (agg A (e1, r1, d1) (e2, r2, d2))"

subsection \<open>Properties\<close>

definition agg_commutative :: "'a Aggregator \<Rightarrow> bool" where
  "agg_commutative agg \<equiv>
    aggregator agg \<and> (\<forall> A e1 e2 d1 d2 r1 r2.
      agg A (e1, r1, d1) (e2, r2, d2) = agg A (e2, r2, d2) (e1, r1, d1))"

definition agg_conservative :: "'a Aggregator \<Rightarrow> bool" where
  "agg_conservative agg \<equiv>
    aggregator agg \<and>
    (\<forall> A e1 e2 d1 d2 r1 r2.
      ((well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
        elect_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
        reject_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2) \<and>
        defer_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2)))"

end

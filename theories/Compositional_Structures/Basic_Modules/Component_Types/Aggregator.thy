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
    \<forall> A e e' d d' r r'.
      well_formed A (e, r, d) \<and> well_formed A (e', r', d') \<longrightarrow>
      well_formed A (agg A (e, r, d) (e', r', d'))"

subsection \<open>Properties\<close>

definition agg_commutative :: "'a Aggregator \<Rightarrow> bool" where
  "agg_commutative agg \<equiv>
    aggregator agg \<and> (\<forall> A e e' d d' r r'.
      agg A (e, r, d) (e', r', d') = agg A (e', r', d') (e, r, d))"

definition agg_conservative :: "'a Aggregator \<Rightarrow> bool" where
  "agg_conservative agg \<equiv>
    aggregator agg \<and>
    (\<forall> A e e' d d' r r'.
      well_formed A (e, r, d) \<and> well_formed A (e', r', d') \<longrightarrow>
        elect_r (agg A (e, r, d) (e', r', d')) \<subseteq> e \<union> e' \<and>
        reject_r (agg A (e, r, d) (e', r', d')) \<subseteq> r \<union> r' \<and>
        defer_r (agg A (e, r, d) (e', r', d')) \<subseteq> d \<union> d')"

end

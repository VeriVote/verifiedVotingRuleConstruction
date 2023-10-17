theory Social_Welfare_Result
  imports Result
begin

subsection \<open>Social Welfare Result\<close>

text \<open>
  A social welfare result contains three sets of relations:
  elected, rejected, and deferred
  A well-formed social welfare result consists only of linear 
  orders on the alternatives.
\<close>

fun well_formed_welfare :: "'a set \<Rightarrow> ('a Preference_Relation) Result \<Rightarrow> bool" where
  "well_formed_welfare A res = (disjoint3 res \<and> 
                                  set_equals_partition {r. linear_order_on A r} res)"

fun limit_set_welfare :: 
  "'a set \<Rightarrow> ('a Preference_Relation) set \<Rightarrow> ('a Preference_Relation) set" where 
  "limit_set_welfare A res = {limit A r | r. r \<in> res \<and> linear_order_on A (limit A r)}"
(* TODO first result assumption does not hold like that *)

end
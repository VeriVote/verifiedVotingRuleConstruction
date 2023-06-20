section \<open>Plurality Rule as Elimination Module\<close>

theory Plurality_Rule
  imports "Compositional_Structures/Basic_Modules/Plurality_Module"
          "Compositional_Structures/Elect_Composition"
          "Compositional_Structures/Revision_Composition"
begin

text \<open>
  This is a definition of the plurality voting rule as elimination module.
  An equivalence proof is given. We use this as an introductory task to refinement of 
  elimination modules. In particular, max eliminators. Here, the Max operator of the set of the 
  scores of all candidates is evaluated and is used as the threshold value. 
  In the refined elimination module we take steps to optimize this threshold value computation. 
  It must be shown that the optimized function refines the Max operator. 
\<close>

subsection \<open>Definition\<close>

fun plurality_rule :: "'a Electoral_Module" where
  "plurality_rule A p = elector plurality_mod A p"
                                        
lemma plureq: 
  assumes "A \<noteq> {}" and "finite A"
  shows "plurality_rule A p = plurality A p"
proof (standard)
  note maxge = score_bounded[where A= A and f = "(\<lambda> x. win_count p x)"]
  note maxex = max_score_in[where A= A and f = "(\<lambda> x. win_count p x)"]
  have "elect plurality A p = {a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a}" by simp
  from assms(2) maxge maxex have elecem: "elect plurality_rule A p = 
    {a \<in> A. win_count p a = Max {win_count p a | a. a\<in> A}}"
    by force
  from assms maxge maxex have "{a \<in> A. win_count p a = Max {win_count p a | a. a\<in> A}} = elect plurality A p "
    by (simp del: win_count.simps, metis (mono_tags, lifting)  order_antisym_conv)
  from elecem this show "elect plurality_rule A p = elect plurality A p"
    by fastforce
next
  show "snd (plurality_rule A p) = snd (plurality A p)"
  proof (standard)
    have recem: "reject plurality_rule A p = 
      {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a}"
      using max_score_in[where A= A and f = "(\<lambda> x. win_count p x)"] assms
            score_bounded[where A= A and f = "(\<lambda> x. win_count p x)"]
      by force
    from this recem show "reject plurality_rule A p = reject plurality A p" by simp
  next
   show "defer plurality_rule A p = defer plurality A p" by simp
  qed
qed
   
subsection \<open>Soundness\<close>

theorem plurality_rule_sound: "electoral_module plurality_rule"
  unfolding plurality_rule.simps
  using elector_sound plurmod_sound
  by blast


  

end

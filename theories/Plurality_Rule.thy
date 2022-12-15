section \<open>Plkurality Rule\<close>

theory Plurality_Rule
  imports "Compositional_Structures/Basic_Modules/Plurality_Module"
          "Compositional_Structures/Elect_Composition"
          "Compositional_Structures/Revision_Composition"
begin

text \<open>
  This is the Borda rule. On each ballot, each alternative is assigned a score
  that depends on how many alternatives are ranked below. The sum of all such
  scores for an alternative is hence called their Borda score. The alternative
  with the highest Borda score is elected.
\<close>

subsection \<open>Definition\<close>

fun plurality_rule :: "'a Electoral_Module" where
  "plurality_rule A p = elector plurality_mod A p"

lemma plureq: 
  assumes "A \<noteq> {}" and "finite A"
  shows "plurality_rule A p = plurality A p"
proof (standard)
  note maxge = nbmax[where A= A and p = p and f=win_count]
  note maxex = nbexmax[where A= A and p = p and f=win_count]
  have "elect plurality A p = {a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a}" by simp
  from assms(2) maxge maxex have elecem: "elect plurality_rule A p = 
    {a \<in> A. win_count p a = Max {win_count p a | a. a\<in> A}}"
    by force
  from assms maxge maxex have "{a \<in> A. win_count p a = Max {win_count p a | a. a\<in> A}} = elect plurality A p "
    apply (simp del: win_count.simps)
    by (metis (mono_tags, lifting)  order_antisym_conv order_le_neq_trans)
  from elecem this show "elect plurality_rule A p = elect plurality A p"
    by fastforce
next
  show "snd (plurality_rule A p) = snd (plurality A p)"
  proof standard
    note maxex = nbexmax[where A= A and p = p and f=win_count]
    from this assms(2) have recem: "reject plurality_rule A p = 
      {a \<in> A. win_count p a < (Max {win_count p alt | alt. alt \<in> A})}"
      by (simp, blast)
    note maxge = nbmax[where A= A and p = p and f=win_count]
    from assms maxex this have "{a \<in> A. win_count p a < (Max {win_count p alt | alt. alt \<in> A})}
    = reject plurality A p"
      by (simp, metis (no_types, lifting) leD order_le_imp_less_or_eq)
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

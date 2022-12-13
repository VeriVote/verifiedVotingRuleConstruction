section \<open>Plkurality Rule\<close>

theory Plurality_Rule
  imports "Compositional_Structures/Basic_Modules/Plurality_Module"
          "Compositional_Structures/Elect_Composition"
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

fun plurality_with_losers :: "'a Electoral_Module" where
  "plurality_with_losers A p = (let plur = plurality_mod A p in
      (defer_r plur, reject_r plur, elect_r plur))"

lemma nbmax:
  fixes f:: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat"
  fixes p:: "'a Profile"
  fixes A :: "'a set"
  fixes alt :: 'a
  assumes aA: "alt \<in> A" and fina: "finite A"
  shows "f p alt \<le> Max {f p x |x. x \<in> A}"
proof -
  from aA have "f p alt \<in> {f p x |x. x \<in> A}" by blast
  from fina this show ?thesis using Max_ge by auto
qed

lemma nbexmax:
  fixes f:: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat"
  fixes p:: "'a Profile"
  fixes A :: "'a set"
  fixes alt :: 'a
  assumes aA: "A \<noteq> {}" and fina: "finite A"
  shows "\<not> (\<forall> alt \<in> A. f p alt < Max {f p x |x. x \<in> A})"
proof -
  from aA have nemp: " {f p x |x. x \<in> A} \<noteq> {}" by simp
  from fina have "finite {f p x |x. x \<in> A}" by simp
  from nemp this Max_in show ?thesis
    using infinite_growing by auto
qed


lemma plureq: 
  assumes "A \<noteq> {}" and "finite A"
  shows "plurality_with_losers A p = plurality A p"
  apply (auto  simp del: win_count.simps)
  using assms(2) nbmax[where A= A and p = p and f=win_count]
  subgoal by fastforce
  using assms(2) nbmax[where A= A and p = p and f=win_count] order_neq_le_trans
  subgoal by fastforce
  using assms(2) nbmax[where A= A and p = p and f=win_count]
  subgoal by fastforce
  using assms nbexmax[where A= A and p = p and f=win_count]
   apply  blast+
  done
  

subsection \<open>Soundness\<close>

theorem plurality_rule_sound: "electoral_module plurality_rule"
  unfolding plurality_rule.simps
  using elector_sound plurmod_sound
  by blast
  

end

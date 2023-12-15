theory Quotient_Modules
  imports Election_Quotients 
          "../Electoral_Module"
begin

lemma invariance_is_congruence:
  fixes
    m :: "('a, 'v, 'r) Electoral_Module" and
    r :: "('a, 'v) Election rel"
  shows
    "(satisfies (fun\<^sub>\<E> m) (Invariance r)) = (fun\<^sub>\<E> m respects r)"
  unfolding satisfies.simps congruent_def
  by blast
  
theorem pass_to_election_quotient:
  fixes
    m :: "('a, 'v, 'r) Electoral_Module" and
    r :: "('a, 'v) Election rel" and
    X :: "('a, 'v) Election set"
  assumes
    "equiv X r" and
    "satisfies (fun\<^sub>\<E> m) (Invariance r)"
  shows
    "\<forall>A \<in> X // r. \<forall>E \<in> A. \<pi>\<^sub>\<Q> (fun\<^sub>\<E> m) A = fun\<^sub>\<E> m E"
  using invariance_is_congruence pass_to_quotient assms
  by blast




end
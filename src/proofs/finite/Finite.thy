theory Finite
  imports "HOL.Finite_Set" "HOL.Relation"
begin


section \<open>Simproc @{verbatim finite_Collect}\<close>
text \<open>
  The simproc @{verbatim finite_Collect} can be used to solve certain finiteness proof oblgations.
  TODO: What kind of proof obligations exactly?
  Below is an example from @{theory HOL.Relation}.
  TODO: Why is the simproc important here?
\<close>

lemma "finite (r\<inverse>) = finite r"
unfolding converse_def conversep_iff using [[simproc add: finite_Collect]]
  by (auto elim: finite_imageD simp: inj_on_def)

section \<open>Lemmas for Proving Finiteness of Sets\<close>
text \<open>
  For automated proofs, it can often help to just pass these with the @{verbatim intro} modifier to @{method auto} and friends.
  TODO: Why and in which cases?
  TODO: Add example.
\<close>
lemmas finite_helpers = finite_imageI finite_subset

section \<open>Tuning the Simplifier for Finiteness Proofs\<close>
subsection \<open>Rewriting to Images\<close>
text \<open>
  One useful technique is to rewrite set comprehensions to images of sets under functions as far as possible by passing @{thm setcompr_eq_image} to the simplifier.
  TODO: Add an example.
\<close>
end
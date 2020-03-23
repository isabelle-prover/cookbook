theory Finite
  imports Main
begin


section \<open>Simproc \<^verbatim>\<open>finite_Collect\<close>\<close>
text \<open>
  The simproc \<^verbatim>\<open>finite_Collect\<close> can be used to solve certain finiteness proof oblgations.
  Essentially, the simproc attempts to rewrite set comprehensions to terms that consist
  of applications @{term image}, @{term vimage}, @{term "(\<inter>)"},
  and @{term "(\<times>)"} as far as possible.
  Below is an example from @{theory HOL.Relation}.
\<close>
lemma "finite (r\<inverse>) = finite r"
  unfolding converse_def conversep_iff using [[simproc add: finite_Collect]]
  apply simp \<comment> \<open>The set was rewritten to an application of @{term image}.\<close>
  by (auto elim: finite_imageD simp: inj_on_def)

section \<open>Lemmas For Proving Finiteness of Sets\<close>
text \<open>
  For automated proofs, it can often help to just pass these with the \<^verbatim>\<open>intro\<close> modifier
  to @{method auto} and friends.
  The theorem @{thm finite_imageI} is set up as an default, but it can help to add \<^verbatim>\<open>intro!\<close>.
  Have a look at the example of the end of the file, to see both theorems in action.
\<close>
lemmas finite_helpers = finite_imageI finite_subset


section \<open>Tuning The Simplifier For Finiteness Proofs\<close>
subsection \<open>Rewriting to Images\<close>
text \<open>
  One useful technique is to rewrite set comprehensions to images of sets under functions as far as
  possible by passing @{thm setcompr_eq_image} or its \<open>n\<close>-ary generalizations to the simplifier.
\<close>

text \<open>Here is the \<open>2\<close>-ary generalization of @{thm setcompr_eq_image}.\<close>
lemma setcompr_eq_image2:
  "{f x y | x y. P x y} = (\<lambda>(x, y). f x y) ` {(x, y). P x y}"
  using setcompr_eq_image[where f = "(\<lambda>(x, y). f x y)" and P = "\<lambda>(x, y). P x y"] by simp

text \<open>In this example, \<^verbatim>\<open>finite_Collect\<close> still does the right thing:\<close>
lemma
  assumes "finite A"
  shows "finite {f x | x. x \<in> A \<and> P x}"
  using assms [[simproc add: finite_Collect]] by simp

text \<open>Here, however, it will produce quite a mess:\<close>
lemma
  assumes "finite (A \<times> B)"
  shows "finite {f x y | x y. x \<in> A \<and> y \<in> B \<and> R x y}"
  using assms [[simproc add: finite_Collect]]
  apply simp
  oops

text \<open>Instead, we use @{thm setcompr_eq_image2} to an image:\<close>
lemma
  assumes "finite (A \<times> B)"
  shows "finite {f x y | x y. x \<in> A \<and> y \<in> B \<and> R x y}"
  using assms
  apply (simp add: setcompr_eq_image2) \<comment> \<open>Looks much better.\<close>
  \<comment> \<open>\<^verbatim>\<open>auto\<close> will apply the following theorems to solve the goal:\<close>
  thm finite_imageI finite_subset[rotated]
  \<comment> \<open>We rotate @{thm finite_subset} to use it as an \<open>elim\<close>-rule\<close>
  apply (auto elim: finite_subset[rotated])
  done

section \<open>Further Pointers\<close>
text \<open>For more examples and an attempt at an proof method for finiteness proof obligations,
see \<^url>\<open>https://github.com/wimmers/isabelle-finite\<close>.\<close>

end
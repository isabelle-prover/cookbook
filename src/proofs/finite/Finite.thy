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


subsection \<open>Finiteness With Context\<close>
text \<open>The theorem @{thm finite_Collect_bounded_ex} (and its obvious \<open>n\<close>-ary generalizations)
can be highly useful for proving finiteness of sets where some of the finiteness theorems
one wants to apply rely on a precondition to hold. Consider the following example:\<close>
lemma
  "finite {s'. \<exists>s. Some s = x \<and> Some s' = g s}" \<comment> \<open>Clearly there is at most one such \<open>s'\<close>.\<close>
proof -
  \<comment> \<open>The statement follows quite immediately from this lemma.\<close>
  have Some_finite: "finite {x. Some x = y}" for y :: "'x option"
    using not_finite_existsD by fastforce
  show ?thesis
    \<comment> \<open>Something like this will not work, however:\<close>
    \<comment> \<open>apply (auto intro: Some_finite)\<close>
    \<comment> \<open>The reason is that we need \<^emph>\<open>context\<close>.
    The argument should go along the lines: there are only finitely such \<open>s\<close>,
    and for each \<open>s\<close> there are only finitely many such \<open>s'\<close>, thus the whole set is finite.\<close>
    apply (subst finite_Collect_bounded_ex) \<comment> \<open>this gives us what we want\<close>
    apply (intro allI impI Some_finite)+
    done
qed


subsection \<open>Advanced Examples Of Proving Finiteness With the Simplifier\<close>

text \<open>The simplifier can sometimes be surprisingly good at solving finiteness goals.
Here is an example:\<close>
lemma
  assumes "finite A" "finite (Collect P)"
  shows "finite {(a,b,c) | a b c. a \<in> A \<and> b < (n :: nat) \<and> P c}"
  using assms [[simproc add: finite_Collect]] by simp

text \<open>This shows what is going on here:\<close>
lemma
  assumes "finite A" "finite (Collect P)"
  shows "finite {(a,b,c) | a b c. a \<in> A \<and> b < (n :: nat) \<and> P c}"
  using [[simproc add: finite_Collect]] apply simp
  apply (intro finite_SigmaI finite_Collect_less_nat assms)
  done

text \<open>A slightly more complicated variant:\<close>
lemma
  assumes "finite A" "finite (Collect P)"
  shows "finite {(d, c, a, b) | a b c d. d < (n :: nat) \<and> P c \<and> (a, b) \<in> A}"
  using assms [[simproc add: finite_Collect]] by simp

text \<open>Here is a more involved example:\<close>
lemma
  fixes n :: nat
  assumes "finite A"
  shows "finite {t. \<exists> a c. a \<in> A \<and> c < n \<and> t = (a,c)}"
  using assms by simp

text \<open>Here is an explanation of what is going on:\<close>
lemma
  fixes n :: nat
  assumes "finite A"
  shows "finite {t. \<exists> a c. a \<in> A \<and> c < n \<and> t = (a,c)}"
  apply simp \<comment> \<open>First the simplifier applies some specific procedures for miniscoping\<close>
  apply (subst finite_Collect_bounded_ex) \<comment> \<open>Now, the context rule comes in\<close>
   apply (subst Collect_mem_eq, rule assms) \<comment> \<open>Solve first subgoal\<close>

  supply [simp del] = finite_Collect_bounded_ex
  apply(intro allI impI)
    \<comment> \<open>The simplifier walks down the propositional connectives using congruence rules\<close>
  apply (subst finite_Collect_bounded_ex) \<comment> \<open>Another application of the congruence rule\<close>
  apply (rule finite_Collect_less_nat) \<comment> \<open>Solve first subgoal\<close>
  apply (simp only: singleton_conv) \<comment> \<open>Rewrite to singleton set\<close>
  apply simp \<comment> \<open>The rest is trivial\<close>
  done


section \<open>Further Pointers\<close>
text \<open>For more examples and an attempt at an proof method for finiteness proof obligations,
see \<^url>\<open>https://github.com/wimmers/isabelle-finite\<close>.
It also contains the \<open>n\<close>-ary generalizations of @{thm setcompr_eq_image}
and @{thm finite_Collect_bounded_ex}.\<close>

end
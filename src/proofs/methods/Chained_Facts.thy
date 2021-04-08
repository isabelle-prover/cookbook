\<^marker>\<open>author Simon Wimmer\<close>
theory Chained_Facts
  imports Main
begin

text \<open>To better understand the way methods work in Isabelle,
it is important to understand the concept of \<open>chained facts\<close>.
This often causes confusion, particularly to the users of
the \<open>intro/elim\<close> and \<open>rule/erule\<close> methods.\<close>

section \<open>Basic Example and Explanation\<close>

text \<open>In the following examples, @{method rule} and @{method intro} behave the same way.\<close>

lemma
  "\<exists>x::nat. x > 0"
  apply (rule exI)
  apply (rule zero_less_one)
  done

lemma
  "\<exists>x::nat. x > 0"
  apply (intro exI)
  apply (rule zero_less_one)
  done

text \<open>We now \<^emph>\<open>chain\<close> in the fact @{thm zero_less_one} with \<open>using\<close>.\<close>
lemma
  "\<exists>x::nat. x > 0"
  using zero_less_one
  apply (rule exI)
  done

lemma
  "\<exists>x::nat. x > 0"
  using zero_less_one
  apply (intro exI)
  apply assumption
  done

text \<open>We note a slight difference. In the variant with intro, a trivial goal remains
that we need to solve by \<open>assumption\<close>.
The reason is that \<open>intro\<close> is a \<^emph>\<open>simple method\<close> in Isabelle jargon, while \<open>rule\<close> is \<^emph>\<open>proper\<close>.
Simple methods ignore chained facts and insert them into the goal state,
while proper methods will usually act on them in some way.

In the example, \<open>rule\<close> matches the chained fact @{thm zero_less_one} on the first premise
of @{thm exI}, and the conclusion of @{thm exI} on the goal.
As @{thm exI} only has one premise, no subgoals are left.
In contrast, \<open>intro\<close> simply ignores @{thm zero_less_one} and matches @{thm exI} only on
the conclusion. The fact is nevertheless inserted into the goal that arises, which
is why we can solve it by \<open>assumption\<close>.

Most older proof methods such as \<open>simp\<close>, \<open>auto\<close>, or \<open>blast\<close> are simple.
Two noteworthy proper methods are \<open>induction\<close> and \<open>cases\<close>.
\<close>


section \<open>Inserting Facts\<close>

text \<open>The behaviour of simple methods can be simulated by \<open>-\<close>, which will insert
any chained facts into the current goal state.\<close>
lemma
  "\<exists>x::nat. x > 0"
  using zero_less_one
  apply -
  apply (rule exI)
  apply assumption
  done

text \<open>Method insert will ignore any chained facts and insert its arguments in the goal state:\<close>
lemma
  "\<exists>x::nat. x > 0"
  using exI
  apply (insert zero_less_one)
  apply (rule exI)
  apply assumption
  done


section \<open>Chained Facts Are Chained\<close>

text \<open>Chained facts are chained through method combinators.\<close>
lemma \<comment> \<open>This works.\<close>
  "\<exists>x::nat. x > 0"
  apply (insert zero_less_one, rule exI)
  apply assumption
  done

lemma \<comment> \<open>This fails because \<open>0 \<noteq> 1\<close> does not match \<open>0 < 1\<close>.\<close>
  "\<exists>x::nat. x > 0"
  using zero_neq_one
  \<^cancel>\<open>apply (insert zero_less_one, rule exI)\<close>
  oops

lemma \<comment> \<open>This works again.\<close>
  "\<exists>x::nat. x > 0"
  using zero_neq_one
  apply (insert zero_less_one)
  apply (rule exI)
  apply assumption
  done

section \<open>More Examples\<close>

text \<open>The following examples outline some typical Isar proof patterns that come up when
chained facts are involved.\<close>

notepad
begin
  have fin_lt_5: "finite {x::nat. x < 5}"
    by auto
  moreover have subs: "{x::nat. x < 4} \<subseteq> {x::nat. x < 5}"
    by auto
  ultimately have "finite {x::nat. x < 4}" \<comment> \<open>Both previous facts are currently chained.\<close>
    \<^cancel>\<open>apply (rule finite_subset)\<close> \<comment> \<open>This fails. Both premises are given but in the wrong order.\<close>
    \<^cancel>\<open>apply (rule finite_subset[rotated])\<close> \<comment> \<open>Hence this works.\<close>
    \<^cancel>\<open>apply (erule finite_subset[rotated])\<close> \<comment> \<open>
      This fails because after matching the premises against the chained facts,
      there is no premise left for \<open>erule\<close> to match on.\<close>
    \<^cancel>\<open>apply (intro finite_subset)\<close> \<comment> \<open>This loops. Be careful! Better stop it quickly.\<close>
    apply (elim finite_subset) \<comment> \<open>
      This does not loop because \<open>elim\<close> matches any of the chained facts against the first premise.\<close>
    apply assumption
    \<^cancel>\<open>apply (elim finite_subset, assumption)\<close> \<comment> \<open>
      This does not work because \<open>assumption\<close> is not happy with chained facts.\<close>
    \<^cancel>\<open>apply (rule finite_subset[rotated])\<close> \<comment> \<open>Hence this works.\<close>
    done
end


lemma length_gt_0_E:
  assumes "length xs = n" "n > 0"
  obtains y ys where "xs = y # ys"
  using assms by (cases xs) auto

notepad
begin
  let ?xs = "[1::nat, 2, 3]"
  have three_gt_0: "(3 :: nat) > 0"
    by auto
  have len: "length ?xs = 3"
    by auto
  then obtain y ys where "?xs = y # ys"
    by (rule length_gt_0_E) simp
  from len obtain y ys where "?xs = y # ys"
    \<^cancel>\<open>apply (intro length_gt_0_E)\<close> \<comment> \<open>Loops. For this kind of \<open>elim\<close>-rules \<open>intro\<close> is useless.\<close>
    by (elim length_gt_0_E; simp)
  from len three_gt_0 obtain y ys where "?xs = y # ys"
    by (rule length_gt_0_E)
  \<comment> \<open>Facts in wrong order.\<close>
  from three_gt_0 len obtain y ys where "?xs = y # ys"
    \<^cancel>\<open>apply (rule length_gt_0_E)\<close> \<comment> \<open>Wrong fact order. Fails.\<close>
    by - (rule length_gt_0_E) \<comment> \<open>Insert facts first.\<close>
  from three_gt_0 len obtain y ys where "?xs = y # ys"
    by - (erule length_gt_0_E) \<comment> \<open>Matching the first fact explicitly.\<close>
  from three_gt_0 len obtain y ys where "?xs = y # ys"
    by (elim length_gt_0_E) \<comment> \<open>In this type of situation \<open>elim\<close> is cleaner.\<close>
  from three_gt_0 len obtain y ys where "?xs = y # ys"
    \<^cancel>\<open>apply (rule length_gt_0_E)\<close> \<comment> \<open>Wrong fact order. Fails.\<close>
    by (elim length_gt_0_E) \<comment> \<open>In this type of situation \<open>elim\<close> is cleaner.\<close>
  from len three_gt_0 obtain y ys where "?xs = y # ys"
    by (elim length_gt_0_E) \<comment> \<open>Because it works essentially uniformly w.r.t\ to fact order.\<close>
end


section \<open>Notes\<close>
text \<open>
\<^item> Eisbach methods are usually proper and can act on the chained facts in various ways.
You can find more information in the Eisbach user manual.
\<^item> In Isabelle/ML, the combinator @{ML SIMPLE_METHOD} is used to turn tactics into simple methods.
\<close>

end

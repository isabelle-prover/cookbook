theory Find
  imports Complex_Main
begin

section \<open>Find theorems with @{command find_theorems}\<close>
text \<open>
  Theorems can be searched by name where @{verbatim *} wildcards are allowed.
  One of the theorems found with the query below is @{thm gauss_sum_nat}.
\<close>
find_theorems name: "gau*"

text \<open>
  You can also search theorems by specifying an arbitrary number of patterns.
  Patterns are allowed to contain wildcards (@{verbatim _}) constants, schematic variables, and types.
  It is also possible to negate a pattern by prefixing it with a @{verbatim -}.
  If a negated pattern occurs in a theorem, it will not be considered by the search.
\<close>
find_theorems "finite (?A::'a rel)"
find_theorems "finite _ \<Longrightarrow> _" "insert _ _" -"card _"
find_theorems "finite ?A \<Longrightarrow> finite ?B \<Longrightarrow> _ (?A \<union> ?B)"

text \<open>
  In addition to patterns, we can take the goal state into account to search for theorems.
  The example below uses intro to search for introduction rules that solve the current goal.
  For the given goal, @{command find_theorems} finds the lemma @{thm bij_betw_byWitness} which we instantiate accordingly.
  Then, we solve the the first two subgoals with @{method simp_all}.
  This leaves us with two subgoals: @{prop \<open>(\<lambda>x. x + 1) ` \<int> \<subseteq> \<int>\<close>} and @{prop \<open>(\<lambda>x. x + 1) ` \<int> \<subseteq> \<int>\<close>}.
  Searching with intro returns a lot of theorems since @{verbatim \<open>\<subseteq>\<close>} often occurs in the conclusion of theorems.
  To filter out irrelevant theorems, we pass the goal as a pattern with the appropriate wildcards.
  Then, @{command find_theorems} gives us the lemma @{thm image_subsetI} with which we can solve the remaining goals.
  Apart from intro, there is also elim, dest, and solves which work analogously.
\<close>
lemma "bij_betw (\<lambda>x. x + 1) \<int> \<int>"
  find_theorems intro
  apply(intro bij_betw_byWitness[where ?f'="\<lambda>x. x - 1"])
     apply(simp_all)
  find_theorems intro
  find_theorems intro "_ ` _ \<subseteq> _"
   apply(simp_all add: image_subsetI)
  done

text \<open>
  To search for theorems that simplify a given term, one can pass simp and a term to @{command find_theorems}.
  In the example below, @{command find_theorems} returns the lemma @{thm rev_rev_ident} with which we can rewrite @{term \<open>rev (rev xs)\<close>} to @{term \<open>xs\<close>}.
\<close>

find_theorems simp: "rev (rev _)"


section \<open>Find constants with @{command find_consts}\<close>

find_consts name: metric

find_consts "'a \<Rightarrow> 'a list"
find_consts strict: "'a \<Rightarrow> 'a list"

find_consts strict: "_ \<Rightarrow> 'a list \<Rightarrow> _ list"
find_consts strict: "_ \<Rightarrow> 'a list \<Rightarrow> _ list" -"('a \<times> 'b) list"

find_consts "('a::ord) list \<Rightarrow> ('a::ord) list"
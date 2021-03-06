All methods act on the first subgoal only unless otherwise stated and fail if they cannot solve the goal, unless stated otherwise.

## General-purpose automation

### Simplifier

- `simp` rewrites the goal using the simplifier (for more information, refer to the cookbook section on the simplifier). This method never fails except when it cannot perform any simplification at all.
- `simp_all` is like `simp`, but acts on *all* goals


### Classical automation

- `blast` is a Tableaux prover that is good at predicate logic and set theory. It can take claset modifiers like `intro`, `dest`, `elim`. It can occasionally solve goals involving equality, but generally handles equality rather poorly compared to methods that use the simplifier. However, for purely ‘logical’ goals that do not require rewriting, it can often be superior.
- `fastforce` and `force` perform both classical proof search using the claset and rewriting using the simplifier. They differ in which heuristic the classical search uses.
- `auto` is similar to `fastforce`/`force`, but does not try quite as hard. It also acts on *all* goals and does never fails (unless it cannot do *anything*).
- `auto2` TODO

The following methods are a bit more specialised, but still useful in some cases:

- `metis` and `meson` are automated theorem provers for first-order logic. They are sometimes suggested by `sledgehammer` or `try0`. Unlike most other Isabelle automation, they do not use any fact database (like the claset), so they will usually require the user to pass many low-level facts explicitly to them, which makes them impractical to use manually (as opposed to generated by `sledgehammer`). However, there are occasional cases where fairly big (but logically simple) goals can easily be solved by `metis` and `meson` but not by any of Isabelle's other methods.
- `smt` (an Isabelle wrapper around the Z3 SMT solver) also needs to be given relevant facts manually and is sometimes suggested by sledgehammer. Unlike the previous two, however, it also knows some things about linear arithmetic and a few other things.
- `satx` uses an external proof-producing SAT solver, replaying its proof in Isabelle
- `argo` is a prover for propositional logic with equality and linear arithmetic


### Less relevant methods

The following methods are not used much these days and you can probably safely ignore them:

- `fast`, `slow`, and `best` are classical provers with different heuristics and roughly the same field of applications as `blast`.
- `slowsimp` and `bestsimp` are variants of `fastforce` with different heuristics.

### Summary

The most widely used and useful methods are `simp`/`simp_all` and `auto`. Since they never fail, they are also very useful for exploration: a usual pattern in writing Isabelle proofs is to do `apply auto` and inspect the proof state to see which goals are ‘left over’. One can then give additional facts to the methods or prove remaining goals separately until nothing remains.

If there is a goal that `auto` should be able to solve but somehow cannot, `force` often works because it tries a bit harder. Despite its name, `fastforce` is usually not really faster than `force`. Which of them is better in any given case seems to be quite random, and it usually does not matter.



## One-step methods

- `assumption` solves the goal with one of the premises
- `subst` performs single-step rewriting of the goal with a given equation. Optional arguments can be used to rewrite the premises instead, or to specify the position to rewrite.
- `rewrite` is essentially a more powerful version of `subst`.
- `rule` performs a single resolution step (it ‘applies’ a rule to the current goal, backward reasoning)
- `drule` and `frule` peform a single step of foward reasoning (they ‘apply’ a rule to one of the premises, yielding a new premise). The difference is that `drule` deletes the premise that is being transformed, whereas `frule` does not.
- `erule` applies resolution of a rule with the goal and with one of the premises being consumed by the first assumption of the rule. An optional numeric argument can be used to consume more than one premise. It is more or less equivalent to `rule, assumption`. This is often useful for elimination rules (e.g. case distinctions).
- `intro` applies resolution with the given rules repeatedly.
- `elim` applies elimination with the given rules repeatedly.
- `safe` applies safe rules from the claset only. This is typically used to split conjunctions in goals with several subgoals, or to split conjunctions in the assumptions by several assumptions, or to prove set equivalence by proving membership in both directions. However, sometimes it can do a bit too much (e.g. `x ∈ {a}` becomes `x ∉ {} ⟹ x = a`). In those cases, using the `intro`/`elim` methods by hand is preferable.
- `clarify` TODO: What does clarify do precisely

All of these except `drule`, `frule`, `erule` are often useful even in high-level proofs, especially when used as the first step of a proof. They are often used as the initial proof method, and the goals they produce are then ‘finished off’ using e.g. `auto`.



## Transfer

TODO


## Special-purpose automation

### Termination

- `relation` can be used in manual termination proofs by giving a suitable well-founded relation by hand (often used in combination with `measure` or `<*lex*>`/`<*mlex*>`).
- `lexicographic_order` attempts to prove termination of a multivariate function automatically by finding a lexicographic combination of termination measures.
- `size_change` is a more sophisticated termination method TODO what does it do

### Arithmetic

- `linarith` solves linear arithmetic goals on natural numbers, integers, and reals. It deals with disjunctions by performing a case distinction, so if the goal contains many disjunctions, this becomes prohibitively slow.
- `smt` also supports linear arithmetic and often deals with disjunctions much better than `linarith`.
- `presburger` solves Presburger arithmetic goals. It can be very useful to prove goals involving divisibility and `mod` on naturals and integers, but in practice it is often prohibitively slow on all but very small goals. TODO link
- `arith` was created to become a wrapper tactic for all kinds of arithmetic decision procedures, but in practice, it only calls `linarith` and `presburger` at the moment.


### Polynomials

- `sos` can prove polynomial inequalities using sum-of-squares witnesses. It is complete for univariate polynomials, but the witness search can often take quite long for larger ones.
- `sturm` can prove various things about univariate real polynomials, such as non-negativity, number of roots, etc.


### Other

- `measurable` proves measurability of functions and sets
- `pratt` can prove that a number is prime using prime certificates. This works even for fairly large primes. TODO link AFP
- `master_theorem` can prove asymptotic relations for divide-and-conquer recurrences corresponding to a generalised version of the Master Theorem. TODO link AFP
- `approximation` proves inequalities on various real-valued functions using interval arithmetic. TODO link
- `real_asymp` proves various asymptotic properties of concrete real-valued functions, such limits, ‘Big-O’, and asymptotic equivalence
- `eval_winding` provides support for evaluating winding numbers of paths in the complex plane in many practically relevant cases TODO link AFP










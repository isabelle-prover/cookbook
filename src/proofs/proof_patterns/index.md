# Proof Patterns

Chapter 1 of the [Isabelle/Isar Reference Manual](https://isabelle.in.tum.de/doc/isar-ref.pdf#chapter.1)
and
Chapter 4 of the official [Programming and Proving in Isabelle/HOL](https://isabelle.in.tum.de/dist/Isabelle2021-1/doc/prog-prove.pdf#chapter.4)
tutorial provide a comprehensive guide for common proof patterns.
Here we list some additional patterns.
Throughout this page, placeholders are put between angle braces `<...>`.

## Definitions in Lemmas

When stating a lemma,
you can use the following syntax to introduce a local definition:

```
defines "<symbol> ≡ <expression>"
```

The fact of such a definition then becomes accessible by `<symbol>_def`.

**Example:** `defines "m ≡ n mod k"`; accessible through `m_def`

## Definitions in Proofs

Inside a proof,
you can use the following syntax to introduce a local definition:

```
define <symbol> where "<symbol> ≡ <expression>"
```

The fact of such a definition then becomes accessible by `<symbol>_def`.

Note that local definitions are different from term abbreviations 
introduced by `let` (cf [Isabelle/Isar Reference Manual](https://isabelle.in.tum.de/doc/isar-ref.pdf#command.let)):
the former are visible within the logic as actual equations
while the latter disappear when Isabelle processes the input.

**Example:** `define m where "m ≡ n mod k"`; accessible through `m_def`


# Lemmas for Proving Finiteness of Sets
For automated proofs, it can often help to just pass these
with the `intro` modifier to `auto` and friends.
```
lemmas finite =
  finite_imageI
  finite_subset
```
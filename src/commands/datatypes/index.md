# Datatypes

## Selectors

In the definition of a datatype,
you can specify selectors that extract a specific position.

**Example:**
```
datatype foo = Foo (foo_l : int) (foo_r : int)
```

You can then access the first element of a foo value `x`
by `foo_l x` and the second one by `foo_r x`.


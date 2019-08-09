# Simplifier for Finiteness
A number of methods on using the simplifier to deal with finiteness proof obligations.

## Rewriting to Images
One useful technique is to rewrite set comprehensions to images of sets under functions
as far as possbile. Try this:
```
apply (simp add: setcompr_eq_image)
```
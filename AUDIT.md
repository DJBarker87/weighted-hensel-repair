# Mathematical audit

## C-001: specialization separability in Proposition 7.10

**Classification:** C — the paper omits an operative hypothesis, but the result is
repairable.

Proposition 7.10 assumes that each global factor
`Rᵢ(X,Y,Z)` is irreducible and separable in `Y`, then says to choose `x₀`
“as in the refinement.”  Its proof later uses the stronger assertion that
`Rᵢ(x₀,Y,Z)` is separable in `Y`.  Generic separability does not imply this
after an arbitrary specialization: over a field of characteristic different
from two, `R(X,Y,Z) = X + Y²` is irreducible and separable in `Y`, while its
specialization at `x₀ = 0` is `Y²` and its derivative vanishes on the branch
`Y`.

The formal statement `full_factor_degree_transfer` therefore states the exact
condition used by the proof for every retained branch:

```lean
regularDerivativeElement (parent index) (branch index branchIndex) x₀
  (parent index).natDegree ≠ 0
```

This condition follows from square-freeness/separability of the specialized
polynomial and is the intrinsic regular-quotient formulation of a simple
branch.  Under it, `card_content_root_specializations_lt_pole_budget` proves
the content-root removal bound through the actual leading coefficient and
weighted resultant; no numerical removal bound is assumed by the
paper-facing theorem.

**Status:** repaired and proved.  The paper should either require
`Rᵢ(x₀,Y,Z)` to be separable in `Y`, require the displayed regular derivative
to be nonzero on each considered branch, or spell out the property of the
refinement's choice of `x₀` that guarantees this.

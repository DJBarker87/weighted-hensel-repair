# Mathematical audit

## Closed C-001: specialization separability in Proposition 7.10

**Original classification:** C — the standalone wording of Revision 14 was
under-hypothesized, but the 2026 source explicitly supplies the needed
condition.

Generic separability of `Rᵢ(X,Y,Z)` in `Y` does not imply separability after
an arbitrary specialization of `X`: over a field of characteristic different
from two, `R(X,Y,Z) = X + Y²` is irreducible and separable in `Y`, while its
specialization at `x₀ = 0` is `Y²`. Thus Proposition 7.10 is not licensed by
generic separability alone.

However, Step 2 of BCHKS26 explicitly chooses `x₀` so that every
`Rᵢ(x₀,Y,Z)` remains separable in `Y` over `K(Z)`, before decomposing the
specializations into irreducible factors `Hᵢⱼ`. The formal proposition now
states that source hypothesis directly:

```lean
(branchPolynomial (specializeX x₀ (parent index))).Separable
```

Equivalently, this is the coprimality condition
`gcd(Rᵢ(x₀,Y,Z), ∂_Y Rᵢ(x₀,Y,Z)) = 1` in `K(Z)[Y]`. The theorem
`regularDerivativeElement_ne_zero_of_specialized_separable` proves that this
condition and `Hᵢⱼ ∣ Rᵢ(x₀,Y,Z)` imply the branchwise intrinsic regular
derivative is nonzero. Consequently `full_factor_degree_transfer` no longer
takes branchwise derivative nonvanishing as a separate hypothesis; it derives
it before constructing the pole/resultant exceptional sets.

**Status:** closed and proved. The standalone proposition should make the
Step 2 choice explicit, but there is no gap in the BCHKS26 argument and no
remaining C–E obligation in this development.

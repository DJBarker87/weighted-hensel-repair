# Correcting the Weighted Hensel Estimate

[![Formal verification](https://github.com/DJBarker87/weighted-hensel-repair/actions/workflows/formal_verification.yml/badge.svg)](https://github.com/DJBarker87/weighted-hensel-repair/actions/workflows/formal_verification.yml)

Standalone Lean 4 verification artifact accompanying
*Correcting the Weighted Hensel Estimate for Reed–Solomon Curve Decodability.*

The `.lean` sources are authoritative. The paper is mathematically
self-contained; this repository supplies an independent machine-checked
verification of its named results.

## Canonical paper artifact

The release identifier `paper-v1.0` is reserved for the verification artifact
corresponding to ePrint Version 1 of the paper. The release records the exact
Git commit and can be replayed with:

```sh
./scripts/verify.sh
```

## One-command verification

```sh
git clone https://github.com/DJBarker87/weighted-hensel-repair.git
cd weighted-hensel-repair
./scripts/verify.sh
```

The script is a transparent wrapper around Mathlib's standard pinned-cache
fetch, `lake build WeightedHensel.Terminal`, `lake env lean Main.lean`, and
source-hygiene scans. The `.lean` sources are the authoritative artifact; the
downloaded `.olean` files are only a Mathlib build cache.

| Replay datum | Expected value |
| --- | ---: |
| First replay after clone | about 2 minutes |
| Clean project build after cache setup | about 1 minute |
| Peak RSS | about 6.5 GiB |
| Swap | none required |
| Toolchain | Lean `v4.32.0`, pinned Mathlib `v4.32.0` |

The script prints the exact checked-out commit. An ePrint identifier or archive
DOI will be added only after it is actually issued.

## Headline results

| Result | Lean theorem |
| --- | --- |
| Direct correction of source recurrence | `corrected_source_hensel_estimate` |
| Division-free recurrence | `division_free_hensel_estimate` |
| Weighted resultant zero count | `weighted_resultant_zero_count` |
| Fixed-branch curve conclusion | `fixed_branch_curve_decodability` |
| Full-factor transfer with BCHKS26 Step 2 separability | `full_factor_degree_transfer` |
| Separable global-to-curve composition | `separable_full_factor_curve_decodability` |
| Inseparable Frobenius extension, Corollary 7.11 | `inseparable_frobenius_curve_decodability` |
| Degree-28 instance | `concrete_degree28_curve_decodable` |
| Degree-3 instance | `concrete_degree3_curve_decodable` |

`Main.lean` is the human-readable front door: it `#check`s these nine
declarations and prints each axiom report.

## Trust boundary

The generic results take polynomial factorizations, branch data, roots,
degree bounds, separability/nonvanishing conditions, agreement data, and
cardinality inequalities as explicit theorem inputs. The concrete modules
discharge the stated numerical parameter calculations and list-size bounds;
they do not claim an executable decoder or an algorithm for discovering
factorizations.

## Scope

This is a standalone Lean 4 verification artifact for *Correcting the
Weighted Hensel Estimate for Reed–Solomon Curve Decodability*. It formalizes
the polynomial weight, monicization, regular quotient, both repaired Hensel
recurrences, both resultant arguments, specialization, truncation,
interpolation, fixed-branch completion, the 2026 full-factor transfer, the
paper's counterexamples, and both numerical Reed–Solomon instances.

It also formalizes the complete inseparable Frobenius extension: factorization
through `Y^(p^f)`, both global degree ledgers, sparse exact truncation,
compatible Frobenius roots, inverse-Frobenius recovery, the rooted second
resultant, source reindexing, and final line interpolation.

The development depends only on Lean and Mathlib. It does not formalize any
protocol, compiler, cryptographic primitive, or deployment machinery.

## Verification status

All Lean sources build without `sorry`, `admit`, project axioms,
`native_decide`, or oracle propositions. The union of the logical axioms
reported by the paper-level declarations is:

```text
propext
Classical.choice
Quot.sound
```

The release surface is aligned with Paper Version 1. Every substantive
mathematical theorem in that version has an identified Lean counterpart,
including the complete inseparable Frobenius extension of Corollary 7.11. The
theorem and section correspondence is recorded in
[PAPER_ALIGNMENT.md](PAPER_ALIGNMENT.md).

Proposition 7.10 uses separability after specializing `X = x₀`. Generic
separability alone would not imply this, but BCHKS26 Step 2 explicitly chooses
`x₀` so that every `Rᵢ(x₀,Y,Z)` remains separable over `K(Z)`. The formal
theorem states that source hypothesis and proves that it implies nonvanishing
of the intrinsic regular derivative on every irreducible branch. The
standalone wording issue in the paper is recorded as closed **C-001** in
[AUDIT.md](AUDIT.md); it is not a gap in the 2026 argument.

## Toolchain and replay

The repository pins:

- Lean `v4.32.0` in `lean-toolchain`;
- Mathlib `v4.32.0` in `lakefile.toml`;
- the exact Mathlib commit and transitive dependencies in
  `lake-manifest.json`.

The canonical clean-checkout replay is:

```sh
./scripts/verify.sh
```

Reviewers who prefer the underlying commands can run:

```sh
lake build WeightedHensel.Terminal
lake env lean Main.lean
```

An optional `lake build` checks the full library target as well.

## Mathematical representation

For a field `K`, the repository uses:

- `Polynomial K` for `K[Z]`;
- `BivariatePolynomial K = Polynomial (Polynomial K)` for `K[Z,T]` or
  `K[Z,Y]`, with the outer variable named by context;
- `TrivariatePolynomial K = Polynomial (BivariatePolynomial K)` for
  `K[X,Z,Y]`, again with the outer variable named by context;
- `RegularQuotient factor` for `K[Z,T]/(Ĥ)`;
- `BranchFunctionField factor` for the corresponding quotient over `K(Z)`.

The weight of zero is represented by `WithBot Nat`. No weight is defined on
arbitrary elements of `BranchFunctionField factor`.

## Paper-to-Lean map

The table names the principal declaration for each result. Several rows also
list supporting declarations where the paper combines more than one
mathematical fact in a single statement.

| Paper result | Lean declaration | Status |
| --- | --- | --- |
| Saturation/base-case example | `saturation_tau_strictly_exceeds_printed_base`, `saturationParent_coefficient_bound` | proved |
| Proposition 3.1: sharp positive-order counterexample | `positive_order_beta_one`, `positive_order_beta_one_regular_weight`, `positiveOrderParent_irreducible`, `positiveOrderParent_separableInResponse` | proved |
| Remark 3.2: derivative-numerator counterexample | `derivative_counterexample_xi_regular_weight`, `derivative_printed_ceiling_fails`, `derivativeCounterexampleParent_irreducible`, `derivativeCounterexampleParent_separableInResponse`, `derivativeSpecializedParent_squarefree` | proved |
| Lemma 4.1: translation preserves the parent bound | `shiftedParentCoefficient_bound` | proved |
| Corrected auxiliary numerator bound, Lemma 4.2 | `exists_sourceAuxiliaryNumerator` | proved |
| Polynomial `W`-divisibility at shifted order zero | `leadingCoeff_dvd_sourceClearedRepresentative_zero` | proved |
| Corrected derivative numerator, Corollary 4.3 | `exists_sourceDerivativeNumerator` | proved |
| Source partition and excluded singleton bookkeeping | `SourceTermIndex.singleton_excluded_of_s_eq_zero`, `SourceTermIndex.recursive_index_lt`, `SourceTermIndex.partition_eq_zero_of_s_eq_t` | proved |
| Source `W`, derivative, and structural ledgers | `SourceTermIndex.w_ledger`, `SourceTermIndex.derivative_ledger`, `source_structural_ledger`, `source_parameter_ledger` | proved |
| Direct `βₜ` induction, Theorem 4.4 | `corrected_source_hensel_estimate` | proved |
| Direct-repair pole, coefficient-resultant, and common-numerator budgets | `sourcePoleBudget_lt_coarse`, `sourceCoefficientResultantBudget_lt_coarse`, `sourceSecondResultantBudget_lt_coarse` | proved |
| Lemma 6.1: regular quotient embedding and domain | `regularToFunctionField_injective`, `regularQuotient_isDomain`, `branchPolynomial_irreducible` | proved |
| Lemma 6.2: monic reduction does not raise weight | `iteratedBivariateWeight_modByMonic_le`, `regularWeightNat_mk_le` | proved |
| Corollary 6.3: quotient weight laws | `regularWeight_add_le`, `regularWeight_mul_le`, `regularWeightNat_pow_le` | proved |
| Lemma 6.4: cleared derivative and coefficient bounds | `regularDerivativeElement_weight_le`, `regularClearedCoefficient_weight_add_le` | proved |
| Denominator-free recurrence, Theorem 6.5 | `divisionFreeCoefficients`, `division_free_defined_estimate`, `divisionFreeCoefficients_image` | proved |
| Relation between the two repairs, Proposition 6.6 | `divisionFree_eq_sourceNumerator`, `divisionFree_sourceNumerator_weight_eq`, `direct_and_divisionFree_ceilings_equivalent` | proved |
| Weighted Sylvester bound, Lemma 7.1 | `weighted_resultant_degree_bound` | proved |
| Nonzero resultant and branch zero count, Corollary 7.2 | `canonicalRepresentative_resultant_ne_zero`, `weighted_resultant_zero_count` | proved |
| Regular specialization and cleared coefficient identity, Lemma 7.3 | `branchSpecialization_parentDivisionFreeCoefficients` | proved |
| High-coefficient zero count and cancellation | `parentDivisionFreeCoefficients_eq_zero_of_many_branches`, `henselCoefficient_eq_zero_of_cleared_eq_zero` | proved |
| Exact finite truncation | `exists_exact_henselTruncation_of_many_branches` | proved |
| Common numerator, Lemma 7.4 | `commonNumerator_image`, `commonNumerator_eval_weightNat_le` | proved |
| Second discrepancy/resultant, Lemma 7.5 | `commonDiscrepancy_eq_zero_of_many_branches`, `secondResultant_identifies_henselTruncation` | proved |
| Heavy-coordinate count, Lemma 7.6 | `maximumDegree_lt_card_heavyCoordinates` | proved |
| Coefficientwise interpolation | `lagrangeCoefficientCurve_eval_at_node`, `candidate_eq_candidateCurve` | proved |
| Fixed-branch completion, Theorem 7.7 / Corollary 7.8 | `fixed_branch_curve_decodability` | proved |
| Published coarse comparison, Corollary 7.9 | `weightedDivisionFreeBudget_lt_coarse`, `sourceSecondResultantBudget_lt_coarse` | proved |
| Full-degree shifted-coefficient counterexample | `fullDegreeCounterexample_specialized_zDegree`, `fullDegreeCounterexample_shifted_zDegree` | proved |
| Shifted-coefficient full-degree lemma | `shiftedCoefficient_fullDegree_le` | proved |
| Specialization content and branch degree sums | `specialization_content_branch_weight_summation`, `specialization_branch_yDegree_summation` | proved |
| Pairwise factor-degree summation | `factor_square_weight_sum_le_global`, `factor_branch_pair_weight_sum_le` | proved |
| Content roots charged to the derivative resultant | `specialization_content_dvd_clearedDerivativeRepresentative`, `card_content_root_specializations_lt_pole_budget` | proved |
| Specialized-parent separability implies branch derivative nonvanishing | `regularDerivativeElement_ne_zero_of_specialized_separable` | proved |
| 2026 full-factor summation, Proposition 7.10 | `full_factor_degree_transfer` | proved from the explicit BCHKS26 Step 2 hypothesis |
| Proposition 7.10 composed with the separable line theorem | `separable_full_factor_curve_decodability` | proved |
| Frobenius factor weighted-degree ledgers, equations (127)–(129) | `fullFactor_frobenius_weight_summation`, `fullFactor_frobenius_yDegree_summation` | proved |
| Inseparable pairwise summation, equations (135)–(136) | `fullFactor_parent_yDegree_summation_le`, `frobenius_factor_square_weight_sum_le` | proved |
| Powered-parent cutoff, equation (137) | `frobenius_parent_order_lt_global_XY_degree`, `frobenius_substitutionDegreeBound` | proved |
| Sparse Taylor coefficients and exact `q`-power truncation | `coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_not_dvd`, `exists_exact_sparse_henselTruncation_of_many_frobenius_branches` | proved |
| Compatible function-field Frobenius roots | `perfectPolynomialFrobeniusRoot_pow`, `bivariateFrobeniusRoot_localRoot`, `regularFrobeniusRootEquiv` | proved |
| Rooted common numerator and second resultant, equation (139) | `frobeniusRootedCommonNumerator_eval_weightNat_le`, `frobeniusRootedDiscrepancy_eq_zero_of_many_branches` | proved |
| Inverse-Frobenius source reindexing | `fixed_branch_frobenius_line_decodability_source_indexed` | proved |
| Inseparable factors, Corollary 7.11 | `inseparable_frobenius_curve_decodability` | proved end to end from the stated global and incidence hypotheses |
| Exact degree-28 Guruswami–Sudan cap | `degree28_guruswamiSudan_list_card_le_100` | proved |
| Exact degree-3 Guruswami–Sudan cap | `degree3_guruswamiSudan_list_card_le_99` | proved |
| Separate analytic list parameters 112 and 113 | `degree28_rateOnlyListExpression_eq_112`, `degree3_rateOnlyListExpression_lt_113` | proved |
| Exact outer and curve-decodability allowances | `exact_degree28_outerExceptionalAllowance`, `exact_degree3_outerExceptionalAllowance`, `exact_degree28_curveDecodabilityAllowance`, `exact_degree3_curveDecodabilityAllowance` | proved |
| Degree-28 released-subcode dimension distinction | `degree28_released_subcode_dimension_strict` | proved |
| Degree-28 fixed-branch concrete specialization | `concrete_degree28_curve_decodable` | proved |
| Degree-3 fixed-branch concrete specialization | `concrete_degree3_curve_decodable` | proved |

The two concrete terminal theorems instantiate the fixed-branch completion
with the exact numerical allowances and GRS normalization. The independent
global factor-selection bookkeeping is `full_factor_degree_transfer`, and
`separable_full_factor_curve_decodability` composes it with the local curve
theorem. The repository does not disguise these results as an executable
decoder.

## Module guide

| Module | Contents |
| --- | --- |
| `Basic` | Ring aliases, Hensel exponent, elementary arithmetic |
| `WeightedDegree` | `WithBot` polynomial weight and exact/subadditive laws |
| `Monicization` | Division-free monicization and coefficient bounds |
| `RegularQuotient` | Canonical representatives, quotient weights, field embedding |
| `SourceRecurrence` | Partitions, exclusion rule, nonnegative exponents, ledgers |
| `DirectRepair` | Shifted coefficients, auxiliary numerators, direct `βₜ` repair |
| `Counterexamples` | Three explicit counterexamples and admissibility checks |
| `DivisionFreeRecurrence` | Intrinsic `δₜ` recurrence and equivalence to `βₜ` |
| `ResultantBound` | Weighted Sylvester determinant and root-pair zero count |
| `Specialization` | Evaluation on the regular quotient and specialized recurrence |
| `PowerSeriesLift` | Simple-root lift and image identities |
| `Truncation` | Vanishing high coefficients and exact finite root |
| `CommonNumerator` | `Δₘ`, discrepancy, and second resultant |
| `Incidence` | Heavy-coordinate double count |
| `Interpolation` | Coefficientwise Lagrange interpolation and candidate recovery |
| `FixedBranch` | Fixed-branch curve completion theorem |
| `CoarseBounds` | Repaired bounds versus the published coarse allowances |
| `FactorDegreeTransfer` | Full weighted-degree preservation and 2026 factor summation |
| `SeparableCorollary` | Proposition 7.10 composed with separable line completion |
| `Frobenius` | Finite-field inverse Frobenius and sparse Taylor identities |
| `FrobeniusBranch` | Compatible quotient/function-field Frobenius roots |
| `FrobeniusTruncation` | Sparse first-resultant coefficient vanishing |
| `FrobeniusExactTruncation` | Exact sparse lift, contraction, and literal `q`-th root |
| `FrobeniusCommonNumerator` | Rooted numerator and second resultant |
| `FrobeniusFactorTransfer` | Inseparable full-factor degree and content bookkeeping |
| `FrobeniusSubstitutionDegree` | Global `(1,k,0)` substitution-degree bound |
| `FrobeniusReindex` | Source-indexed inverse-Frobenius transport |
| `FrobeniusCorollary` | Complete Corollary 7.11 composition |
| `JohnsonBound` | Exact finite incidence/list-cardinality inequality |
| `CurveDecodability` | GRS normalization and multiplier restoration |
| `ConcreteParameters` | Both exact numerical parameter columns |
| `Terminal` | Nine paper-level terminal declarations and axiom reports |

## Terminal declarations

`WeightedHensel/Terminal.lean` reports axioms for:

```text
corrected_source_hensel_estimate
division_free_hensel_estimate
weighted_resultant_zero_count
fixed_branch_curve_decodability
full_factor_degree_transfer
separable_full_factor_curve_decodability
inseparable_frobenius_curve_decodability
concrete_degree28_curve_decodable
concrete_degree3_curve_decodable
```

## Concrete values

| Parameter | Degree-28 combination | Degree-3 fold |
| --- | ---: | ---: |
| Evaluation-domain size | 1,048,576 | 262,144 |
| Maximum candidate degree | 1,024 | 255 |
| Challenge-curve degree / branch weight | 28 | 3 |
| Strict support threshold | 38,229 | 9,557 |
| Concrete GS list cap | 100 | 99 |
| Analytic parameter used in the allowance | 112 exactly | less than 113, hence 113 |
| Outer exceptional allowance | 87,316,067,086,790 | 2,388,155,905,379 |
| Curve-decodability allowance | 336,869,026,605,739 | 9,396,508,281,246 |

The values 112 and 113 are not rounded forms of 100 and 99; the formal
development proves that distinction explicitly. In the first instance, the
released message image has dimension 1024 while the ambient space of
polynomials of degree at most 1024 has dimension 1025.

## Noncomputability and external mathematical data

Classical choice is used for quotient representatives, roots/factor choices,
finite assignment choices, and interpolation. Real square roots are used only
in the concrete analytic calculations. The inseparable proof uses finite-field
inverse Frobenius and, for the generic compatible polynomial root, the standard
Mathlib algebraic closure. No executable decoder is claimed.

The generic theorems take the paper's operative algebraic data as explicit
hypotheses: polynomial factorizations, irreducibility, branch roots,
specialized-parent separability for the full-factor transfer, nonvanishing
leading coefficients and regular derivatives for the fixed-branch interface,
degree bounds, candidate-root identities, agreement supports, and cardinality
inequalities.
For Corollary 7.11 it additionally takes the characteristic, Frobenius exponents,
global `(1,k,0)` bound, and the same explicit support-incidence inequality.
The development proves the consequences of those hypotheses; it does not
formalize the cited papers' interpolation-polynomial construction or an
algorithm that discovers the factors.

## Independence and audit discipline

This standalone repository depends only on Lean and Mathlib. It has no
application-specific API or external project dependency.

The canonical release audit is:

```sh
git diff --check
rg -n '\b(sorry|admit|sorryAx|axiom|native_decide)\b' --glob '*.lean' .
lake build WeightedHensel.Terminal
lake build
```

See [AUDIT.md](AUDIT.md) for classifications C–E. C-001 is closed by exposing
the separability condition already imposed in BCHKS26 Step 2; there are no
unclosed C–E obligations.

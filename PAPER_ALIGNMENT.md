# Paper-to-Lean alignment: ePrint Version 1

This document records the correspondence between the first public version of
“Correcting the Weighted Hensel Estimate for Reed–Solomon Curve Decodability”
and the standalone Lean 4 verification artifact in this repository.

The paper is mathematically self-contained. This Lean development provides an
independent machine-checked verification of its principal named results; the
paper does not depend on the formal artifact.

## Manuscript identity

The alignment is identified by the paper title, ePrint Version 1, and theorem
numbering rather than by a development filename. Documentary and bibliographic
statements are outside the formal-proof claim.

The manuscript records the checked Lean mathematical state
`f237d80eafdfbb8fdf5a3464e65510c824452bd5`. The canonical `paper-v1.0`
release is a descendant of that commit containing only archival documentation
and the Version 1 PDF; it does not alter any Lean theorem statement or proof.
The release tag, rather than mutable `main`, records the exact archival commit.
No PDF hash or self-referential release commit is embedded here.

Corollary 7.11 is stated with `k ≥ 1`, and its local parameters are
`D_R = D_H = G_i` and `ℓ = q_i = p^(f_i)`.

## Named results

| Manuscript result | Principal Lean declarations | Status |
| --- | --- | --- |
| Order-zero saturation counterexample | `saturation_tau_strictly_exceeds_printed_base`, `saturationParent_coefficient_bound` | proved |
| Proposition 3.1, positive-order counterexample | `positive_order_beta_one`, `positive_order_beta_one_regular_weight`, `positiveOrderParent_irreducible`, `positiveOrderParent_separableInResponse` | proved |
| Remark 3.2, derivative-numerator counterexample | `derivative_counterexample_xi_regular_weight`, `derivative_printed_ceiling_fails`, `derivativeCounterexampleParent_irreducible`, `derivativeCounterexampleParent_separableInResponse`, `derivativeSpecializedParent_squarefree` | proved |
| Lemma 4.1, shifted parent coefficient bound | `shiftedParentCoefficient_bound` | proved |
| Lemma 4.2, corrected auxiliary numerator | `exists_sourceAuxiliaryNumerator`, `leadingCoeff_dvd_sourceClearedRepresentative_zero` | proved |
| Corollary 4.3, corrected derivative numerator | `exists_sourceDerivativeNumerator` | proved |
| Source recurrence bookkeeping | `SourceTermIndex.singleton_excluded_of_s_eq_zero`, `SourceTermIndex.recursive_index_lt`, `SourceTermIndex.partition_eq_zero_of_s_eq_t`, `SourceTermIndex.w_ledger`, `SourceTermIndex.derivative_ledger`, `source_structural_ledger`, `source_parameter_ledger` | proved |
| Theorem 4.4, direct corrected Hensel estimate | `corrected_source_hensel_estimate` | proved |
| Lemma 6.1, regular quotient embedding and domain | `regularToFunctionField_injective`, `regularQuotient_isDomain`, `branchPolynomial_irreducible` | proved |
| Lemma 6.2 and Corollary 6.3, monic reduction and quotient weight laws | `iteratedBivariateWeight_modByMonic_le`, `regularWeightNat_mk_le`, `regularWeight_add_le`, `regularWeight_mul_le`, `regularWeightNat_pow_le` | proved |
| Lemma 6.4, cleared derivative and shifted coefficient estimates | `regularDerivativeElement_weight_le`, `regularClearedCoefficient_weight_add_le` | proved |
| Theorem 6.5, denominator-free recurrence | `divisionFreeCoefficients`, `division_free_defined_estimate`, `divisionFreeCoefficients_image` | proved |
| Proposition 6.6, equivalence of the two repairs | `divisionFree_eq_sourceNumerator`, `divisionFree_sourceNumerator_weight_eq`, `direct_and_divisionFree_ceilings_equivalent` | proved |
| Lemma 7.1, weighted Sylvester estimate | `weighted_resultant_degree_bound` | proved |
| Corollary 7.2, nonzero resultant and zero count | `canonicalRepresentative_resultant_ne_zero`, `weighted_resultant_zero_count` | proved |
| Lemma 7.3, regular specialization | `branchSpecialization_parentDivisionFreeCoefficients` | proved |
| First resultant, high-order vanishing, and exact truncation | `parentDivisionFreeCoefficients_eq_zero_of_many_branches`, `henselCoefficient_eq_zero_of_cleared_eq_zero`, `exists_exact_henselTruncation_of_many_branches` | proved |
| Lemma 7.4, common numerator | `commonNumerator_image`, `commonNumerator_eval_weightNat_le` | proved |
| Lemma 7.5, second discrepancy and resultant | `commonDiscrepancy_eq_zero_of_many_branches`, `secondResultant_identifies_henselTruncation` | proved |
| Lemma 7.6, abstract heavy-coordinate count with an independent zero budget | `maximumDegree_lt_card_heavyCoordinates` | proved |
| Coefficientwise interpolation | `lagrangeCoefficientCurve_eval_at_node`, `candidate_eq_candidateCurve` | proved |
| Theorem 7.7 and Corollary 7.8, fixed-branch completion | `fixed_branch_curve_decodability` | proved |
| Corollary 7.9, comparison with the published coarse bounds | `weightedDivisionFreeBudget_lt_coarse`, `sourcePoleBudget_lt_coarse`, `sourceCoefficientResultantBudget_lt_coarse`, `sourceSecondResultantBudget_lt_coarse` | proved |
| Shifted-degree counterexample and full-degree remedy | `fullDegreeCounterexample_specialized_zDegree`, `fullDegreeCounterexample_shifted_zDegree`, `shiftedCoefficient_fullDegree_le` | proved |
| Proposition 7.10, full-factor summation | `full_factor_degree_transfer` | proved under the explicit specialized-parent separability hypothesis |
| Proposition 7.10 composed with separable line completion | `separable_full_factor_curve_decodability` | proved |
| Corollary 7.11, global Frobenius degree sums | `fullFactor_frobenius_weight_summation`, `fullFactor_frobenius_yDegree_summation`, `full_factor_frobenius_degree_transfer` | proved |
| Corollary 7.11, `(1,k,0)` powered substitution degree | `frobenius_parent_order_lt_global_XY_degree`, `frobenius_substitutionDegreeBound` | proved |
| Corollary 7.11, sparse exact truncation | `coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_not_dvd`, `exists_exact_sparse_henselTruncation_of_many_frobenius_branches` | proved |
| Corollary 7.11, compatible inverse-Frobenius branch | `perfectPolynomialFrobeniusRoot_pow`, `bivariateFrobeniusRoot_localRoot`, `regularFrobeniusRootEquiv`, `regularWeightNat_regularFrobeniusRootEquiv` | proved |
| Corollary 7.11, rooted common numerator | `frobeniusRootedCommonNumerator`, `frobeniusRootedCommonNumerator_eval_weightNat_le` | proved |
| Corollary 7.11, rooted discrepancy and second resultant | `frobeniusRootedDiscrepancy`, `frobeniusRootedDiscrepancy_weightNat_le`, `frobeniusRootedDiscrepancy_eq_zero_of_many_branches` | proved |
| Corollary 7.11, source-indexed inverse-Frobenius reindexing | `fixed_branch_frobenius_line_decodability_source_indexed` | proved |
| Corollary 7.11, complete inseparable conclusion for `k ≥ 1` | `inseparable_frobenius_curve_decodability` | proved; the formal interfaces are slightly more general |

## Terminal declarations

`Main.lean` checks and prints axiom reports for the seven declarations that
directly correspond to paper-level conclusions:

```text
corrected_source_hensel_estimate
division_free_hensel_estimate
weighted_resultant_zero_count
fixed_branch_curve_decodability
full_factor_degree_transfer
separable_full_factor_curve_decodability
inseparable_frobenius_curve_decodability
```

It also checks two supplementary application-specific numerical instances:

```text
concrete_degree28_curve_decodable
concrete_degree3_curve_decodable
```

Thus the canonical entry point contains nine headline terminal declarations in
total. The reported axiom union is `propext`, `Classical.choice`, and
`Quot.sound`. The canonical verification command is `./scripts/verify.sh`.

## Trust boundary

The formalization checks the mathematical consequences of explicit
factorizations, branch data, degree bounds, specialized separability,
nonvanishing conditions, agreement sets, and cardinality inequalities. It does
not implement a factor-finding algorithm or an executable Guruswami–Sudan
decoder. This is the same boundary stated in the manuscript.

## Supplementary numerical boundary

The formulas and exact arithmetic for `A_cd` and `A_out` are retained and
checked in `ConcreteParameters.lean`. `A_cd` is the S-two curve-decodability
interface bound. `A_out` is an application-specific companion ledger whose
fixed coefficients and weighted-degree caps are explicit numerical inputs.
These two numerical instances are supplementary and are not used by any
theorem in Paper Version 1.

Subject to the stated trust boundary, every substantive theorem of Paper
Version 1 has an identified Lean counterpart.

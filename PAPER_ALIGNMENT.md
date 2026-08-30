# Paper-to-Lean alignment: ePrint Version 1

This document records the correspondence between the first public version of
“Correcting the Weighted Hensel Estimate for Reed–Solomon Curve Decodability”
and the standalone Lean 4 verification artifact in this repository.

The manuscript is identified here by its full title, ePrint Version 1, and its
internal theorem and section numbering. Development filenames are deliberately
not part of the archival identity. The paper is mathematically self-contained;
the Lean repository is an independent machine-checked verification artifact,
not a dependency of the mathematical argument.

## Named mathematical results

| Paper result | Principal Lean declarations | Status |
| --- | --- | --- |
| Saturation/base-case counterexample in Section 3 | `saturation_tau_strictly_exceeds_printed_base`, `saturationParent_coefficient_bound` | proved |
| Proposition 3.1, sharp positive-order counterexample | `positive_order_beta_one`, `positive_order_beta_one_regular_weight`, `positiveOrderParent_irreducible`, `positiveOrderParent_separableInResponse` | proved |
| Remark 3.2, derivative-numerator counterexample | `derivative_counterexample_xi_regular_weight`, `derivative_printed_ceiling_fails`, `derivativeCounterexampleParent_irreducible`, `derivativeCounterexampleParent_separableInResponse`, `derivativeSpecializedParent_squarefree` | proved |
| Lemma 4.1, translation preserves the parent bound | `shiftedParentCoefficient_bound` | proved |
| Lemma 4.2, corrected auxiliary-numerator bound | `exists_sourceAuxiliaryNumerator`, `leadingCoeff_dvd_sourceClearedRepresentative_zero` | proved |
| Corollary 4.3, corrected derivative numerator | `exists_sourceDerivativeNumerator` | proved |
| Source recurrence partition, singleton exclusion, and exponent regularity | `SourceTermIndex.singleton_excluded_of_s_eq_zero`, `SourceTermIndex.recursive_index_lt`, `SourceTermIndex.partition_eq_zero_of_s_eq_t`, `SourceTermIndex.one_le_s_add_epsilon`, `SourceTermIndex.two_le_two_mul_s_add_q` | proved |
| Source `W`, derivative, and structural ledgers | `SourceTermIndex.w_ledger`, `SourceTermIndex.derivative_ledger`, `source_structural_ledger`, `source_parameter_ledger` | proved |
| Theorem 4.4, corrected original numerators | `corrected_source_hensel_estimate` | proved |
| Direct-repair pole and resultant budgets | `sourcePoleBudget_lt_coarse`, `sourceCoefficientResultantBudget_lt_coarse`, `sourceSecondResultantBudget_lt_coarse` | proved |
| Lemma 6.1, regular quotient embedding and domain | `regularToFunctionField_injective`, `regularQuotient_isDomain`, `branchPolynomial_irreducible` | proved |
| Lemma 6.2, monic reduction does not raise weight | `iteratedBivariateWeight_modByMonic_le`, `regularWeightNat_mk_le` | proved |
| Corollary 6.3, quotient weight laws | `regularWeight_add_le`, `regularWeight_mul_le`, `regularWeightNat_pow_le` | proved |
| Lemma 6.4, cleared derivative and coefficient bounds | `regularDerivativeElement_weight_le`, `regularClearedCoefficient_weight_add_le` | proved |
| Theorem 6.5, denominator-free recurrence | `divisionFreeCoefficients`, `division_free_defined_estimate`, `divisionFreeCoefficients_image` | proved |
| Proposition 6.6, equivalence of the two repairs | `divisionFree_eq_sourceNumerator`, `divisionFree_sourceNumerator_weight_eq`, `direct_and_divisionFree_ceilings_equivalent` | proved |
| Lemma 7.1, weighted Sylvester estimate | `weighted_resultant_degree_bound` | proved |
| Corollary 7.2, nonzero resultant and branch zero count | `canonicalRepresentative_resultant_ne_zero`, `weighted_resultant_zero_count` | proved |
| Lemma 7.3, regular specialization | `branchSpecialization_parentDivisionFreeCoefficients` | proved |
| First resultant and finite Hensel truncation | `parentDivisionFreeCoefficients_eq_zero_of_many_branches`, `henselCoefficient_eq_zero_of_cleared_eq_zero`, `exists_exact_henselTruncation_of_many_branches` | proved |
| Lemma 7.4, common numerator | `commonNumerator_image`, `commonNumerator_eval_weightNat_le` | proved |
| Lemma 7.5, discrepancy and second resultant | `commonDiscrepancy_eq_zero_of_many_branches`, `secondResultant_identifies_henselTruncation` | proved |
| Lemma 7.6, heavy-coordinate count | `maximumDegree_lt_card_heavyCoordinates` | proved |
| Coefficientwise interpolation and recovery | `lagrangeCoefficientCurve_eval_at_node`, `candidate_eq_candidateCurve` | proved |
| Theorem 7.7 and Corollary 7.8, fixed-branch completion | `fixed_branch_curve_decodability` | proved |
| Corollary 7.9, published coarse allowance | `weightedDivisionFreeBudget_lt_coarse`, `sourcePoleBudget_lt_coarse`, `sourceCoefficientResultantBudget_lt_coarse`, `sourceSecondResultantBudget_lt_coarse` | proved |
| Full-degree shifted-coefficient counterexample and replacement | `fullDegreeCounterexample_specialized_zDegree`, `fullDegreeCounterexample_shifted_zDegree`, `shiftedCoefficient_fullDegree_le` | proved |
| Specialization content and branch degree sums | `specialization_content_branch_weight_summation`, `specialization_branch_yDegree_summation` | proved |
| Pairwise full-factor degree summation | `factor_square_weight_sum_le_global`, `factor_branch_pair_weight_sum_le` | proved |
| Content roots charged to the derivative resultant | `specialization_content_dvd_clearedDerivativeRepresentative`, `card_content_root_specializations_lt_pole_budget` | proved |
| Specialized-parent separability implies branch derivative nonvanishing | `regularDerivativeElement_ne_zero_of_specialized_separable` | proved |
| Proposition 7.10, separable full-factor transfer | `full_factor_degree_transfer` | proved from the explicit specialized-parent separability hypothesis |
| Separable global transfer composed with line completion | `separable_full_factor_curve_decodability` | proved |
| Corollary 7.11, inseparable factors | `inseparable_frobenius_curve_decodability` | proved |
| Numerical and fixed-branch checks | declarations listed under “Retained numerical checks” | proved |

The direct theorem consumes the literal recurrence, certified partition
indices, auxiliary-numerator bounds, and degree identities. Separate theorems
construct the auxiliary numerators and prove their bounds. This mirrors the
dependency structure of Section 4 without claiming an executable procedure
for discovering a factorization or recurrence.

## Corollary 7.11: inseparable Frobenius ledger

The inseparable proof is divided into reviewable transitions corresponding to
the paper's factor sums, truncation, Frobenius-root, and interpolation stages.

| Paper step | Lean declarations |
| --- | --- |
| Factorization through `Y^(qᵢ)` and weighted factor sums | `fullFactor_frobenius_weight_summation`, `fullFactor_frobenius_yDegree_summation`, `full_factor_frobenius_degree_transfer` |
| Specialized-parent and pairwise degree sums | `fullFactor_parent_yDegree_summation_le`, `frobenius_factor_square_weight_sum_le` |
| `(1,k,0)` substitution-degree bound | `frobenius_parent_order_lt_global_XY_degree`, `frobenius_substitutionDegreeBound` |
| Taylor support only at indices divisible by `qᵢ` | `coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_not_dvd` |
| First resultant and exact sparse truncation | `exists_exact_sparse_henselTruncation_of_many_frobenius_branches` |
| Compatible polynomial, quotient, and function-field roots | `perfectPolynomialFrobeniusRoot_pow`, `bivariateFrobeniusRoot_localRoot`, `regularFrobeniusRootEquiv` |
| Rooted common numerator | `frobeniusRootedCommonNumerator_eval_weightNat_le` |
| Rooted discrepancy and second resultant | `frobeniusRootedDiscrepancy_eq_zero_of_many_branches` |
| Inverse-Frobenius source reindexing | `fixed_branch_frobenius_line_decodability_source_indexed` |
| Full global selection and final interpolation | `inseparable_frobenius_curve_decodability` |

The terminal corollary takes the characteristic, Frobenius exponents, global
weighted and `(1,k,0)` degree bounds, explicit factorizations and branch data,
and the paper's support-incidence inequality. It proves the powered-candidate
degree ledger, sparse truncation, compatible root recovery, rooted second
resultant, source-indexed reindexing, and final degree-one challenge curve. It
does not take that final curve conclusion as an assumption.

## Separable full-factor transfer

The Lean statement of Proposition 7.10 explicitly assumes that each
specialized parent `Rᵢ(x₀,Y,Z)` is separable over `K(Z)`. The development then
derives branch derivative nonvanishing through
`regularDerivativeElement_ne_zero_of_specialized_separable`. Specialization
content is tracked and charged to the regular derivative numerator through
`specialization_content_dvd_clearedDerivativeRepresentative` and
`card_content_root_specializations_lt_pole_budget`.

The theorem `separable_full_factor_curve_decodability` composes this global
selection theorem with the fixed-branch line conclusion. Thus the global
transfer and local completion are both visible in the terminal dependency
graph.

## Retained numerical checks

The numerical modules remain part of the artifact even where the manuscript
uses them only as parameter checks.

| Paper claim | Lean declaration | Status |
| --- | --- | --- |
| Degree-28 exact list cap `100` | `degree28_guruswamiSudan_list_card_le_100` | proved from the stated pairwise-overlap hypothesis |
| Degree-3 exact list cap `99` | `degree3_guruswamiSudan_list_card_le_99` | proved from the stated pairwise-overlap hypothesis |
| Separate analytic parameter `112` | `degree28_rateOnlyListExpression_eq_112` | proved |
| Separate analytic bound `< 113`, hence `113` | `degree3_rateOnlyListExpression_lt_113` | proved |
| Exact outer exceptional allowances | `exact_degree28_outerExceptionalAllowance`, `exact_degree3_outerExceptionalAllowance` | proved |
| Exact curve-decodability allowances | `exact_degree28_curveDecodabilityAllowance`, `exact_degree3_curveDecodabilityAllowance` | proved |
| `1024 < 1025` released-subcode distinction | `degree28_released_subcode_dimension_strict` | proved |
| Degree-28 fixed-branch instance | `concrete_degree28_curve_decodable` | proved |
| Degree-3 fixed-branch instance | `concrete_degree3_curve_decodable` | proved |

The analytic allowance parameters `112` and `113` are distinct from the exact
list caps `100` and `99`. The two concrete terminal theorems instantiate the
fixed-branch interface; they do not construct a list-decoding interpolant or
discover its factors algorithmically.

## Terminal interface and trust boundary

`Main.lean` checks and prints axioms for these nine paper-level declarations:

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

The generic results expose the paper's operative algebraic and combinatorial
data as hypotheses: factorizations, irreducibility and separability, branch
roots, degree bounds, nonvanishing specialization conditions, agreement
supports, and cardinality inequalities. Lean proves the consequences stated
in the paper. No executable decoder or factor-discovery algorithm is claimed.

Subject to this explicit trust boundary, every substantive mathematical
theorem of Paper Version 1 has an identified machine-checked Lean counterpart.
The paper itself remains mathematically self-contained, and this repository
serves as its independent verification artifact.

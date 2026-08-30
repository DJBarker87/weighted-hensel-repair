# Revision 16 paper-to-Lean reconciliation

## Audit basis

This audit compares the standalone Lean development with the 29-page PDF
`Correcting_the_Weighted_Hensel_Estimate_for_Reed_Solomon_Curve_Decodability_Revision16.pdf`.
The audited PDF has SHA-256 digest
`65d92663b6a922760d84b436c33ceab9cb803ffbeb70cb57a721c0c72b536bd5`.
Documentary and bibliographic sentences are outside the mathematical proof
claim; every named mathematical result and every numerical claim used by a
terminal theorem is included below.

## Named mathematical results

| Paper result | Principal Lean declarations | Status |
| --- | --- | --- |
| Saturation/base-case example preceding Proposition 3.1 | `saturation_tau_strictly_exceeds_printed_base`, `saturationParent_coefficient_bound` | proved |
| Proposition 3.1, sharp positive-order counterexample | `positive_order_beta_one`, `positive_order_beta_one_regular_weight`, `positiveOrderParent_irreducible`, `positiveOrderParent_separableInResponse` | proved |
| Remark 3.2, derivative-numerator counterexample | `derivative_counterexample_xi_regular_weight`, `derivative_printed_ceiling_fails`, `derivativeCounterexampleParent_irreducible`, `derivativeCounterexampleParent_separableInResponse`, `derivativeSpecializedParent_squarefree` | proved |
| Lemma 4.1, translation preserves the parent bound | `shiftedParentCoefficient_bound` | proved |
| Lemma 4.2, corrected auxiliary-numerator bound | `exists_sourceAuxiliaryNumerator`, `leadingCoeff_dvd_sourceClearedRepresentative_zero` | proved |
| Corollary 4.3, corrected derivative numerator | `exists_sourceDerivativeNumerator` | proved |
| Source recurrence partition, singleton exclusion, and exponent regularity | `SourceTermIndex.singleton_excluded_of_s_eq_zero`, `SourceTermIndex.recursive_index_lt`, `SourceTermIndex.partition_eq_zero_of_s_eq_t`, `SourceTermIndex.one_le_s_add_epsilon`, `SourceTermIndex.two_le_two_mul_s_add_q` | proved |
| Three source ledgers | `SourceTermIndex.w_ledger`, `SourceTermIndex.derivative_ledger`, `source_structural_ledger`, `source_parameter_ledger` | proved |
| Theorem 4.4, corrected original numerators | `corrected_source_hensel_estimate` | proved |
| Lemma 6.1, regular quotient embedding and domain | `regularToFunctionField_injective`, `regularQuotient_isDomain`, `branchPolynomial_irreducible` | proved |
| Lemma 6.2, monic reduction does not raise weight | `iteratedBivariateWeight_modByMonic_le`, `regularWeightNat_mk_le` | proved |
| Corollary 6.3, quotient weight laws | `regularWeight_add_le`, `regularWeight_mul_le`, `regularWeightNat_pow_le` | proved |
| Lemma 6.4, cleared derivative and coefficient bounds | `regularDerivativeElement_weight_le`, `regularClearedCoefficient_weight_add_le` | proved |
| Theorem 6.5, denominator-free recurrence | `divisionFreeCoefficients`, `division_free_defined_estimate`, `divisionFreeCoefficients_image` | proved |
| Proposition 6.6, equivalence of repairs | `divisionFree_eq_sourceNumerator`, `divisionFree_sourceNumerator_weight_eq`, `direct_and_divisionFree_ceilings_equivalent` | proved |
| Lemma 7.1, weighted Sylvester estimate | `weighted_resultant_degree_bound` | proved |
| Corollary 7.2, nonzero resultant and zero count | `canonicalRepresentative_resultant_ne_zero`, `weighted_resultant_zero_count` | proved |
| Lemma 7.3, regular specialization | `branchSpecialization_parentDivisionFreeCoefficients` | proved |
| High-order coefficient vanishing and exact truncation | `parentDivisionFreeCoefficients_eq_zero_of_many_branches`, `henselCoefficient_eq_zero_of_cleared_eq_zero`, `exists_exact_henselTruncation_of_many_branches` | proved |
| Lemma 7.4, common numerator | `commonNumerator_image`, `commonNumerator_eval_weightNat_le` | proved |
| Lemma 7.5, second resultant | `commonDiscrepancy_eq_zero_of_many_branches`, `secondResultant_identifies_henselTruncation` | proved |
| Lemma 7.6, heavy-coordinate count | `maximumDegree_lt_card_heavyCoordinates` | proved |
| Coefficientwise interpolation and recovery | `lagrangeCoefficientCurve_eval_at_node`, `candidate_eq_candidateCurve` | proved |
| Theorem 7.7 and Corollary 7.8, fixed-branch completion | `fixed_branch_curve_decodability` | proved |
| Corollary 7.9, published coarse allowance | `weightedDivisionFreeBudget_lt_coarse`, `sourcePoleBudget_lt_coarse`, `sourceCoefficientResultantBudget_lt_coarse`, `sourceSecondResultantBudget_lt_coarse` | proved |
| Shifted-coefficient counterexample and replacement | `fullDegreeCounterexample_specialized_zDegree`, `fullDegreeCounterexample_shifted_zDegree`, `shiftedCoefficient_fullDegree_le` | proved |
| Proposition 7.10, full-factor summation | `full_factor_degree_transfer` | proved under the explicit BCHKS26 Step 2 specialized-parent separability hypothesis |
| Proposition 7.10 composed with line completion | `separable_full_factor_curve_decodability` | proved |
| Corollary 7.11, inseparable factors | `inseparable_frobenius_curve_decodability` | proved |
| Table 1 and Appendix A arithmetic | declarations listed under “Concrete instances” below | proved |

The direct theorem deliberately consumes the literal recurrence, certified
partition indices, auxiliary-numerator estimates, and degree identities. The
construction and bound for the auxiliary numerators are separate theorems.
Together they match the dependency structure of Section 4; the terminal
theorem does not pretend that a factorization or recurrence is discovered by
an executable procedure.

## Corollary 7.11 ledger

The inseparable proof is split so that each mathematical transition in the
paper can be reviewed independently.

| Paper step | Lean declarations |
| --- | --- |
| Factorization through `Y^(qᵢ)` and equations (127)–(129) | `fullFactor_frobenius_weight_summation`, `fullFactor_frobenius_yDegree_summation`, `full_factor_frobenius_degree_transfer` |
| Specialized-parent and pairwise sums, equations (135)–(136) | `fullFactor_parent_yDegree_summation_le`, `frobenius_factor_square_weight_sum_le` |
| Powered-candidate cutoff, equation (137) | `frobenius_parent_order_lt_global_XY_degree`, `frobenius_substitutionDegreeBound` |
| Taylor support only at indices divisible by `qᵢ` | `coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_not_dvd` |
| First resultant and exact sparse truncation | `exists_exact_sparse_henselTruncation_of_many_frobenius_branches` |
| Compatible polynomial, quotient, and function-field roots | `perfectPolynomialFrobeniusRoot_pow`, `bivariateFrobeniusRoot_localRoot`, `regularFrobeniusRootEquiv` |
| Rooted numerator and equation (139) | `frobeniusRootedCommonNumerator_eval_weightNat_le`, `frobeniusRootedDiscrepancy_eq_zero_of_many_branches` |
| Inverse-Frobenius source reindexing | `fixed_branch_frobenius_line_decodability_source_indexed` |
| Full global selection, rooted second resultant, interpolation, and line (140) | `inseparable_frobenius_curve_decodability` |

The terminal corollary takes the characteristic, Frobenius exponents, global
weighted and `(1,k,0)` degree bounds, explicit factorizations and branch data,
and the paper's support-incidence inequality. It proves the powered-candidate
degree ledger, sparse truncation, compatible root recovery, and the final
degree-one challenge curve. No nonvanishing or root-extraction oracle
proposition is inserted to bypass those steps.

## Full-factor transfer

The Lean statement of Proposition 7.10 explicitly assumes that each
specialized parent `Rᵢ(x₀,Y,Z)` is separable over `K(Z)`. This is the choice
made in BCHKS26 Step 2. The development derives branch derivative
nonvanishing via
`regularDerivativeElement_ne_zero_of_specialized_separable`; it does not take
branchwise nonvanishing as an unexplained project assumption. Specialization
content is tracked and charged to the regular derivative numerator through
`specialization_content_dvd_clearedDerivativeRepresentative` and
`card_content_root_specializations_lt_pole_budget`.

## Concrete instances

| Paper claim | Lean declaration | Status |
| --- | --- | --- |
| Degree-28 exact GS cap `100` | `degree28_guruswamiSudan_list_card_le_100` | proved from the stated pairwise-overlap hypothesis |
| Degree-3 exact GS cap `99` | `degree3_guruswamiSudan_list_card_le_99` | proved from the stated pairwise-overlap hypothesis |
| Separate analytic parameter `112` | `degree28_rateOnlyListExpression_eq_112` | proved |
| Separate analytic bound `< 113`, hence `113` | `degree3_rateOnlyListExpression_lt_113` | proved |
| Exact outer exceptional allowances | `exact_degree28_outerExceptionalAllowance`, `exact_degree3_outerExceptionalAllowance` | proved |
| Exact curve-decodability allowances | `exact_degree28_curveDecodabilityAllowance`, `exact_degree3_curveDecodabilityAllowance` | proved |
| `1024 < 1025` released-subcode distinction | `degree28_released_subcode_dimension_strict` | proved |
| Degree-28 fixed-branch instance | `concrete_degree28_curve_decodable` | proved |
| Degree-3 fixed-branch instance | `concrete_degree3_curve_decodable` | proved |

The values `112` and `113` are the analytic allowance parameters, not rounded
forms of the exact list caps `100` and `99`. The two terminal concrete
theorems instantiate the fixed-branch interface; they do not construct the
Guruswami–Sudan interpolant or its factorization.

## Revision 16 documentary delta

Revision 16 predates completion of the Frobenius modules. Its mathematical
Corollary 7.11 is the statement checked above, but these documentary sentences
must be changed in the forthcoming manuscript version:

1. The introduction says that Corollary 7.11 is “not yet formalized.”
2. The paragraph after Corollary 7.11 repeats that the inseparable corollary is
   not yet formalized.
3. Section 8 repeats that the Frobenius-root argument is not yet formalized.
4. The conclusion says the inseparable extension remains manuscript-only.

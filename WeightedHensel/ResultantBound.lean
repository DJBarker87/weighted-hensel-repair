/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.DivisionFreeRecurrence
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Weighted resultant bound

The determinant estimate records a potential for every Sylvester row.  A
determinant term uses each row exactly once, which is the formal cancellation
of the `tau` contribution required by the paper.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Determinant degree bound with row potentials. -/
theorem matrix_det_natDegree_le_of_potentials
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι (Polynomial K))
    (rowPotential columnBudget : ι → Nat) (totalBudget : Nat)
    (entries : ∀ row column, matrix row column ≠ 0 →
      (matrix row column).natDegree + rowPotential row ≤
        columnBudget column)
    (budgets : ∑ column, columnBudget column ≤
      totalBudget + ∑ row, rowPotential row) :
    matrix.det.natDegree ≤ totalBudget := by
  classical
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro permutation
  by_cases productZero :
      ∏ column : ι, matrix (permutation column) column = 0
  · simp [productZero]
  have entryNeZero : ∀ column : ι,
      matrix (permutation column) column ≠ 0 := by
    intro column entryZero
    apply productZero
    exact Finset.prod_eq_zero (Finset.mem_univ column) entryZero
  calc
    (Equiv.Perm.sign permutation •
        ∏ column : ι, matrix (permutation column) column).natDegree ≤
        (∏ column : ι, matrix (permutation column) column).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with sign | sign
      · rw [sign, one_smul]
      · rw [sign, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ column : ι,
        (matrix (permutation column) column).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ totalBudget := by
      have entrySum :
          ∑ column : ι,
              ((matrix (permutation column) column).natDegree +
                rowPotential (permutation column)) ≤
            ∑ column : ι, columnBudget column := by
        exact Finset.sum_le_sum fun column _ ↦
          entries (permutation column) column (entryNeZero column)
      have permutedPotential :
          ∑ column : ι, rowPotential (permutation column) =
            ∑ row : ι, rowPotential row :=
        Equiv.sum_comp permutation rowPotential
      rw [Finset.sum_add_distrib, permutedPotential] at entrySum
      exact Nat.le_of_add_le_add_right (entrySum.trans budgets)

/-- Weighted Sylvester estimate.  The key row-index identities are proved
inside the two block cases; the `tau` shifts cancel before the final sum. -/
theorem resultant_natDegree_le_mul_weight
    {K : Type*} [Field K]
    (representative modulus : BivariatePolynomial K)
    (m d tau representativeWeight : Nat)
    (representativeCoefficients : ∀ coefficient,
      representative.coeff coefficient ≠ 0 →
        (representative.coeff coefficient).natDegree + coefficient * tau ≤
          representativeWeight)
    (modulusCoefficients : ∀ coefficient,
      modulus.coeff coefficient ≠ 0 →
        (modulus.coeff coefficient).natDegree + coefficient * tau ≤
          d * tau) :
    (Polynomial.resultant representative modulus m d).natDegree ≤
      d * representativeWeight := by
  classical
  let rowPotential : Fin (m + d) → Nat := fun row ↦ row.1 * tau
  let columnBudget : Fin (m + d) → Nat := fun column ↦
    column.addCases
      (fun shift : Fin m ↦ d * tau + shift.1 * tau)
      (fun shift : Fin d ↦ representativeWeight + shift.1 * tau)
  unfold Polynomial.resultant
  apply matrix_det_natDegree_le_of_potentials
    (Polynomial.sylvester representative modulus m d)
    rowPotential columnBudget (d * representativeWeight)
  · intro row column entryNeZero
    induction column using Fin.addCases with
    | left column =>
        have entryDescription :
            column.1 ≤ row.1 ∧ row.1 ≤ column.1 + d ∧
              modulus.coeff (row.1 - column.1) ≠ 0 := by
          simpa [Polynomial.sylvester] using entryNeZero
        have bounded := modulusCoefficients
          (row.1 - column.1) entryDescription.2.2
        have rowWeight : row.1 * tau =
            (row.1 - column.1) * tau + column.1 * tau := by
          rw [← Nat.add_mul, Nat.sub_add_cancel entryDescription.1]
        have indexCancel : row.1 - column.1 + column.1 - column.1 =
            row.1 - column.1 := by omega
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left,
          Set.mem_Icc, entryDescription.1, entryDescription.2.1, and_self,
          ↓reduceIte, rowPotential, columnBudget]
        rw [rowWeight]
        simpa [Nat.add_assoc, indexCancel] using
          Nat.add_le_add_right bounded (column.1 * tau)
    | right column =>
        have entryDescription :
            column.1 ≤ row.1 ∧ row.1 ≤ column.1 + m ∧
              representative.coeff (row.1 - column.1) ≠ 0 := by
          simpa [Polynomial.sylvester] using entryNeZero
        have bounded := representativeCoefficients
          (row.1 - column.1) entryDescription.2.2
        have rowWeight : row.1 * tau =
            (row.1 - column.1) * tau + column.1 * tau := by
          rw [← Nat.add_mul, Nat.sub_add_cancel entryDescription.1]
        have indexCancel : row.1 - column.1 + column.1 - column.1 =
            row.1 - column.1 := by omega
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right,
          Set.mem_Icc, entryDescription.1, entryDescription.2.1, and_self,
          ↓reduceIte, rowPotential, columnBudget]
        rw [rowWeight]
        simpa [Nat.add_assoc, indexCancel] using
          Nat.add_le_add_right bounded (column.1 * tau)
  · dsimp [columnBudget, rowPotential]
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd,
      Fin.val_natAdd, Finset.sum_add_distrib]
    simp_rw [Nat.add_mul]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    have productCommute : m * (d * tau) = d * (m * tau) := by ac_rfl
    exact le_of_eq (by rw [productCommute]; omega)

/-- Instantiation for a polynomial `P` of weight at most `C` and the
monicized branch equation of degree `h`. -/
theorem weighted_resultant_degree_bound
    {K : Type*} [Field K] (factor representative : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell DH tau C : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (representativeWeight : iteratedBivariateWeight tau representative ≤ C) :
    (Polynomial.resultant representative (monicization factor)).natDegree ≤
      factor.natDegree * C := by
  have representativeCoefficients : ∀ coefficient,
      representative.coeff coefficient ≠ 0 →
        (representative.coeff coefficient).natDegree + coefficient * tau ≤ C := by
    intro coefficient coefficientNeZero
    exact (coeff_weight_le_iteratedBivariateWeight tau representative coefficient
      (Polynomial.mem_support_iff.mpr coefficientNeZero)).trans representativeWeight
  have modulusCoefficients : ∀ coefficient,
      (monicization factor).coeff coefficient ≠ 0 →
        ((monicization factor).coeff coefficient).natDegree +
            coefficient * tau ≤ factor.natDegree * tau := by
    intro coefficient coefficientNeZero
    rw [← generatorWeightEq]
    exact monicization_coefficientWeight_le factor factorNeZero ell DH
      factorCoefficientBound coefficient
      (Polynomial.mem_support_iff.mpr coefficientNeZero)
  rw [monicization_natDegree]
  exact (resultant_natDegree_le_mul_weight representative
    (monicization factor) representative.natDegree factor.natDegree tau C
    representativeCoefficients modulusCoefficients)

/-- A common root forces every resultant computed with valid degree bounds
to vanish.  The explicit bounds make this stable under specialization degree
drops. -/
theorem resultant_eq_zero_of_common_root_of_natDegree_le
    {K : Type*} [Field K]
    (left right : Polynomial K) (leftDegree rightDegree : Nat) (root : K)
    (leftDegreePositive : 0 < leftDegree)
    (leftDegreeLe : left.natDegree ≤ leftDegree)
    (rightDegreeLe : right.natDegree ≤ rightDegree)
    (leftRoot : left.IsRoot root) (rightRoot : right.IsRoot root) :
    Polynomial.resultant left right leftDegree rightDegree = 0 := by
  by_cases leftExact : left.natDegree = leftDegree
  · have leftNeZero : left ≠ 0 := by
      intro leftZero
      simp [leftZero] at leftExact
      omega
    obtain ⟨quotient, factorization⟩ := Polynomial.dvd_iff_isRoot.mpr leftRoot
    have quotientNeZero : quotient ≠ 0 := by
      intro quotientZero
      rw [quotientZero, mul_zero] at factorization
      exact leftNeZero factorization
    have linearNeZero : (Polynomial.X - Polynomial.C root : Polynomial K) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero root
    have productDegree :
        (Polynomial.X - Polynomial.C root : Polynomial K).natDegree +
            quotient.natDegree = leftDegree := by
      rw [← Polynomial.natDegree_mul linearNeZero quotientNeZero,
        ← factorization, leftExact]
    rw [← productDegree, factorization]
    rw [Polynomial.resultant_mul_left _ _ _ _ rightDegreeLe,
      Polynomial.natDegree_X_sub_C,
      Polynomial.resultant_X_sub_C_left right rightDegree root rightDegreeLe,
      rightRoot]
    simp
  · by_cases rightExact : right.natDegree = rightDegree
    · by_cases rightZero : right = 0
      · rw [rightZero, Polynomial.resultant_zero_right]
        simp [leftDegreePositive.ne']
      · obtain ⟨quotient, factorization⟩ :=
          Polynomial.dvd_iff_isRoot.mpr rightRoot
        have quotientNeZero : quotient ≠ 0 := by
          intro quotientZero
          rw [quotientZero, mul_zero] at factorization
          exact rightZero factorization
        have linearNeZero :
            (Polynomial.X - Polynomial.C root : Polynomial K) ≠ 0 :=
          Polynomial.X_sub_C_ne_zero root
        have productDegree :
            (Polynomial.X - Polynomial.C root : Polynomial K).natDegree +
                quotient.natDegree = rightDegree := by
          rw [← Polynomial.natDegree_mul linearNeZero quotientNeZero,
            ← factorization, rightExact]
        rw [← productDegree, factorization]
        rw [Polynomial.resultant_mul_right _ _ _ _ leftDegreeLe,
          Polynomial.natDegree_X_sub_C,
          Polynomial.resultant_X_sub_C_right left leftDegree root leftDegreeLe,
          leftRoot]
        simp
    · exact Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _
        (lt_of_le_of_ne leftDegreeLe leftExact)
        (lt_of_le_of_ne rightDegreeLe rightExact)

/-- The controlling resultant of a nonzero regular class on a fixed
irreducible branch is nonzero. -/
theorem canonicalRepresentative_resultant_ne_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (element : RegularQuotient factor) (elementNeZero : element ≠ 0) :
    Polynomial.resultant
        (canonicalRepresentative factor factorIrreducible.ne_zero element)
        (monicization factor) ≠ 0 := by
  let representative :=
    canonicalRepresentative factor factorIrreducible.ne_zero element
  let rationalMap : Polynomial K →+* RationalFunctionField K :=
    algebraMap (Polynomial K) (RationalFunctionField K)
  let mappedRepresentative := representative.map rationalMap
  let mappedFactor := branchPolynomial factor
  have representativeNeZero : representative ≠ 0 := by
    intro representativeZero
    apply elementNeZero
    rw [← mk_canonicalRepresentative factor factorIrreducible.ne_zero element]
    simp [representative, representativeZero]
  have rationalMapInjective : Function.Injective rationalMap :=
    IsFractionRing.injective (Polynomial K) (RationalFunctionField K)
  have mappedRepresentativeNeZero : mappedRepresentative ≠ 0 :=
    (Polynomial.map_ne_zero_iff rationalMapInjective).mpr representativeNeZero
  have mappedFactorIrreducible : Irreducible mappedFactor :=
    branchPolynomial_irreducible factor factorIrreducible factorPositive
  have mappedFactorNeZero : mappedFactor ≠ 0 := mappedFactorIrreducible.ne_zero
  have mappedLeadingNeZero : mappedFactor.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr mappedFactorNeZero
  let unscaledRepresentative :=
    mappedRepresentative.scaleRoots mappedFactor.leadingCoeff⁻¹
  have unscaledRepresentativeNeZero : unscaledRepresentative ≠ 0 :=
    Polynomial.scaleRoots_ne_zero mappedRepresentativeNeZero _
  have representativeDegreeLt : representative.natDegree < factor.natDegree :=
    canonicalRepresentative_natDegree_lt factor factorIrreducible.ne_zero
      factorPositive element
  have unscaledDegreeLt :
      unscaledRepresentative.natDegree < mappedFactor.natDegree := by
    rw [Polynomial.natDegree_scaleRoots,
      Polynomial.natDegree_map_eq_of_injective rationalMapInjective,
      branchPolynomial_natDegree]
    exact representativeDegreeLt
  have mappedFactorNotDvd : ¬ mappedFactor ∣ unscaledRepresentative :=
    Polynomial.not_dvd_of_natDegree_lt unscaledRepresentativeNeZero
      unscaledDegreeLt
  have coprime : IsCoprime unscaledRepresentative mappedFactor :=
    (mappedFactorIrreducible.coprime_iff_not_dvd.mpr mappedFactorNotDvd).symm
  have unscaledResultantNeZero :
      Polynomial.resultant unscaledRepresentative mappedFactor ≠ 0 := by
    intro resultantZero
    exact (Polynomial.resultant_eq_zero_iff.mp resultantZero).2 coprime
  have scaleBack :
      unscaledRepresentative.scaleRoots mappedFactor.leadingCoeff =
        mappedRepresentative := by
    change (mappedRepresentative.scaleRoots mappedFactor.leadingCoeff⁻¹).scaleRoots
        mappedFactor.leadingCoeff = mappedRepresentative
    rw [← Polynomial.scaleRoots_mul]
    simp [mappedLeadingNeZero]
  have mappedNormalizedResultantNeZero :
      Polynomial.resultant mappedRepresentative
          mappedFactor.integralNormalization ≠ 0 := by
    rw [← scaleBack]
    rw [Polynomial.resultant_integralNormalization unscaledRepresentative
      mappedFactor (by rw [branchPolynomial_natDegree]; omega)]
    exact mul_ne_zero (pow_ne_zero _ mappedLeadingNeZero)
      unscaledResultantNeZero
  intro resultantZero
  have mappedResultantZero := congrArg rationalMap resultantZero
  rw [← Polynomial.resultant_map_map] at mappedResultantZero
  have mappedNormalization :
      (monicization factor).map rationalMap =
        mappedFactor.integralNormalization := by
    exact (Polynomial.integralNormalization_map rationalMap factor (by
      intro mappedZero
      apply factorIrreducible.ne_zero
      apply Polynomial.leadingCoeff_eq_zero.mp
      apply rationalMapInjective
      simpa using mappedZero)).symm
  have representativeDegreeMap : mappedRepresentative.natDegree =
      representative.natDegree :=
    Polynomial.natDegree_map_eq_of_injective rationalMapInjective _
  have normalizationDegreeMap :
      ((monicization factor).map rationalMap).natDegree =
        (monicization factor).natDegree :=
    Polynomial.natDegree_map_eq_of_injective rationalMapInjective _
  simp only [map_zero] at mappedResultantZero
  change Polynomial.resultant mappedRepresentative
      ((monicization factor).map rationalMap)
      representative.natDegree (monicization factor).natDegree = 0
        at mappedResultantZero
  rw [← representativeDegreeMap, ← normalizationDegreeMap]
    at mappedResultantZero
  apply mappedNormalizedResultantNeZero
  rw [← mappedNormalization]
  exact mappedResultantZero

/-- A branch-root specialization killing a regular element makes its fixed
controlling resultant vanish at the same `z`. -/
theorem eval_canonicalRepresentative_resultant_eq_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (element : RegularQuotient factor)
    (z t : K)
    (rootPair : (monicization factor).eval₂ (Polynomial.evalRingHom z) t = 0)
    (specializationZero :
      regularSpecialization factor z t rootPair element = 0) :
    (Polynomial.resultant
        (canonicalRepresentative factor factorNeZero element)
        (monicization factor)).eval z = 0 := by
  let representative := canonicalRepresentative factor factorNeZero element
  let modulus := monicization factor
  let evaluation := Polynomial.evalRingHom z
  have representativeRoot : (representative.map evaluation).IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    rw [← regularSpecialization_eq_eval_canonical factor factorNeZero
      z t rootPair element]
    exact specializationZero
  have modulusRoot : (modulus.map evaluation).IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact rootPair
  have swappedResultantZero : Polynomial.resultant
      (modulus.map evaluation) (representative.map evaluation)
      factor.natDegree representative.natDegree = 0 :=
    resultant_eq_zero_of_common_root_of_natDegree_le _ _ _ _ t
      factorPositive
      (by rw [← monicization_natDegree factor]; exact Polynomial.natDegree_map_le)
      Polynomial.natDegree_map_le modulusRoot representativeRoot
  have specializedResultantZero : Polynomial.resultant
      (representative.map evaluation) (modulus.map evaluation)
      representative.natDegree factor.natDegree = 0 := by
    rw [Polynomial.resultant_comm, swappedResultantZero, mul_zero]
  change evaluation (Polynomial.resultant representative modulus
      representative.natDegree modulus.natDegree) = 0
  rw [← Polynomial.resultant_map_map, monicization_natDegree]
  exact specializedResultantZero

/-- Degree bound for the one controlling resultant attached to a quotient
class. -/
theorem canonicalRepresentative_resultant_natDegree_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell DH : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (element : RegularQuotient factor) :
    (Polynomial.resultant
        (canonicalRepresentative factor factorNeZero element)
        (monicization factor)).natDegree ≤
      factor.natDegree * regularWeightNat factor factorNeZero
        (DH + ell - ell * factor.natDegree) element := by
  let tau := DH + ell - ell * factor.natDegree
  let representative := canonicalRepresentative factor factorNeZero element
  have representativeCoefficients : ∀ coefficient,
      representative.coeff coefficient ≠ 0 →
        (representative.coeff coefficient).natDegree + coefficient * tau ≤
          regularWeightNat factor factorNeZero tau element := by
    intro coefficient coefficientNeZero
    exact coeff_weight_le_iteratedBivariateWeight tau representative coefficient
      (Polynomial.mem_support_iff.mpr coefficientNeZero)
  have modulusCoefficients : ∀ coefficient,
      (monicization factor).coeff coefficient ≠ 0 →
        ((monicization factor).coeff coefficient).natDegree +
            coefficient * tau ≤ factor.natDegree * tau := by
    intro coefficient coefficientNeZero
    exact monicization_coefficientWeight_le factor factorNeZero ell DH
      factorCoefficientBound coefficient
      (Polynomial.mem_support_iff.mpr coefficientNeZero)
  rw [monicization_natDegree]
  exact resultant_natDegree_le_mul_weight representative (monicization factor)
    representative.natDegree factor.natDegree tau
    (regularWeightNat factor factorNeZero tau element)
    representativeCoefficients modulusCoefficients

/-- Fixed-branch root-pair zero count. -/
theorem card_rootPair_specializations_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree) (ell DH : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (element : RegularQuotient factor) (elementNeZero : element ≠ 0)
    (challenges : Finset K) (rootValue : K → K)
    (rootPair : ∀ z ∈ challenges,
      (monicization factor).eval₂ (Polynomial.evalRingHom z) (rootValue z) = 0)
    (specializationZero : ∀ z (zMem : z ∈ challenges),
      regularSpecialization factor z (rootValue z) (rootPair z zMem) element = 0) :
    challenges.card ≤ factor.natDegree *
      regularWeightNat factor factorIrreducible.ne_zero
        (DH + ell - ell * factor.natDegree) element := by
  classical
  let controllingResultant := Polynomial.resultant
    (canonicalRepresentative factor factorIrreducible.ne_zero element)
    (monicization factor)
  have resultantNeZero : controllingResultant ≠ 0 :=
    canonicalRepresentative_resultant_ne_zero factor factorIrreducible
      factorPositive element elementNeZero
  calc
    challenges.card ≤ controllingResultant.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z zMem
      rw [Polynomial.mem_roots resultantNeZero, Polynomial.IsRoot]
      apply eval_canonicalRepresentative_resultant_eq_zero factor
        factorIrreducible.ne_zero factorPositive element z (rootValue z)
        (rootPair z (by simpa using zMem))
      exact specializationZero z (by simpa using zMem)
    _ ≤ factor.natDegree *
        regularWeightNat factor factorIrreducible.ne_zero
          (DH + ell - ell * factor.natDegree) element :=
      canonicalRepresentative_resultant_natDegree_le factor
        factorIrreducible.ne_zero ell DH factorCoefficientBound element

/-- More than `h*C` valid root-pair zeros force the regular class to be
zero.  This is the paper's weighted resultant zero-count theorem. -/
theorem weighted_resultant_zero_count
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree) (ell DH C : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (element : RegularQuotient factor)
    (elementWeight : regularWeightNat factor factorIrreducible.ne_zero
      (DH + ell - ell * factor.natDegree) element ≤ C)
    (challenges : Finset K) (rootValue : K → K)
    (rootPair : ∀ z ∈ challenges,
      (monicization factor).eval₂ (Polynomial.evalRingHom z) (rootValue z) = 0)
    (specializationZero : ∀ z (zMem : z ∈ challenges),
      regularSpecialization factor z (rootValue z) (rootPair z zMem) element = 0)
    (manyZeros : factor.natDegree * C < challenges.card) :
    element = 0 := by
  by_contra elementNeZero
  have countBound := card_rootPair_specializations_le factor factorIrreducible
    factorPositive ell DH factorCoefficientBound element elementNeZero challenges
    rootValue rootPair specializationZero
  have weightedBound := Nat.mul_le_mul_left factor.natDegree elementWeight
  omega

#print axioms matrix_det_natDegree_le_of_potentials
#print axioms resultant_natDegree_le_mul_weight
#print axioms weighted_resultant_degree_bound
#print axioms resultant_eq_zero_of_common_root_of_natDegree_le
#print axioms canonicalRepresentative_resultant_ne_zero
#print axioms eval_canonicalRepresentative_resultant_eq_zero
#print axioms canonicalRepresentative_resultant_natDegree_le
#print axioms card_rootPair_specializations_le
#print axioms weighted_resultant_zero_count

end

end WeightedHensel

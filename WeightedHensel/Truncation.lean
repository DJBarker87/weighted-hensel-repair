/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.PowerSeriesLift
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Truncation of the fixed-branch Hensel series

Finite branch specialization is performed only on the regular quotient.
The first theorem records the Taylor-coefficient vanishing for a single
polynomial branch.  The second applies the weighted resultant zero count to
the canonical recursively defined coefficient `δ_t`.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- A polynomial branch of degree strictly below `t` kills the specialized
canonical coefficient `δ_t`. -/
theorem branchSpecialization_parentDivisionFreeCoefficients_eq_zero_of_degree_lt
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (d : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (candidateRoot : challengeCandidatePolynomial z candidate parent = 0)
    (t : Nat) (degreeLt : candidate.natDegree < t) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (parentDivisionFreeCoefficients parent factor x₀ d t) = 0 := by
  rw [branchSpecialization_parentDivisionFreeCoefficients parent factor
    factorPositive x₀ z candidate localRoot d dPositive parentDegreeLe
    candidateRoot t,
    coeff_shiftedCandidateSeries_eq_zero_of_natDegree_lt x₀ candidate t
      degreeLt,
    mul_zero]

/-- If more than `h C_t` valid polynomial branches kill the coefficient
`δ_t`, the weighted resultant forces `δ_t=0` in the regular quotient. -/
theorem parentDivisionFreeCoefficients_eq_zero_of_many_branches
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ : K) (ell DH DR d b tau m t : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (parentDegreeLe : parent.natDegree ≤ d)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z) ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) parent = 0)
    (candidateDegree : ∀ z ∈ challenges, (candidate z).natDegree ≤ m)
    (aboveDegree : m < t)
    (manyBranches : factor.natDegree *
      divisionFreeCeiling tau (sourceMu DR ell d b) t < challenges.card) :
    parentDivisionFreeCoefficients parent factor x₀ d t = 0 := by
  classical
  let delta := parentDivisionFreeCoefficients parent factor x₀ d t
  by_cases deltaZero : delta = 0
  · exact deltaZero
  have deltaWeightWithBot : regularWeight factor factorIrreducible.ne_zero tau
        delta ≤
      (divisionFreeCeiling tau (sourceMu DR ell d b) t : Nat) := by
    exact parentDivisionFreeCoefficients_weight_le parent factor x₀ ell DH DR
      d b tau factorIrreducible.ne_zero factorCoefficientBound
      generatorWeightEq globalBound tauEq ellLeDR dPositive ellDLeDR wLeB t
  have deltaWeight : regularWeightNat factor factorIrreducible.ne_zero tau
        delta ≤ divisionFreeCeiling tau (sourceMu DR ell d b) t := by
    rw [regularWeight_eq_coe factor factorIrreducible.ne_zero tau deltaZero] at deltaWeightWithBot
    exact WithBot.coe_le_coe.mp deltaWeightWithBot
  have deltaWeightForResultant :
      regularWeightNat factor factorIrreducible.ne_zero
          (DH + ell - ell * factor.natDegree) delta ≤
        divisionFreeCeiling tau (sourceMu DR ell d b) t := by
    simpa only [generatorWeightEq] using deltaWeight
  let rootValue : K → K := fun z ↦
    branchRootValue factor x₀ z (candidate z)
  let rootPair : ∀ z ∈ challenges,
      (monicization factor).eval₂ (Polynomial.evalRingHom z) (rootValue z) = 0 :=
    fun z zMem ↦ branchRootPair factor factorPositive x₀ z (candidate z)
      (localRoot z zMem)
  apply weighted_resultant_zero_count factor factorIrreducible factorPositive
    ell DH (divisionFreeCeiling tau (sourceMu DR ell d b) t)
    factorCoefficientBound delta deltaWeightForResultant challenges rootValue
    rootPair
  · intro z zMem
    change branchSpecialization factor factorPositive x₀ z (candidate z)
        (localRoot z zMem) delta = 0
    apply
      branchSpecialization_parentDivisionFreeCoefficients_eq_zero_of_degree_lt
        parent factor factorPositive x₀ z (candidate z) (localRoot z zMem) d
        dPositive parentDegreeLe (candidateRoot z zMem) t
    exact (candidateDegree z zMem).trans_lt aboveDegree
  · exact manyBranches

/-! ## From cleared coefficients to the finite root -/

/-- A zero cleared coefficient forces the corresponding function-field
Hensel coefficient to vanish once the two clearing factors are nonzero. -/
theorem henselCoefficient_eq_zero_of_cleared_eq_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (eta : RegularQuotient factor) (etaNeZero : eta ≠ 0)
    (delta : Nat → RegularQuotient factor)
    (alpha : Nat → BranchFunctionField factor)
    (deltaImage : ∀ order,
      regularToFunctionField factor factorPositive (delta order) =
        regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) *
          regularToFunctionField factor factorPositive eta ^
              henselExponent order *
            alpha order)
    (t : Nat) (deltaZero : delta t = 0) :
    alpha t = 0 := by
  let mapToField := regularToFunctionField factor factorPositive
  have etaImageNeZero : mapToField eta ≠ 0 :=
    regularToFunctionField_ne_zero factor factorNeZero factorPositive etaNeZero
  have leadingImageNeZero :
      mapToField (regularLeadingCoefficient factor) ≠ 0 := by
    simpa [mapToField, regularLeadingCoefficient] using
      (regularCoefficientMap_injective factor factorPositive).ne
        (Polynomial.leadingCoeff_ne_zero.mpr factorNeZero)
  have clearedProductZero :
      mapToField (regularLeadingCoefficient factor) *
          mapToField eta ^ henselExponent t * alpha t = 0 := by
    rw [← deltaImage t, deltaZero, map_zero]
  rcases mul_eq_zero.mp clearedProductZero with clearingZero | alphaZero
  · rcases mul_eq_zero.mp clearingZero with leadingZero | etaPowerZero
    · exact (leadingImageNeZero leadingZero).elim
    · exact (pow_ne_zero _ etaImageNeZero etaPowerZero).elim
  · exact alphaZero

/-- Polynomial evaluation modulo `U^order` only sees the input series modulo
`U^order`. -/
theorem trunc_eval_coe_trunc
    {R : Type*} [CommRing R]
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat) :
    PowerSeries.trunc order
        (polynomial.eval (PowerSeries.trunc order series : PowerSeries R)) =
      PowerSeries.trunc order (polynomial.eval series) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp only [Polynomial.eval_add, map_add, leftInduction, rightInduction]
  | monomial exponent coefficient =>
      simp only [Polynomial.eval_monomial]
      calc
        PowerSeries.trunc order
            (coefficient *
              (PowerSeries.trunc order series : PowerSeries R) ^ exponent) =
          PowerSeries.trunc order
            ((PowerSeries.trunc order coefficient : PowerSeries R) *
              (PowerSeries.trunc order series : PowerSeries R) ^ exponent) := by
            rw [PowerSeries.trunc_trunc_mul]
        _ = PowerSeries.trunc order
            (coefficient *
              (PowerSeries.trunc order series : PowerSeries R) ^ exponent) := by
            rw [PowerSeries.trunc_trunc_mul]
        _ = PowerSeries.trunc order
            (coefficient *
              (PowerSeries.trunc order
                ((PowerSeries.trunc order series : PowerSeries R) ^ exponent) :
                  PowerSeries R)) := by
            rw [PowerSeries.trunc_mul_trunc]
        _ = PowerSeries.trunc order
            (coefficient *
              (PowerSeries.trunc order (series ^ exponent) : PowerSeries R)) := by
            rw [PowerSeries.trunc_trunc_pow]
        _ = PowerSeries.trunc order (coefficient * series ^ exponent) := by
            rw [PowerSeries.trunc_mul_trunc]

/-- A power-series root remains a root modulo `U^order` after literal
truncation. -/
theorem trunc_eval_coe_trunc_eq_zero_of_isRoot
    {R : Type*} [CommRing R]
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat)
    (root : polynomial.IsRoot series) :
    PowerSeries.trunc order
        (polynomial.eval (PowerSeries.trunc order series : PowerSeries R)) = 0 := by
  rw [trunc_eval_coe_trunc polynomial series order, root.eq_zero, map_zero]

/-- Vanishing in the open coefficient gap bounds the degree of the literal
finite truncation. -/
theorem natDegree_trunc_le_of_coeff_eq_zero
    {R : Type*} [Semiring R] (series : PowerSeries R)
    (degree bound : Nat)
    (coefficientZero : ∀ order, degree < order → order < bound →
      PowerSeries.coeff order series = 0) :
    (PowerSeries.trunc bound series).natDegree ≤ degree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro order orderLarge
  rw [PowerSeries.coeff_trunc]
  split_ifs with orderBelow
  · exact coefficientZero order orderLarge orderBelow
  · rfl

/-- The degree-`m` Hensel polynomial in the shifted variable `U`. -/
def henselTruncation
    {R : Type*} [Semiring R] (m : Nat) (series : PowerSeries R) :
    Polynomial R :=
  PowerSeries.trunc (m + 1) series

/-- If all coefficients in the open gap vanish, truncation at the large
cutoff is exactly the degree-`m` Hensel polynomial. -/
theorem trunc_eq_henselTruncation_of_gap_zero
    {R : Type*} [Semiring R] (series : PowerSeries R)
    (m bound : Nat) (mLtBound : m < bound)
    (gapZero : ∀ order, m < order → order < bound →
      PowerSeries.coeff order series = 0) :
    PowerSeries.trunc bound series = henselTruncation m series := by
  ext order
  rw [PowerSeries.coeff_trunc, henselTruncation,
    PowerSeries.coeff_trunc]
  by_cases orderLtBound : order < bound
  · by_cases orderLtSucc : order < m + 1
    · rw [if_pos orderLtBound, if_pos orderLtSucc]
    · rw [if_pos orderLtBound, if_neg orderLtSucc]
      exact gapZero order (by omega) orderLtBound
  · have orderNotLtSucc : ¬order < m + 1 := by omega
    rw [if_neg orderLtBound, if_neg orderNotLtSucc]

/-- If a finite polynomial model maps to the shifted power-series parent,
then a truncated root is an exact polynomial root as soon as its substituted
degree lies below the modulus cutoff. -/
theorem finiteTruncation_isRoot
    {L : Type*} [Field L]
    (powerSeriesParent : Polynomial (PowerSeries L))
    (polynomialParent : Polynomial (Polynomial L))
    (parentMap : polynomialParent.map
        (Polynomial.coeToPowerSeries.ringHom (R := L)) = powerSeriesParent)
    (root : PowerSeries L) (rootEquation : powerSeriesParent.IsRoot root)
    (xBound : Nat)
    (evaluationDegree :
      (polynomialParent.eval (PowerSeries.trunc xBound root)).natDegree <
        xBound) :
    polynomialParent.IsRoot (PowerSeries.trunc xBound root) := by
  let finiteRoot := PowerSeries.trunc xBound root
  have completedEvaluation : powerSeriesParent.eval
        (finiteRoot : PowerSeries L) =
      ((polynomialParent.eval finiteRoot : Polynomial L) : PowerSeries L) := by
    calc
      powerSeriesParent.eval (finiteRoot : PowerSeries L) =
          ((polynomialParent.map
            (Polynomial.coeToPowerSeries.ringHom (R := L))).eval
              (finiteRoot : PowerSeries L)) := by rw [parentMap]
      _ = _ := by
        rw [Polynomial.eval_map]
        symm
        simpa using Polynomial.hom_eval₂ polynomialParent
          (RingHom.id (Polynomial L))
          (Polynomial.coeToPowerSeries.ringHom (R := L)) finiteRoot
  have moduloZero := trunc_eval_coe_trunc_eq_zero_of_isRoot
    powerSeriesParent root xBound rootEquation
  rw [completedEvaluation,
    PowerSeries.trunc_coe_eq_self evaluationDegree] at moduloZero
  exact moduloZero

/-- Once all root coefficients between `m` and the cutoff vanish, the
literal truncation has degree at most `m`; with the paper's substituted
degree bound it is already an exact root. -/
theorem finiteTruncation_isRoot_of_gap_coefficients_zero
    {L : Type*} [Field L]
    (powerSeriesParent : Polynomial (PowerSeries L))
    (polynomialParent : Polynomial (Polynomial L))
    (parentMap : polynomialParent.map
        (Polynomial.coeToPowerSeries.ringHom (R := L)) = powerSeriesParent)
    (root : PowerSeries L) (rootEquation : powerSeriesParent.IsRoot root)
    (m xBound : Nat)
    (gapZero : ∀ order, m < order → order < xBound →
      PowerSeries.coeff order root = 0)
    (evaluationDegree :
      (polynomialParent.eval (PowerSeries.trunc xBound root)).natDegree <
        xBound) :
    (PowerSeries.trunc xBound root).natDegree ≤ m ∧
      polynomialParent.IsRoot (PowerSeries.trunc xBound root) := by
  exact ⟨natDegree_trunc_le_of_coeff_eq_zero root m xBound gapZero,
    finiteTruncation_isRoot powerSeriesParent polynomialParent parentMap root
      rootEquation xBound evaluationDegree⟩

/-- Complete truncation theorem for one fixed branch.  The regular
zero-count kills every coefficient in `m < t < xBound`; cancellation in the
function field kills the true Hensel coefficients, and the finite degree
bound makes the degree-`m` truncation an exact root. -/
theorem exists_exact_henselTruncation_of_many_branches
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (ell DH DR d b tau m xBound : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (parentDegreeLe : parent.natDegree ≤ d)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (etaNeZero : regularDerivativeElement parent factor x₀ d ≠ 0)
    (mLtXBound : m < xBound)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z) ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) parent = 0)
    (candidateDegree : ∀ z ∈ challenges, (candidate z).natDegree ≤ m)
    (manyBranches : ∀ t, m < t → t < xBound →
      factor.natDegree * divisionFreeCeiling tau (sourceMu DR ell d b) t <
        challenges.card)
    (substitutionDegreeBound :
      ∀ gamma : Polynomial (BranchFunctionField factor),
        gamma.natDegree ≤ m →
          ((functionFieldPolynomialParent parent factor x₀).eval gamma).natDegree <
            xBound) :
    ∃ root : PowerSeries (BranchFunctionField factor),
      (functionFieldShiftedParent parent factor x₀).IsRoot root ∧
        PowerSeries.constantCoeff root =
          AdjoinRoot.root (branchPolynomial factor) ∧
        (henselTruncation m root).natDegree ≤ m ∧
        (functionFieldPolynomialParent parent factor x₀).IsRoot
          (henselTruncation m root) := by
  obtain ⟨root, rootEquation, rootConstant⟩ :=
    exists_functionField_powerSeriesRoot parent factor factorIrreducible.ne_zero
      factorPositive x₀ d parentDegreeLe factorDvd etaNeZero
  have deltaImage : ∀ t,
      regularToFunctionField factor factorPositive
          (parentDivisionFreeCoefficients parent factor x₀ d t) =
        regularToFunctionField factor factorPositive
              (regularLeadingCoefficient factor) *
          regularToFunctionField factor factorPositive
              (regularDerivativeElement parent factor x₀ d) ^
            henselExponent t * PowerSeries.coeff t root := by
    intro t
    exact parentDivisionFreeCoefficients_image_of_root parent factor
      factorPositive x₀ d dPositive parentDegreeLe root rootEquation
      rootConstant t
  have gapZero : ∀ order, m < order → order < xBound →
      PowerSeries.coeff order root = 0 := by
    intro order aboveDegree belowCutoff
    have deltaZero := parentDivisionFreeCoefficients_eq_zero_of_many_branches
      parent factor factorIrreducible factorPositive x₀ ell DH DR d b tau m
      order factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
      dPositive ellDLeDR wLeB parentDegreeLe challenges candidate localRoot
      candidateRoot candidateDegree aboveDegree
        (manyBranches order aboveDegree belowCutoff)
    exact henselCoefficient_eq_zero_of_cleared_eq_zero factor
      factorIrreducible.ne_zero factorPositive
      (regularDerivativeElement parent factor x₀ d) etaNeZero
      (parentDivisionFreeCoefficients parent factor x₀ d)
      (fun t ↦ PowerSeries.coeff t root) deltaImage order deltaZero
  have largeTruncationDegree :
      (PowerSeries.trunc xBound root).natDegree ≤ m :=
    natDegree_trunc_le_of_coeff_eq_zero root m xBound gapZero
  have largeTruncationRoot :
      (functionFieldPolynomialParent parent factor x₀).IsRoot
        (PowerSeries.trunc xBound root) :=
    finiteTruncation_isRoot (functionFieldShiftedParent parent factor x₀)
      (functionFieldPolynomialParent parent factor x₀)
      (map_functionFieldPolynomialParent parent factor x₀) root rootEquation
      xBound (substitutionDegreeBound (PowerSeries.trunc xBound root)
        largeTruncationDegree)
  have truncationEq := trunc_eq_henselTruncation_of_gap_zero root m xBound
    mLtXBound gapZero
  have truncationDegree : (henselTruncation m root).natDegree ≤ m := by
    rw [← truncationEq]
    exact largeTruncationDegree
  refine ⟨root, rootEquation, rootConstant, truncationDegree, ?_⟩
  rw [← truncationEq]
  exact largeTruncationRoot

#print axioms
  branchSpecialization_parentDivisionFreeCoefficients_eq_zero_of_degree_lt
#print axioms parentDivisionFreeCoefficients_eq_zero_of_many_branches
#print axioms henselCoefficient_eq_zero_of_cleared_eq_zero
#print axioms finiteTruncation_isRoot_of_gap_coefficients_zero
#print axioms exists_exact_henselTruncation_of_many_branches

end

end WeightedHensel

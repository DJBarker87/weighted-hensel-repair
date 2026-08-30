/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.Truncation

/-!
# The common numerator and second resultant

This module defines equation (76) literally in `O[X]`, proves its
function-field image (77), its fixed-coordinate weight bound, and the second
resultant implication used to recover the truncated root value.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Embed a ground-field scalar as a regular quotient coefficient. -/
def regularBaseMap
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    K →+* RegularQuotient factor :=
  (AdjoinRoot.of (monicization factor)).comp Polynomial.C

/-- The degree-`m` Hensel polynomial centered at `x₀`, written from an
arbitrary coefficient family. -/
def centeredCoefficientTruncation
    {K L : Type*} [Semiring K] [Field L] (baseMap : K →+* L) (x₀ : K)
    (alpha : Nat → L) (m : Nat) : Polynomial L :=
  ∑ t ∈ Finset.range (m + 1),
    Polynomial.C (alpha t) *
      (Polynomial.X - Polynomial.C (baseMap x₀)) ^ t

/-- Equation (76): one common integral numerator for the degree-`m`
truncated root. -/
def commonNumerator
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K) (d m : Nat) :
    Polynomial (RegularQuotient factor) :=
  ∑ t ∈ Finset.range (m + 1),
    Polynomial.C
        (parentDivisionFreeCoefficients parent factor x₀ d t *
          regularDerivativeElement parent factor x₀ d ^
            (henselExponent m - henselExponent t)) *
      (Polynomial.X - Polynomial.C (regularBaseMap factor x₀)) ^ t

/-- Equation (77), first in a form that accepts any already-proved image
identity for the cleared coefficients. -/
theorem commonNumerator_image
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d m : Nat) (alpha : Nat → BranchFunctionField factor)
    (deltaImage : ∀ t,
      regularToFunctionField factor factorPositive
          (parentDivisionFreeCoefficients parent factor x₀ d t) =
        regularToFunctionField factor factorPositive
              (regularLeadingCoefficient factor) *
          regularToFunctionField factor factorPositive
              (regularDerivativeElement parent factor x₀ d) ^
            henselExponent t * alpha t) :
    (commonNumerator parent factor x₀ d m).map
        (regularToFunctionField factor factorPositive) =
      Polynomial.C
          (regularToFunctionField factor factorPositive
                (regularLeadingCoefficient factor) *
            regularToFunctionField factor factorPositive
                (regularDerivativeElement parent factor x₀ d) ^
              henselExponent m) *
        centeredCoefficientTruncation (branchBaseMap factor) x₀ alpha m := by
  classical
  unfold commonNumerator centeredCoefficientTruncation
  rw [Polynomial.map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t tMem
  have tLeM : t ≤ m := by
    have tLtSucc := Finset.mem_range.mp tMem
    omega
  have exponentLe : henselExponent t ≤ henselExponent m :=
    henselExponent_monotone tLeM
  have exponentJoin : henselExponent t +
      (henselExponent m - henselExponent t) = henselExponent m :=
    Nat.add_sub_of_le exponentLe
  have baseMapImage :
      regularToFunctionField factor factorPositive
          (regularBaseMap factor x₀) = branchBaseMap factor x₀ := by
    change regularToFunctionField factor factorPositive
        (AdjoinRoot.of (monicization factor) (Polynomial.C x₀)) =
      regularCoefficientMap factor (Polynomial.C x₀)
    exact regularToFunctionField_of factor factorPositive (Polynomial.C x₀)
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C]
  rw [map_mul, map_pow, deltaImage t]
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [baseMapImage]
  calc
    _ = Polynomial.C
          (regularToFunctionField factor factorPositive
                (regularLeadingCoefficient factor) *
            (regularToFunctionField factor factorPositive
                  (regularDerivativeElement parent factor x₀ d) ^
                henselExponent t *
              regularToFunctionField factor factorPositive
                  (regularDerivativeElement parent factor x₀ d) ^
                (henselExponent m - henselExponent t)) * alpha t) *
          (Polynomial.X -
            Polynomial.C (branchBaseMap factor x₀)) ^ t := by
      ring_nf
    _ = _ := by
      rw [← pow_add, exponentJoin]
      rw [Polynomial.C_mul]
      ring

/-- Equation (77) for the coefficients of an actual function-field Hensel
root. -/
theorem commonNumerator_image_of_root
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d m : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (root : PowerSeries (BranchFunctionField factor))
    (rootEquation : (functionFieldShiftedParent parent factor x₀).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (branchPolynomial factor)) :
    (commonNumerator parent factor x₀ d m).map
        (regularToFunctionField factor factorPositive) =
      Polynomial.C
          (regularToFunctionField factor factorPositive
                (regularLeadingCoefficient factor) *
            regularToFunctionField factor factorPositive
                (regularDerivativeElement parent factor x₀ d) ^
              henselExponent m) *
        centeredCoefficientTruncation (branchBaseMap factor) x₀
          (fun t ↦ PowerSeries.coeff t root) m := by
  apply commonNumerator_image parent factor factorPositive x₀ d m
  intro t
  exact parentDivisionFreeCoefficients_image_of_root parent factor
    factorPositive x₀ d dPositive parentDegreeLe root rootEquation
      rootConstant t

/-! ## The fixed-coordinate weight ledger -/

/-- Ground-field scalars have weight zero in the regular quotient. -/
theorem regularBaseMap_weightNat_eq_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell DH tau : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (scalar : K) :
    regularWeightNat factor factorNeZero tau
        (regularBaseMap factor scalar) = 0 := by
  have scalarBound := regularWeightNat_of_le_natDegree factor factorNeZero
    ell DH factorCoefficientBound (Polynomial.C scalar)
  rw [generatorWeightEq] at scalarBound
  apply Nat.eq_zero_of_le_zero
  simpa [regularBaseMap] using scalarBound

/-- Evaluating equation (76) at a ground-field coordinate leaves the
same finite sum inside the regular quotient. -/
theorem commonNumerator_eval_regularBaseMap
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K) (d m : Nat) (x : K) :
    (commonNumerator parent factor x₀ d m).eval (regularBaseMap factor x) =
      ∑ t ∈ Finset.range (m + 1),
        parentDivisionFreeCoefficients parent factor x₀ d t *
          regularDerivativeElement parent factor x₀ d ^
            (henselExponent m - henselExponent t) *
          regularBaseMap factor ((x - x₀) ^ t) := by
  classical
  simp only [commonNumerator, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro t _tMem
  rw [map_pow, map_sub]

/-- The paper's common ceiling `C_m = tau + e_m mu` bounds the common
numerator after evaluation at every ground-field coordinate. -/
theorem commonNumerator_eval_weightNat_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ x : K)
    (ell DH DR d b tau m : Nat)
    (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b) :
    regularWeightNat factor factorNeZero tau
        ((commonNumerator parent factor x₀ d m).eval
          (regularBaseMap factor x)) ≤
      divisionFreeCeiling tau (sourceMu DR ell d b) m := by
  classical
  rw [commonNumerator_eval_regularBaseMap]
  apply regularWeightNat_finset_sum_le factor factorNeZero tau
    (divisionFreeCeiling tau (sourceMu DR ell d b) m)
  intro t tMem
  have tLeM : t ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp tMem)
  have exponentLe : henselExponent t ≤ henselExponent m :=
    henselExponent_monotone tLeM
  let delta := parentDivisionFreeCoefficients parent factor x₀ d t
  let eta := regularDerivativeElement parent factor x₀ d
  let etaPower := eta ^ (henselExponent m - henselExponent t)
  let scalar := regularBaseMap factor ((x - x₀) ^ t)
  have deltaBound : regularWeightNat factor factorNeZero tau delta ≤
      divisionFreeCeiling tau (sourceMu DR ell d b) t := by
    exact parentDivisionFreeCoefficients_weightNat_le parent factor x₀ ell DH
      DR d b tau factorNeZero factorCoefficientBound generatorWeightEq
      globalBound tauEq ellLeDR dPositive ellDLeDR wLeB t
  have etaBound : regularWeightNat factor factorNeZero tau eta ≤
      sourceMu DR ell d b := by
    exact regularDerivativeElement_weight_le parent factor x₀ ell DH DR d b
      tau factorNeZero factorCoefficientBound generatorWeightEq globalBound
      tauEq wLeB dPositive
  have etaPowerRaw := regularWeightNat_pow_le factor factorNeZero ell DH
    factorCoefficientBound eta (henselExponent m - henselExponent t)
  rw [generatorWeightEq] at etaPowerRaw
  have etaPowerBound : regularWeightNat factor factorNeZero tau etaPower ≤
      (henselExponent m - henselExponent t) * sourceMu DR ell d b :=
    etaPowerRaw.trans
      (Nat.mul_le_mul_left (henselExponent m - henselExponent t) etaBound)
  have scalarWeight : regularWeightNat factor factorNeZero tau scalar = 0 := by
    exact regularBaseMap_weightNat_eq_zero factor factorNeZero ell DH tau
      factorCoefficientBound generatorWeightEq ((x - x₀) ^ t)
  have firstRaw := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound delta etaPower
  have secondRaw := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound (delta * etaPower) scalar
  rw [generatorWeightEq] at firstRaw secondRaw
  have firstBound : regularWeightNat factor factorNeZero tau
      (delta * etaPower) ≤
        divisionFreeCeiling tau (sourceMu DR ell d b) t +
          (henselExponent m - henselExponent t) * sourceMu DR ell d b :=
    firstRaw.trans (Nat.add_le_add deltaBound etaPowerBound)
  change regularWeightNat factor factorNeZero tau
      (delta * etaPower * scalar) ≤ _
  refine secondRaw.trans ?_
  rw [scalarWeight, Nat.add_zero]
  refine firstBound.trans ?_
  unfold divisionFreeCeiling
  rw [Nat.add_assoc, ← Nat.add_mul,
    Nat.add_sub_of_le exponentLe]

/-! ## The challenge discrepancy -/

/-- Equation (79): the regular discrepancy between the common numerator
and a degree-bounded challenge polynomial in `Z`. -/
def commonDiscrepancy
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K) (d m : Nat)
    (x : K) (challenge : Polynomial K) : RegularQuotient factor :=
  (commonNumerator parent factor x₀ d m).eval (regularBaseMap factor x) -
    regularLeadingCoefficient factor *
      regularDerivativeElement parent factor x₀ d ^ henselExponent m *
      AdjoinRoot.of (monicization factor) challenge

/-- The second-resultant input has the same ceiling as the common
numerator whenever the challenge has degree at most `ell`. -/
theorem commonDiscrepancy_weightNat_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ x : K)
    (ell DH DR d b tau m : Nat) (challenge : Polynomial K)
    (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (challengeDegree : challenge.natDegree ≤ ell) :
    regularWeightNat factor factorNeZero tau
        (commonDiscrepancy parent factor x₀ d m x challenge) ≤
      divisionFreeCeiling tau (sourceMu DR ell d b) m := by
  let eta := regularDerivativeElement parent factor x₀ d
  let leading := regularLeadingCoefficient factor
  let challengeElement := AdjoinRoot.of (monicization factor) challenge
  let correction := leading * eta ^ henselExponent m * challengeElement
  have numeratorBound := commonNumerator_eval_weightNat_le parent factor x₀ x
    ell DH DR d b tau m factorNeZero factorCoefficientBound generatorWeightEq
    globalBound tauEq ellLeDR dPositive ellDLeDR wLeB
  have leadingRaw := regularWeightNat_of_le_natDegree factor factorNeZero ell DH
    factorCoefficientBound factor.leadingCoeff
  have challengeRaw := regularWeightNat_of_le_natDegree factor factorNeZero ell DH
    factorCoefficientBound challenge
  have etaBound := regularDerivativeElement_weight_le parent factor x₀ ell DH DR
    d b tau factorNeZero factorCoefficientBound generatorWeightEq globalBound
    tauEq wLeB dPositive
  have etaPowerRaw := regularWeightNat_pow_le factor factorNeZero ell DH
    factorCoefficientBound eta (henselExponent m)
  have firstRaw := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound leading (eta ^ henselExponent m)
  have secondRaw := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound (leading * eta ^ henselExponent m) challengeElement
  rw [generatorWeightEq] at leadingRaw challengeRaw etaPowerRaw firstRaw secondRaw
  have etaPowerBound : regularWeightNat factor factorNeZero tau
      (eta ^ henselExponent m) ≤
        henselExponent m * sourceMu DR ell d b :=
    etaPowerRaw.trans (Nat.mul_le_mul_left (henselExponent m) etaBound)
  have correctionBound : regularWeightNat factor factorNeZero tau correction ≤
      divisionFreeCeiling tau (sourceMu DR ell d b) m := by
    refine secondRaw.trans ((Nat.add_le_add
      (firstRaw.trans (Nat.add_le_add leadingRaw etaPowerBound))
      (challengeRaw.trans challengeDegree)).trans ?_)
    unfold divisionFreeCeiling
    omega
  unfold commonDiscrepancy
  rw [sub_eq_add_neg]
  exact (regularWeightNat_add_le factor factorNeZero tau _ _).trans
    (max_le numeratorBound (by simpa [correction] using correctionBound))

/-! ## Specialization and the second resultant -/

/-- Taylor coefficients through degree `m` reconstruct a polynomial of
degree at most `m` at every coordinate. -/
theorem sum_shiftedCandidateSeries_coeff_eq_eval
    {K : Type*} [Field K] (x₀ x : K) (candidate : Polynomial K) (m : Nat)
    (candidateDegree : candidate.natDegree ≤ m) :
    (∑ t ∈ Finset.range (m + 1),
      PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) *
        (x - x₀) ^ t) = candidate.eval x := by
  classical
  have degreeTaylor : (Polynomial.taylor x₀ candidate).natDegree < m + 1 := by
    rw [Polynomial.natDegree_taylor]
    omega
  calc
    _ = ∑ t ∈ Finset.range (m + 1),
        (Polynomial.taylor x₀ candidate).coeff t * (x - x₀) ^ t := by
      apply Finset.sum_congr rfl
      intro t _tMem
      rw [shiftedCandidateSeries, shiftedEvaluationHom_eq_coe_taylor,
        Polynomial.coeff_coe]
    _ = (Polynomial.taylor x₀ candidate).eval (x - x₀) :=
      (Polynomial.eval_eq_sum_range' degreeTaylor (x - x₀)).symm
    _ = candidate.eval x := Polynomial.taylor_eval_sub x₀ candidate x

@[simp] theorem branchSpecialization_regularBaseMap
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0) (scalar : K) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (regularBaseMap factor scalar) = scalar := by
  change branchSpecialization factor factorPositive x₀ z candidate localRoot
      (AdjoinRoot.of (monicization factor) (Polynomial.C scalar)) = scalar
  simpa only [Polynomial.eval_C] using
    branchSpecialization_of factor factorPositive x₀ z candidate
    localRoot (Polynomial.C scalar)

/-- Specializing the common numerator at a valid degree-`m` branch gives
the branch value times the common clearing factor. -/
theorem branchSpecialization_commonNumerator_eval
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (d m : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (candidateRoot : challengeCandidatePolynomial z candidate parent = 0)
    (candidateDegree : candidate.natDegree ≤ m) (x : K) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        ((commonNumerator parent factor x₀ d m).eval
          (regularBaseMap factor x)) =
      factor.leadingCoeff.eval z *
        branchSpecialization factor factorPositive x₀ z candidate localRoot
            (regularDerivativeElement parent factor x₀ d) ^ henselExponent m *
        candidate.eval x := by
  classical
  rw [commonNumerator_eval_regularBaseMap, map_sum]
  calc
    _ = ∑ t ∈ Finset.range (m + 1),
        (factor.leadingCoeff.eval z *
          branchSpecialization factor factorPositive x₀ z candidate localRoot
              (regularDerivativeElement parent factor x₀ d) ^
            henselExponent m) *
          (PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) *
            (x - x₀) ^ t) := by
      apply Finset.sum_congr rfl
      intro t tMem
      have tLeM : t ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp tMem)
      have exponentLe : henselExponent t ≤ henselExponent m :=
        henselExponent_monotone tLeM
      have exponentJoin : henselExponent t +
          (henselExponent m - henselExponent t) = henselExponent m :=
        Nat.add_sub_of_le exponentLe
      simp only [map_mul, map_pow, branchSpecialization_regularBaseMap]
      rw [branchSpecialization_parentDivisionFreeCoefficients parent factor
        factorPositive x₀ z candidate localRoot d dPositive parentDegreeLe
        candidateRoot t]
      calc
        _ = factor.leadingCoeff.eval z *
              (branchSpecialization factor factorPositive x₀ z candidate
                    localRoot
                    (regularDerivativeElement parent factor x₀ d) ^
                  henselExponent t *
                branchSpecialization factor factorPositive x₀ z candidate
                    localRoot
                    (regularDerivativeElement parent factor x₀ d) ^
                  (henselExponent m - henselExponent t)) *
              (PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) *
                (x - x₀) ^ t) := by ring
        _ = _ := by rw [← pow_add, exponentJoin]
    _ = (factor.leadingCoeff.eval z *
          branchSpecialization factor factorPositive x₀ z candidate localRoot
              (regularDerivativeElement parent factor x₀ d) ^
            henselExponent m) *
        (∑ t ∈ Finset.range (m + 1),
          PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) *
            (x - x₀) ^ t) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_shiftedCandidateSeries_coeff_eq_eval x₀ x candidate m
        candidateDegree]

/-- An agreeing challenge makes the discrepancy vanish at the
corresponding regular branch specialization. -/
theorem branchSpecialization_commonDiscrepancy_eq_zero
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (d m : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (candidateRoot : challengeCandidatePolynomial z candidate parent = 0)
    (candidateDegree : candidate.natDegree ≤ m)
    (x : K) (challenge : Polynomial K)
    (agreement : challenge.eval z = candidate.eval x) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (commonDiscrepancy parent factor x₀ d m x challenge) = 0 := by
  unfold commonDiscrepancy
  rw [map_sub, branchSpecialization_commonNumerator_eval parent factor
    factorPositive x₀ z candidate localRoot d m dPositive parentDegreeLe
    candidateRoot candidateDegree x]
  simp only [map_mul, map_pow,
    branchSpecialization_regularLeadingCoefficient,
    branchSpecialization_of, agreement, sub_self]

/-- Once the regular discrepancy is identically zero, every valid
nondegenerate specialization agrees at the coordinate, including branches
which were not used as incidences in the resultant argument. -/
theorem candidate_eval_eq_challenge_eval_of_discrepancy_eq_zero
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (d m : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (candidateRoot : challengeCandidatePolynomial z candidate parent = 0)
    (candidateDegree : candidate.natDegree ≤ m)
    (leadingNeZero : factor.leadingCoeff.eval z ≠ 0)
    (etaImageNeZero :
      branchSpecialization factor factorPositive x₀ z candidate localRoot
          (regularDerivativeElement parent factor x₀ d) ≠ 0)
    (x : K) (challenge : Polynomial K)
    (discrepancyZero :
      commonDiscrepancy parent factor x₀ d m x challenge = 0) :
    candidate.eval x = challenge.eval z := by
  let specialization :=
    branchSpecialization factor factorPositive x₀ z candidate localRoot
  have specializedZero := congrArg specialization discrepancyZero
  rw [map_zero] at specializedZero
  unfold commonDiscrepancy at specializedZero
  rw [map_sub, branchSpecialization_commonNumerator_eval parent factor
    factorPositive x₀ z candidate localRoot d m dPositive parentDegreeLe
    candidateRoot candidateDegree x] at specializedZero
  dsimp only [specialization] at specializedZero
  simp only [map_mul, map_pow, branchSpecialization_regularLeadingCoefficient,
    branchSpecialization_of] at specializedZero
  have clearingNeZero : factor.leadingCoeff.eval z *
      specialization (regularDerivativeElement parent factor x₀ d) ^
        henselExponent m ≠ 0 :=
    mul_ne_zero leadingNeZero (pow_ne_zero _ etaImageNeZero)
  apply (mul_left_cancel₀ clearingNeZero)
  exact sub_eq_zero.mp (by
    simpa only [mul_sub] using specializedZero)

/-- More than `h C_m` agreeing valid branches force the regular challenge
discrepancy to vanish.  This is the paper's second resultant use. -/
theorem commonDiscrepancy_eq_zero_of_many_branches
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ x : K) (ell DH DR d b tau m : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (parentDegreeLe : parent.natDegree ≤ d)
    (challenge : Polynomial K) (challengeDegree : challenge.natDegree ≤ ell)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z) ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) parent = 0)
    (candidateDegree : ∀ z ∈ challenges, (candidate z).natDegree ≤ m)
    (agreement : ∀ z ∈ challenges, challenge.eval z = (candidate z).eval x)
    (manyBranches : factor.natDegree *
      divisionFreeCeiling tau (sourceMu DR ell d b) m < challenges.card) :
    commonDiscrepancy parent factor x₀ d m x challenge = 0 := by
  classical
  let discrepancy := commonDiscrepancy parent factor x₀ d m x challenge
  have discrepancyWeight := commonDiscrepancy_weightNat_le parent factor x₀ x
    ell DH DR d b tau m challenge factorIrreducible.ne_zero
    factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
    dPositive ellDLeDR wLeB challengeDegree
  have discrepancyWeightForResultant :
      regularWeightNat factor factorIrreducible.ne_zero
          (DH + ell - ell * factor.natDegree) discrepancy ≤
        divisionFreeCeiling tau (sourceMu DR ell d b) m := by
    simpa only [generatorWeightEq] using discrepancyWeight
  let rootValue : K → K := fun z ↦ branchRootValue factor x₀ z (candidate z)
  let rootPair : ∀ z ∈ challenges,
      (monicization factor).eval₂ (Polynomial.evalRingHom z) (rootValue z) = 0 :=
    fun z zMem ↦ branchRootPair factor factorPositive x₀ z (candidate z)
      (localRoot z zMem)
  apply weighted_resultant_zero_count factor factorIrreducible factorPositive
    ell DH (divisionFreeCeiling tau (sourceMu DR ell d b) m)
    factorCoefficientBound discrepancy discrepancyWeightForResultant challenges
    rootValue rootPair
  · intro z zMem
    change branchSpecialization factor factorPositive x₀ z (candidate z)
        (localRoot z zMem) discrepancy = 0
    exact branchSpecialization_commonDiscrepancy_eq_zero parent factor
      factorPositive x₀ z (candidate z) (localRoot z zMem) d m dPositive
      parentDegreeLe (candidateRoot z zMem) (candidateDegree z zMem) x
      challenge (agreement z zMem)
  · exact manyBranches

/-- Cancellation of the nonzero common clearing factor turns a zero
regular discrepancy into the desired equality in the branch function
field. -/
theorem centeredCoefficientTruncation_eval_eq_challenge_of_discrepancy_eq_zero
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d m : Nat) (alpha : Nat → BranchFunctionField factor)
    (deltaImage : ∀ t,
      regularToFunctionField factor factorPositive
          (parentDivisionFreeCoefficients parent factor x₀ d t) =
        regularToFunctionField factor factorPositive
              (regularLeadingCoefficient factor) *
          regularToFunctionField factor factorPositive
              (regularDerivativeElement parent factor x₀ d) ^
            henselExponent t * alpha t)
    (etaNeZero : regularDerivativeElement parent factor x₀ d ≠ 0)
    (x : K) (challenge : Polynomial K)
    (discrepancyZero :
      commonDiscrepancy parent factor x₀ d m x challenge = 0) :
    (centeredCoefficientTruncation (branchBaseMap factor) x₀ alpha m).eval
        (branchBaseMap factor x) = regularCoefficientMap factor challenge := by
  let iota := regularToFunctionField factor factorPositive
  let leadingImage := iota (regularLeadingCoefficient factor)
  let etaImage := iota (regularDerivativeElement parent factor x₀ d)
  let clearing := leadingImage * etaImage ^ henselExponent m
  have baseMapImage (scalar : K) :
      iota (regularBaseMap factor scalar) = branchBaseMap factor scalar := by
    change regularToFunctionField factor factorPositive
        (AdjoinRoot.of (monicization factor) (Polynomial.C scalar)) =
      regularCoefficientMap factor (Polynomial.C scalar)
    exact regularToFunctionField_of factor factorPositive (Polynomial.C scalar)
  have numeratorImage :
      iota ((commonNumerator parent factor x₀ d m).eval
          (regularBaseMap factor x)) =
        clearing *
          (centeredCoefficientTruncation (branchBaseMap factor) x₀ alpha m).eval
            (branchBaseMap factor x) := by
    rw [← Polynomial.eval_map_apply,
      commonNumerator_image parent factor factorPositive x₀ d m alpha
        deltaImage,
      baseMapImage]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  have challengeImage :
      iota (AdjoinRoot.of (monicization factor) challenge) =
        regularCoefficientMap factor challenge :=
    regularToFunctionField_of factor factorPositive challenge
  have correctionImage :
      iota (regularLeadingCoefficient factor *
          regularDerivativeElement parent factor x₀ d ^ henselExponent m *
          AdjoinRoot.of (monicization factor) challenge) =
        clearing * regularCoefficientMap factor challenge := by
    simp only [map_mul, map_pow, challengeImage]
    rfl
  have clearedEquality :
      clearing *
          (centeredCoefficientTruncation (branchBaseMap factor) x₀ alpha m).eval
            (branchBaseMap factor x) =
        clearing * regularCoefficientMap factor challenge := by
    have mappedZero := congrArg iota discrepancyZero
    rw [map_zero] at mappedZero
    unfold commonDiscrepancy at mappedZero
    rw [map_sub, numeratorImage, correctionImage] at mappedZero
    exact sub_eq_zero.mp mappedZero
  have leadingImageNeZero : leadingImage ≠ 0 := by
    unfold leadingImage iota regularLeadingCoefficient
    rw [regularToFunctionField_of]
    intro imageZero
    apply Polynomial.leadingCoeff_ne_zero.mpr factorNeZero
    apply regularCoefficientMap_injective factor factorPositive
    simpa using imageZero
  have etaImageNeZero : etaImage ≠ 0 := by
    exact regularToFunctionField_ne_zero factor factorNeZero factorPositive
      etaNeZero
  have clearingNeZero : clearing ≠ 0 := by
    exact mul_ne_zero leadingImageNeZero (pow_ne_zero _ etaImageNeZero)
  exact mul_left_cancel₀ clearingNeZero clearedEquality

/-- The cancellation conclusion instantiated with an actual Hensel root. -/
theorem centeredHenselTruncation_eval_eq_challenge_of_discrepancy_eq_zero
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d m : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (root : PowerSeries (BranchFunctionField factor))
    (rootEquation : (functionFieldShiftedParent parent factor x₀).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (branchPolynomial factor))
    (etaNeZero : regularDerivativeElement parent factor x₀ d ≠ 0)
    (x : K) (challenge : Polynomial K)
    (discrepancyZero :
      commonDiscrepancy parent factor x₀ d m x challenge = 0) :
    (centeredCoefficientTruncation (branchBaseMap factor) x₀
        (fun t ↦ PowerSeries.coeff t root) m).eval (branchBaseMap factor x) =
      regularCoefficientMap factor challenge := by
  apply centeredCoefficientTruncation_eval_eq_challenge_of_discrepancy_eq_zero
    parent factor factorNeZero factorPositive x₀ d m
      (fun t ↦ PowerSeries.coeff t root)
  · intro t
    exact parentDivisionFreeCoefficients_image_of_root parent factor
      factorPositive x₀ d dPositive parentDegreeLe root rootEquation
      rootConstant t
  · exact etaNeZero
  · exact discrepancyZero

/-- Paper-level second-resultant theorem: enough agreeing valid branches
identify the value of the truncated Hensel root at the fixed coordinate. -/
theorem secondResultant_identifies_henselTruncation
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ x : K) (ell DH DR d b tau m : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (parentDegreeLe : parent.natDegree ≤ d)
    (root : PowerSeries (BranchFunctionField factor))
    (rootEquation : (functionFieldShiftedParent parent factor x₀).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (branchPolynomial factor))
    (etaNeZero : regularDerivativeElement parent factor x₀ d ≠ 0)
    (challenge : Polynomial K) (challengeDegree : challenge.natDegree ≤ ell)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z) ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) parent = 0)
    (candidateDegree : ∀ z ∈ challenges, (candidate z).natDegree ≤ m)
    (agreement : ∀ z ∈ challenges, challenge.eval z = (candidate z).eval x)
    (manyBranches : factor.natDegree *
      divisionFreeCeiling tau (sourceMu DR ell d b) m < challenges.card) :
    (centeredCoefficientTruncation (branchBaseMap factor) x₀
        (fun t ↦ PowerSeries.coeff t root) m).eval (branchBaseMap factor x) =
      regularCoefficientMap factor challenge := by
  have discrepancyZero := commonDiscrepancy_eq_zero_of_many_branches parent
    factor factorIrreducible factorPositive x₀ x ell DH DR d b tau m
    factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
    dPositive ellDLeDR wLeB parentDegreeLe challenge challengeDegree
    challenges candidate localRoot candidateRoot candidateDegree agreement
    manyBranches
  exact centeredHenselTruncation_eval_eq_challenge_of_discrepancy_eq_zero
    parent factor factorIrreducible.ne_zero factorPositive x₀ d m dPositive
    parentDegreeLe root rootEquation rootConstant etaNeZero x challenge
    discrepancyZero

#print axioms commonNumerator_image
#print axioms commonNumerator_image_of_root
#print axioms regularBaseMap_weightNat_eq_zero
#print axioms commonNumerator_eval_regularBaseMap
#print axioms commonNumerator_eval_weightNat_le
#print axioms commonDiscrepancy_weightNat_le
#print axioms sum_shiftedCandidateSeries_coeff_eq_eval
#print axioms branchSpecialization_commonNumerator_eval
#print axioms branchSpecialization_commonDiscrepancy_eq_zero
#print axioms candidate_eval_eq_challenge_eval_of_discrepancy_eq_zero
#print axioms commonDiscrepancy_eq_zero_of_many_branches
#print axioms centeredCoefficientTruncation_eval_eq_challenge_of_discrepancy_eq_zero
#print axioms centeredHenselTruncation_eval_eq_challenge_of_discrepancy_eq_zero
#print axioms secondResultant_identifies_henselTruncation

end

end WeightedHensel

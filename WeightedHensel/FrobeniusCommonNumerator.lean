/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FrobeniusTruncation
import WeightedHensel.CommonNumerator

/-!
# Rooted common numerators

The source recurrence lives in the separable variable `Ytilde = Y^q`.
For the inverse-Frobenius branch, the coefficient at rooted order `t` is
the regular inverse-Frobenius image of the source coefficient at order
`t*q`.  The common clearing exponent remains `e_(k*q)`; this is exactly
the numerator used by the second resultant in the inseparable case.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- The rooted regular derivative element. -/
def frobeniusRootedEta
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (x₀ : K) (d : Nat) :
    RegularQuotient (bivariateFrobeniusRoot p f factor) :=
  regularFrobeniusRootEquiv p f factor factorNeZero
    (regularDerivativeElement parent factor x₀ d)

/-- The rooted numerator coefficient at order `t`, obtained from the source
coefficient at order `t*q`. -/
def frobeniusRootedCoefficient
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (x₀ : K) (d t : Nat) :
    RegularQuotient (bivariateFrobeniusRoot p f factor) :=
  regularFrobeniusRootEquiv p f factor factorNeZero
    (parentDivisionFreeCoefficients parent factor x₀ d
      (t * frobeniusPower p f))

/-- Compatible specialization of a rooted numerator coefficient. -/
theorem branchSpecialization_frobeniusRootedCoefficient
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (d t : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (sourceLocalRoot :
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          ((candidate ^ frobeniusPower p f).eval x₀) = 0)
    (sourceCandidateRoot :
      challengeCandidatePolynomial (z ^ frobeniusPower p f)
        (candidate ^ frobeniusPower p f) parent = 0) :
    branchSpecialization
        (bivariateFrobeniusRoot p f factor)
        (by simpa using factorPositive)
        x₀ z candidate
        (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
          sourceLocalRoot)
        (frobeniusRootedCoefficient p f parent factor factorNeZero x₀ d t) =
      (bivariateFrobeniusRoot p f factor).leadingCoeff.eval z *
        branchSpecialization
            (bivariateFrobeniusRoot p f factor)
            (by simpa using factorPositive)
            x₀ z candidate
            (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
              sourceLocalRoot)
            (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
          henselExponent (t * frobeniusPower p f) *
        PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) := by
  let rootedFactor := bivariateFrobeniusRoot p f factor
  let rootedLocalRoot :=
    bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
      sourceLocalRoot
  let rootedSpecialization :=
    branchSpecialization rootedFactor
      (by simpa [rootedFactor] using factorPositive)
      x₀ z candidate rootedLocalRoot
  let sourceSpecialization :=
    branchSpecialization factor factorPositive x₀
      (z ^ frobeniusPower p f)
      (candidate ^ frobeniusPower p f) sourceLocalRoot
  apply iterateFrobenius_inj K p f
  change (rootedSpecialization
        (frobeniusRootedCoefficient p f parent factor factorNeZero x₀ d t)) ^
      frobeniusPower p f =
    (rootedFactor.leadingCoeff.eval z *
        rootedSpecialization
            (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
          henselExponent (t * frobeniusPower p f) *
        PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate)) ^
      frobeniusPower p f
  rw [show rootedSpecialization
          (frobeniusRootedCoefficient p f parent factor factorNeZero x₀ d t) ^
            frobeniusPower p f =
        sourceSpecialization
          (parentDivisionFreeCoefficients parent factor x₀ d
            (t * frobeniusPower p f)) by
      exact branchSpecialization_regularFrobeniusRootEquiv_pow p f factor
        factorNeZero factorPositive x₀ z candidate sourceLocalRoot
        (parentDivisionFreeCoefficients parent factor x₀ d
          (t * frobeniusPower p f))]
  rw [branchSpecialization_parentDivisionFreeCoefficients parent factor
    factorPositive x₀ (z ^ frobeniusPower p f)
    (candidate ^ frobeniusPower p f) sourceLocalRoot d dPositive
    parentDegreeLe sourceCandidateRoot (t * frobeniusPower p f)]
  rw [mul_pow, mul_pow,
    eval_leadingCoeff_bivariateFrobeniusRoot_pow]
  rw [← pow_mul, Nat.mul_comm (henselExponent
    (t * frobeniusPower p f)) (frobeniusPower p f), pow_mul]
  rw [show rootedSpecialization
          (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
            frobeniusPower p f =
        sourceSpecialization
          (regularDerivativeElement parent factor x₀ d) by
      exact branchSpecialization_regularFrobeniusRootEquiv_pow p f factor
        factorNeZero factorPositive x₀ z candidate sourceLocalRoot
        (regularDerivativeElement parent factor x₀ d)]
  rw [coeff_shiftedCandidateSeries_frobeniusPower_mul]

/-- The rooted common numerator at degree `k`, with common derivative
exponent `e_(k*q)`. -/
def frobeniusRootedCommonNumerator
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (x₀ : K) (d k : Nat) :
    Polynomial (RegularQuotient (bivariateFrobeniusRoot p f factor)) :=
  ∑ t ∈ Finset.range (k + 1),
    Polynomial.C
        (frobeniusRootedCoefficient p f parent factor factorNeZero x₀ d t *
          frobeniusRootedEta p f parent factor factorNeZero x₀ d ^
            (henselExponent (k * frobeniusPower p f) -
              henselExponent (t * frobeniusPower p f))) *
      (Polynomial.X -
        Polynomial.C
          (regularBaseMap (bivariateFrobeniusRoot p f factor) x₀)) ^ t

/-- Evaluation of the rooted common numerator at a ground-field coordinate. -/
theorem frobeniusRootedCommonNumerator_eval_regularBaseMap
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (x₀ : K) (d k : Nat) (x : K) :
    (frobeniusRootedCommonNumerator p f parent factor factorNeZero x₀ d k).eval
        (regularBaseMap (bivariateFrobeniusRoot p f factor) x) =
      ∑ t ∈ Finset.range (k + 1),
        frobeniusRootedCoefficient p f parent factor factorNeZero x₀ d t *
          frobeniusRootedEta p f parent factor factorNeZero x₀ d ^
            (henselExponent (k * frobeniusPower p f) -
              henselExponent (t * frobeniusPower p f)) *
          regularBaseMap (bivariateFrobeniusRoot p f factor)
            ((x - x₀) ^ t) := by
  classical
  simp only [frobeniusRootedCommonNumerator, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro t _tMem
  rw [map_pow, map_sub]

/-- A compatible branch specialization of the rooted common numerator is
the original candidate value times the common rooted clearing factor. -/
theorem branchSpecialization_frobeniusRootedCommonNumerator_eval
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (d k : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (sourceLocalRoot :
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          ((candidate ^ frobeniusPower p f).eval x₀) = 0)
    (sourceCandidateRoot :
      challengeCandidatePolynomial (z ^ frobeniusPower p f)
        (candidate ^ frobeniusPower p f) parent = 0)
    (candidateDegree : candidate.natDegree ≤ k) (x : K) :
    branchSpecialization
        (bivariateFrobeniusRoot p f factor)
        (by simpa using factorPositive)
        x₀ z candidate
        (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
          sourceLocalRoot)
        ((frobeniusRootedCommonNumerator p f parent factor factorNeZero
          x₀ d k).eval
            (regularBaseMap (bivariateFrobeniusRoot p f factor) x)) =
      (bivariateFrobeniusRoot p f factor).leadingCoeff.eval z *
        branchSpecialization
            (bivariateFrobeniusRoot p f factor)
            (by simpa using factorPositive)
            x₀ z candidate
            (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
              sourceLocalRoot)
            (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
          henselExponent (k * frobeniusPower p f) *
        candidate.eval x := by
  classical
  let rootedFactor := bivariateFrobeniusRoot p f factor
  let rootedLocalRoot :=
    bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
      sourceLocalRoot
  let rootedSpecialization :=
    branchSpecialization rootedFactor
      (by simpa [rootedFactor] using factorPositive)
      x₀ z candidate rootedLocalRoot
  rw [frobeniusRootedCommonNumerator_eval_regularBaseMap, map_sum]
  calc
    _ = ∑ t ∈ Finset.range (k + 1),
        (rootedFactor.leadingCoeff.eval z *
          rootedSpecialization
              (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
            henselExponent (k * frobeniusPower p f)) *
          (PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) *
            (x - x₀) ^ t) := by
      apply Finset.sum_congr rfl
      intro t tMem
      have tLeK : t ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp tMem)
      have indexLe : t * frobeniusPower p f ≤
          k * frobeniusPower p f :=
        Nat.mul_le_mul_right (frobeniusPower p f) tLeK
      have exponentLe :
          henselExponent (t * frobeniusPower p f) ≤
            henselExponent (k * frobeniusPower p f) :=
        henselExponent_monotone indexLe
      have exponentJoin :
          henselExponent (t * frobeniusPower p f) +
              (henselExponent (k * frobeniusPower p f) -
                henselExponent (t * frobeniusPower p f)) =
            henselExponent (k * frobeniusPower p f) :=
        Nat.add_sub_of_le exponentLe
      simp only [map_mul, map_pow, branchSpecialization_regularBaseMap]
      rw [branchSpecialization_frobeniusRootedCoefficient p f parent factor
        factorNeZero factorPositive x₀ z candidate d t dPositive
        parentDegreeLe sourceLocalRoot sourceCandidateRoot]
      calc
        _ = rootedFactor.leadingCoeff.eval z *
              (rootedSpecialization
                    (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
                  henselExponent (t * frobeniusPower p f) *
                rootedSpecialization
                    (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
                  (henselExponent (k * frobeniusPower p f) -
                    henselExponent (t * frobeniusPower p f))) *
              (PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) *
                (x - x₀) ^ t) := by ring
        _ = _ := by rw [← pow_add, exponentJoin]
    _ = (rootedFactor.leadingCoeff.eval z *
          rootedSpecialization
              (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
            henselExponent (k * frobeniusPower p f)) *
        (∑ t ∈ Finset.range (k + 1),
          PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) *
            (x - x₀) ^ t) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_shiftedCandidateSeries_coeff_eq_eval x₀ x candidate k
        candidateDegree]

/-- The rooted discrepancy used by the second weighted resultant. -/
def frobeniusRootedDiscrepancy
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (x₀ : K) (d k : Nat)
    (x : K) (challenge : Polynomial K) :
    RegularQuotient (bivariateFrobeniusRoot p f factor) :=
  (frobeniusRootedCommonNumerator p f parent factor factorNeZero
      x₀ d k).eval
      (regularBaseMap (bivariateFrobeniusRoot p f factor) x) -
    regularLeadingCoefficient (bivariateFrobeniusRoot p f factor) *
      frobeniusRootedEta p f parent factor factorNeZero x₀ d ^
        henselExponent (k * frobeniusPower p f) *
      AdjoinRoot.of
        (monicization (bivariateFrobeniusRoot p f factor)) challenge

/-- Agreement at a compatible rooted challenge kills the rooted discrepancy. -/
theorem branchSpecialization_frobeniusRootedDiscrepancy_eq_zero
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (d k : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (sourceLocalRoot :
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          ((candidate ^ frobeniusPower p f).eval x₀) = 0)
    (sourceCandidateRoot :
      challengeCandidatePolynomial (z ^ frobeniusPower p f)
        (candidate ^ frobeniusPower p f) parent = 0)
    (candidateDegree : candidate.natDegree ≤ k)
    (x : K) (challenge : Polynomial K)
    (agreement : challenge.eval z = candidate.eval x) :
    branchSpecialization
        (bivariateFrobeniusRoot p f factor)
        (by simpa using factorPositive)
        x₀ z candidate
        (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
          sourceLocalRoot)
        (frobeniusRootedDiscrepancy p f parent factor factorNeZero
          x₀ d k x challenge) = 0 := by
  unfold frobeniusRootedDiscrepancy
  rw [map_sub,
    branchSpecialization_frobeniusRootedCommonNumerator_eval p f parent factor
      factorNeZero factorPositive x₀ z candidate d k dPositive parentDegreeLe
      sourceLocalRoot sourceCandidateRoot candidateDegree x]
  simp only [map_mul, map_pow,
    branchSpecialization_regularLeadingCoefficient,
    branchSpecialization_of, agreement, sub_self]

/-- Vanishing of the rooted discrepancy identifies the candidate value,
provided the two clearing factors do not vanish. -/
theorem candidate_eval_eq_challenge_eval_of_frobeniusRootedDiscrepancy_eq_zero
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (d k : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (sourceLocalRoot :
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          ((candidate ^ frobeniusPower p f).eval x₀) = 0)
    (sourceCandidateRoot :
      challengeCandidatePolynomial (z ^ frobeniusPower p f)
        (candidate ^ frobeniusPower p f) parent = 0)
    (candidateDegree : candidate.natDegree ≤ k)
    (leadingNeZero :
      (bivariateFrobeniusRoot p f factor).leadingCoeff.eval z ≠ 0)
    (etaImageNeZero :
      branchSpecialization
          (bivariateFrobeniusRoot p f factor)
          (by simpa using factorPositive)
          x₀ z candidate
          (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
            sourceLocalRoot)
          (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ≠ 0)
    (x : K) (challenge : Polynomial K)
    (discrepancyZero :
      frobeniusRootedDiscrepancy p f parent factor factorNeZero
        x₀ d k x challenge = 0) :
    candidate.eval x = challenge.eval z := by
  let rootedFactor := bivariateFrobeniusRoot p f factor
  let rootedLocalRoot :=
    bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
      sourceLocalRoot
  let specialization :=
    branchSpecialization rootedFactor
      (by simpa [rootedFactor] using factorPositive)
      x₀ z candidate rootedLocalRoot
  have specializedZero := congrArg specialization discrepancyZero
  rw [map_zero] at specializedZero
  unfold frobeniusRootedDiscrepancy at specializedZero
  rw [map_sub,
    branchSpecialization_frobeniusRootedCommonNumerator_eval p f parent factor
      factorNeZero factorPositive x₀ z candidate d k dPositive parentDegreeLe
      sourceLocalRoot sourceCandidateRoot candidateDegree x] at specializedZero
  dsimp only [specialization, rootedFactor, rootedLocalRoot] at specializedZero
  simp only [map_mul, map_pow, branchSpecialization_regularLeadingCoefficient,
    branchSpecialization_of] at specializedZero
  have clearingNeZero :
      (bivariateFrobeniusRoot p f factor).leadingCoeff.eval z *
        branchSpecialization
            (bivariateFrobeniusRoot p f factor)
            (by simpa using factorPositive)
            x₀ z candidate
            (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
              sourceLocalRoot)
            (frobeniusRootedEta p f parent factor factorNeZero x₀ d) ^
          henselExponent (k * frobeniusPower p f) ≠ 0 :=
    mul_ne_zero leadingNeZero (pow_ne_zero _ etaImageNeZero)
  apply (mul_left_cancel₀ clearingNeZero)
  exact sub_eq_zero.mp (by simpa only [mul_sub] using specializedZero)

/-- The rooted common numerator has the source ceiling at order `k*q`. -/
theorem frobeniusRootedCommonNumerator_eval_weightNat_le
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (x₀ x : K) (ell DH DR d b tau k : Nat)
    (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b) :
    regularWeightNat
        (bivariateFrobeniusRoot p f factor)
        (bivariateFrobeniusRoot_ne_zero p f factorNeZero) tau
        ((frobeniusRootedCommonNumerator p f parent factor factorNeZero
          x₀ d k).eval
            (regularBaseMap (bivariateFrobeniusRoot p f factor) x)) ≤
      divisionFreeCeiling tau (sourceMu DR ell d b)
        (k * frobeniusPower p f) := by
  classical
  let rootedFactor := bivariateFrobeniusRoot p f factor
  let rootedFactorNeZero :=
    bivariateFrobeniusRoot_ne_zero p f factorNeZero
  have rootedCoefficientBound :
      ∀ exponent ∈ rootedFactor.support,
        (rootedFactor.coeff exponent).natDegree + ell * exponent ≤ DH :=
    bivariateFrobeniusRoot_coefficientBound p f ell DH factor
      factorCoefficientBound
  have rootedGeneratorWeightEq :
      DH + ell - ell * rootedFactor.natDegree = tau := by
    simpa [rootedFactor] using generatorWeightEq
  rw [frobeniusRootedCommonNumerator_eval_regularBaseMap]
  apply regularWeightNat_finset_sum_le rootedFactor rootedFactorNeZero tau
    (divisionFreeCeiling tau (sourceMu DR ell d b)
      (k * frobeniusPower p f))
  intro t tMem
  have tLeK : t ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp tMem)
  have indexLe : t * frobeniusPower p f ≤ k * frobeniusPower p f :=
    Nat.mul_le_mul_right (frobeniusPower p f) tLeK
  have exponentLe :
      henselExponent (t * frobeniusPower p f) ≤
        henselExponent (k * frobeniusPower p f) :=
    henselExponent_monotone indexLe
  let delta :=
    frobeniusRootedCoefficient p f parent factor factorNeZero x₀ d t
  let eta := frobeniusRootedEta p f parent factor factorNeZero x₀ d
  let etaPower := eta ^
    (henselExponent (k * frobeniusPower p f) -
      henselExponent (t * frobeniusPower p f))
  let scalar := regularBaseMap rootedFactor ((x - x₀) ^ t)
  have sourceDeltaBound :
      regularWeightNat factor factorNeZero tau
          (parentDivisionFreeCoefficients parent factor x₀ d
            (t * frobeniusPower p f)) ≤
        divisionFreeCeiling tau (sourceMu DR ell d b)
          (t * frobeniusPower p f) := by
    exact parentDivisionFreeCoefficients_weightNat_le parent factor x₀ ell DH
      DR d b tau factorNeZero factorCoefficientBound generatorWeightEq
      globalBound tauEq ellLeDR dPositive ellDLeDR wLeB
      (t * frobeniusPower p f)
  have deltaBound :
      regularWeightNat rootedFactor rootedFactorNeZero tau delta ≤
        divisionFreeCeiling tau (sourceMu DR ell d b)
          (t * frobeniusPower p f) := by
    simpa [delta, frobeniusRootedCoefficient, rootedFactor,
      rootedFactorNeZero, regularWeightNat_regularFrobeniusRootEquiv] using
      sourceDeltaBound
  have sourceEtaBound :
      regularWeightNat factor factorNeZero tau
          (regularDerivativeElement parent factor x₀ d) ≤
        sourceMu DR ell d b := by
    exact regularDerivativeElement_weight_le parent factor x₀ ell DH DR d b
      tau factorNeZero factorCoefficientBound generatorWeightEq globalBound
      tauEq wLeB dPositive
  have etaBound :
      regularWeightNat rootedFactor rootedFactorNeZero tau eta ≤
        sourceMu DR ell d b := by
    simpa [eta, frobeniusRootedEta, rootedFactor, rootedFactorNeZero,
      regularWeightNat_regularFrobeniusRootEquiv] using sourceEtaBound
  have etaPowerRaw := regularWeightNat_pow_le rootedFactor rootedFactorNeZero
    ell DH rootedCoefficientBound eta
    (henselExponent (k * frobeniusPower p f) -
      henselExponent (t * frobeniusPower p f))
  rw [rootedGeneratorWeightEq] at etaPowerRaw
  have etaPowerBound :
      regularWeightNat rootedFactor rootedFactorNeZero tau etaPower ≤
        (henselExponent (k * frobeniusPower p f) -
          henselExponent (t * frobeniusPower p f)) *
            sourceMu DR ell d b :=
    etaPowerRaw.trans
      (Nat.mul_le_mul_left
        (henselExponent (k * frobeniusPower p f) -
          henselExponent (t * frobeniusPower p f)) etaBound)
  have scalarWeight :
      regularWeightNat rootedFactor rootedFactorNeZero tau scalar = 0 := by
    exact regularBaseMap_weightNat_eq_zero rootedFactor rootedFactorNeZero
      ell DH tau rootedCoefficientBound rootedGeneratorWeightEq
      ((x - x₀) ^ t)
  have firstRaw := regularWeightNat_mul_le rootedFactor rootedFactorNeZero
    ell DH rootedCoefficientBound delta etaPower
  have secondRaw := regularWeightNat_mul_le rootedFactor rootedFactorNeZero
    ell DH rootedCoefficientBound (delta * etaPower) scalar
  rw [rootedGeneratorWeightEq] at firstRaw secondRaw
  have firstBound :
      regularWeightNat rootedFactor rootedFactorNeZero tau
          (delta * etaPower) ≤
        divisionFreeCeiling tau (sourceMu DR ell d b)
            (t * frobeniusPower p f) +
          (henselExponent (k * frobeniusPower p f) -
            henselExponent (t * frobeniusPower p f)) *
              sourceMu DR ell d b :=
    firstRaw.trans (Nat.add_le_add deltaBound etaPowerBound)
  change regularWeightNat rootedFactor rootedFactorNeZero tau
      (delta * etaPower * scalar) ≤ _
  refine secondRaw.trans ?_
  rw [scalarWeight, Nat.add_zero]
  refine firstBound.trans ?_
  unfold divisionFreeCeiling
  rw [Nat.add_assoc, ← Nat.add_mul,
    Nat.add_sub_of_le exponentLe]

/-- The rooted discrepancy has the same `k*q` ceiling when its challenge
polynomial has degree at most `ell`. -/
theorem frobeniusRootedDiscrepancy_weightNat_le
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (x₀ x : K) (ell DH DR d b tau k : Nat)
    (challenge : Polynomial K) (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (challengeDegree : challenge.natDegree ≤ ell) :
    regularWeightNat
        (bivariateFrobeniusRoot p f factor)
        (bivariateFrobeniusRoot_ne_zero p f factorNeZero) tau
        (frobeniusRootedDiscrepancy p f parent factor factorNeZero
          x₀ d k x challenge) ≤
      divisionFreeCeiling tau (sourceMu DR ell d b)
        (k * frobeniusPower p f) := by
  let rootedFactor := bivariateFrobeniusRoot p f factor
  let rootedFactorNeZero :=
    bivariateFrobeniusRoot_ne_zero p f factorNeZero
  have rootedCoefficientBound :
      ∀ exponent ∈ rootedFactor.support,
        (rootedFactor.coeff exponent).natDegree + ell * exponent ≤ DH :=
    bivariateFrobeniusRoot_coefficientBound p f ell DH factor
      factorCoefficientBound
  have rootedGeneratorWeightEq :
      DH + ell - ell * rootedFactor.natDegree = tau := by
    simpa [rootedFactor] using generatorWeightEq
  let eta := frobeniusRootedEta p f parent factor factorNeZero x₀ d
  let leading := regularLeadingCoefficient rootedFactor
  let challengeElement :=
    AdjoinRoot.of (monicization rootedFactor) challenge
  let correction :=
    leading * eta ^ henselExponent (k * frobeniusPower p f) *
      challengeElement
  have numeratorBound :=
    frobeniusRootedCommonNumerator_eval_weightNat_le p f parent factor x₀ x
      ell DH DR d b tau k factorNeZero factorCoefficientBound
      generatorWeightEq globalBound tauEq ellLeDR dPositive ellDLeDR wLeB
  have leadingRaw := regularWeightNat_of_le_natDegree rootedFactor
    rootedFactorNeZero ell DH rootedCoefficientBound rootedFactor.leadingCoeff
  have challengeRaw := regularWeightNat_of_le_natDegree rootedFactor
    rootedFactorNeZero ell DH rootedCoefficientBound challenge
  have sourceEtaBound :
      regularWeightNat factor factorNeZero tau
          (regularDerivativeElement parent factor x₀ d) ≤
        sourceMu DR ell d b := by
    exact regularDerivativeElement_weight_le parent factor x₀ ell DH DR d b
      tau factorNeZero factorCoefficientBound generatorWeightEq globalBound
      tauEq wLeB dPositive
  have etaBound :
      regularWeightNat rootedFactor rootedFactorNeZero tau eta ≤
        sourceMu DR ell d b := by
    simpa [eta, frobeniusRootedEta, rootedFactor, rootedFactorNeZero,
      regularWeightNat_regularFrobeniusRootEquiv] using sourceEtaBound
  have etaPowerRaw := regularWeightNat_pow_le rootedFactor
    rootedFactorNeZero ell DH rootedCoefficientBound eta
      (henselExponent (k * frobeniusPower p f))
  have firstRaw := regularWeightNat_mul_le rootedFactor rootedFactorNeZero
    ell DH rootedCoefficientBound leading
      (eta ^ henselExponent (k * frobeniusPower p f))
  have secondRaw := regularWeightNat_mul_le rootedFactor rootedFactorNeZero
    ell DH rootedCoefficientBound
      (leading * eta ^ henselExponent (k * frobeniusPower p f))
      challengeElement
  rw [rootedGeneratorWeightEq] at leadingRaw challengeRaw etaPowerRaw firstRaw secondRaw
  have etaPowerBound :
      regularWeightNat rootedFactor rootedFactorNeZero tau
          (eta ^ henselExponent (k * frobeniusPower p f)) ≤
        henselExponent (k * frobeniusPower p f) *
          sourceMu DR ell d b :=
    etaPowerRaw.trans
      (Nat.mul_le_mul_left
        (henselExponent (k * frobeniusPower p f)) etaBound)
  have rootedWLeB : rootedFactor.leadingCoeff.natDegree ≤ b := by
    simpa [rootedFactor, leadingCoeff_bivariateFrobeniusRoot] using wLeB
  have correctionBound :
      regularWeightNat rootedFactor rootedFactorNeZero tau correction ≤
        divisionFreeCeiling tau (sourceMu DR ell d b)
          (k * frobeniusPower p f) := by
    refine secondRaw.trans ((Nat.add_le_add
      (firstRaw.trans (Nat.add_le_add (leadingRaw.trans rootedWLeB) etaPowerBound))
      (challengeRaw.trans challengeDegree)).trans ?_)
    unfold divisionFreeCeiling
    omega
  unfold frobeniusRootedDiscrepancy
  rw [sub_eq_add_neg]
  exact (regularWeightNat_add_le rootedFactor rootedFactorNeZero tau _ _).trans
    (max_le numeratorBound (by simpa [correction] using correctionBound))

/-- More than the rooted `h*C_(k*q)` budget of agreeing compatible
specializations forces the rooted discrepancy to vanish. -/
theorem frobeniusRootedDiscrepancy_eq_zero_of_many_branches
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ x : K) (ell DH DR d b tau k : Nat)
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
    (sourceLocalRoot : ∀ z ∈ challenges,
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          (((candidate z) ^ frobeniusPower p f).eval x₀) = 0)
    (sourceCandidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial (z ^ frobeniusPower p f)
        ((candidate z) ^ frobeniusPower p f) parent = 0)
    (candidateDegree : ∀ z ∈ challenges, (candidate z).natDegree ≤ k)
    (agreement : ∀ z ∈ challenges,
      challenge.eval z = (candidate z).eval x)
    (manyBranches : factor.natDegree *
      divisionFreeCeiling tau (sourceMu DR ell d b)
        (k * frobeniusPower p f) < challenges.card) :
    frobeniusRootedDiscrepancy p f parent factor factorIrreducible.ne_zero
      x₀ d k x challenge = 0 := by
  classical
  let rootedFactor := bivariateFrobeniusRoot p f factor
  let rootedFactorNeZero :=
    bivariateFrobeniusRoot_ne_zero p f factorIrreducible.ne_zero
  have rootedIrreducible :=
    bivariateFrobeniusRoot_irreducible p f factorIrreducible
  have rootedPositive : 0 < rootedFactor.natDegree := by
    simpa [rootedFactor] using factorPositive
  have rootedCoefficientBound :
      ∀ exponent ∈ rootedFactor.support,
        (rootedFactor.coeff exponent).natDegree + ell * exponent ≤ DH :=
    bivariateFrobeniusRoot_coefficientBound p f ell DH factor
      factorCoefficientBound
  let discrepancy :=
    frobeniusRootedDiscrepancy p f parent factor factorIrreducible.ne_zero
      x₀ d k x challenge
  have discrepancyWeight :=
    frobeniusRootedDiscrepancy_weightNat_le p f parent factor x₀ x ell DH DR
      d b tau k challenge factorIrreducible.ne_zero factorCoefficientBound
      generatorWeightEq globalBound tauEq ellLeDR dPositive ellDLeDR wLeB
      challengeDegree
  have discrepancyWeightForResultant :
      regularWeightNat rootedFactor rootedFactorNeZero
          (DH + ell - ell * rootedFactor.natDegree) discrepancy ≤
        divisionFreeCeiling tau (sourceMu DR ell d b)
          (k * frobeniusPower p f) := by
    have rootedGeneratorWeightEq :
        DH + ell - ell * rootedFactor.natDegree = tau := by
      simpa [rootedFactor] using generatorWeightEq
    simpa only [rootedGeneratorWeightEq] using discrepancyWeight
  let rootValue : K → K := fun z ↦
    branchRootValue rootedFactor x₀ z (candidate z)
  let rootPair : ∀ z ∈ challenges,
      (monicization rootedFactor).eval₂
        (Polynomial.evalRingHom z) (rootValue z) = 0 :=
    fun z zMem ↦ branchRootPair rootedFactor rootedPositive x₀ z
      (candidate z)
      (bivariateFrobeniusRoot_localRoot p f factor x₀ z (candidate z)
        (sourceLocalRoot z zMem))
  apply weighted_resultant_zero_count rootedFactor rootedIrreducible
    rootedPositive ell DH
    (divisionFreeCeiling tau (sourceMu DR ell d b)
      (k * frobeniusPower p f))
    rootedCoefficientBound discrepancy discrepancyWeightForResultant
    challenges rootValue rootPair
  · intro z zMem
    change branchSpecialization rootedFactor rootedPositive x₀ z
        (candidate z)
        (bivariateFrobeniusRoot_localRoot p f factor x₀ z (candidate z)
          (sourceLocalRoot z zMem)) discrepancy = 0
    exact branchSpecialization_frobeniusRootedDiscrepancy_eq_zero p f parent
      factor factorIrreducible.ne_zero factorPositive x₀ z (candidate z) d k
      dPositive parentDegreeLe (sourceLocalRoot z zMem)
      (sourceCandidateRoot z zMem) (candidateDegree z zMem) x challenge
      (agreement z zMem)
  · simpa [rootedFactor] using manyBranches

#print axioms branchSpecialization_frobeniusRootedCoefficient
#print axioms branchSpecialization_frobeniusRootedCommonNumerator_eval
#print axioms frobeniusRootedCommonNumerator_eval_weightNat_le
#print axioms frobeniusRootedDiscrepancy_weightNat_le
#print axioms frobeniusRootedDiscrepancy_eq_zero_of_many_branches

end

end WeightedHensel

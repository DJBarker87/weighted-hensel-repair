/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.ConcreteParameters
import WeightedHensel.FrobeniusCorollary
import WeightedHensel.SeparableCorollary

/-!
# Terminal verification results

The terminal dependency graph includes both global-to-local factor paths:
the separable Proposition 7.10 composition and the inseparable Frobenius
extension of Corollary 7.11.  Seven terminal declarations correspond directly
to paper conclusions.  The two supplementary concrete theorems below
instantiate the generic fixed-branch theorem with every numerical table
entry.  Their `challenges` argument is the surviving good-challenge set; the
ambient universes `Kˣ` and `K` are checked separately in
`ConcreteParameters`.  GRS words are normalized on entry and their nonzero
multipliers are restored in the conclusion.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-- The degree-28, domain-`2^20` fixed-branch instance at the exact published
curve-decodability allowance. -/
theorem concrete_degree28_curve_decodable
    {K : Type*} [Field K]
    (points multiplier : Fin 1048576 → K)
    (pointsInjective : Function.Injective points)
    (multiplierNeZero : ∀ coordinate, multiplier coordinate ≠ 0)
    (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ : K) (DH DR d b tau : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + 28 * exponent ≤ DH)
    (generatorWeightEq :
      DH + 28 - 28 * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent 28 DR)
    (tauEq : tau = b + 28) (ellLeDR : 28 ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : 28 * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (parentDegreeLe : parent.natDegree ≤ d)
    (bEq : b = DH - 28 * factor.natDegree)
    (DHLe : DH ≤ 117078) (DRLe : DR ≤ 117078)
    (factorDegreeLe : factor.natDegree ≤ d) (dLe : d ≤ 112)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (support : K → Finset (Fin 1048576))
    (received : Fin 1048576 → Polynomial K)
    (manyChallenges :
      degree28CurveDecodabilityCount < challenges.card)
    (supportLarge : ∀ z ∈ challenges,
      38229 < (support z).card)
    (grsAgreement : ∀ z ∈ challenges, ∀ coordinate ∈ support z,
      multiplier coordinate * (candidate z).eval (points coordinate) =
        (received coordinate).eval z)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ 1024)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ 28)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z)
        ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) parent = 0)
    (leadingSpecializationNeZero : ∀ z ∈ challenges,
      factor.leadingCoeff.eval z ≠ 0)
    (derivativeSpecializationNeZero : ∀ z (zMem : z ∈ challenges),
      branchSpecialization factor factorPositive x₀ z (candidate z)
          (localRoot z zMem)
          (regularDerivativeElement parent factor x₀ d) ≠ 0) :
    ∃ coefficientCurve : Nat → Polynomial K,
      (∀ j, j ≤ 28 → (coefficientCurve j).natDegree ≤ 1024) ∧
      (∀ z ∈ challenges,
        candidate z = candidateCurve coefficientCurve 28 z) ∧
      ∀ z ∈ challenges, ∀ coordinate,
        multiplier coordinate *
            (candidate z).eval (points coordinate) =
          ∑ j ∈ Finset.range 29,
            z ^ j *
              (multiplier coordinate *
                (coefficientCurve j).eval (points coordinate)) := by
  classical
  let normalizedReceived : Fin 1048576 → Polynomial K :=
    normalizeGRSChallenge multiplier received
  have factorPositive' : 1 ≤ factor.natDegree := by omega
  have tauLe : tau ≤ 117078 :=
    sourceTau_le_commonDegree DH 117078 28 factor.natDegree tau DHLe
      factorPositive' generatorWeightEq.symm
  have muLe : sourceMu DR 28 d b ≤ d * 117078 := by
    apply sourceMu_le_commonDegree DH DR 117078 28 factor.natDegree d
      (sourceMu DR 28 d b) DHLe DRLe dPositive
    simp [sourceMu, bEq]
  have branchBudgetLt :
      factor.natDegree *
          divisionFreeCeiling tau (sourceMu DR 28 d b) 1024 <
        112 * ((2 * 1024 + 1) * 112 * 117078) :=
    degree28_fixedBranchBudget_lt factor.natDegree d tau
      (sourceMu DR 28 d b) factorPositive' factorDegreeLe dPositive dLe
      tauLe muLe
  have incidence :
      1024 * challenges.card +
          Fintype.card (Fin 1048576) *
            (factor.natDegree *
              divisionFreeCeiling tau (sourceMu DR 28 d b) 1024) <
        challenges.card * (38229 + 1) := by
    simpa using degree28_concrete_incidence challenges.card
      (factor.natDegree *
        divisionFreeCeiling tau (sourceMu DR 28 d b) 1024)
      manyChallenges branchBudgetLt
  have normalizedAgreement : ∀ z ∈ challenges,
      ∀ coordinate ∈ support z,
        (candidate z).eval (points coordinate) =
          (normalizedReceived coordinate).eval z := by
    intro z zMem coordinate coordinateMem
    exact normalize_grs_agreement points multiplier received (candidate z)
      coordinate z (multiplierNeZero coordinate)
      (grsAgreement z zMem coordinate coordinateMem)
  have normalizedDegree : ∀ coordinate,
      (normalizedReceived coordinate).natDegree ≤ 28 := by
    intro coordinate
    exact (normalizeGRSChallenge_natDegree_le multiplier received coordinate).trans
      (receivedDegree coordinate)
  obtain ⟨coefficientCurve, curveDegree, candidatesOnCurve⟩ :=
    fixed_branch_curve_decodability points pointsInjective parent factor
      factorIrreducible factorPositive x₀ 28 DH DR d b tau 1024 28 38229
      factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
      dPositive ellDLeDR wLeB parentDegreeLe (by norm_num) challenges
      candidate support normalizedReceived supportLarge normalizedAgreement
      candidateDegree normalizedDegree localRoot candidateRoot
      leadingSpecializationNeZero derivativeSpecializationNeZero incidence
  refine ⟨coefficientCurve, curveDegree, candidatesOnCurve, ?_⟩
  intro z zMem coordinate
  rw [candidatesOnCurve z zMem]
  simpa using restore_candidateCurve_grs points multiplier coefficientCurve
    28 z coordinate

/-- The degree-3, domain-`2^18` fixed-branch instance at the exact published
curve-decodability allowance. -/
theorem concrete_degree3_curve_decodable
    {K : Type*} [Field K]
    (points multiplier : Fin 262144 → K)
    (pointsInjective : Function.Injective points)
    (multiplierNeZero : ∀ coordinate, multiplier coordinate ≠ 0)
    (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ : K) (DH DR d b tau : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + 3 * exponent ≤ DH)
    (generatorWeightEq :
      DH + 3 - 3 * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent 3 DR)
    (tauEq : tau = b + 3) (ellLeDR : 3 ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : 3 * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (parentDegreeLe : parent.natDegree ≤ d)
    (bEq : b = DH - 3 * factor.natDegree)
    (DHLe : DH ≤ 12594) (DRLe : DR ≤ 12594)
    (factorDegreeLe : factor.natDegree ≤ d) (dLe : d ≤ 113)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (support : K → Finset (Fin 262144))
    (received : Fin 262144 → Polynomial K)
    (manyChallenges :
      degree3CurveDecodabilityCount < challenges.card)
    (supportLarge : ∀ z ∈ challenges,
      9557 < (support z).card)
    (grsAgreement : ∀ z ∈ challenges, ∀ coordinate ∈ support z,
      multiplier coordinate * (candidate z).eval (points coordinate) =
        (received coordinate).eval z)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ 255)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ 3)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z)
        ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) parent = 0)
    (leadingSpecializationNeZero : ∀ z ∈ challenges,
      factor.leadingCoeff.eval z ≠ 0)
    (derivativeSpecializationNeZero : ∀ z (zMem : z ∈ challenges),
      branchSpecialization factor factorPositive x₀ z (candidate z)
          (localRoot z zMem)
          (regularDerivativeElement parent factor x₀ d) ≠ 0) :
    ∃ coefficientCurve : Nat → Polynomial K,
      (∀ j, j ≤ 3 → (coefficientCurve j).natDegree ≤ 255) ∧
      (∀ z ∈ challenges,
        candidate z = candidateCurve coefficientCurve 3 z) ∧
      ∀ z ∈ challenges, ∀ coordinate,
        multiplier coordinate *
            (candidate z).eval (points coordinate) =
          ∑ j ∈ Finset.range 4,
            z ^ j *
              (multiplier coordinate *
                (coefficientCurve j).eval (points coordinate)) := by
  classical
  let normalizedReceived : Fin 262144 → Polynomial K :=
    normalizeGRSChallenge multiplier received
  have factorPositive' : 1 ≤ factor.natDegree := by omega
  have tauLe : tau ≤ 12594 :=
    sourceTau_le_commonDegree DH 12594 3 factor.natDegree tau DHLe
      factorPositive' generatorWeightEq.symm
  have muLe : sourceMu DR 3 d b ≤ d * 12594 := by
    apply sourceMu_le_commonDegree DH DR 12594 3 factor.natDegree d
      (sourceMu DR 3 d b) DHLe DRLe dPositive
    simp [sourceMu, bEq]
  have branchBudgetLt :
      factor.natDegree *
          divisionFreeCeiling tau (sourceMu DR 3 d b) 255 <
        113 * ((2 * 255 + 1) * 113 * 12594) :=
    degree3_fixedBranchBudget_lt factor.natDegree d tau
      (sourceMu DR 3 d b) factorPositive' factorDegreeLe dPositive dLe
      tauLe muLe
  have incidence :
      255 * challenges.card +
          Fintype.card (Fin 262144) *
            (factor.natDegree *
              divisionFreeCeiling tau (sourceMu DR 3 d b) 255) <
        challenges.card * (9557 + 1) := by
    simpa using degree3_concrete_incidence challenges.card
      (factor.natDegree *
        divisionFreeCeiling tau (sourceMu DR 3 d b) 255)
      manyChallenges branchBudgetLt
  have normalizedAgreement : ∀ z ∈ challenges,
      ∀ coordinate ∈ support z,
        (candidate z).eval (points coordinate) =
          (normalizedReceived coordinate).eval z := by
    intro z zMem coordinate coordinateMem
    exact normalize_grs_agreement points multiplier received (candidate z)
      coordinate z (multiplierNeZero coordinate)
      (grsAgreement z zMem coordinate coordinateMem)
  have normalizedDegree : ∀ coordinate,
      (normalizedReceived coordinate).natDegree ≤ 3 := by
    intro coordinate
    exact (normalizeGRSChallenge_natDegree_le multiplier received coordinate).trans
      (receivedDegree coordinate)
  obtain ⟨coefficientCurve, curveDegree, candidatesOnCurve⟩ :=
    fixed_branch_curve_decodability points pointsInjective parent factor
      factorIrreducible factorPositive x₀ 3 DH DR d b tau 255 3 9557
      factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
      dPositive ellDLeDR wLeB parentDegreeLe (by norm_num) challenges
      candidate support normalizedReceived supportLarge normalizedAgreement
      candidateDegree normalizedDegree localRoot candidateRoot
      leadingSpecializationNeZero derivativeSpecializationNeZero incidence
  refine ⟨coefficientCurve, curveDegree, candidatesOnCurve, ?_⟩
  intro z zMem coordinate
  rw [candidatesOnCurve z zMem]
  simpa using restore_candidateCurve_grs points multiplier coefficientCurve
    3 z coordinate

#print axioms corrected_source_hensel_estimate
#print axioms division_free_hensel_estimate
#print axioms weighted_resultant_zero_count
#print axioms fixed_branch_curve_decodability
#print axioms full_factor_degree_transfer
#print axioms separable_full_factor_curve_decodability
#print axioms inseparable_frobenius_curve_decodability
#print axioms concrete_degree28_curve_decodable
#print axioms concrete_degree3_curve_decodable

end

end WeightedHensel

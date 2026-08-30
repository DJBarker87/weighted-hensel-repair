/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.Interpolation

/-!
# Fixed-branch curve completion

This module combines the exact incidence double count, the second weighted
resultant, regular specialization, and coefficientwise interpolation.  All
specialization conditions are explicit in the terminal theorem.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Fixed-branch completion theorem.  More support incidences than the
literal second-resultant budget produce `M+1` coefficient polynomials of
degree at most `m`, and every surviving challenge candidate is their
degree-`M` specialization.

The hypotheses `leadingSpecializationNeZero` and
`derivativeSpecializationNeZero` are the precise pole-free/simple-root
conditions used in the cancellation step. -/
theorem fixed_branch_curve_decodability
    {K Domain : Type*} [Field K] [Fintype Domain]
    (points : Domain → K) (pointsInjective : Function.Injective points)
    (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ : K) (ell DH DR d b tau m M agreementThreshold : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (parentDegreeLe : parent.natDegree ≤ d)
    (MLeEll : M ≤ ell)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (support : K → Finset Domain)
    (received : Domain → Polynomial K)
    (supportLarge : ∀ z ∈ challenges,
      agreementThreshold < (support z).card)
    (agreement : ∀ z ∈ challenges, ∀ coordinate ∈ support z,
      (candidate z).eval (points coordinate) = (received coordinate).eval z)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ m)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ M)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z) ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) parent = 0)
    (leadingSpecializationNeZero : ∀ z ∈ challenges,
      factor.leadingCoeff.eval z ≠ 0)
    (derivativeSpecializationNeZero : ∀ (z) (zMem : z ∈ challenges),
      branchSpecialization factor factorPositive x₀ z (candidate z)
          (localRoot z zMem)
          (regularDerivativeElement parent factor x₀ d) ≠ 0)
    (incidenceLarge :
      m * challenges.card + Fintype.card Domain *
          (factor.natDegree *
            divisionFreeCeiling tau (sourceMu DR ell d b) m) <
        challenges.card * (agreementThreshold + 1)) :
    ∃ coefficientCurve : Nat → Polynomial K,
      (∀ j, j ≤ M → (coefficientCurve j).natDegree ≤ m) ∧
      ∀ z ∈ challenges,
        candidate z = candidateCurve coefficientCurve M z := by
  classical
  let branchBudget := factor.natDegree *
    divisionFreeCeiling tau (sourceMu DR ell d b) m
  have manyHeavy : m <
      (heavyCoordinates challenges support branchBudget).card := by
    apply maximumDegree_lt_card_heavyCoordinates challenges support
      agreementThreshold m branchBudget supportLarge
    simpa only [branchBudget] using incidenceLarge
  obtain ⟨nodes, nodesSubset, nodesCard⟩ :=
    Finset.exists_subset_card_eq
      (s := heavyCoordinates challenges support branchBudget)
      (n := m + 1) (by omega)
  have pointsInjectiveOn : Set.InjOn points nodes := pointsInjective.injOn
  have nodeDiscrepancyZero : ∀ node ∈ nodes,
      commonDiscrepancy parent factor x₀ d m (points node)
        (received node) = 0 := by
    intro node nodeMem
    let fiber := supportFiber challenges support node
    have nodeHeavy := nodesSubset nodeMem
    have fiberLarge : branchBudget < fiber.card :=
      (Finset.mem_filter.mp nodeHeavy).2
    apply commonDiscrepancy_eq_zero_of_many_branches parent factor
      factorIrreducible factorPositive x₀ (points node) ell DH DR d b tau m
      factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
      dPositive ellDLeDR wLeB parentDegreeLe (received node)
      ((receivedDegree node).trans MLeEll) fiber candidate
    · intro z zMem
      exact localRoot z (Finset.mem_filter.mp zMem).1
    · intro z zMem
      exact candidateRoot z (Finset.mem_filter.mp zMem).1
    · intro z zMem
      exact candidateDegree z (Finset.mem_filter.mp zMem).1
    · intro z zMem
      exact (agreement z (Finset.mem_filter.mp zMem).1 node
        (Finset.mem_filter.mp zMem).2).symm
    · simpa only [fiber, branchBudget] using fiberLarge
  let coefficientCurve :=
    lagrangeCoefficientCurve nodes points received
  refine ⟨coefficientCurve, ?_, ?_⟩
  · intro j jLeM
    exact lagrangeCoefficientCurve_natDegree_le nodes points
      pointsInjectiveOn received m j nodesCard
  · intro z zMem
    apply candidate_eq_candidateCurve nodes points pointsInjectiveOn received
      M m nodesCard receivedDegree z (candidate z) (candidateDegree z zMem)
    intro node nodeMem
    apply candidate_eval_eq_challenge_eval_of_discrepancy_eq_zero parent
      factor factorPositive x₀ z (candidate z) (localRoot z zMem) d m
      dPositive parentDegreeLe (candidateRoot z zMem)
      (candidateDegree z zMem) (leadingSpecializationNeZero z zMem)
      (derivativeSpecializationNeZero z zMem) (points node) (received node)
      (nodeDiscrepancyZero node nodeMem)

#print axioms fixed_branch_curve_decodability

end

end WeightedHensel

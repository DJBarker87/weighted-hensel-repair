/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.CurveDecodability
import WeightedHensel.FactorDegreeTransfer

/-!
# Global separable factor transfer to curve completion

This file composes Proposition 7.10 with the fixed-branch line theorem.
It is deliberately separate from the inseparable Frobenius composition so
reviewers can inspect the two global-to-local paths independently.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Proposition 7.10 composed with fixed-branch line completion.

The global factorization selects a genuine simple branch and removes all
content, leading-coefficient, and derivative-resultant exceptions.  Under
the literal incidence inequality consumed by the second resultant, the
surviving candidates lie on a degree-one curve of degree-`m` messages.
-/
theorem separable_full_factor_curve_decodability
    {K Domain I J : Type*} [Field K] [Fintype Domain]
    [DecidableEq I] [DecidableEq J]
    (points : Domain → K) (pointsInjective : Function.Injective points)
    (indices : Finset I) (branchIndices : I → Finset J)
    (Q : TrivariatePolynomial K) (globalContent : BivariatePolynomial K)
    (parent : I → TrivariatePolynomial K)
    (multiplicity : I → Nat)
    (x₀ : K) (content : I → Polynomial K)
    (branch : I → J → BivariatePolynomial K)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (DX DY DZ B m agreementThreshold : Nat)
    (DXPositive : 1 ≤ DX) (DYPositive : 1 ≤ DY)
    (DZPositive : 1 ≤ DZ) (BPositive : 1 ≤ B)
    (globalContentNeZero : globalContent ≠ 0)
    (parentNeZero : ∀ index, index ∈ indices → parent index ≠ 0)
    (parentPositive : ∀ index, index ∈ indices →
      1 ≤ (parent index).natDegree)
    (multiplicityPositive : ∀ index, index ∈ indices →
      1 ≤ multiplicity index)
    (globalFactorization : Q = Polynomial.C globalContent *
      ∏ index ∈ indices, parent index ^ multiplicity index)
    (contentNeZero : ∀ index, index ∈ indices → content index ≠ 0)
    (branchNeZero : ∀ index, index ∈ indices →
      ∀ branchIndex, branchIndex ∈ branchIndices index →
        branch index branchIndex ≠ 0)
    (branchPositive : ∀ index, index ∈ indices →
      ∀ branchIndex, branchIndex ∈ branchIndices index →
        0 < (branch index branchIndex).natDegree)
    (branchIrreducible : ∀ index, index ∈ indices →
      ∀ branchIndex, branchIndex ∈ branchIndices index →
        Irreducible (branch index branchIndex))
    (specializationFactorization : ∀ index, index ∈ indices →
      specializeX x₀ (parent index) = Polynomial.C (content index) *
        ∏ branchIndex ∈ branchIndices index, branch index branchIndex)
    (specializedSeparable : ∀ index, index ∈ indices →
      (branchPolynomial (specializeX x₀ (parent index))).Separable)
    (QYDegree : Q.natDegree ≤ DY)
    (QWeightedDegree : fullYZWeightedDegree 1 Q ≤ DZ)
    (candidateRoot : ∀ z, z ∈ challenges →
      challengeCandidatePolynomial z (candidate z) Q = 0)
    (candidateDegree : ∀ z, z ∈ challenges →
      (candidate z).natDegree ≤ m)
    (challengeCountLarge :
      2 * DX * DY ^ 2 * DZ + B * DY < challenges.card)
    (support : K → Finset Domain)
    (received : Domain → Polynomial K)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ 1)
    (supportLarge : ∀ z ∈ challenges,
      agreementThreshold < (support z).card)
    (agreement : ∀ z ∈ challenges, ∀ coordinate ∈ support z,
      (candidate z).eval (points coordinate) = (received coordinate).eval z) :
    ∃ index,
      index ∈ activeFactorIndices indices branchIndices ∧
      ∃ branchIndex, branchIndex ∈ branchIndices index ∧
      ∃ surviving : Finset K,
        (∀ order yExponent,
          shiftedParentCoefficient x₀ order yExponent (parent index) ≠ 0 →
          (shiftedParentCoefficient x₀ order yExponent
              (parent index)).natDegree + yExponent ≤
            fullYZWeightedDegree 1 (parent index)) ∧
        (2 * DX - 1) *
              ((parent index).natDegree *
                (branch index branchIndex).natDegree *
                  fullYZWeightedDegree 1 (parent index)) +
            B < surviving.card ∧
        (∀ z, z ∈ surviving →
          z ∈ challenges ∧
          challengeCandidatePolynomial z (candidate z) (parent index) = 0 ∧
          (content index).eval z ≠ 0 ∧
          ∃ localRoot :
              (branch index branchIndex).eval₂
                (Polynomial.evalRingHom z) ((candidate z).eval x₀) = 0,
            (branch index branchIndex).leadingCoeff.eval z ≠ 0 ∧
            specializedDerivativeValue (parent index) x₀ z
              (shiftedCandidateSeries x₀ (candidate z))
              (parent index).natDegree ≠ 0) ∧
        ((m * surviving.card + Fintype.card Domain *
              ((branch index branchIndex).natDegree *
                divisionFreeCeiling
                  (fullYZWeightedDegree 1 (parent index) -
                      (branch index branchIndex).natDegree + 1)
                  (sourceMu (fullYZWeightedDegree 1 (parent index)) 1
                    (parent index).natDegree
                    (fullYZWeightedDegree 1 (parent index) -
                      (branch index branchIndex).natDegree)) m) <
            surviving.card * (agreementThreshold + 1)) →
          IsCandidateCurve candidate surviving m 1) := by
  classical
  have globalMultiplierPositive : 1 ≤ 2 * DX * DY ^ 2 := by
    have twoDXPositive : 0 < 2 * DX :=
      Nat.mul_pos (by omega) DXPositive
    have dySquarePositive : 0 < DY ^ 2 := pow_pos DYPositive 2
    exact Nat.mul_pos twoDXPositive dySquarePositive
  have transferCount :
      2 * DX * DY ^ 2 * DZ + ((B - 1) + 1) * DY <
        challenges.card := by
    rwa [Nat.sub_add_cancel BPositive]
  obtain ⟨index, indexActive, branchIndex, branchIndexMem, surviving,
      shiftedBound, survivingLargeRaw, survivingData⟩ :=
    full_factor_degree_transfer indices branchIndices Q globalContent parent
      multiplicity x₀ content branch challenges candidate DX DY DZ (B - 1)
      globalContentNeZero parentNeZero parentPositive multiplicityPositive
      globalFactorization contentNeZero branchNeZero branchPositive
      branchIrreducible specializationFactorization specializedSeparable
      QYDegree QWeightedDegree globalMultiplierPositive candidateRoot
      transferCount
  have indexMem : index ∈ indices :=
    (Finset.mem_filter.mp indexActive).1
  let selectedParent := parent index
  let selectedFactor := branch index branchIndex
  let G := fullYZWeightedDegree 1 selectedParent
  let d := selectedParent.natDegree
  let h := selectedFactor.natDegree
  let b := G - h
  let tau := b + 1
  have factorIrreducible : Irreducible selectedFactor :=
    branchIrreducible index indexMem branchIndex branchIndexMem
  have factorPositive : 0 < selectedFactor.natDegree :=
    branchPositive index indexMem branchIndex branchIndexMem
  have factorWeightLe : localBivariateWeight 1 selectedFactor ≤ G := by
    have termLe : localBivariateWeight 1 selectedFactor ≤
        ∑ candidateBranch ∈ branchIndices index,
          localBivariateWeight 1 (branch index candidateBranch) :=
      Finset.single_le_sum
        (f := fun candidateBranch ↦
          localBivariateWeight 1 (branch index candidateBranch))
        (fun _ _ ↦ Nat.zero_le _) branchIndexMem
    have sumBound := specialization_content_branch_weight_summation
      (parent index) x₀ 1 (branchIndices index) (content index)
      (branch index) (contentNeZero index indexMem)
      (branchNeZero index indexMem)
      (specializationFactorization index indexMem)
    dsimp only [selectedParent, selectedFactor, G] at *
    omega
  have factorCoefficientBound : ∀ exponent ∈ selectedFactor.support,
      (selectedFactor.coeff exponent).natDegree + 1 * exponent ≤ G := by
    intro exponent exponentMem
    simpa only [Nat.mul_comm] using
      (coeff_weight_le_localBivariateWeight 1 selectedFactor exponent
        exponentMem).trans factorWeightLe
  have dPositive : 1 ≤ d := by
    simpa only [d, selectedParent] using parentPositive index indexMem
  have hPositive : 1 ≤ h := by
    dsimp only [h]
    omega
  have parentCoefficientBound : ParentCoefficientBound selectedParent 1 G :=
    parentCoefficientBound_fullYZWeightedDegree 1 selectedParent
  have parentLeadingMem : d ∈ selectedParent.support :=
    Polynomial.natDegree_mem_support_of_nonzero (parentNeZero index indexMem)
  have dLeG : d ≤ G := by
    have bound := parentCoefficientBound d parentLeadingMem
    omega
  have GPositive : 1 ≤ G := dPositive.trans dLeG
  have factorNeZero : selectedFactor ≠ 0 := factorIrreducible.ne_zero
  have factorLeadingMem : h ∈ selectedFactor.support :=
    Polynomial.natDegree_mem_support_of_nonzero factorNeZero
  have leadingBound : selectedFactor.leadingCoeff.natDegree + h ≤ G := by
    simpa [h] using factorCoefficientBound h factorLeadingMem
  have wLeB : selectedFactor.leadingCoeff.natDegree ≤ b := by
    dsimp only [b]
    omega
  have generatorWeightEq : G + 1 - 1 * h = tau := by
    dsimp only [tau, b]
    omega
  have survivingLarge :
      (2 * DX - 1) *
            (selectedParent.natDegree * selectedFactor.natDegree * G) +
          B < surviving.card := by
    dsimp only [selectedParent, selectedFactor, G]
    omega
  have localRoot : ∀ z ∈ surviving,
      selectedFactor.eval₂ (Polynomial.evalRingHom z)
        ((candidate z).eval x₀) = 0 := by
    intro z zMem
    exact (survivingData z zMem).2.2.2.choose
  have localCandidateRoot : ∀ z ∈ surviving,
      challengeCandidatePolynomial z (candidate z) selectedParent = 0 := by
    intro z zMem
    exact (survivingData z zMem).2.1
  have localCandidateDegree : ∀ z ∈ surviving,
      (candidate z).natDegree ≤ m := by
    intro z zMem
    exact candidateDegree z (survivingData z zMem).1
  have leadingNeZero : ∀ z ∈ surviving,
      selectedFactor.leadingCoeff.eval z ≠ 0 := by
    intro z zMem
    exact (survivingData z zMem).2.2.2.choose_spec.1
  have derivativeNeZero : ∀ z (zMem : z ∈ surviving),
      branchSpecialization selectedFactor factorPositive x₀ z (candidate z)
          (localRoot z zMem)
          (regularDerivativeElement selectedParent selectedFactor x₀ d) ≠ 0 := by
    intro z zMem
    rw [branchSpecialization_regularDerivativeElement]
    exact mul_ne_zero (pow_ne_zero _ (leadingNeZero z zMem))
      (survivingData z zMem).2.2.2.choose_spec.2
  have localSupportLarge : ∀ z ∈ surviving,
      agreementThreshold < (support z).card := by
    intro z zMem
    exact supportLarge z (survivingData z zMem).1
  have localAgreement : ∀ z ∈ surviving,
      ∀ coordinate ∈ support z,
        (candidate z).eval (points coordinate) = (received coordinate).eval z := by
    intro z zMem coordinate coordinateMem
    exact agreement z (survivingData z zMem).1 coordinate coordinateMem
  refine ⟨index, indexActive, branchIndex, branchIndexMem, surviving,
    shiftedBound, survivingLarge, survivingData, ?_⟩
  intro incidenceLarge
  have completion := fixed_branch_curve_decodability points pointsInjective
    selectedParent selectedFactor factorIrreducible factorPositive x₀ 1 G G
    d b tau m 1 agreementThreshold factorCoefficientBound generatorWeightEq
    parentCoefficientBound rfl GPositive dPositive (by simpa using dLeG) wLeB (by rfl) le_rfl
    surviving candidate support received localSupportLarge localAgreement
    localCandidateDegree receivedDegree localRoot localCandidateRoot leadingNeZero
    derivativeNeZero (by
      simpa only [selectedParent, selectedFactor, G, d, h, b, tau] using
        incidenceLarge)
  simpa only [IsCandidateCurve] using completion

#print axioms separable_full_factor_curve_decodability

end

end WeightedHensel

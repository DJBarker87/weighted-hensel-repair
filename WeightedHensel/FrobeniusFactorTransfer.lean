/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FactorDegreeTransfer
import WeightedHensel.FrobeniusFixedBranch
import Mathlib.Algebra.Polynomial.Expand

/-!
# Full-factor transfer through inseparable Frobenius powers

This module formalizes Corollary 7.11.  The global factor is obtained from a
separable parent in Ytilde by substituting Ytilde = Y^q.  The variable X has
weight zero, Z has weight one, and Ytilde has weight q.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-- Substitute Ytilde = Y^q in a trivariate parent. -/
def expandResponse
    {K : Type*} [Field K] (q : Nat)
    (parent : TrivariatePolynomial K) : TrivariatePolynomial K :=
  Polynomial.expand (BivariatePolynomial K) q parent

theorem expandResponse_ne_zero
    {K : Type*} [Field K] (q : Nat) (qPositive : 0 < q)
    (parent : TrivariatePolynomial K) (parentNeZero : Ne parent 0) :
    Ne (expandResponse q parent) 0 := by
  exact (Polynomial.expand_ne_zero qPositive).mpr parentNeZero

@[simp] theorem expandResponse_natDegree
    {K : Type*} [Field K] (q : Nat)
    (parent : TrivariatePolynomial K) :
    (expandResponse q parent).natDegree = parent.natDegree * q := by
  exact Polynomial.natDegree_expand q parent

/-- Substitution Ytilde = Y^q changes weight q on Ytilde into weight one
on Y, without changing the full weighted degree. -/
theorem fullYZWeightedDegree_expandResponse
    {K : Type*} [Field K] (q : Nat) (qPositive : 0 < q)
    (parent : TrivariatePolynomial K) :
    fullYZWeightedDegree 1 (expandResponse q parent) =
      fullYZWeightedDegree q parent := by
  unfold fullYZWeightedDegree
  simp only [localBivariateWeight_eq_iteratedBivariateWeight]
  apply le_antisymm
  · apply iteratedBivariateWeight_le_of_coeff
    intro exponent exponentMem
    have coefficientNeZero :
        Ne ((expandResponse q parent).coeff exponent) 0 :=
      Polynomial.mem_support_iff.mp exponentMem
    have qDvd : q ∣ exponent := by
      by_contra notDvd
      apply coefficientNeZero
      rw [expandResponse, Polynomial.coeff_expand qPositive, if_neg notDvd]
    have sourceCoefficientNeZero : Ne (parent.coeff (exponent / q)) 0 := by
      simpa [expandResponse, Polynomial.coeff_expand qPositive, qDvd] using
        coefficientNeZero
    have sourceMem : exponent / q ∈ parent.support :=
      Polynomial.mem_support_iff.mpr sourceCoefficientNeZero
    have sourceBound :=
      coeff_weight_le_iteratedBivariateWeight q parent (exponent / q)
        sourceMem
    rw [expandResponse, Polynomial.coeff_expand qPositive, if_pos qDvd,
      Nat.mul_one]
    rw [Nat.div_mul_cancel qDvd] at sourceBound
    exact sourceBound
  · apply iteratedBivariateWeight_le_of_coeff
    intro exponent exponentMem
    have coefficientNeZero : Ne (parent.coeff exponent) 0 :=
      Polynomial.mem_support_iff.mp exponentMem
    have expandedCoefficientNeZero :
        Ne ((expandResponse q parent).coeff (exponent * q)) 0 := by
      rw [expandResponse, Polynomial.coeff_expand_mul qPositive]
      exact coefficientNeZero
    have expandedMem : exponent * q ∈ (expandResponse q parent).support :=
      Polynomial.mem_support_iff.mpr expandedCoefficientNeZero
    have expandedBound :=
      coeff_weight_le_iteratedBivariateWeight 1 (expandResponse q parent)
        (exponent * q) expandedMem
    rw [expandResponse, Polynomial.coeff_expand_mul qPositive] at expandedBound
    simpa [expandResponse] using expandedBound

/-- Specializing X commutes with substitution in the outer response
variable. -/
theorem specializeX_expandResponse
    {K : Type*} [Field K] (q : Nat) (x0 : K)
    (parent : TrivariatePolynomial K) :
    specializeX x0 (expandResponse q parent) =
      Polynomial.expand (Polynomial K) q (specializeX x0 parent) := by
  unfold specializeX expandResponse
  exact Polynomial.map_expand

/-- Candidate substitution into the expanded factor is candidate-power
substitution into its separable parent. -/
theorem challengeCandidatePolynomial_expandResponse
    {K : Type*} [Field K] (q : Nat) (z : K)
    (candidate : Polynomial K) (parent : TrivariatePolynomial K) :
    challengeCandidatePolynomial z candidate (expandResponse q parent) =
      challengeCandidatePolynomial z (candidate ^ q) parent := by
  unfold challengeCandidatePolynomial specializeChallenge expandResponse
  rw [Polynomial.map_expand, Polynomial.expand_eval]

/-- The shifted coefficient condition used by the source recurrence follows
from the full q-weighted parent degree. -/
theorem shiftedCoefficient_frobeniusFullDegree_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x0 : K) (q order yExponent : Nat)
    (coefficientNeZero :
      Ne (shiftedParentCoefficient x0 order yExponent parent) 0) :
    (shiftedParentCoefficient x0 order yExponent parent).natDegree +
        q * yExponent <= fullYZWeightedDegree q parent := by
  exact shiftedCoefficient_fullDegree_le parent x0 q order yExponent
    coefficientNeZero

/-- Weighted-degree half of (129), derived from the literal factorization
through Y powers. -/
theorem fullFactor_frobenius_weight_summation
    {K I : Type*} [Field K] [DecidableEq I]
    (indices : Finset I) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (parent : I -> TrivariatePolynomial K) (q multiplicity : I -> Nat)
    (qPositive : forall index, index ∈ indices -> 0 < q index)
    (contentNeZero : Ne content 0)
    (parentNeZero : forall index, index ∈ indices -> Ne (parent index) 0)
    (factorization : Q = Polynomial.C content *
      ∏ index ∈ indices,
        expandResponse (q index) (parent index) ^ multiplicity index)
    (DZ : Nat) (QDegree : fullYZWeightedDegree 1 Q <= DZ) :
    content.natDegree +
        ∑ index ∈ indices,
          multiplicity index * fullYZWeightedDegree (q index) (parent index) <=
      DZ := by
  have expandedNeZero : forall index, index ∈ indices ->
      Ne (expandResponse (q index) (parent index)) 0 := by
    intro index indexMem
    exact expandResponse_ne_zero (q index) (qPositive index indexMem)
      (parent index) (parentNeZero index indexMem)
  have bound := fullFactor_weight_summation indices Q content
    (fun index => expandResponse (q index) (parent index)) multiplicity
    contentNeZero expandedNeZero factorization DZ QDegree
  calc
    content.natDegree +
        ∑ index ∈ indices,
          multiplicity index * fullYZWeightedDegree (q index) (parent index) =
      content.natDegree +
        ∑ index ∈ indices,
          multiplicity index *
            fullYZWeightedDegree 1
              (expandResponse (q index) (parent index)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro index indexMem
        rw [fullYZWeightedDegree_expandResponse
          (q index) (qPositive index indexMem)]
    _ <= DZ := bound

/-- Ordinary Y-degree half of (129): each separable Ytilde-degree is
multiplied by its Frobenius power in the global polynomial. -/
theorem fullFactor_frobenius_yDegree_summation
    {K I : Type*} [Field K] [DecidableEq I]
    (indices : Finset I) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (parent : I -> TrivariatePolynomial K) (q multiplicity : I -> Nat)
    (qPositive : forall index, index ∈ indices -> 0 < q index)
    (contentNeZero : Ne content 0)
    (parentNeZero : forall index, index ∈ indices -> Ne (parent index) 0)
    (factorization : Q = Polynomial.C content *
      ∏ index ∈ indices,
        expandResponse (q index) (parent index) ^ multiplicity index)
    (DY : Nat) (QDegree : Q.natDegree <= DY) :
    ∑ index ∈ indices,
        multiplicity index * (q index * (parent index).natDegree) <= DY := by
  have expandedNeZero : forall index, index ∈ indices ->
      Ne (expandResponse (q index) (parent index)) 0 := by
    intro index indexMem
    exact expandResponse_ne_zero (q index) (qPositive index indexMem)
      (parent index) (parentNeZero index indexMem)
  have bound := fullFactor_yDegree_summation indices Q content
    (fun index => expandResponse (q index) (parent index)) multiplicity
    contentNeZero expandedNeZero factorization DY QDegree
  calc
    ∑ index ∈ indices,
        multiplicity index * (q index * (parent index).natDegree) =
      ∑ index ∈ indices,
        multiplicity index *
          (expandResponse (q index) (parent index)).natDegree := by
        apply Finset.sum_congr rfl
        intro index indexMem
        rw [expandResponse_natDegree]
        congr 1
        exact Nat.mul_comm _ _
    _ <= DY := bound

/-- Forgetting the positive Frobenius factors gives the unpowered parent
Y-degree budget used in the pairwise pigeonhole ledger (135). -/
theorem fullFactor_parent_yDegree_summation_le
    {I : Type*} [DecidableEq I] (indices : Finset I)
    (multiplicity q degree : I -> Nat) (DY : Nat)
    (qPositive : forall index, index ∈ indices -> 0 < q index)
    (poweredBudget :
      ∑ index ∈ indices,
        multiplicity index * (q index * degree index) <= DY) :
    ∑ index ∈ indices, multiplicity index * degree index <= DY := by
  refine (Finset.sum_le_sum ?_).trans poweredBudget
  intro index indexMem
  have oneLeQ : 1 <= q index := by
    have qPos := qPositive index indexMem
    omega
  calc
    multiplicity index * degree index =
        multiplicity index * (1 * degree index) := by ring
    _ <= multiplicity index * (q index * degree index) := by gcongr

/-- Active-factor degree budgets for the inseparable factorization.  The
ordinary parent degree drops the positive q factor; the weighted budget keeps
the exact q-weighted full degree. -/
theorem activeFactor_frobenius_degree_budgets
    {K I J : Type*} [Field K] [DecidableEq I] [DecidableEq J]
    (indices : Finset I) (branchIndices : I -> Finset J)
    (Q : TrivariatePolynomial K) (globalContent : BivariatePolynomial K)
    (parent : I -> TrivariatePolynomial K)
    (q multiplicity : I -> Nat)
    (x0 : K) (content : I -> Polynomial K)
    (branch : I -> J -> BivariatePolynomial K)
    (qPositive : forall index, index ∈ indices -> 0 < q index)
    (globalContentNeZero : Ne globalContent 0)
    (parentNeZero : forall index, index ∈ indices -> Ne (parent index) 0)
    (multiplicityPositive :
      forall index, index ∈ indices -> 1 <= multiplicity index)
    (globalFactorization : Q = Polynomial.C globalContent *
      ∏ index ∈ indices,
        expandResponse (q index) (parent index) ^ multiplicity index)
    (contentNeZero : forall index, index ∈ indices -> Ne (content index) 0)
    (branchNeZero : forall index, index ∈ indices ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        Ne (branch index branchIndex) 0)
    (specializationFactorization : forall index, index ∈ indices ->
      specializeX x0 (parent index) = Polynomial.C (content index) *
        ∏ branchIndex ∈ branchIndices index, branch index branchIndex)
    (DY DZ : Nat) (QYDegree : Q.natDegree <= DY)
    (QWeightedDegree : fullYZWeightedDegree 1 Q <= DZ) :
    (∑ index ∈ activeFactorIndices indices branchIndices,
        multiplicity index * (parent index).natDegree) <= DY ∧
      (globalContent.natDegree +
          ∑ index ∈ inactiveFactorIndices indices branchIndices,
            (content index).natDegree) +
        ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index) <= DZ := by
  classical
  have poweredYBudget :
      ∑ index ∈ indices,
          multiplicity index * (q index * (parent index).natDegree) <= DY :=
    fullFactor_frobenius_yDegree_summation indices Q globalContent parent q
      multiplicity qPositive globalContentNeZero parentNeZero
      globalFactorization DY QYDegree
  have allYBudget :
      ∑ index ∈ indices,
          multiplicity index * (parent index).natDegree <= DY :=
    fullFactor_parent_yDegree_summation_le indices multiplicity q
      (fun index => (parent index).natDegree) DY qPositive poweredYBudget
  have allWeightedBudget : globalContent.natDegree +
      ∑ index ∈ indices,
        multiplicity index * fullYZWeightedDegree (q index) (parent index) <=
        DZ :=
    fullFactor_frobenius_weight_summation indices Q globalContent parent q
      multiplicity qPositive globalContentNeZero parentNeZero
      globalFactorization DZ QWeightedDegree
  have activeYBudget :
      ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index * (parent index).natDegree <= DY :=
    (Finset.sum_le_sum_of_subset
      (Finset.filter_subset
        (fun index => Ne (branchIndices index) ∅) indices)).trans allYBudget
  have inactiveContentLe :
      ∑ index ∈ inactiveFactorIndices indices branchIndices,
          (content index).natDegree <=
        ∑ index ∈ inactiveFactorIndices indices branchIndices,
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index) := by
    apply Finset.sum_le_sum
    intro index indexMem
    have indexInIndices : index ∈ indices := by
      rw [inactiveFactorIndices] at indexMem
      exact (Finset.mem_filter.mp indexMem).1
    have contentDegreeLe : (content index).natDegree <=
        fullYZWeightedDegree (q index) (parent index) := by
      have localBudget := specialization_content_branch_weight_summation
        (parent index) x0 (q index) (branchIndices index) (content index)
        (branch index) (contentNeZero index indexInIndices)
        (branchNeZero index indexInIndices)
        (specializationFactorization index indexInIndices)
      omega
    calc
      (content index).natDegree <=
          fullYZWeightedDegree (q index) (parent index) := contentDegreeLe
      _ = 1 * fullYZWeightedDegree (q index) (parent index) := by omega
      _ <= multiplicity index *
          fullYZWeightedDegree (q index) (parent index) := by
        exact Nat.mul_le_mul_right _
          (multiplicityPositive index indexInIndices)
  have degreePartition :
      (∑ index ∈ inactiveFactorIndices indices branchIndices,
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index)) +
        ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index) =
        ∑ index ∈ indices,
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index) := by
    simpa [inactiveFactorIndices, activeFactorIndices] using
      Finset.sum_filter_add_sum_filter_not indices
        (fun index => branchIndices index = ∅)
        (fun index =>
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index))
  refine ⟨activeYBudget, ?_⟩
  calc
    (globalContent.natDegree +
          ∑ index ∈ inactiveFactorIndices indices branchIndices,
            (content index).natDegree) +
        ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index) <=
      (globalContent.natDegree +
          ∑ index ∈ inactiveFactorIndices indices branchIndices,
            multiplicity index *
              fullYZWeightedDegree (q index) (parent index)) +
        ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index) :=
      Nat.add_le_add_right (Nat.add_le_add_left inactiveContentLe _) _
    _ = globalContent.natDegree +
        ∑ index ∈ indices,
          multiplicity index *
            fullYZWeightedDegree (q index) (parent index) := by
      rw [Nat.add_assoc, degreePartition]
    _ <= DZ := allWeightedBudget

/-- Every successful challenge outside the explicit global/inactive content
discard set is assigned to a separable parent and one of its specialized
branches, with the powered candidate substituted into that parent. -/
theorem exists_active_frobenius_factor_branch_assignment
    {K I J : Type*} [Field K] [DecidableEq K]
    [DecidableEq I] [DecidableEq J]
    (indices : Finset I) (branchIndices : I -> Finset J)
    (Q : TrivariatePolynomial K) (globalContent : BivariatePolynomial K)
    (parent : I -> TrivariatePolynomial K)
    (q multiplicity : I -> Nat)
    (x0 : K) (content : I -> Polynomial K)
    (branch : I -> J -> BivariatePolynomial K)
    (globalFactorization : Q = Polynomial.C globalContent *
      ∏ index ∈ indices,
        expandResponse (q index) (parent index) ^ multiplicity index)
    (multiplicityPositive :
      forall index, index ∈ indices -> 1 <= multiplicity index)
    (specializationFactorization : forall index, index ∈ indices ->
      specializeX x0 (parent index) = Polynomial.C (content index) *
        ∏ branchIndex ∈ branchIndices index, branch index branchIndex)
    (challenges : Finset K) (candidate : K -> Polynomial K)
    (candidateRoot : forall z, z ∈ challenges ->
      challengeCandidatePolynomial z (candidate z) Q = 0)
    (z : K) (zMem : z ∈ challenges)
    (zNotDiscarded : z ∉ factorTransferDiscarded indices branchIndices
      globalContent content challenges) :
    exists index, index ∈ activeFactorIndices indices branchIndices ∧
      exists branchIndex, branchIndex ∈ branchIndices index ∧
        challengeCandidatePolynomial z
            ((candidate z) ^ q index) (parent index) = 0 ∧
          ((content index).eval z = 0 ∨
            (branch index branchIndex).eval₂ (Polynomial.evalRingHom z)
              (((candidate z) ^ q index).eval x0) = 0) := by
  classical
  have globalContentValueNeZero :
      Ne (globalContent.eval (Polynomial.C z)) 0 := by
    intro contentZero
    apply zNotDiscarded
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨zMem, contentZero⟩
  obtain ⟨index, indexMem, expandedFactorRoot⟩ :=
    exists_factor_root_of_fullFactorization indices Q globalContent
      (fun candidateIndex =>
        expandResponse (q candidateIndex) (parent candidateIndex))
      multiplicity multiplicityPositive globalFactorization z (candidate z)
      (candidateRoot z zMem) globalContentValueNeZero
  have factorRoot :
      challengeCandidatePolynomial z
        ((candidate z) ^ q index) (parent index) = 0 := by
    rw [← challengeCandidatePolynomial_expandResponse]
    exact expandedFactorRoot
  have localAlternative := content_root_or_exists_branch_root
    (parent index) x0 (branchIndices index) (content index) (branch index)
    (specializationFactorization index indexMem) z
    ((candidate z) ^ q index) factorRoot
  rcases localAlternative with contentZero |
      ⟨branchIndex, branchIndexMem, branchRoot⟩
  · have branchNonempty : Ne (branchIndices index) ∅ := by
      intro branchEmpty
      apply zNotDiscarded
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨index, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨indexMem, branchEmpty⟩
      · exact Finset.mem_filter.mpr ⟨zMem, contentZero⟩
    obtain ⟨branchIndex, branchIndexMem⟩ :=
      Finset.nonempty_iff_ne_empty.mpr branchNonempty
    refine ⟨index, Finset.mem_filter.mpr ⟨indexMem, branchNonempty⟩,
      branchIndex, branchIndexMem, factorRoot, Or.inl contentZero⟩
  · have branchNonempty : Ne (branchIndices index) ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨branchIndex, branchIndexMem⟩
    refine ⟨index, Finset.mem_filter.mpr ⟨indexMem, branchNonempty⟩,
      branchIndex, branchIndexMem, factorRoot, Or.inr branchRoot⟩

/-- Equation (136), with the powered Y-degree budget used only to derive the
unpowered parent-degree budget. -/
theorem frobenius_factor_square_weight_sum_le
    {I : Type*} [DecidableEq I] (indices : Finset I)
    (multiplicity q degree fullDegree : I -> Nat) (DY : Nat)
    (qPositive : forall index, index ∈ indices -> 0 < q index)
    (multiplicityPositive :
      forall index, index ∈ indices -> 1 <= multiplicity index)
    (poweredYBudget :
      ∑ index ∈ indices,
        multiplicity index * (q index * degree index) <= DY) :
    ∑ index ∈ indices,
        degree index * degree index * fullDegree index <=
      DY ^ 2 *
        ∑ index ∈ indices, multiplicity index * fullDegree index := by
  have yBudget :=
    fullFactor_parent_yDegree_summation_le indices multiplicity q degree DY
      qPositive poweredYBudget
  exact factor_square_weight_sum_le indices multiplicity degree fullDegree DY
    multiplicityPositive yBudget

/-- Numerical Corollary 7.11 transfer once the explicit local exceptional
sets have been constructed. -/
theorem frobenius_factor_degree_transfer_of_local_exception_bounds
    {K I J : Type*} [Field K] [DecidableEq I] [DecidableEq J]
    (indices : Finset I) (branchIndices : I -> Finset J)
    (parent : I -> TrivariatePolynomial K)
    (q multiplicity : I -> Nat)
    (branchDegree assigned removed surviving : I -> J -> Nat)
    (DX DY DZ gammaN discardedDegree challengeCount : Nat)
    (multiplicityPositive :
      forall index, index ∈ indices -> 1 <= multiplicity index)
    (branchDegreeSumLe : forall index, index ∈ indices ->
      ∑ branchIndex ∈ branchIndices index,
        branchDegree index branchIndex <= (parent index).natDegree)
    (branchCountLe : forall index, index ∈ indices ->
      (branchIndices index).card <= (parent index).natDegree)
    (yDegreeBudget :
      ∑ index ∈ indices,
        multiplicity index * (parent index).natDegree <= DY)
    (weightedDegreeBudget : discardedDegree +
      ∑ index ∈ indices,
        multiplicity index *
          fullYZWeightedDegree (q index) (parent index) <= DZ)
    (globalMultiplierPositive : 1 <= 2 * DX * DY ^ 2)
    (challengeCountLe : challengeCount <= discardedDegree +
      ∑ index ∈ indices,
        ∑ branchIndex ∈ branchIndices index,
          assigned index branchIndex)
    (challengeCountLarge :
      2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY < challengeCount)
    (removalPartition : forall index, index ∈ indices ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        assigned index branchIndex =
          removed index branchIndex + surviving index branchIndex)
    (removedSmall : forall index, index ∈ indices ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        removed index branchIndex <
          (parent index).natDegree * branchDegree index branchIndex *
            fullYZWeightedDegree (q index) (parent index)) :
    exists index, index ∈ indices ∧
      exists branchIndex, branchIndex ∈ branchIndices index ∧
        (forall x0 order yExponent,
          Ne (shiftedParentCoefficient x0 order yExponent (parent index)) 0 ->
            (shiftedParentCoefficient x0 order yExponent
                (parent index)).natDegree + q index * yExponent <=
              fullYZWeightedDegree (q index) (parent index)) ∧
        (2 * DX - 1) *
              ((parent index).natDegree *
                branchDegree index branchIndex *
                  fullYZWeightedDegree (q index) (parent index)) +
            gammaN + 1 < surviving index branchIndex := by
  obtain ⟨index, indexMem, branchIndex, branchIndexMem, assignedLarge⟩ :=
    exists_factor_branch_above_preliminary_allowance indices branchIndices
      multiplicity (fun index => (parent index).natDegree)
      (fun index => fullYZWeightedDegree (q index) (parent index))
      branchDegree assigned DX DY DZ gammaN discardedDegree challengeCount
      multiplicityPositive branchDegreeSumLe branchCountLe yDegreeBudget
      weightedDegreeBudget globalMultiplierPositive challengeCountLe
      challengeCountLarge
  have DXPositive : 1 <= DX := by
    by_contra notPositive
    have DXZero : DX = 0 := Nat.eq_zero_of_not_pos notPositive
    simp [DXZero] at globalMultiplierPositive
  refine ⟨index, indexMem, branchIndex, branchIndexMem, ?_, ?_⟩
  · intro x0 order yExponent coefficientNeZero
    exact shiftedCoefficient_frobeniusFullDegree_le
      (parent index) x0 (q index) order yExponent coefficientNeZero
  · exact remove_local_exception_budget DX
      ((parent index).natDegree * branchDegree index branchIndex *
        fullYZWeightedDegree (q index) (parent index))
      gammaN (assigned index branchIndex) (removed index branchIndex)
      (surviving index branchIndex) DXPositive assignedLarge
      (removedSmall index indexMem branchIndex branchIndexMem)
      (removalPartition index indexMem branchIndex branchIndexMem)

/-- Corollary 7.11, global algebraic transfer.

The theorem starts from the literal factorization through Y^(q_i), derives
both global degree ledgers, constructs the discard and disjoint assignment
sets, charges specialization content to the q_i-weighted derivative
resultant, and returns a genuine simple branch for the powered candidates.
-/
theorem full_factor_frobenius_degree_transfer
    {K I J : Type*} [Field K] [DecidableEq K]
    [DecidableEq I] [DecidableEq J]
    (indices : Finset I) (branchIndices : I -> Finset J)
    (Q : TrivariatePolynomial K) (globalContent : BivariatePolynomial K)
    (parent : I -> TrivariatePolynomial K)
    (q multiplicity : I -> Nat)
    (x0 : K) (content : I -> Polynomial K)
    (branch : I -> J -> BivariatePolynomial K)
    (challenges : Finset K) (candidate : K -> Polynomial K)
    (DX DY DZ gammaN : Nat)
    (qPositive : forall index, index ∈ indices -> 0 < q index)
    (globalContentNeZero : Ne globalContent 0)
    (parentNeZero : forall index, index ∈ indices -> Ne (parent index) 0)
    (parentPositive :
      forall index, index ∈ indices -> 1 <= (parent index).natDegree)
    (multiplicityPositive :
      forall index, index ∈ indices -> 1 <= multiplicity index)
    (globalFactorization : Q = Polynomial.C globalContent *
      ∏ index ∈ indices,
        expandResponse (q index) (parent index) ^ multiplicity index)
    (contentNeZero : forall index, index ∈ indices -> Ne (content index) 0)
    (branchNeZero : forall index, index ∈ indices ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        Ne (branch index branchIndex) 0)
    (branchPositive : forall index, index ∈ indices ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        0 < (branch index branchIndex).natDegree)
    (branchIrreducible : forall index, index ∈ indices ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        Irreducible (branch index branchIndex))
    (specializationFactorization : forall index, index ∈ indices ->
      specializeX x0 (parent index) = Polynomial.C (content index) *
        ∏ branchIndex ∈ branchIndices index, branch index branchIndex)
    (specializedSeparable : forall index, index ∈ indices ->
      (branchPolynomial (specializeX x0 (parent index))).Separable)
    (QYDegree : Q.natDegree <= DY)
    (QWeightedDegree : fullYZWeightedDegree 1 Q <= DZ)
    (globalMultiplierPositive : 1 <= 2 * DX * DY ^ 2)
    (candidateRoot : forall z, z ∈ challenges ->
      challengeCandidatePolynomial z (candidate z) Q = 0)
    (challengeCountLarge :
      2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY < challenges.card) :
    exists index, index ∈ activeFactorIndices indices branchIndices ∧
      exists branchIndex, branchIndex ∈ branchIndices index ∧
        exists surviving : Finset K,
          (forall order yExponent,
            Ne (shiftedParentCoefficient x0 order yExponent
              (parent index)) 0 ->
              (shiftedParentCoefficient x0 order yExponent
                  (parent index)).natDegree + q index * yExponent <=
                fullYZWeightedDegree (q index) (parent index)) ∧
          (2 * DX - 1) *
                ((parent index).natDegree *
                  (branch index branchIndex).natDegree *
                    fullYZWeightedDegree (q index) (parent index)) +
              gammaN + 1 < surviving.card ∧
          forall z, z ∈ surviving ->
            z ∈ challenges ∧
            challengeCandidatePolynomial z
              ((candidate z) ^ q index) (parent index) = 0 ∧
            Ne ((content index).eval z) 0 ∧
            exists localRoot :
                (branch index branchIndex).eval₂
                  (Polynomial.evalRingHom z)
                  (((candidate z) ^ q index).eval x0) = 0,
              Ne ((branch index branchIndex).leadingCoeff.eval z) 0 ∧
              Ne (specializedDerivativeValue (parent index) x0 z
                (shiftedCandidateSeries x0 ((candidate z) ^ q index))
                (parent index).natDegree) 0 := by
  classical
  let active := activeFactorIndices indices branchIndices
  let discarded := factorTransferDiscarded indices branchIndices
    globalContent content challenges
  let source := challenges \ discarded
  let assignmentProperty : K -> I -> J -> Prop :=
    fun z index branchIndex =>
      challengeCandidatePolynomial z
          ((candidate z) ^ q index) (parent index) = 0 ∧
        ((content index).eval z = 0 ∨
          (branch index branchIndex).eval₂ (Polynomial.evalRingHom z)
            (((candidate z) ^ q index).eval x0) = 0)
  have assignmentExists : forall z, z ∈ source ->
      exists index, index ∈ active ∧
        exists branchIndex, branchIndex ∈ branchIndices index ∧
          assignmentProperty z index branchIndex := by
    intro z zMem
    have zMemChallenges : z ∈ challenges := (Finset.mem_sdiff.mp zMem).1
    have zNotDiscarded : z ∉ discarded := (Finset.mem_sdiff.mp zMem).2
    exact exists_active_frobenius_factor_branch_assignment indices
      branchIndices Q globalContent parent q multiplicity x0 content branch
      globalFactorization multiplicityPositive specializationFactorization
      challenges candidate candidateRoot z zMemChallenges zNotDiscarded
  obtain ⟨assigned, assignmentCount, assignedProperty⟩ :=
    exists_disjoint_factor_branch_assignment source active branchIndices
      assignmentProperty assignmentExists
  let discardedDegree := globalContent.natDegree +
    ∑ index ∈ inactiveFactorIndices indices branchIndices,
      (content index).natDegree
  have discardedSubset : discarded ⊆ challenges := by
    intro z zMem
    rcases Finset.mem_union.mp zMem with globalMem | inactiveMem
    · exact (Finset.mem_filter.mp globalMem).1
    · obtain ⟨index, indexMem, localMem⟩ :=
        Finset.mem_biUnion.mp inactiveMem
      exact (Finset.mem_filter.mp localMem).1
  have discardedCard : discarded.card <= discardedDegree :=
    factorTransferDiscarded_card_le indices branchIndices globalContent
      content challenges globalContentNeZero contentNeZero
  have challengeCountLe : challenges.card <= discardedDegree +
      ∑ index ∈ active,
        ∑ branchIndex ∈ branchIndices index,
          (assigned index branchIndex).card := by
    have partition := Finset.card_sdiff_add_card_eq_card discardedSubset
    dsimp [source] at assignmentCount
    omega
  obtain ⟨yDegreeBudget, weightedDegreeBudget⟩ :=
    activeFactor_frobenius_degree_budgets indices branchIndices Q
      globalContent parent q multiplicity x0 content branch qPositive
      globalContentNeZero parentNeZero multiplicityPositive
      globalFactorization contentNeZero branchNeZero
      specializationFactorization DY DZ QYDegree QWeightedDegree
  have branchDegreeSumLe : forall index, index ∈ active ->
      ∑ branchIndex ∈ branchIndices index,
        (branch index branchIndex).natDegree <=
          (parent index).natDegree := by
    intro index indexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    exact specialization_branch_yDegree_summation (parent index) x0
      (branchIndices index) (content index) (branch index)
      (contentNeZero index indexInIndices)
      (branchNeZero index indexInIndices)
      (specializationFactorization index indexInIndices)
  have branchCountLe : forall index, index ∈ active ->
      (branchIndices index).card <= (parent index).natDegree := by
    intro index indexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    exact specialization_branch_count_le (parent index) x0
      (branchIndices index) (content index) (branch index)
      (contentNeZero index indexInIndices)
      (branchNeZero index indexInIndices)
      (branchPositive index indexInIndices)
      (specializationFactorization index indexInIndices)
  have branchWeightLe : forall index, index ∈ active ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        localBivariateWeight (q index) (branch index branchIndex) <=
          fullYZWeightedDegree (q index) (parent index) := by
    intro index indexMem branchIndex branchIndexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    have termLe :
        localBivariateWeight (q index) (branch index branchIndex) <=
          ∑ candidateBranch ∈ branchIndices index,
            localBivariateWeight (q index)
              (branch index candidateBranch) :=
      Finset.single_le_sum
        (f := fun candidateBranch =>
          localBivariateWeight (q index) (branch index candidateBranch))
        (fun _ _ => Nat.zero_le _) branchIndexMem
    have sumBound := specialization_content_branch_weight_summation
      (parent index) x0 (q index) (branchIndices index) (content index)
      (branch index) (contentNeZero index indexInIndices)
      (branchNeZero index indexInIndices)
      (specializationFactorization index indexInIndices)
    omega
  have factorDvd : forall index, index ∈ active ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        branch index branchIndex ∣ specializeX x0 (parent index) := by
    intro index indexMem branchIndex branchIndexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    rw [specializationFactorization index indexInIndices]
    exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (branch index) branchIndexMem)
      (Polynomial.C (content index))
  have etaNeZero : forall index, index ∈ active ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        Ne (regularDerivativeElement (parent index)
          (branch index branchIndex) x0 (parent index).natDegree) 0 := by
    intro index indexMem branchIndex branchIndexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    exact regularDerivativeElement_ne_zero_of_specialized_separable
      (parent index) (branch index branchIndex)
      (branchIrreducible index indexInIndices branchIndex branchIndexMem)
      (branchPositive index indexInIndices branchIndex branchIndexMem)
      x0 (parent index).natDegree le_rfl
      (factorDvd index indexMem branchIndex branchIndexMem)
      (specializedSeparable index indexInIndices)
  let localData (index : I) (indexMem : index ∈ active)
      (branchIndex : J) (branchIndexMem : branchIndex ∈ branchIndices index) :=
    poleResultantExceptionalData (parent index)
      (branch index branchIndex)
      (branchIrreducible index (Finset.mem_filter.mp indexMem).1
        branchIndex branchIndexMem)
      (branchPositive index (Finset.mem_filter.mp indexMem).1
        branchIndex branchIndexMem)
      (parentPositive index (Finset.mem_filter.mp indexMem).1)
      (q index) (qPositive index (Finset.mem_filter.mp indexMem).1)
      x0 (content index)
      (∏ candidateBranch ∈ branchIndices index,
        branch index candidateBranch)
      (specializationFactorization index
        (Finset.mem_filter.mp indexMem).1)
      (factorDvd index indexMem branchIndex branchIndexMem)
      (branchWeightLe index indexMem branchIndex branchIndexMem)
      (etaNeZero index indexMem branchIndex branchIndexMem)
      (assigned index branchIndex)
  let removed : I -> J -> Finset K := fun index branchIndex =>
    if indexMem : index ∈ active then
      if branchIndexMem : branchIndex ∈ branchIndices index then
        (localData index indexMem branchIndex branchIndexMem).exceptional
      else ∅
    else ∅
  let surviving : I -> J -> Finset K := fun index branchIndex =>
    assigned index branchIndex \ removed index branchIndex
  have removedSmall : forall index, index ∈ active ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        (removed index branchIndex).card <
          (parent index).natDegree *
            (branch index branchIndex).natDegree *
              fullYZWeightedDegree (q index) (parent index) := by
    intro index indexMem branchIndex branchIndexMem
    simpa [removed, indexMem, branchIndexMem] using
      (localData index indexMem branchIndex branchIndexMem).exceptionalCard
  have removedSubset : forall index, index ∈ active ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        removed index branchIndex ⊆ assigned index branchIndex := by
    intro index indexMem branchIndex branchIndexMem
    simpa [removed, indexMem, branchIndexMem] using
      (localData index indexMem branchIndex branchIndexMem).exceptionalSubset
  have removalPartition : forall index, index ∈ active ->
      forall branchIndex, branchIndex ∈ branchIndices index ->
        (assigned index branchIndex).card =
          (removed index branchIndex).card +
            (surviving index branchIndex).card := by
    intro index indexMem branchIndex branchIndexMem
    have partition := Finset.card_sdiff_add_card_eq_card
      (removedSubset index indexMem branchIndex branchIndexMem)
    dsimp [surviving]
    omega
  obtain ⟨index, indexMem, branchIndex, branchIndexMem,
      coefficientBound, survivingLarge⟩ :=
    frobenius_factor_degree_transfer_of_local_exception_bounds active
      branchIndices parent q multiplicity
      (fun index branchIndex => (branch index branchIndex).natDegree)
      (fun index branchIndex => (assigned index branchIndex).card)
      (fun index branchIndex => (removed index branchIndex).card)
      (fun index branchIndex => (surviving index branchIndex).card)
      DX DY DZ gammaN discardedDegree challenges.card
      (fun index indexMem =>
        multiplicityPositive index (Finset.mem_filter.mp indexMem).1)
      branchDegreeSumLe branchCountLe yDegreeBudget weightedDegreeBudget
      globalMultiplierPositive challengeCountLe challengeCountLarge
      removalPartition removedSmall
  refine ⟨index, indexMem, branchIndex, branchIndexMem,
    surviving index branchIndex, ?_, survivingLarge, ?_⟩
  · intro order yExponent coefficientNeZero
    exact coefficientBound x0 order yExponent coefficientNeZero
  · intro z zMem
    have zMemAssigned : z ∈ assigned index branchIndex :=
      (Finset.mem_sdiff.mp zMem).1
    have zNotRemoved : z ∉ removed index branchIndex :=
      (Finset.mem_sdiff.mp zMem).2
    obtain ⟨zMemSource, factorRoot, localAlternative⟩ :=
      assignedProperty index indexMem branchIndex branchIndexMem z zMemAssigned
    have zMemChallenges : z ∈ challenges :=
      (Finset.mem_sdiff.mp zMemSource).1
    have zNotExceptional : z ∉
        (localData index indexMem branchIndex branchIndexMem).exceptional := by
      simpa [removed, indexMem, branchIndexMem] using zNotRemoved
    obtain ⟨leadingValueNeZero, resultantValueNeZero⟩ :=
      (localData index indexMem branchIndex branchIndexMem).regularOutside
        z zMemAssigned zNotExceptional
    have contentValueNeZero : Ne ((content index).eval z) 0 := by
      intro contentZero
      apply zNotExceptional
      exact
        (localData index indexMem branchIndex branchIndexMem).contentIncluded
          z zMemAssigned contentZero
    have localRoot : (branch index branchIndex).eval₂
        (Polynomial.evalRingHom z)
        (((candidate z) ^ q index).eval x0) = 0 :=
      localAlternative.resolve_left contentValueNeZero
    let rootPair := branchRootPair (branch index branchIndex)
      (branchPositive index (Finset.mem_filter.mp indexMem).1
        branchIndex branchIndexMem)
      x0 z ((candidate z) ^ q index) localRoot
    let specialization := branchSpecialization
      (branch index branchIndex)
      (branchPositive index (Finset.mem_filter.mp indexMem).1
        branchIndex branchIndexMem)
      x0 z ((candidate z) ^ q index) localRoot
    have xiSpecializationNeZero : Ne
        (specialization
          (localData index indexMem branchIndex branchIndexMem).xi) 0 := by
      intro xiZero
      apply resultantValueNeZero
      exact eval_canonicalRepresentative_resultant_eq_zero
        (branch index branchIndex)
        (branchIrreducible index (Finset.mem_filter.mp indexMem).1
          branchIndex branchIndexMem).ne_zero
        (branchPositive index (Finset.mem_filter.mp indexMem).1
          branchIndex branchIndexMem)
        (localData index indexMem branchIndex branchIndexMem).xi z
        (branchRootValue (branch index branchIndex) x0 z
          ((candidate z) ^ q index))
        rootPair xiZero
    have mappedClearing := congrArg specialization
      (localData index indexMem branchIndex branchIndexMem).clearing
    rw [map_mul, branchSpecialization_of] at mappedClearing
    have etaSpecializationNeZero : Ne
        (specialization
          (regularDerivativeElement (parent index)
            (branch index branchIndex) x0 (parent index).natDegree)) 0 := by
      rw [mappedClearing]
      exact mul_ne_zero leadingValueNeZero xiSpecializationNeZero
    have derivativeValueNeZero : Ne
        (specializedDerivativeValue (parent index) x0 z
          (shiftedCandidateSeries x0 ((candidate z) ^ q index))
          (parent index).natDegree) 0 := by
      intro derivativeZero
      apply etaSpecializationNeZero
      rw [branchSpecialization_regularDerivativeElement (parent index)
        (branch index branchIndex)
        (branchPositive index (Finset.mem_filter.mp indexMem).1
          branchIndex branchIndexMem)
        x0 z ((candidate z) ^ q index) localRoot
        (parent index).natDegree, derivativeZero, mul_zero]
    exact ⟨zMemChallenges, factorRoot, contentValueNeZero, localRoot,
      leadingValueNeZero, derivativeValueNeZero⟩

/-- Swap the X and Z variables in every Y coefficient.  The resulting
bivariate presentation has coefficient ring K[Z], inner variable X, and
outer variable Y. -/
def swapXZEquiv
    {K : Type*} [Field K] :
    TrivariatePolynomial K ≃ₐ[K] TrivariatePolynomial K :=
  Polynomial.mapAlgEquiv (Polynomial.Bivariate.swap (R := K))

/-- The (1,k,0)-weighted degree in (X,Y,Z): X has weight one, Y has
weight k, and Z belongs to the weight-zero coefficient ring. -/
def fullXYWeightedDegree
    {K : Type*} [Field K] (k : Nat)
    (parent : TrivariatePolynomial K) : Nat :=
  localBivariateWeight k (swapXZEquiv parent)

/-- Exact factor summation for the (1,k,0)-weight. -/
theorem fullFactor_XY_weight_summation
    {K I : Type*} [Field K] [DecidableEq I]
    (indices : Finset I) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (factor : I -> TrivariatePolynomial K) (multiplicity : I -> Nat)
    (contentNeZero : Ne content 0)
    (factorNeZero : forall index, index ∈ indices -> Ne (factor index) 0)
    (factorization : Q = Polynomial.C content *
      ∏ index ∈ indices, factor index ^ multiplicity index)
    (k : Nat) :
    fullXYWeightedDegree k Q =
      fullXYWeightedDegree k (Polynomial.C content) +
        ∑ index ∈ indices,
          multiplicity index * fullXYWeightedDegree k (factor index) := by
  have mappedContentNeZero :
      Ne (swapXZEquiv (Polynomial.C content)) 0 := by
    simpa using
      (swapXZEquiv : TrivariatePolynomial K ≃ₐ[K]
        TrivariatePolynomial K).injective.ne
          (Polynomial.C_ne_zero.mpr contentNeZero)
  have mappedFactorNeZero : forall index, index ∈ indices ->
      Ne (swapXZEquiv (factor index)) 0 := by
    intro index indexMem
    simpa using
      (swapXZEquiv : TrivariatePolynomial K ≃ₐ[K]
        TrivariatePolynomial K).injective.ne (factorNeZero index indexMem)
  have mappedPowerNeZero : forall index, index ∈ indices ->
      Ne ((swapXZEquiv (factor index)) ^ multiplicity index) 0 := by
    intro index indexMem
    exact pow_ne_zero _ (mappedFactorNeZero index indexMem)
  have mappedProductNeZero : Ne
      (∏ index ∈ indices,
        (swapXZEquiv (factor index)) ^ multiplicity index) 0 := by
    apply (Finset.prod_ne_zero_iff
      (s := indices)
      (f := fun index =>
        (swapXZEquiv (factor index)) ^ multiplicity index)).mpr
    exact mappedPowerNeZero
  unfold fullXYWeightedDegree
  rw [factorization, map_mul, map_prod]
  simp_rw [map_pow]
  rw [
    localBivariateWeight_mul_eq k _ _ mappedContentNeZero
      mappedProductNeZero,
    localBivariateWeight_finset_prod_eq k indices]
  · congr 1
    apply Finset.sum_congr rfl
    intro index indexMem
    rw [localBivariateWeight_pow_eq k
      (swapXZEquiv (factor index)) (mappedFactorNeZero index indexMem)]
  · intro index indexMem
    exact mappedPowerNeZero index indexMem

/-- The outer Y-degree contribution is always visible in the
(1,k,0)-weighted degree. -/
theorem yDegree_mul_le_fullXYWeightedDegree
    {K : Type*} [Field K] (k : Nat)
    (parent : TrivariatePolynomial K) (parentNeZero : Ne parent 0) :
    parent.natDegree * k <= fullXYWeightedDegree k parent := by
  let swapped := swapXZEquiv parent
  have swappedNeZero : Ne swapped 0 := by
    simpa [swapped] using
      (swapXZEquiv : TrivariatePolynomial K ≃ₐ[K]
        TrivariatePolynomial K).injective.ne parentNeZero
  have degreeEq : swapped.natDegree = parent.natDegree := by
    unfold swapped swapXZEquiv
    exact Polynomial.natDegree_map_eq_of_injective
      (Polynomial.Bivariate.swap (R := K)).injective parent
  have leadingMem : swapped.natDegree ∈ swapped.support :=
    Polynomial.natDegree_mem_support_of_nonzero swappedNeZero
  have lower := coeff_weight_le_localBivariateWeight k swapped
    swapped.natDegree leadingMem
  unfold fullXYWeightedDegree
  rw [← degreeEq]
  exact (Nat.le_add_left _ _).trans lower

/-- Equation (137): the selected separable parent inherits enough
(1,k,0)-degree from the global factorization to force q*d*k < DX and hence
q*k < DX. -/
theorem frobenius_parent_order_lt_global_XY_degree
    {K I : Type*} [Field K] [DecidableEq I]
    (indices : Finset I) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (parent : I -> TrivariatePolynomial K)
    (q multiplicity : I -> Nat)
    (contentNeZero : Ne content 0)
    (parentNeZero : forall index, index ∈ indices -> Ne (parent index) 0)
    (qPositive : forall index, index ∈ indices -> 0 < q index)
    (multiplicityPositive :
      forall index, index ∈ indices -> 1 <= multiplicity index)
    (parentPositive :
      forall index, index ∈ indices -> 1 <= (parent index).natDegree)
    (globalFactorization : Q = Polynomial.C content *
      ∏ index ∈ indices,
        expandResponse (q index) (parent index) ^ multiplicity index)
    (k DX : Nat) (globalDegreeLt : fullXYWeightedDegree k Q < DX)
    (index : I) (indexMem : index ∈ indices) :
    q index * (parent index).natDegree * k < DX ∧ q index * k < DX := by
  have expandedNeZero :
      Ne (expandResponse (q index) (parent index)) 0 :=
    expandResponse_ne_zero (q index) (qPositive index indexMem)
      (parent index) (parentNeZero index indexMem)
  have exactSum := fullFactor_XY_weight_summation indices Q content
    (fun candidateIndex =>
      expandResponse (q candidateIndex) (parent candidateIndex))
    multiplicity contentNeZero
    (fun candidateIndex candidateMem =>
      expandResponse_ne_zero (q candidateIndex)
        (qPositive candidateIndex candidateMem)
        (parent candidateIndex) (parentNeZero candidateIndex candidateMem))
    globalFactorization k
  have factorWeightLeQ :
      fullXYWeightedDegree k
          (expandResponse (q index) (parent index)) <=
        fullXYWeightedDegree k Q := by
    rw [exactSum]
    exact (calc
      fullXYWeightedDegree k
          (expandResponse (q index) (parent index)) <=
        multiplicity index *
          fullXYWeightedDegree k
            (expandResponse (q index) (parent index)) := by
          have multiplicityPos : 1 <= multiplicity index :=
            multiplicityPositive index indexMem
          calc
            _ = 1 * fullXYWeightedDegree k
                (expandResponse (q index) (parent index)) := by ring
            _ <= _ := Nat.mul_le_mul_right _ multiplicityPos
      _ <= ∑ candidateIndex ∈ indices,
          multiplicity candidateIndex *
            fullXYWeightedDegree k
              (expandResponse (q candidateIndex)
                (parent candidateIndex)) :=
        Finset.single_le_sum
          (f := fun candidateIndex =>
            multiplicity candidateIndex *
              fullXYWeightedDegree k
                (expandResponse (q candidateIndex)
                  (parent candidateIndex)))
          (fun _ _ => Nat.zero_le _) indexMem
      _ <= fullXYWeightedDegree k (Polynomial.C content) +
          ∑ candidateIndex ∈ indices,
            multiplicity candidateIndex *
              fullXYWeightedDegree k
                (expandResponse (q candidateIndex)
                  (parent candidateIndex)) :=
        Nat.le_add_left _ _)
  have degreeLower :=
    yDegree_mul_le_fullXYWeightedDegree k
      (expandResponse (q index) (parent index)) expandedNeZero
  rw [expandResponse_natDegree] at degreeLower
  have productLt :
      q index * (parent index).natDegree * k < DX := by
    calc
      q index * (parent index).natDegree * k =
          ((parent index).natDegree * q index) * k := by ring
      _ <= fullXYWeightedDegree k
          (expandResponse (q index) (parent index)) := degreeLower
      _ <= fullXYWeightedDegree k Q := factorWeightLeQ
      _ < DX := globalDegreeLt
  have orderLeProduct :
      q index * k <= q index * (parent index).natDegree * k := by
    calc
      q index * k = q index * 1 * k := by ring
      _ <= q index * (parent index).natDegree * k :=
        Nat.mul_le_mul_right k
          (Nat.mul_le_mul_left (q index) (parentPositive index indexMem))
  exact ⟨productLt, orderLeProduct.trans_lt productLt⟩

#print axioms fullFactor_XY_weight_summation
#print axioms yDegree_mul_le_fullXYWeightedDegree
#print axioms frobenius_parent_order_lt_global_XY_degree
#print axioms full_factor_frobenius_degree_transfer
#print axioms frobenius_factor_square_weight_sum_le
#print axioms frobenius_factor_degree_transfer_of_local_exception_bounds
#print axioms exists_active_frobenius_factor_branch_assignment
#print axioms activeFactor_frobenius_degree_budgets
#print axioms fullFactor_frobenius_weight_summation
#print axioms fullFactor_frobenius_yDegree_summation
#print axioms fullFactor_parent_yDegree_summation_le
#print axioms fullYZWeightedDegree_expandResponse
#print axioms specializeX_expandResponse
#print axioms challengeCandidatePolynomial_expandResponse
#print axioms shiftedCoefficient_frobeniusFullDegree_le

end

end WeightedHensel

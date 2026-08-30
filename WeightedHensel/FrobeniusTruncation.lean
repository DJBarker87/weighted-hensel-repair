/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FrobeniusBranch
import WeightedHensel.Truncation

/-!
# Sparse Frobenius truncation

A powered candidate has no Taylor coefficient outside indices divisible by
`q = p^f`.  This file feeds that literal coefficient vanishing into the
regular-quotient recurrence and the first weighted resultant.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Any zero candidate Taylor coefficient kills the corresponding
specialized division-free coefficient. -/
theorem branchSpecialization_parentDivisionFreeCoefficients_eq_zero_of_coeff
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (d : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (candidateRoot : challengeCandidatePolynomial z candidate parent = 0)
    (t : Nat)
    (coefficientZero :
      PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) = 0) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (parentDivisionFreeCoefficients parent factor x₀ d t) = 0 := by
  rw [branchSpecialization_parentDivisionFreeCoefficients parent factor
    factorPositive x₀ z candidate localRoot d dPositive parentDegreeLe
    candidateRoot t, coefficientZero, mul_zero]

/-- The first resultant needs only literal specialized coefficient
vanishing; a degree bound is one sufficient source, but not the only one. -/
theorem parentDivisionFreeCoefficients_eq_zero_of_many_branches_of_coeff
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ : K) (ell DH DR d b tau t : Nat)
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
    (coefficientZero : ∀ z ∈ challenges,
      PowerSeries.coeff t
        (shiftedCandidateSeries x₀ (candidate z)) = 0)
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
    rw [regularWeight_eq_coe factor factorIrreducible.ne_zero tau deltaZero]
      at deltaWeightWithBot
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
    exact branchSpecialization_parentDivisionFreeCoefficients_eq_zero_of_coeff
      parent factor factorPositive x₀ z (candidate z) (localRoot z zMem) d
      dPositive parentDegreeLe (candidateRoot z zMem) t
      (coefficientZero z zMem)
  · exact manyBranches

/-- A powered degree-`k` candidate has zero translated coefficient either
above order `qk` or at an index not divisible by `q`. -/
theorem coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_sparse
    {K : Type*} [Field K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (x₀ : K) (candidate : Polynomial K) (k order : Nat)
    (degreeLe : candidate.natDegree ≤ k)
    (sparse : frobeniusPower p f * k < order ∨
      ¬frobeniusPower p f ∣ order) :
    PowerSeries.coeff order
        (shiftedCandidateSeries x₀
          (candidate ^ frobeniusPower p f)) = 0 := by
  rcases sparse with aboveDegree | notDivisible
  · apply coeff_shiftedCandidateSeries_eq_zero_of_natDegree_lt
    exact (natDegree_frobeniusPower_le p f k candidate degreeLe).trans_lt
      aboveDegree
  · exact
      coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_not_dvd
        p f x₀ candidate order notDivisible

/-- First-resultant vanishing for every forbidden Frobenius index. -/
theorem parentDivisionFreeCoefficients_eq_zero_of_many_frobenius_branches
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (x₀ : K) (ell DH DR d b tau k t : Nat)
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
      factor.eval₂ (Polynomial.evalRingHom z)
        (((candidate z) ^ frobeniusPower p f).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z
        ((candidate z) ^ frobeniusPower p f) parent = 0)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ k)
    (sparse : frobeniusPower p f * k < t ∨
      ¬frobeniusPower p f ∣ t)
    (manyBranches : factor.natDegree *
      divisionFreeCeiling tau (sourceMu DR ell d b) t < challenges.card) :
    parentDivisionFreeCoefficients parent factor x₀ d t = 0 := by
  apply parentDivisionFreeCoefficients_eq_zero_of_many_branches_of_coeff
    parent factor factorIrreducible factorPositive x₀ ell DH DR d b tau t
    factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
    dPositive ellDLeDR wLeB parentDegreeLe challenges
    (fun z ↦ (candidate z) ^ frobeniusPower p f) localRoot candidateRoot
  · intro z zMem
    exact coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_sparse
      p f x₀ (candidate z) k t (candidateDegree z zMem) sparse
  · exact manyBranches

#print axioms parentDivisionFreeCoefficients_eq_zero_of_many_branches_of_coeff
#print axioms coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_sparse
#print axioms parentDivisionFreeCoefficients_eq_zero_of_many_frobenius_branches

end

end WeightedHensel

/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FrobeniusFixedBranch

/-!
# Source-indexed Frobenius fixed-branch completion

The intrinsic fixed-branch theorem is naturally indexed by compatible
Frobenius roots.  Corollary 7.11 is stated at the original source
challenges.  Over a finite field inverse Frobenius is a bijection, so this
module transports the entire incidence problem, including its cardinality,
back to the source indexing.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Fixed-branch Frobenius completion indexed by the source challenges.

Unlike `fixed_branch_frobenius_line_decodability`, no compatible roots occur
in the statement.  They are constructed internally using inverse Frobenius,
and the bijection proves that all support and incidence cardinalities are
unchanged.
-/
theorem fixed_branch_frobenius_line_decodability_source_indexed
    {K Domain : Type*} [Field K] [Finite K] [Fintype Domain]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (points : Domain → K) (pointsInjective : Function.Injective points)
    (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ : K) (DH DR d b tau k agreementThreshold : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree +
        frobeniusPower p f * exponent ≤ DH)
    (generatorWeightEq :
      DH + frobeniusPower p f -
        frobeniusPower p f * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent (frobeniusPower p f) DR)
    (tauEq : tau = b + frobeniusPower p f)
    (ellLeDR : frobeniusPower p f ≤ DR)
    (dPositive : 1 ≤ d)
    (ellDLeDR : frobeniusPower p f * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (parentDegreeLe : parent.natDegree ≤ d)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (support : K → Finset Domain)
    (receivedConstant receivedLinear : Domain → K)
    (supportLarge : ∀ z ∈ challenges,
      agreementThreshold < (support z).card)
    (agreement : ∀ z ∈ challenges, ∀ coordinate ∈ support z,
      (candidate z).eval (points coordinate) =
        receivedConstant coordinate + receivedLinear coordinate * z)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ k)
    (sourceLocalRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z)
          (((candidate z) ^ frobeniusPower p f).eval x₀) = 0)
    (sourceCandidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z
        ((candidate z) ^ frobeniusPower p f) parent = 0)
    (sourceLeadingNeZero : ∀ z ∈ challenges,
      factor.leadingCoeff.eval z ≠ 0)
    (sourceDerivativeNeZero : ∀ (z) (zMem : z ∈ challenges),
      branchSpecialization factor factorPositive x₀ z
          ((candidate z) ^ frobeniusPower p f)
          (sourceLocalRoot z zMem)
          (regularDerivativeElement parent factor x₀ d) ≠ 0)
    (incidenceLarge :
      k * challenges.card + Fintype.card Domain *
          (factor.natDegree *
            divisionFreeCeiling tau
              (sourceMu DR (frobeniusPower p f) d b)
              (k * frobeniusPower p f)) <
        challenges.card * (agreementThreshold + 1)) :
    ∃ v₀ v₁ : Polynomial K,
      v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
      ∀ z ∈ challenges,
        candidate z = v₀ + Polynomial.C z * v₁ := by
  classical
  let q := frobeniusPower p f
  let inverse : K → K := fun z ↦
    (iterateFrobeniusEquiv K p f).symm z
  let rootedChallenges := challenges.image inverse
  let rootedCandidate : K → Polynomial K := fun z ↦ candidate (z ^ q)
  let rootedSupport : K → Finset Domain := fun z ↦ support (z ^ q)
  have inverseInjective : Function.Injective inverse := by
    exact (iterateFrobeniusEquiv K p f).symm.injective
  have rootedCard : rootedChallenges.card = challenges.card := by
    exact Finset.card_image_of_injective challenges inverseInjective
  have rootedSupportLarge : ∀ z ∈ rootedChallenges,
      agreementThreshold < (rootedSupport z).card := by
    intro z zMem
    obtain ⟨source, sourceMem, rfl⟩ := Finset.mem_image.mp zMem
    simpa only [rootedSupport, inverse, q, frobeniusRoot_pow] using
      supportLarge source sourceMem
  have rootedAgreement : ∀ z ∈ rootedChallenges,
      ∀ coordinate ∈ rootedSupport z,
        (rootedCandidate z).eval (points coordinate) =
          receivedConstant coordinate + receivedLinear coordinate * z ^ q := by
    intro z zMem coordinate coordinateMem
    obtain ⟨source, sourceMem, rfl⟩ := Finset.mem_image.mp zMem
    have coordinateSource : coordinate ∈ support source := by
      simpa only [rootedSupport, inverse, q, frobeniusRoot_pow] using
        coordinateMem
    simpa only [rootedCandidate, rootedSupport, inverse, q,
      frobeniusRoot_pow] using
        agreement source sourceMem coordinate coordinateSource
  have rootedCandidateDegree : ∀ z ∈ rootedChallenges,
      (rootedCandidate z).natDegree ≤ k := by
    intro z zMem
    obtain ⟨source, sourceMem, rfl⟩ := Finset.mem_image.mp zMem
    simpa only [rootedCandidate, inverse, q, frobeniusRoot_pow] using
      candidateDegree source sourceMem
  have rootedLocalRoot : ∀ z ∈ rootedChallenges,
      factor.eval₂ (Polynomial.evalRingHom (z ^ q))
          (((rootedCandidate z) ^ q).eval x₀) = 0 := by
    intro z zMem
    obtain ⟨source, sourceMem, rfl⟩ := Finset.mem_image.mp zMem
    simpa only [rootedCandidate, inverse, q, frobeniusRoot_pow] using
      sourceLocalRoot source sourceMem
  have rootedParentRoot : ∀ z ∈ rootedChallenges,
      challengeCandidatePolynomial (z ^ q)
        ((rootedCandidate z) ^ q) parent = 0 := by
    intro z zMem
    obtain ⟨source, sourceMem, rfl⟩ := Finset.mem_image.mp zMem
    simpa only [rootedCandidate, inverse, q, frobeniusRoot_pow] using
      sourceCandidateRoot source sourceMem
  have rootedLeadingNeZero : ∀ z ∈ rootedChallenges,
      factor.leadingCoeff.eval (z ^ q) ≠ 0 := by
    intro z zMem
    obtain ⟨source, sourceMem, rfl⟩ := Finset.mem_image.mp zMem
    simpa only [inverse, q, frobeniusRoot_pow] using
      sourceLeadingNeZero source sourceMem
  have rootedDerivativeNeZero : ∀ z (zMem : z ∈ rootedChallenges),
      branchSpecialization factor factorPositive x₀ (z ^ q)
          ((rootedCandidate z) ^ q)
          (rootedLocalRoot z zMem)
          (regularDerivativeElement parent factor x₀ d) ≠ 0 := by
    intro z zMem
    obtain ⟨source, sourceMem, rfl⟩ := Finset.mem_image.mp zMem
    simpa only [rootedCandidate, inverse, q, frobeniusRoot_pow] using
      sourceDerivativeNeZero source sourceMem
  have rootedIncidenceLarge :
      k * rootedChallenges.card + Fintype.card Domain *
          (factor.natDegree *
            divisionFreeCeiling tau (sourceMu DR q d b) (k * q)) <
        rootedChallenges.card * (agreementThreshold + 1) := by
    simpa only [rootedCard, q] using incidenceLarge
  obtain ⟨v₀, v₁, v₀Degree, v₁Degree, rootedConclusion⟩ :=
    fixed_branch_frobenius_line_decodability p f points pointsInjective
      parent factor factorIrreducible factorPositive x₀ DH DR d b tau k
      agreementThreshold factorCoefficientBound generatorWeightEq globalBound
      tauEq ellLeDR dPositive ellDLeDR wLeB parentDegreeLe rootedChallenges
      rootedCandidate rootedSupport receivedConstant receivedLinear
      rootedSupportLarge rootedAgreement rootedCandidateDegree rootedLocalRoot
      rootedParentRoot rootedLeadingNeZero rootedDerivativeNeZero
      rootedIncidenceLarge
  refine ⟨v₀, v₁, v₀Degree, v₁Degree, ?_⟩
  intro source sourceMem
  let root := inverse source
  have rootMem : root ∈ rootedChallenges := by
    exact Finset.mem_image.mpr ⟨source, sourceMem, rfl⟩
  have conclusion := rootedConclusion root rootMem
  simpa only [rootedCandidate, root, inverse, q, frobeniusRoot_pow] using
    conclusion

#print axioms fixed_branch_frobenius_line_decodability_source_indexed

end

end WeightedHensel

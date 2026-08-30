/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FrobeniusCommonNumerator
import WeightedHensel.Interpolation

/-!
# Fixed-branch completion after inverse Frobenius

For an inseparable parent R(X, Y^q, Z), the separable Hensel recurrence is
run in the variable Ytilde = Y^q. A compatible root z lies above the source
challenge z^q. The powered received line is a^q + b^q Z^q; after the rooted
second resultant, interpolation recovers two degree-k polynomials and hence
the original line at every surviving source challenge.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- The powered received line in a compatible Frobenius-root challenge. -/
def frobeniusLineChallenge
    {K : Type*} [Field K] (q : Nat) (constant linear : K) : Polynomial K :=
  Polynomial.C constant + Polynomial.C linear * Polynomial.X ^ q

@[simp] theorem frobeniusLineChallenge_eval
    {K : Type*} [Field K] (q : Nat) (constant linear z : K) :
    (frobeniusLineChallenge q constant linear).eval z =
      constant + linear * z ^ q := by
  simp [frobeniusLineChallenge]

theorem frobeniusLineChallenge_natDegree_le
    {K : Type*} [Field K] (q : Nat) (constant linear : K) :
    (frobeniusLineChallenge q constant linear).natDegree ≤ q := by
  unfold frobeniusLineChallenge
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · refine Polynomial.natDegree_mul_le.trans ?_
    simp

/-- Scalar Lagrange interpolation on selected heavy coordinates. -/
def lagrangeScalarCurve
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (values : Domain → K) : Polynomial K :=
  Lagrange.interpolate nodes points values

theorem lagrangeScalarCurve_natDegree_le
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (values : Domain → K) (k : Nat) (nodesCard : nodes.card = k + 1) :
    (lagrangeScalarCurve nodes points values).natDegree ≤ k := by
  apply Polynomial.natDegree_le_iff_degree_le.mpr
  calc
    (lagrangeScalarCurve nodes points values).degree ≤
        (nodes.card - 1 : Nat) := by
      exact Lagrange.degree_interpolate_le values pointsInjectiveOn
    _ = (k : WithBot Nat) := by rw [nodesCard]; simp

theorem lagrangeScalarCurve_eval_at_node
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (values : Domain → K) (node : Domain) (nodeMem : node ∈ nodes) :
    (lagrangeScalarCurve nodes points values).eval (points node) =
      values node := by
  exact Lagrange.eval_interpolate_at_node values pointsInjectiveOn nodeMem

/-- The line through the two coefficientwise Lagrange interpolants. -/
def frobeniusLineCandidateCurve
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (constant linear : Domain → K) (q : Nat) (z : K) : Polynomial K :=
  lagrangeScalarCurve nodes points constant +
    Polynomial.C (z ^ q) * lagrangeScalarCurve nodes points linear

theorem frobeniusLineCandidateCurve_natDegree_le
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (constant linear : Domain → K) (q k : Nat)
    (nodesCard : nodes.card = k + 1) (z : K) :
    (frobeniusLineCandidateCurve nodes points constant linear q z).natDegree ≤
      k := by
  unfold frobeniusLineCandidateCurve
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact lagrangeScalarCurve_natDegree_le nodes points pointsInjectiveOn
      constant k nodesCard
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      (lagrangeScalarCurve_natDegree_le nodes points pointsInjectiveOn
        linear k nodesCard)

theorem frobeniusLineCandidateCurve_eval_at_node
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (constant linear : Domain → K) (q : Nat) (z : K)
    (node : Domain) (nodeMem : node ∈ nodes) :
    (frobeniusLineCandidateCurve nodes points constant linear q z).eval
        (points node) = constant node + linear node * z ^ q := by
  simp only [frobeniusLineCandidateCurve, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [lagrangeScalarCurve_eval_at_node nodes points pointsInjectiveOn
      constant node nodeMem,
    lagrangeScalarCurve_eval_at_node nodes points pointsInjectiveOn
      linear node nodeMem]
  ring

/-- A degree-k candidate matching a received line on k+1 nodes is its
coefficientwise Lagrange interpolation. -/
theorem candidate_eq_frobeniusLineCandidateCurve
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (constant linear : Domain → K) (q k : Nat)
    (nodesCard : nodes.card = k + 1)
    (z : K) (candidate : Polynomial K)
    (candidateDegree : candidate.natDegree ≤ k)
    (matchesNodes : ∀ node ∈ nodes,
      candidate.eval (points node) = constant node + linear node * z ^ q) :
    candidate =
      frobeniusLineCandidateCurve nodes points constant linear q z := by
  have rightDegree := frobeniusLineCandidateCurve_natDegree_le nodes points
    pointsInjectiveOn constant linear q k nodesCard z
  have leftDegreeLt : candidate.degree < (nodes.card : WithBot Nat) := by
    calc
      _ ≤ (k : WithBot Nat) :=
        Polynomial.degree_le_of_natDegree_le candidateDegree
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self k
  have rightDegreeLt :
      (frobeniusLineCandidateCurve nodes points constant linear q z).degree <
        (nodes.card : WithBot Nat) := by
    calc
      _ ≤ (k : WithBot Nat) :=
        Polynomial.degree_le_of_natDegree_le rightDegree
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self k
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq nodes
    pointsInjectiveOn leftDegreeLt rightDegreeLt
  intro node nodeMem
  rw [frobeniusLineCandidateCurve_eval_at_node nodes points pointsInjectiveOn
    constant linear q z node nodeMem]
  exact matchesNodes node nodeMem

/-- Fixed-branch completion for an inseparable factor.

Challenges are indexed by compatible roots z; the source branch and powered
candidate are specialized at z^q. Source nonvanishing is transported through
the Frobenius quotient equivalence rather than re-assumed for the rooted
branch. The conclusion is the original line at the source challenge z^q.
-/
theorem fixed_branch_frobenius_line_decodability
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
        receivedConstant coordinate +
          receivedLinear coordinate * z ^ frobeniusPower p f)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ k)
    (sourceLocalRoot : ∀ z ∈ challenges,
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          (((candidate z) ^ frobeniusPower p f).eval x₀) = 0)
    (sourceCandidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial (z ^ frobeniusPower p f)
        ((candidate z) ^ frobeniusPower p f) parent = 0)
    (sourceLeadingNeZero : ∀ z ∈ challenges,
      factor.leadingCoeff.eval (z ^ frobeniusPower p f) ≠ 0)
    (sourceDerivativeNeZero : ∀ (z) (zMem : z ∈ challenges),
      branchSpecialization factor factorPositive x₀
          (z ^ frobeniusPower p f)
          ((candidate z) ^ frobeniusPower p f)
          (sourceLocalRoot z zMem)
          (regularDerivativeElement parent factor x₀ d) ≠ 0)
    (incidenceLarge :
      k * challenges.card + Fintype.card Domain *
          (factor.natDegree *
            divisionFreeCeiling tau (sourceMu DR (frobeniusPower p f) d b)
              (k * frobeniusPower p f)) <
        challenges.card * (agreementThreshold + 1)) :
    ∃ v₀ v₁ : Polynomial K,
      v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
      ∀ z ∈ challenges,
        candidate z = v₀ + Polynomial.C (z ^ frobeniusPower p f) * v₁ := by
  classical
  let q := frobeniusPower p f
  let branchBudget := factor.natDegree *
    divisionFreeCeiling tau (sourceMu DR q d b) (k * q)
  have manyHeavy : k <
      (heavyCoordinates challenges support branchBudget).card := by
    apply maximumDegree_lt_card_heavyCoordinates challenges support
      agreementThreshold k branchBudget supportLarge
    simpa only [q, branchBudget] using incidenceLarge
  obtain ⟨nodes, nodesSubset, nodesCard⟩ :=
    Finset.exists_subset_card_eq
      (s := heavyCoordinates challenges support branchBudget)
      (n := k + 1) (by omega)
  have pointsInjectiveOn : Set.InjOn points nodes := pointsInjective.injOn
  have nodeDiscrepancyZero : ∀ node ∈ nodes,
      frobeniusRootedDiscrepancy p f parent factor factorIrreducible.ne_zero
        x₀ d k (points node)
        (frobeniusLineChallenge q (receivedConstant node)
          (receivedLinear node)) = 0 := by
    intro node nodeMem
    let fiber := supportFiber challenges support node
    have nodeHeavy := nodesSubset nodeMem
    have fiberLarge : branchBudget < fiber.card :=
      (Finset.mem_filter.mp nodeHeavy).2
    apply frobeniusRootedDiscrepancy_eq_zero_of_many_branches p f parent
      factor factorIrreducible factorPositive x₀ (points node) q DH DR d b tau
      k factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
      dPositive ellDLeDR wLeB parentDegreeLe
      (frobeniusLineChallenge q (receivedConstant node)
        (receivedLinear node))
      (frobeniusLineChallenge_natDegree_le q (receivedConstant node)
        (receivedLinear node))
      fiber candidate
    · intro z zMem
      exact sourceLocalRoot z (Finset.mem_filter.mp zMem).1
    · intro z zMem
      exact sourceCandidateRoot z (Finset.mem_filter.mp zMem).1
    · intro z zMem
      exact candidateDegree z (Finset.mem_filter.mp zMem).1
    · intro z zMem
      rw [frobeniusLineChallenge_eval]
      exact (agreement z (Finset.mem_filter.mp zMem).1 node
        (Finset.mem_filter.mp zMem).2).symm
    · simpa only [fiber, branchBudget, q] using fiberLarge
  let v₀ := lagrangeScalarCurve nodes points receivedConstant
  let v₁ := lagrangeScalarCurve nodes points receivedLinear
  refine ⟨v₀, v₁, ?_, ?_, ?_⟩
  · exact lagrangeScalarCurve_natDegree_le nodes points pointsInjectiveOn
      receivedConstant k nodesCard
  · exact lagrangeScalarCurve_natDegree_le nodes points pointsInjectiveOn
      receivedLinear k nodesCard
  · intro z zMem
    change candidate z =
      frobeniusLineCandidateCurve nodes points receivedConstant receivedLinear
        q z
    apply candidate_eq_frobeniusLineCandidateCurve nodes points
      pointsInjectiveOn receivedConstant receivedLinear q k nodesCard z
      (candidate z) (candidateDegree z zMem)
    intro node nodeMem
    have rootedLeadingNeZero :
        (bivariateFrobeniusRoot p f factor).leadingCoeff.eval z ≠ 0 := by
      intro rootedZero
      have compatibility :=
        eval_leadingCoeff_bivariateFrobeniusRoot_pow p f factor z
      rw [rootedZero, zero_pow (frobeniusPower_ne_zero p f)] at compatibility
      exact sourceLeadingNeZero z zMem compatibility.symm
    have rootedEtaNeZero :
        branchSpecialization
            (bivariateFrobeniusRoot p f factor)
            (by simpa using factorPositive)
            x₀ z (candidate z)
            (bivariateFrobeniusRoot_localRoot p f factor x₀ z (candidate z)
              (sourceLocalRoot z zMem))
            (frobeniusRootedEta p f parent factor factorIrreducible.ne_zero
              x₀ d) ≠ 0 := by
      exact branchSpecialization_regularFrobeniusRootEquiv_ne_zero p f factor
        factorIrreducible.ne_zero factorPositive x₀ z (candidate z)
        (sourceLocalRoot z zMem)
        (regularDerivativeElement parent factor x₀ d)
        (sourceDerivativeNeZero z zMem)
    rw [← frobeniusLineChallenge_eval]
    apply candidate_eval_eq_challenge_eval_of_frobeniusRootedDiscrepancy_eq_zero
      p f parent factor factorIrreducible.ne_zero factorPositive x₀ z
      (candidate z) d k dPositive parentDegreeLe (sourceLocalRoot z zMem)
      (sourceCandidateRoot z zMem) (candidateDegree z zMem)
      rootedLeadingNeZero rootedEtaNeZero (points node)
      (frobeniusLineChallenge q (receivedConstant node)
        (receivedLinear node))
      (nodeDiscrepancyZero node nodeMem)

#print axioms frobeniusLineChallenge_natDegree_le
#print axioms candidate_eq_frobeniusLineCandidateCurve
#print axioms fixed_branch_frobenius_line_decodability

end

end WeightedHensel

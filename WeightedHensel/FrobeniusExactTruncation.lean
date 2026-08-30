/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FrobeniusTruncation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Exact sparse Frobenius truncation

The first resultant kills both kinds of forbidden source coefficient:
orders above `q * k`, and orders not divisible by `q = p ^ f`.  The usual
finite-degree argument then identifies the source Hensel lift with an exact
sparse polynomial.  Contracting the exponents by `q` gives degree at most
`k`; after embedding in an algebraic closure, coefficientwise inverse
Frobenius gives a literal `q`-th root of that exact polynomial.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Coefficientwise inverse Frobenius over any perfect field. -/
def perfectPolynomialFrobeniusRoot
    {E : Type*} [Field E] [PerfectField E]
    (p f : Nat) [Fact p.Prime] [CharP E p]
    (polynomial : Polynomial E) : Polynomial E :=
  polynomial.map (iterateFrobeniusEquiv E p f).symm

/-- Raising the coefficientwise inverse-Frobenius polynomial to `p^f`
produces its sparse exponent expansion. -/
theorem perfectPolynomialFrobeniusRoot_pow
    {E : Type*} [Field E] [PerfectField E]
    (p f : Nat) [Fact p.Prime] [CharP E p]
    (polynomial : Polynomial E) :
    perfectPolynomialFrobeniusRoot p f polynomial ^ frobeniusPower p f =
      Polynomial.expand E (frobeniusPower p f) polynomial := by
  let inverse : E →+* E := (iterateFrobeniusEquiv E p f).symm
  have mapped :=
    Polynomial.map_iterateFrobenius_expand
      p (polynomial.map inverse) f
  rw [Polynomial.map_expand, Polynomial.map_map] at mapped
  have composition :
      (iterateFrobenius E p f).comp inverse = RingHom.id E := by
    ext value
    exact (iterateFrobeniusEquiv E p f).apply_symm_apply value
  rw [composition, Polynomial.map_id] at mapped
  exact mapped.symm

@[simp] theorem natDegree_perfectPolynomialFrobeniusRoot
    {E : Type*} [Field E] [PerfectField E]
    (p f : Nat) [Fact p.Prime] [CharP E p]
    (polynomial : Polynomial E) :
    (perfectPolynomialFrobeniusRoot p f polynomial).natDegree =
      polynomial.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (iterateFrobeniusEquiv E p f).symm.injective polynomial

/-- Contract the exact source Hensel polynomial along the indices divisible
by `q`. -/
def frobeniusContractedHenselPolynomial
    {L : Type*} [Field L]
    (p f k : Nat) (root : PowerSeries L) : Polynomial L :=
  Polynomial.contract (frobeniusPower p f)
    (henselTruncation (frobeniusPower p f * k) root)

/-- A sparse exact Hensel polynomial has a literal `q`-th root after the
canonical embedding into its algebraic closure. -/
def algebraicClosureHenselRoot
    {L : Type*} [Field L]
    (p f k : Nat) [Fact p.Prime] [CharP L p]
    (root : PowerSeries L) : Polynomial (AlgebraicClosure L) :=
  perfectPolynomialFrobeniusRoot p f
    ((frobeniusContractedHenselPolynomial p f k root).map
      (algebraMap L (AlgebraicClosure L)))

/-- Complete sparse truncation theorem for the inseparable source branch.

It returns the actual simple-root Hensel series, vanishing of every
forbidden coefficient below the global `X` cutoff, the exact source
polynomial root, its exponent contraction of degree at most `k`, and the
literal `q`-th root in an algebraic closure. -/
theorem exists_exact_sparse_henselTruncation_of_many_frobenius_branches
    {K : Type*} [Field K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (DH DR d b tau k xBound : Nat)
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
    (factorDvd : factor ∣ specializeX x₀ parent)
    (etaNeZero : regularDerivativeElement parent factor x₀ d ≠ 0)
    (poweredDegreeLt : frobeniusPower p f * k < xBound)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z)
        (((candidate z) ^ frobeniusPower p f).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z
        ((candidate z) ^ frobeniusPower p f) parent = 0)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ k)
    (manyBranches : ∀ order,
      (frobeniusPower p f * k < order ∨
        ¬frobeniusPower p f ∣ order) →
      order < xBound →
      factor.natDegree *
          divisionFreeCeiling tau
            (sourceMu DR (frobeniusPower p f) d b) order <
        challenges.card)
    (substitutionDegreeBound :
      ∀ gamma : Polynomial (BranchFunctionField factor),
        gamma.natDegree ≤ frobeniusPower p f * k →
          ((functionFieldPolynomialParent parent factor x₀).eval gamma).natDegree <
            xBound) :
    ∃ root : PowerSeries (BranchFunctionField factor),
      (functionFieldShiftedParent parent factor x₀).IsRoot root ∧
      PowerSeries.constantCoeff root =
        AdjoinRoot.root (branchPolynomial factor) ∧
      (∀ order,
        (frobeniusPower p f * k < order ∨
          ¬frobeniusPower p f ∣ order) →
        order < xBound → PowerSeries.coeff order root = 0) ∧
      (henselTruncation (frobeniusPower p f * k) root).natDegree ≤
        frobeniusPower p f * k ∧
      (functionFieldPolynomialParent parent factor x₀).IsRoot
        (henselTruncation (frobeniusPower p f * k) root) ∧
      (frobeniusContractedHenselPolynomial p f k root).natDegree ≤ k ∧
      Polynomial.expand (BranchFunctionField factor) (frobeniusPower p f)
          (frobeniusContractedHenselPolynomial p f k root) =
        henselTruncation (frobeniusPower p f * k) root ∧
      ∃ rooted : Polynomial (AlgebraicClosure (BranchFunctionField factor)),
        rooted.natDegree ≤ k ∧
        rooted ^ frobeniusPower p f =
          (henselTruncation (frobeniusPower p f * k) root).map
            (algebraMap (BranchFunctionField factor)
              (AlgebraicClosure (BranchFunctionField factor))) := by
  let q := frobeniusPower p f
  have qPositive : 0 < q := frobeniusPower_pos p f
  have qNeZero : q ≠ 0 := Nat.ne_of_gt qPositive
  have poweredCandidateDegree : ∀ z ∈ challenges,
      ((candidate z) ^ q).natDegree ≤ q * k := by
    intro z zMem
    exact natDegree_frobeniusPower_le p f k (candidate z)
      (candidateDegree z zMem)
  obtain ⟨root, rootEquation, rootConstant, finiteDegree, finiteRoot⟩ :=
    exists_exact_henselTruncation_of_many_branches parent factor
      factorIrreducible factorPositive x₀ q DH DR d b tau (q * k) xBound
      factorCoefficientBound generatorWeightEq globalBound tauEq ellLeDR
      dPositive ellDLeDR wLeB parentDegreeLe factorDvd etaNeZero
      poweredDegreeLt challenges (fun z ↦ (candidate z) ^ q) localRoot
      candidateRoot poweredCandidateDegree
      (fun order aboveDegree belowCutoff ↦
        manyBranches order (Or.inl aboveDegree) belowCutoff)
      substitutionDegreeBound
  have deltaImage : ∀ order,
      regularToFunctionField factor factorPositive
          (parentDivisionFreeCoefficients parent factor x₀ d order) =
        regularToFunctionField factor factorPositive
              (regularLeadingCoefficient factor) *
          regularToFunctionField factor factorPositive
              (regularDerivativeElement parent factor x₀ d) ^
            henselExponent order * PowerSeries.coeff order root := by
    intro order
    exact parentDivisionFreeCoefficients_image_of_root parent factor
      factorPositive x₀ d dPositive parentDegreeLe root rootEquation
      rootConstant order
  have forbiddenZero : ∀ order,
      (q * k < order ∨ ¬q ∣ order) → order < xBound →
        PowerSeries.coeff order root = 0 := by
    intro order forbidden belowCutoff
    have deltaZero :=
      parentDivisionFreeCoefficients_eq_zero_of_many_frobenius_branches
        parent factor factorIrreducible factorPositive p f x₀ q DH DR d b tau
        k order factorCoefficientBound generatorWeightEq globalBound tauEq
        ellLeDR dPositive ellDLeDR wLeB parentDegreeLe challenges candidate
        localRoot candidateRoot candidateDegree forbidden
        (manyBranches order forbidden belowCutoff)
    exact henselCoefficient_eq_zero_of_cleared_eq_zero factor
      factorIrreducible.ne_zero factorPositive
      (regularDerivativeElement parent factor x₀ d) etaNeZero
      (parentDivisionFreeCoefficients parent factor x₀ d)
      (fun t ↦ PowerSeries.coeff t root) deltaImage order deltaZero
  let finitePolynomial := henselTruncation (q * k) root
  let contracted := Polynomial.contract q finitePolynomial
  have contractedDegree : contracted.natDegree ≤ k := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro order orderLarge
    rw [show contracted.coeff order = finitePolynomial.coeff (order * q) by
      exact Polynomial.coeff_contract qNeZero finitePolynomial order]
    unfold finitePolynomial henselTruncation
    rw [PowerSeries.coeff_trunc]
    have notBelow : ¬order * q < q * k + 1 := by
      have productLarge : q * k < order * q := by
        calc
          q * k = k * q := Nat.mul_comm q k
          _ < order * q :=
            (Nat.mul_lt_mul_right qPositive).2 orderLarge
      omega
    simp only [if_neg notBelow]
  have expandContracted :
      Polynomial.expand (BranchFunctionField factor) q contracted =
        finitePolynomial := by
    ext order
    rw [Polynomial.coeff_expand qPositive,
      Polynomial.coeff_contract qNeZero]
    split_ifs with divisible
    · rw [Nat.div_mul_cancel divisible]
    · unfold finitePolynomial henselTruncation
      rw [PowerSeries.coeff_trunc]
      split_ifs with belowTruncation
      · have orderLe : order ≤ q * k := by omega
        have qkLt : q * k < xBound := by
          simpa only [q] using poweredDegreeLt
        exact (forbiddenZero order (Or.inr divisible)
          (orderLe.trans_lt qkLt)).symm
      · rfl
  letI : CharP (BranchFunctionField factor) p :=
    charP_of_injective_ringHom (branchBaseMap factor).injective p
  let rooted : Polynomial (AlgebraicClosure (BranchFunctionField factor)) :=
    algebraicClosureHenselRoot p f k root
  have closureRootDegree :
      rooted.natDegree ≤ k := by
    unfold rooted
    rw [algebraicClosureHenselRoot,
      natDegree_perfectPolynomialFrobeniusRoot]
    rw [Polynomial.natDegree_map_eq_of_injective
      (algebraMap (BranchFunctionField factor)
        (AlgebraicClosure (BranchFunctionField factor))).injective]
    exact contractedDegree
  have closureRootPower :
      rooted ^ q =
        finitePolynomial.map
          (algebraMap (BranchFunctionField factor)
            (AlgebraicClosure (BranchFunctionField factor))) := by
    unfold rooted
    rw [algebraicClosureHenselRoot,
      perfectPolynomialFrobeniusRoot_pow]
    rw [← Polynomial.map_expand]
    exact congrArg
      (Polynomial.map
        (algebraMap (BranchFunctionField factor)
          (AlgebraicClosure (BranchFunctionField factor))))
      (by simpa only [q, frobeniusContractedHenselPolynomial,
          finitePolynomial, contracted] using expandContracted)
  refine ⟨root, rootEquation, rootConstant, ?_, finiteDegree, finiteRoot,
    ?_, ?_, rooted, closureRootDegree, ?_⟩
  · simpa only [q] using forbiddenZero
  · simpa only [frobeniusContractedHenselPolynomial, q, finitePolynomial,
      contracted] using contractedDegree
  · simpa only [frobeniusContractedHenselPolynomial, q, finitePolynomial,
      contracted] using expandContracted
  · simpa only [q, finitePolynomial] using closureRootPower

#print axioms perfectPolynomialFrobeniusRoot_pow
#print axioms exists_exact_sparse_henselTruncation_of_many_frobenius_branches

end

end WeightedHensel

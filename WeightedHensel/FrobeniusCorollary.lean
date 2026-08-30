/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FrobeniusExactTruncation
import WeightedHensel.FrobeniusReindex
import WeightedHensel.FrobeniusSubstitutionDegree

/-!
# The inseparable Frobenius extension

This module composes the full-factor transfer, sparse Hensel truncation,
compatible Frobenius roots, the second resultant, and source-indexed
interpolation.  It is the formal counterpart of Corollary 7.11.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- The paper-facing substitution-degree condition with its function-field
instance derived from branch irreducibility. -/
def FrobeniusSubstitutionDegreeBound
    {K : Type*} [Field K]
    (p f k DX : Nat) (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree) (x₀ : K) : Prop := by
  letI : Fact (Irreducible (branchPolynomial factor)) :=
    ⟨branchPolynomial_irreducible factor factorIrreducible factorPositive⟩
  exact ∀ gamma : Polynomial (BranchFunctionField factor),
    gamma.natDegree ≤ frobeniusPower p f * k →
      ((functionFieldPolynomialParent parent factor x₀).eval
        gamma).natDegree < DX

/-- The exact sparse Hensel completion produced in the proof of
Corollary 7.11.  This is a transparent abbreviation for the full
mathematical conclusion, not an oracle proposition. -/
def SparseFrobeniusCompletion
    {K : Type*} [Field K]
    (p f k DX : Nat) (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree) (x₀ : K) : Prop := by
  letI : Fact (Irreducible (branchPolynomial factor)) :=
    ⟨branchPolynomial_irreducible factor factorIrreducible factorPositive⟩
  exact
  ∃ root : PowerSeries (BranchFunctionField factor),
    (functionFieldShiftedParent parent factor x₀).IsRoot root ∧
    PowerSeries.constantCoeff root =
      AdjoinRoot.root (branchPolynomial factor) ∧
    (∀ order,
      (frobeniusPower p f * k < order ∨
        ¬frobeniusPower p f ∣ order) →
      order < DX → PowerSeries.coeff order root = 0) ∧
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
            (AlgebraicClosure (BranchFunctionField factor)))

/-- The source-indexed line conclusion of Corollary 7.11. -/
def SourceLineCompletion
    {K : Type*} [Field K] (k : Nat)
    (challenges : Finset K) (candidate : K → Polynomial K) : Prop :=
  ∃ v₀ v₁ : Polynomial K,
    v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
    ∀ z ∈ challenges,
      candidate z = v₀ + Polynomial.C z * v₁

/-- Completion of one branch selected by the global factor summation.

All local Hensel parameters are derived from the single full weighted
degree `G`: `d = deg_Y parent`, `h = deg_Y factor`,
`b = G-qh`, and `tau = b+q`.  The surviving-cardinality estimate proves
every first-resultant inequality below `DX`.  The final line conclusion is
conditional only on the explicit incidence inequality used in the paper.
-/
theorem selected_frobenius_branch_completion
    {K Domain : Type*} [Field K] [Finite K] [Fintype Domain]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (points : Domain → K) (pointsInjective : Function.Injective points)
    (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ : K) (k DX reserve agreementThreshold : Nat)
    (factorWeightLe : localBivariateWeight (frobeniusPower p f) factor ≤
      fullYZWeightedDegree (frobeniusPower p f) parent)
    (parentNeZero : parent ≠ 0)
    (parentPositive : 1 ≤ parent.natDegree)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (etaNeZero : regularDerivativeElement parent factor x₀
      parent.natDegree ≠ 0)
    (poweredDegreeLt : frobeniusPower p f * k < DX)
    (substitutionDegreeBound :
      FrobeniusSubstitutionDegreeBound p f k DX parent factor
        factorIrreducible factorPositive x₀)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (localRoot : ∀ z ∈ challenges,
      factor.eval₂ (Polynomial.evalRingHom z)
        (((candidate z) ^ frobeniusPower p f).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z
        ((candidate z) ^ frobeniusPower p f) parent = 0)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ k)
    (leadingNeZero : ∀ z ∈ challenges,
      factor.leadingCoeff.eval z ≠ 0)
    (derivativeValueNeZero : ∀ z ∈ challenges,
      specializedDerivativeValue parent x₀ z
        (shiftedCandidateSeries x₀
          ((candidate z) ^ frobeniusPower p f))
        parent.natDegree ≠ 0)
    (cardLarge :
      (2 * DX - 1) *
          (parent.natDegree * factor.natDegree *
            fullYZWeightedDegree (frobeniusPower p f) parent) +
        reserve < challenges.card)
    (support : K → Finset Domain)
    (receivedConstant receivedLinear : Domain → K)
    (supportLarge : ∀ z ∈ challenges,
      agreementThreshold < (support z).card)
    (agreement : ∀ z ∈ challenges, ∀ coordinate ∈ support z,
      (candidate z).eval (points coordinate) =
        receivedConstant coordinate + receivedLinear coordinate * z) :
    SparseFrobeniusCompletion p f k DX parent factor factorIrreducible
      factorPositive x₀ ∧
    ((k * challenges.card + Fintype.card Domain *
          (factor.natDegree *
            divisionFreeCeiling
              (fullYZWeightedDegree (frobeniusPower p f) parent -
                  frobeniusPower p f * factor.natDegree +
                frobeniusPower p f)
              (sourceMu
                (fullYZWeightedDegree (frobeniusPower p f) parent)
                (frobeniusPower p f) parent.natDegree
                (fullYZWeightedDegree (frobeniusPower p f) parent -
                  frobeniusPower p f * factor.natDegree))
              (k * frobeniusPower p f)) <
        challenges.card * (agreementThreshold + 1)) →
      SourceLineCompletion k challenges candidate) := by
  classical
  let q := frobeniusPower p f
  let G := fullYZWeightedDegree q parent
  let d := parent.natDegree
  let h := factor.natDegree
  let b := G - q * h
  let tau := b + q
  have qPositive : 1 ≤ q := frobeniusPower_pos p f
  have dPositive : 1 ≤ d := by simpa only [d] using parentPositive
  have hPositive : 1 ≤ h := by
    dsimp only [h]
    omega
  have parentCoefficientBound : ParentCoefficientBound parent q G := by
    exact parentCoefficientBound_fullYZWeightedDegree q parent
  have parentLeadingMem : d ∈ parent.support := by
    exact Polynomial.natDegree_mem_support_of_nonzero parentNeZero
  have qdLeG : q * d ≤ G := by
    have leadingBound := parentCoefficientBound d parentLeadingMem
    omega
  have qLeG : q ≤ G := by
    have qLeQd : q ≤ q * d := Nat.le_mul_of_pos_right q dPositive
    exact qLeQd.trans qdLeG
  have GPositive : 1 ≤ G := qPositive.trans qLeG
  have factorNeZero : factor ≠ 0 := factorIrreducible.ne_zero
  have factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + q * exponent ≤ G := by
    intro exponent exponentMem
    simpa only [G, q, Nat.mul_comm] using
      (coeff_weight_le_localBivariateWeight q factor exponent
        exponentMem).trans factorWeightLe
  have factorLeadingMem : h ∈ factor.support := by
    exact Polynomial.natDegree_mem_support_of_nonzero factorNeZero
  have leadingBound :
      factor.leadingCoeff.natDegree + q * h ≤ G := by
    simpa [h] using factorCoefficientBound h factorLeadingMem
  have wLeB : factor.leadingCoeff.natDegree ≤ b := by
    dsimp [b]
    omega
  have generatorWeightEq : G + q - q * h = tau := by
    dsimp [tau, b]
    omega
  have tauLe : tau ≤ G := by
    exact sourceTau_le_commonDegree G G q h tau le_rfl hPositive
      generatorWeightEq.symm
  have muLe : sourceMu G q d b ≤ d * G := by
    exact sourceMu_le_commonDegree G G G q h d (sourceMu G q d b)
      le_rfl le_rfl dPositive (by rfl)
  have allCoefficientResultants : ∀ order,
      (q * k < order ∨ ¬q ∣ order) → order < DX →
        h * divisionFreeCeiling tau (sourceMu G q d b) order <
          challenges.card := by
    intro order forbidden belowCutoff
    have orderPositive : 0 < order := by
      rcases forbidden with aboveDegree | notDivisible
      · omega
      · by_contra notPositive
        have orderZero : order = 0 := Nat.eq_zero_of_not_pos notPositive
        subst order
        exact notDivisible (dvd_zero q)
    have coarse := weightedDivisionFreeBudget_lt_coarse
      h tau (sourceMu G q d b) d G order hPositive orderPositive
      dPositive GPositive tauLe muLe
    have coefficientLe : 2 * order + 1 ≤ 2 * DX - 1 := by omega
    calc
      h * divisionFreeCeiling tau (sourceMu G q d b) order <
          h * ((2 * order + 1) * d * G) := coarse
      _ = (2 * order + 1) * (d * h * G) := by ring
      _ ≤ (2 * DX - 1) * (d * h * G) :=
        Nat.mul_le_mul_right (d * h * G) coefficientLe
      _ ≤ (2 * DX - 1) * (d * h * G) + reserve :=
        Nat.le_add_right _ _
      _ < challenges.card := by
        simpa only [d, h, G] using cardLarge
  letI : Fact (Irreducible (branchPolynomial factor)) :=
    ⟨branchPolynomial_irreducible factor factorIrreducible factorPositive⟩
  have substitutionDegreeBound' :
      ∀ gamma : Polynomial (BranchFunctionField factor),
        gamma.natDegree ≤ q * k →
          ((functionFieldPolynomialParent parent factor x₀).eval
            gamma).natDegree < DX := by
    simpa only [FrobeniusSubstitutionDegreeBound, q] using
      substitutionDegreeBound
  have sparse : SparseFrobeniusCompletion p f k DX parent factor
      factorIrreducible factorPositive x₀ := by
    simpa only [SparseFrobeniusCompletion] using
      (exists_exact_sparse_henselTruncation_of_many_frobenius_branches
      p f parent factor factorIrreducible factorPositive x₀ G G d b tau k
      DX factorCoefficientBound generatorWeightEq parentCoefficientBound rfl
      qLeG dPositive qdLeG wLeB (by rfl) factorDvd etaNeZero
      poweredDegreeLt challenges candidate localRoot candidateRoot
      candidateDegree allCoefficientResultants substitutionDegreeBound')
  refine ⟨sparse, ?_⟩
  intro incidenceLarge
  have sourceDerivativeNeZero : ∀ z (zMem : z ∈ challenges),
      branchSpecialization factor factorPositive x₀ z
          ((candidate z) ^ q) (localRoot z zMem)
          (regularDerivativeElement parent factor x₀ d) ≠ 0 := by
    intro z zMem
    rw [branchSpecialization_regularDerivativeElement]
    exact mul_ne_zero
      (pow_ne_zero _ (leadingNeZero z zMem))
      (derivativeValueNeZero z zMem)
  exact fixed_branch_frobenius_line_decodability_source_indexed
    p f points pointsInjective parent factor factorIrreducible factorPositive
    x₀ G G d b tau k agreementThreshold factorCoefficientBound
    generatorWeightEq parentCoefficientBound rfl qLeG dPositive qdLeG wLeB
    (by rfl) challenges candidate support receivedConstant receivedLinear
    supportLarge agreement candidateDegree localRoot candidateRoot
    leadingNeZero sourceDerivativeNeZero (by
      simpa only [q, G, d, h, b, tau] using incidenceLarge)

/-- Corollary 7.11: full inseparable-factor transfer and Frobenius line
completion.

The global threshold selects a separable parent in `Ye`, an irreducible
branch, and a surviving source-indexed challenge set.  The theorem derives
the shifted coefficient bound, equation (137), the exact sparse Hensel
root and its compatible `q`-th root.  Under precisely the displayed
support-incidence inequality, it also returns the original source line.
-/
theorem inseparable_frobenius_curve_decodability
    {K Domain I J : Type*} [Field K] [Finite K] [Fintype Domain]
    [DecidableEq I] [DecidableEq J]
    (p : Nat) [Fact p.Prime] [CharP K p]
    (f : I → Nat)
    (points : Domain → K) (pointsInjective : Function.Injective points)
    (indices : Finset I) (branchIndices : I → Finset J)
    (Q : TrivariatePolynomial K) (globalContent : BivariatePolynomial K)
    (parent : I → TrivariatePolynomial K)
    (multiplicity : I → Nat)
    (x₀ : K) (content : I → Polynomial K)
    (branch : I → J → BivariatePolynomial K)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (DX DY DZ B k agreementThreshold : Nat)
    (DXPositive : 1 ≤ DX) (DYPositive : 1 ≤ DY)
    (DZPositive : 1 ≤ DZ) (BPositive : 1 ≤ B)
    (globalContentNeZero : globalContent ≠ 0)
    (parentNeZero : ∀ index, index ∈ indices → parent index ≠ 0)
    (parentPositive : ∀ index, index ∈ indices →
      1 ≤ (parent index).natDegree)
    (multiplicityPositive : ∀ index, index ∈ indices →
      1 ≤ multiplicity index)
    (globalFactorization : Q = Polynomial.C globalContent *
      ∏ index ∈ indices,
        expandResponse (frobeniusPower p (f index)) (parent index) ^
          multiplicity index)
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
    (QXYDegree : fullXYWeightedDegree k Q < DX)
    (candidateRoot : ∀ z, z ∈ challenges →
      challengeCandidatePolynomial z (candidate z) Q = 0)
    (candidateDegree : ∀ z, z ∈ challenges →
      (candidate z).natDegree ≤ k)
    (challengeCountLarge :
      2 * DX * DY ^ 2 * DZ + B * DY < challenges.card)
    (support : K → Finset Domain)
    (receivedConstant receivedLinear : Domain → K)
    (supportLarge : ∀ z ∈ challenges,
      agreementThreshold < (support z).card)
    (agreement : ∀ z ∈ challenges, ∀ coordinate ∈ support z,
      (candidate z).eval (points coordinate) =
        receivedConstant coordinate + receivedLinear coordinate * z) :
    ∃ index,
      index ∈ activeFactorIndices indices branchIndices ∧
      ∃ branchIndex, branchIndex ∈ branchIndices index ∧
      ∃ surviving : Finset K,
        (∀ order yExponent,
          shiftedParentCoefficient x₀ order yExponent (parent index) ≠ 0 →
          (shiftedParentCoefficient x₀ order yExponent
              (parent index)).natDegree +
              frobeniusPower p (f index) * yExponent ≤
            fullYZWeightedDegree (frobeniusPower p (f index))
              (parent index)) ∧
        (2 * DX - 1) *
              ((parent index).natDegree *
                (branch index branchIndex).natDegree *
                  fullYZWeightedDegree (frobeniusPower p (f index))
                    (parent index)) +
            B < surviving.card ∧
        (∀ z, z ∈ surviving →
          z ∈ challenges ∧
          challengeCandidatePolynomial z
            ((candidate z) ^ frobeniusPower p (f index))
            (parent index) = 0 ∧
          (content index).eval z ≠ 0 ∧
          ∃ localRoot :
              (branch index branchIndex).eval₂
                (Polynomial.evalRingHom z)
                (((candidate z) ^ frobeniusPower p (f index)).eval x₀) = 0,
            (branch index branchIndex).leadingCoeff.eval z ≠ 0 ∧
            specializedDerivativeValue (parent index) x₀ z
              (shiftedCandidateSeries x₀
                ((candidate z) ^ frobeniusPower p (f index)))
              (parent index).natDegree ≠ 0) ∧
        (∃ selectedIrreducible : Irreducible (branch index branchIndex),
          ∃ selectedPositive : 0 < (branch index branchIndex).natDegree,
            SparseFrobeniusCompletion p (f index) k DX (parent index)
              (branch index branchIndex) selectedIrreducible
              selectedPositive x₀) ∧
        ((k * surviving.card + Fintype.card Domain *
              ((branch index branchIndex).natDegree *
                divisionFreeCeiling
                  (fullYZWeightedDegree (frobeniusPower p (f index))
                        (parent index) -
                      frobeniusPower p (f index) *
                        (branch index branchIndex).natDegree +
                    frobeniusPower p (f index))
                  (sourceMu
                    (fullYZWeightedDegree (frobeniusPower p (f index))
                      (parent index))
                    (frobeniusPower p (f index))
                    (parent index).natDegree
                    (fullYZWeightedDegree (frobeniusPower p (f index))
                        (parent index) -
                      frobeniusPower p (f index) *
                        (branch index branchIndex).natDegree))
                  (k * frobeniusPower p (f index))) <
            surviving.card * (agreementThreshold + 1)) →
          SourceLineCompletion k surviving candidate) := by
  classical
  let q : I → Nat := fun index ↦ frobeniusPower p (f index)
  have qPositive : ∀ index, index ∈ indices → 0 < q index := by
    intro index _
    exact frobeniusPower_pos p (f index)
  have globalMultiplierPositive : 1 ≤ 2 * DX * DY ^ 2 := by
    have twoDXPositive : 0 < 2 * DX :=
      Nat.mul_pos (by omega) DXPositive
    have dySquarePositive : 0 < DY ^ 2 := pow_pos DYPositive 2
    exact (Nat.mul_pos twoDXPositive dySquarePositive)
  have transferCount :
      2 * DX * DY ^ 2 * DZ + ((B - 1) + 1) * DY <
        challenges.card := by
    rwa [Nat.sub_add_cancel BPositive]
  obtain ⟨index, indexActive, branchIndex, branchIndexMem, surviving,
      shiftedBound, survivingLargeRaw, survivingData⟩ :=
    full_factor_frobenius_degree_transfer indices branchIndices Q
      globalContent parent q multiplicity x₀ content branch challenges
      candidate DX DY DZ (B - 1) qPositive globalContentNeZero parentNeZero
      parentPositive multiplicityPositive (by
        simpa only [q] using globalFactorization)
      contentNeZero branchNeZero branchPositive branchIrreducible
      specializationFactorization specializedSeparable QYDegree
      QWeightedDegree globalMultiplierPositive candidateRoot transferCount
  have indexMem : index ∈ indices :=
    (Finset.mem_filter.mp indexActive).1
  let selectedParent := parent index
  let selectedFactor := branch index branchIndex
  let selectedQ := q index
  let selectedG := fullYZWeightedDegree selectedQ selectedParent
  have selectedFactorIrreducible : Irreducible selectedFactor := by
    exact branchIrreducible index indexMem branchIndex branchIndexMem
  have selectedFactorPositive : 0 < selectedFactor.natDegree := by
    exact branchPositive index indexMem branchIndex branchIndexMem
  have selectedFactorWeight :
      localBivariateWeight selectedQ selectedFactor ≤ selectedG := by
    have termLe : localBivariateWeight selectedQ selectedFactor ≤
        ∑ candidateBranch ∈ branchIndices index,
          localBivariateWeight selectedQ (branch index candidateBranch) :=
      Finset.single_le_sum
        (f := fun candidateBranch ↦
          localBivariateWeight selectedQ (branch index candidateBranch))
        (fun _ _ ↦ Nat.zero_le _) branchIndexMem
    have sumBound := specialization_content_branch_weight_summation
      (parent index) x₀ selectedQ (branchIndices index) (content index)
      (branch index) (contentNeZero index indexMem)
      (branchNeZero index indexMem)
      (specializationFactorization index indexMem)
    dsimp only [selectedFactor, selectedParent, selectedG] at *
    omega
  have selectedFactorDvd : selectedFactor ∣
      specializeX x₀ selectedParent := by
    dsimp only [selectedFactor, selectedParent]
    rw [specializationFactorization index indexMem]
    exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (branch index) branchIndexMem)
      (Polynomial.C (content index))
  have selectedEtaNeZero :
      regularDerivativeElement selectedParent selectedFactor x₀
        selectedParent.natDegree ≠ 0 := by
    exact regularDerivativeElement_ne_zero_of_specialized_separable
      selectedParent selectedFactor selectedFactorIrreducible
      selectedFactorPositive x₀ selectedParent.natDegree le_rfl
      selectedFactorDvd (specializedSeparable index indexMem)
  have selectedOrder := frobenius_parent_order_lt_global_XY_degree
    indices Q globalContent parent q multiplicity globalContentNeZero
    parentNeZero qPositive multiplicityPositive parentPositive (by
      simpa only [q] using globalFactorization)
    k DX QXYDegree index indexMem
  have selectedPoweredDegreeLt : selectedQ * k < DX := by
    simpa only [selectedQ] using selectedOrder.2
  letI : Fact (Irreducible (branchPolynomial selectedFactor)) :=
    ⟨branchPolynomial_irreducible selectedFactor
      selectedFactorIrreducible selectedFactorPositive⟩
  have selectedSubstitutionRaw :
      ∀ gamma : Polynomial (BranchFunctionField selectedFactor),
        gamma.natDegree ≤ selectedQ * k →
          ((functionFieldPolynomialParent selectedParent selectedFactor x₀).eval
            gamma).natDegree < DX := by
    exact frobenius_substitutionDegreeBound indices Q globalContent parent q
      multiplicity globalContentNeZero parentNeZero qPositive
      multiplicityPositive (by simpa only [q] using globalFactorization)
      k DX QXYDegree index indexMem selectedFactor x₀
  have selectedSubstitution :
      FrobeniusSubstitutionDegreeBound p (f index) k DX selectedParent
        selectedFactor selectedFactorIrreducible selectedFactorPositive x₀ := by
    simpa only [FrobeniusSubstitutionDegreeBound, selectedQ, q] using
      selectedSubstitutionRaw
  have survivingLarge :
      (2 * DX - 1) *
            (selectedParent.natDegree * selectedFactor.natDegree *
              selectedG) +
          B < surviving.card := by
    dsimp only [selectedParent, selectedFactor, selectedG, selectedQ, q] at survivingLargeRaw
    dsimp only [selectedParent, selectedFactor, selectedG, selectedQ, q]
    omega
  have selectedLocalRoot : ∀ z ∈ surviving,
      selectedFactor.eval₂ (Polynomial.evalRingHom z)
        (((candidate z) ^ selectedQ).eval x₀) = 0 := by
    intro z zMem
    exact (survivingData z zMem).2.2.2.choose
  have selectedCandidateRoot : ∀ z ∈ surviving,
      challengeCandidatePolynomial z ((candidate z) ^ selectedQ)
        selectedParent = 0 := by
    intro z zMem
    exact (survivingData z zMem).2.1
  have selectedCandidateDegree : ∀ z ∈ surviving,
      (candidate z).natDegree ≤ k := by
    intro z zMem
    exact candidateDegree z (survivingData z zMem).1
  have selectedLeadingNeZero : ∀ z ∈ surviving,
      selectedFactor.leadingCoeff.eval z ≠ 0 := by
    intro z zMem
    exact (survivingData z zMem).2.2.2.choose_spec.1
  have selectedDerivativeNeZero : ∀ z ∈ surviving,
      specializedDerivativeValue selectedParent x₀ z
        (shiftedCandidateSeries x₀ ((candidate z) ^ selectedQ))
        selectedParent.natDegree ≠ 0 := by
    intro z zMem
    exact (survivingData z zMem).2.2.2.choose_spec.2
  have selectedSupportLarge : ∀ z ∈ surviving,
      agreementThreshold < (support z).card := by
    intro z zMem
    exact supportLarge z (survivingData z zMem).1
  have selectedAgreement : ∀ z ∈ surviving,
      ∀ coordinate ∈ support z,
        (candidate z).eval (points coordinate) =
          receivedConstant coordinate + receivedLinear coordinate * z := by
    intro z zMem coordinate coordinateMem
    exact agreement z (survivingData z zMem).1 coordinate coordinateMem
  have completion := selected_frobenius_branch_completion
    p (f index) points pointsInjective selectedParent selectedFactor
    selectedFactorIrreducible selectedFactorPositive x₀ k DX B
    agreementThreshold (by
      simpa only [selectedQ, q, selectedG] using selectedFactorWeight)
    (parentNeZero index indexMem) (parentPositive index indexMem)
    selectedFactorDvd selectedEtaNeZero (by
      simpa only [selectedQ, q] using selectedPoweredDegreeLt)
    selectedSubstitution surviving candidate (by
      simpa only [selectedQ, q] using selectedLocalRoot)
    (by simpa only [selectedQ, q] using selectedCandidateRoot)
    selectedCandidateDegree selectedLeadingNeZero (by
      simpa only [selectedQ, q] using selectedDerivativeNeZero)
    survivingLarge support receivedConstant receivedLinear selectedSupportLarge
    selectedAgreement
  refine ⟨index, indexActive, branchIndex, branchIndexMem, surviving,
    shiftedBound, survivingLarge, survivingData, ?_, ?_⟩
  · exact ⟨selectedFactorIrreducible, selectedFactorPositive,
      by simpa only [selectedParent, selectedFactor] using completion.1⟩
  · simpa only [selectedParent, selectedFactor, selectedQ, selectedG, q]
      using completion.2

#print axioms selected_frobenius_branch_completion
#print axioms inseparable_frobenius_curve_decodability

end

end WeightedHensel

/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.CoarseBounds
import WeightedHensel.PowerSeriesLift
import WeightedHensel.ResultantBound
import WeightedHensel.Specialization
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Full-degree factor transfer for the 2026 refinement

The variable `X` has weight zero.  The full degree below is the weighted
degree in `(Y,Z)` before specializing or translating `X`.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-- Full `(Y,Z)` weighted degree of a trivariate polynomial, with `X`
assigned weight zero. -/
def fullYZWeightedDegree
    {K : Type*} [Field K] (ell : Nat)
    (parent : TrivariatePolynomial K) : Nat :=
  localBivariateWeight ell parent

/-- The full weighted degree supplies the literal global coefficient
condition. -/
theorem parentCoefficientBound_fullYZWeightedDegree
    {K : Type*} [Field K] (ell : Nat)
    (parent : TrivariatePolynomial K) :
    ParentCoefficientBound parent ell
      (fullYZWeightedDegree ell parent) := by
  intro exponent exponentMem
  simpa [fullYZWeightedDegree, Nat.mul_comm] using
    coeff_weight_le_localBivariateWeight ell parent exponent exponentMem

/-- The shifted-coefficient preservation theorem (105), for arbitrary
weight `ell`. -/
theorem shiftedCoefficient_fullDegree_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ : K) (ell order yExponent : Nat)
    (coefficientNeZero :
      shiftedParentCoefficient x₀ order yExponent parent ≠ 0) :
    (shiftedParentCoefficient x₀ order yExponent parent).natDegree +
        ell * yExponent ≤ fullYZWeightedDegree ell parent := by
  exact shiftedParentCoefficient_bound parent x₀ ell
    (fullYZWeightedDegree ell parent) order yExponent
    (parentCoefficientBound_fullYZWeightedDegree ell parent)
    coefficientNeZero

/-! ## Evaluation homomorphisms used by the global assignment -/

/-- Evaluate a trivariate polynomial at `Z=z` and then at the polynomial
`Y=candidate(X)`. -/
def challengeEvaluationHom
    {K : Type*} [Field K] (z : K) (candidate : Polynomial K) :
    TrivariatePolynomial K →+* Polynomial K :=
  (Polynomial.evalRingHom candidate).comp
    (Polynomial.mapRingHom (Polynomial.evalRingHom (Polynomial.C z)))

@[simp] theorem challengeEvaluationHom_apply
    {K : Type*} [Field K] (z : K) (candidate : Polynomial K)
    (parent : TrivariatePolynomial K) :
    challengeEvaluationHom z candidate parent =
      challengeCandidatePolynomial z candidate parent := by
  rfl

@[simp] theorem challengeCandidatePolynomial_C
    {K : Type*} [Field K] (z : K) (candidate : Polynomial K)
    (content : BivariatePolynomial K) :
    challengeCandidatePolynomial z candidate (Polynomial.C content) =
      content.eval (Polynomial.C z) := by
  simp [challengeCandidatePolynomial, specializeChallenge]

/-- Evaluation first at `Z=z` and then at `X=x₀` commutes with mapping
the `X`-coefficients first and then evaluating `Z=z`. -/
theorem challengeSpecializationHom_commutes
    {K : Type*} [Field K] (x₀ z : K) :
    (Polynomial.evalRingHom x₀).comp
        (Polynomial.evalRingHom (Polynomial.C z)) =
      (Polynomial.evalRingHom z).comp
        (Polynomial.mapRingHom (Polynomial.evalRingHom x₀)) := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    simp
  · simp

/-- Evaluating a candidate-substituted parent at `X=x₀` is literal
evaluation of `R(x₀,Y,Z)` at `(Y,Z)=(candidate(x₀),z)`. -/
theorem eval_challengeCandidatePolynomial
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (candidate : Polynomial K) :
    (challengeCandidatePolynomial z candidate parent).eval x₀ =
      (specializeX x₀ parent).eval₂ (Polynomial.evalRingHom z)
        (candidate.eval x₀) := by
  unfold challengeCandidatePolynomial specializeChallenge specializeX
  rw [Polynomial.eval₂_map, ← Polynomial.eval_map]
  change ((Polynomial.evalRingHom x₀).comp
      (challengeEvaluationHom z candidate)) parent =
    ((Polynomial.evalRingHom (candidate.eval x₀)).comp
      (Polynomial.mapRingHom
        ((Polynomial.evalRingHom z).comp
          (Polynomial.mapRingHom (Polynomial.evalRingHom x₀))))) parent
  congr 1
  apply Polynomial.ringHom_ext
  · intro coefficient
    simpa [challengeEvaluationHom] using
      DFunLike.congr_fun (challengeSpecializationHom_commutes x₀ z) coefficient
  · simp [challengeEvaluationHom]

/-- A successful challenge outside the global content roots kills at least
one factor in the product (106). -/
theorem exists_factor_root_of_fullFactorization
    {K ι : Type*} [Field K] [DecidableEq ι]
    (indices : Finset ι) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (factor : ι → TrivariatePolynomial K) (multiplicity : ι → Nat)
    (multiplicityPositive : ∀ index ∈ indices, 1 ≤ multiplicity index)
    (factorization : Q = Polynomial.C content *
      ∏ index ∈ indices, factor index ^ multiplicity index)
    (z : K) (candidate : Polynomial K)
    (candidateRoot : challengeCandidatePolynomial z candidate Q = 0)
    (contentValueNeZero : content.eval (Polynomial.C z) ≠ 0) :
    ∃ index ∈ indices,
      challengeCandidatePolynomial z candidate (factor index) = 0 := by
  classical
  have mappedFactorization := congrArg
    (challengeEvaluationHom z candidate) factorization
  rw [map_mul, map_prod] at mappedFactorization
  simp only [map_pow, challengeEvaluationHom_apply,
    challengeCandidatePolynomial_C] at mappedFactorization
  rw [candidateRoot] at mappedFactorization
  have productZero :
      ∏ index ∈ indices,
          challengeCandidatePolynomial z candidate (factor index) ^
            multiplicity index = 0 := by
    exact (mul_eq_zero.mp mappedFactorization.symm).resolve_left
      contentValueNeZero
  obtain ⟨index, indexMem, powerZero⟩ :=
    Finset.prod_eq_zero_iff.mp productZero
  refine ⟨index, indexMem, ?_⟩
  exact (pow_eq_zero_iff (Nat.ne_zero_of_lt
    (multiplicityPositive index indexMem))).mp powerZero

/-- At `X=x₀`, a selected factor root is either a specialization-content
root or lies on one of the displayed nonconstant branches. -/
theorem content_root_or_exists_branch_root
    {K κ : Type*} [Field K] [DecidableEq κ]
    (parent : TrivariatePolynomial K) (x₀ : K)
    (branchIndices : Finset κ) (content : Polynomial K)
    (branch : κ → BivariatePolynomial K)
    (factorization : specializeX x₀ parent = Polynomial.C content *
      ∏ branchIndex ∈ branchIndices, branch branchIndex)
    (z : K) (candidate : Polynomial K)
    (candidateRoot : challengeCandidatePolynomial z candidate parent = 0) :
    content.eval z = 0 ∨
      ∃ branchIndex ∈ branchIndices,
        (branch branchIndex).eval₂ (Polynomial.evalRingHom z)
          (candidate.eval x₀) = 0 := by
  classical
  have localParentZero :
      (specializeX x₀ parent).eval₂ (Polynomial.evalRingHom z)
          (candidate.eval x₀) = 0 := by
    rw [← eval_challengeCandidatePolynomial parent x₀ z candidate,
      candidateRoot]
    simp
  let localEvaluation : BivariatePolynomial K →+* K :=
    Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (candidate.eval x₀)
  have mappedFactorization := congrArg localEvaluation factorization
  rw [map_mul, map_prod] at mappedFactorization
  dsimp [localEvaluation] at mappedFactorization
  rw [Polynomial.eval₂_C] at mappedFactorization
  change (specializeX x₀ parent).eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = content.eval z *
        ∏ branchIndex ∈ branchIndices,
          (branch branchIndex).eval₂ (Polynomial.evalRingHom z)
            (candidate.eval x₀) at mappedFactorization
  rw [localParentZero] at mappedFactorization
  rcases mul_eq_zero.mp mappedFactorization.symm with contentZero | productZero
  · exact Or.inl contentZero
  · exact Or.inr (Finset.prod_eq_zero_iff.mp productZero)

/-! ## Global-content exceptional values -/

/-- Swapping the two variables transposes literal coefficients. -/
theorem coeff_coeff_bivariateSwap
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K)
    (xExponent zExponent : Nat) :
    ((Polynomial.Bivariate.swap polynomial).coeff xExponent).coeff zExponent =
      (polynomial.coeff zExponent).coeff xExponent := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp [leftInduction, rightInduction]
  | monomial exponent coefficient =>
      rw [Polynomial.Bivariate.swap_monomial,
        Polynomial.coeff_mul_C, Polynomial.coeff_map]
      by_cases exponentEq : zExponent = exponent
      · subst zExponent
        simp
      · have reverse : exponent ≠ zExponent := by
          intro equality
          exact exponentEq equality.symm
        simp [Polynomial.coeff_monomial, exponentEq, reverse]

/-- Every polynomial-in-`X` coefficient of `C(X,Z)` has `Z`-degree at most
the displayed outer `Z`-degree of `C`. -/
theorem bivariateSwap_coefficient_natDegree_le
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K)
    (xExponent : Nat) :
    ((Polynomial.Bivariate.swap polynomial).coeff xExponent).natDegree ≤
      polynomial.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro zExponent polynomialDegreeLt
  calc
    ((Polynomial.Bivariate.swap polynomial).coeff xExponent).coeff zExponent =
        (polynomial.coeff zExponent).coeff xExponent :=
      coeff_coeff_bivariateSwap polynomial xExponent zExponent
    _ = 0 := by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt polynomialDegreeLt]
      simp

/-- Substitution `C(X,z)` is the coefficientwise `z`-evaluation of the
swapped polynomial in `X`. -/
theorem bivariateSwap_map_eq_eval
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K) (z : K) :
    (Polynomial.Bivariate.swap polynomial).map (Polynomial.evalRingHom z) =
      polynomial.eval (Polynomial.C z) := by
  simpa [Polynomial.aeval_def] using
    (Polynomial.Bivariate.aveal_eq_map_swap (R := K) (A := K) z polynomial).symm

/-- The values `z` for which a nonzero `C(X,Z)` becomes the zero polynomial
in `X` number at most `deg_Z C`, as used in (113). -/
theorem global_content_root_card_le
    {K : Type*} [Field K] [DecidableEq K]
    (content : BivariatePolynomial K) (contentNeZero : content ≠ 0)
    (challenges : Finset K) :
    (challenges.filter fun z ↦ content.eval (Polynomial.C z) = 0).card ≤
      content.natDegree := by
  classical
  let witness := (Polynomial.Bivariate.swap content).leadingCoeff
  have swappedNeZero : Polynomial.Bivariate.swap content ≠ 0 := by
    intro swappedZero
    apply contentNeZero
    apply (Polynomial.Bivariate.swap : BivariatePolynomial K ≃ₐ[K]
      BivariatePolynomial K).injective
    simpa using swappedZero
  have witnessNeZero : witness ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr swappedNeZero
  calc
    (challenges.filter fun z ↦ content.eval (Polynomial.C z) = 0).card ≤
        witness.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z zMem
      rw [Polynomial.mem_roots witnessNeZero, Polynomial.IsRoot]
      have contentZero := (Finset.mem_filter.mp zMem).2
      have swappedMapZero :
          (Polynomial.Bivariate.swap content).map
              (Polynomial.evalRingHom z) = 0 := by
        rw [bivariateSwap_map_eq_eval, contentZero]
      have leadingMappedZero := congrArg
        (fun polynomial : Polynomial K ↦
          polynomial.coeff (Polynomial.Bivariate.swap content).natDegree)
        swappedMapZero
      rw [Polynomial.coeff_map] at leadingMappedZero
      simpa [witness] using leadingMappedZero
    _ ≤ content.natDegree :=
      bivariateSwap_coefficient_natDegree_le content
        (Polynomial.Bivariate.swap content).natDegree

/-- Challenges where the global content becomes the zero polynomial in
`X`. -/
def globalContentExceptional
    {K : Type*} [Field K] [DecidableEq K]
    (content : BivariatePolynomial K) (challenges : Finset K) : Finset K :=
  challenges.filter fun z ↦ content.eval (Polynomial.C z) = 0

/-- Indices whose specialization has no nonconstant `Y`-branch. -/
def inactiveFactorIndices
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ) : Finset ι :=
  indices.filter fun index ↦ branchIndices index = ∅

/-- Factors with at least one nonconstant specialized branch. -/
def activeFactorIndices
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ) : Finset ι :=
  indices.filter fun index ↦ branchIndices index ≠ ∅

/-- The union of the roots of specialization contents belonging to inactive
factors. -/
def inactiveContentExceptional
    {K ι κ : Type*} [Field K] [DecidableEq K] [DecidableEq ι]
    [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (content : ι → Polynomial K) (challenges : Finset K) : Finset K :=
  (inactiveFactorIndices indices branchIndices).biUnion fun index ↦
    challenges.filter fun z ↦ (content index).eval z = 0

/-- The complete set discarded in equation (113). -/
def factorTransferDiscarded
    {K ι κ : Type*} [Field K] [DecidableEq K] [DecidableEq ι]
    [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (globalContent : BivariatePolynomial K)
    (content : ι → Polynomial K) (challenges : Finset K) : Finset K :=
  globalContentExceptional globalContent challenges ∪
    inactiveContentExceptional indices branchIndices content challenges

/-- Roots of a nonzero specialization-content polynomial in a fixed finite
challenge set number at most its degree. -/
theorem local_content_root_card_le
    {K : Type*} [Field K] [DecidableEq K]
    (content : Polynomial K) (contentNeZero : content ≠ 0)
    (challenges : Finset K) :
    (challenges.filter fun z ↦ content.eval z = 0).card ≤
      content.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro z zMem
  rw [Polynomial.mem_roots contentNeZero, Polynomial.IsRoot]
  exact (Finset.mem_filter.mp zMem).2

/-- Literal finite-set form of (113), before charging the displayed degrees
to the global weighted-degree ledger. -/
theorem factorTransferDiscarded_card_le
    {K ι κ : Type*} [Field K] [DecidableEq K] [DecidableEq ι]
    [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (globalContent : BivariatePolynomial K)
    (content : ι → Polynomial K) (challenges : Finset K)
    (globalContentNeZero : globalContent ≠ 0)
    (contentNeZero : ∀ index ∈ indices, content index ≠ 0) :
    (factorTransferDiscarded indices branchIndices globalContent content
      challenges).card ≤
      globalContent.natDegree +
        ∑ index ∈ inactiveFactorIndices indices branchIndices,
          (content index).natDegree := by
  classical
  calc
    (factorTransferDiscarded indices branchIndices globalContent content
        challenges).card ≤
      (globalContentExceptional globalContent challenges).card +
        (inactiveContentExceptional indices branchIndices content
          challenges).card :=
      Finset.card_union_le _ _
    _ ≤ globalContent.natDegree +
        ∑ index ∈ inactiveFactorIndices indices branchIndices,
          (challenges.filter fun z ↦ (content index).eval z = 0).card :=
      Nat.add_le_add
        (global_content_root_card_le globalContent globalContentNeZero challenges)
        Finset.card_biUnion_le
    _ ≤ globalContent.natDegree +
        ∑ index ∈ inactiveFactorIndices indices branchIndices,
          (content index).natDegree := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro index indexMem
      have indexInIndices : index ∈ indices := by
        rw [inactiveFactorIndices] at indexMem
        exact (Finset.mem_filter.mp indexMem).1
      exact local_content_root_card_le (content index)
        (contentNeZero index indexInIndices) challenges

/-! ## The specialization-only counterexample -/

/-- Equation (103), represented as `Y + Z + X Z^N`. -/
def fullDegreeCounterexample
    {K : Type*} [Field K] (N : Nat) : TrivariatePolynomial K :=
  Polynomial.X + Polynomial.C
    (Polynomial.X + Polynomial.C Polynomial.X * Polynomial.X ^ N)

theorem fullDegreeCounterexample_specialize_zero
    {K : Type*} [Field K] (N : Nat) :
    specializeX 0 (fullDegreeCounterexample (K := K) N) =
      Polynomial.X + Polynomial.C Polynomial.X := by
  ext yExponent zExponent
  simp [fullDegreeCounterexample, specializeX, Polynomial.coeff_add]

/-- The specialized polynomial has literal `Z`-degree one in its constant
`Y` coefficient. -/
theorem fullDegreeCounterexample_specialized_zDegree
    {K : Type*} [Field K] (N : Nat) :
    ((specializeX 0 (fullDegreeCounterexample (K := K) N)).coeff 0).natDegree =
      1 := by
  rw [fullDegreeCounterexample_specialize_zero]
  simp

/-- The coefficient of `U` and `Y^0` after translating at zero is `Z^N`. -/
theorem fullDegreeCounterexample_shifted_coefficient
    {K : Type*} [Field K] (N : Nat) :
    shiftedParentCoefficient 0 1 0
        (fullDegreeCounterexample (K := K) N) = Polynomial.X ^ N := by
  have coefficientIdentity :
      (fullDegreeCounterexample (K := K) N).coeff 0 =
        Polynomial.X + Polynomial.C Polynomial.X * Polynomial.X ^ N := by
    rw [fullDegreeCounterexample, Polynomial.coeff_add,
      Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_add]
  rw [shiftedParentCoefficient, coefficientIdentity,
    Polynomial.C_mul_X_pow_eq_monomial,
    ← Polynomial.monomial_one_one_eq_X,
    shiftedChallengeCoefficient_add,
    shiftedChallengeCoefficient_monomial,
    shiftedChallengeCoefficient_monomial]
  simp [← Polynomial.C_mul_X_pow_eq_monomial]

/-- Consequently the shifted coefficient has `Z`-degree `N`, however large
`N` is. -/
theorem fullDegreeCounterexample_shifted_zDegree
    {K : Type*} [Field K] (N : Nat) :
    (shiftedParentCoefficient 0 1 0
        (fullDegreeCounterexample (K := K) N)).natDegree = N := by
  rw [fullDegreeCounterexample_shifted_coefficient]
  exact Polynomial.natDegree_X_pow N

/-! ## Specialization preserves the full bound -/

/-- Specializing the weight-zero variable `X` cannot increase the full
`(Y,Z)` weighted degree.  This is the unshifted case of (105), stated for
the entire specialized polynomial. -/
theorem specializeX_fullYZWeightedDegree_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ : K) (ell : Nat) :
    localBivariateWeight ell (specializeX x₀ parent) ≤
      fullYZWeightedDegree ell parent := by
  apply localBivariateWeight_le_of_coeff
  intro yExponent yExponentMem
  have coefficientNeZero :
      (specializeX x₀ parent).coeff yExponent ≠ 0 :=
    Polynomial.mem_support_iff.mp yExponentMem
  have shiftedNeZero :
      shiftedParentCoefficient x₀ 0 yExponent parent ≠ 0 := by
    rwa [shiftedParentCoefficient_zero]
  have bounded := shiftedCoefficient_fullDegree_le parent x₀ ell 0
    yExponent shiftedNeZero
  rw [shiftedParentCoefficient_zero] at bounded
  simpa [Nat.mul_comm] using bounded

/-! ## Full weighted-degree factorization -/

/-- Exact weighted degree of a nonzero power. -/
theorem localBivariateWeight_pow_eq
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (ell : Nat) (polynomial : BivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) (power : Nat) :
    localBivariateWeight ell (polynomial ^ power) =
      power * localBivariateWeight ell polynomial := by
  induction power with
  | zero => simpa using localBivariateWeight_constant ell (1 : K)
  | succ power induction =>
      rw [pow_succ, localBivariateWeight_mul_eq ell]
      · rw [induction, Nat.succ_mul]
      · exact pow_ne_zero _ polynomialNeZero
      · exact polynomialNeZero

/-- Exact weighted degree of a finite product of nonzero factors. -/
theorem localBivariateWeight_finset_prod_eq
    {K ι : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    [DecidableEq ι] (ell : Nat) (indices : Finset ι)
    (factor : ι → BivariatePolynomial K)
    (factorNeZero : ∀ index ∈ indices, factor index ≠ 0) :
    localBivariateWeight ell (∏ index ∈ indices, factor index) =
      ∑ index ∈ indices, localBivariateWeight ell (factor index) := by
  induction indices using Finset.induction_on with
  | empty => simpa using localBivariateWeight_constant ell (1 : K)
  | @insert index indices indexNotMem induction =>
      rw [Finset.prod_insert indexNotMem, Finset.sum_insert indexNotMem,
        localBivariateWeight_mul_eq ell]
      · rw [induction]
        intro other otherMem
        exact factorNeZero other (Finset.mem_insert_of_mem otherMem)
      · exact factorNeZero index (Finset.mem_insert_self index indices)
      · exact Finset.prod_ne_zero_iff.mpr fun other otherMem ↦
          factorNeZero other (Finset.mem_insert_of_mem otherMem)

/-- A nonzero coefficient polynomial embedded as an outer constant has
exactly its ordinary `Z`-degree. -/
theorem localBivariateWeight_C_eq_natDegree
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (ell : Nat) (coefficient : Polynomial K)
    (coefficientNeZero : coefficient ≠ 0) :
    localBivariateWeight ell (Polynomial.C coefficient) =
      coefficient.natDegree := by
  apply le_antisymm (localBivariateWeight_C_le_natDegree ell coefficient)
  have constantMem : 0 ∈ (Polynomial.C coefficient).support := by
    exact Polynomial.mem_support_iff.mpr (by simpa using coefficientNeZero)
  simpa using coeff_weight_le_localBivariateWeight ell
    (Polynomial.C coefficient) 0 constantMem

/-! ## Explicit specialization content -/

/-- For one global factor, specialization content and all specialized branch
factors are charged to that factor's full weighted degree.  No primitive or
content-free specialization assumption is made. -/
theorem specialization_content_branch_weight_summation
    {K ι : Type*} [Field K] [DecidableEq ι]
    (parent : TrivariatePolynomial K) (x₀ : K) (ell : Nat)
    (indices : Finset ι) (content : Polynomial K)
    (branch : ι → BivariatePolynomial K)
    (contentNeZero : content ≠ 0)
    (branchNeZero : ∀ index ∈ indices, branch index ≠ 0)
    (factorization : specializeX x₀ parent = Polynomial.C content *
      ∏ index ∈ indices, branch index) :
    content.natDegree +
        ∑ index ∈ indices, localBivariateWeight ell (branch index) ≤
      fullYZWeightedDegree ell parent := by
  have productNeZero : ∏ index ∈ indices, branch index ≠ 0 := by
    apply (Finset.prod_ne_zero_iff
      (s := indices) (f := branch)).mpr
    exact branchNeZero
  calc
    content.natDegree +
          ∑ index ∈ indices, localBivariateWeight ell (branch index) =
        localBivariateWeight ell (specializeX x₀ parent) := by
      rw [factorization,
        localBivariateWeight_mul_eq ell _ _
          (Polynomial.C_ne_zero.mpr contentNeZero) productNeZero,
        localBivariateWeight_C_eq_natDegree ell content contentNeZero,
        localBivariateWeight_finset_prod_eq ell indices branch branchNeZero]
    _ ≤ fullYZWeightedDegree ell parent :=
      specializeX_fullYZWeightedDegree_le parent x₀ ell

/-- The `Y`-degrees of all specialized branch factors sum to at most the
global factor's `Y`-degree.  The specialization content is tracked as an
outer constant and contributes zero here. -/
theorem specialization_branch_yDegree_summation
    {K ι : Type*} [Field K] [DecidableEq ι]
    (parent : TrivariatePolynomial K) (x₀ : K)
    (indices : Finset ι) (content : Polynomial K)
    (branch : ι → BivariatePolynomial K)
    (contentNeZero : content ≠ 0)
    (branchNeZero : ∀ index ∈ indices, branch index ≠ 0)
    (factorization : specializeX x₀ parent = Polynomial.C content *
      ∏ index ∈ indices, branch index) :
    ∑ index ∈ indices, (branch index).natDegree ≤ parent.natDegree := by
  have productNeZero : ∏ index ∈ indices, branch index ≠ 0 := by
    apply (Finset.prod_ne_zero_iff
      (s := indices) (f := branch)).mpr
    exact branchNeZero
  have specializedDegree : (specializeX x₀ parent).natDegree =
      ∑ index ∈ indices, (branch index).natDegree := by
    rw [factorization,
      Polynomial.natDegree_mul
        (Polynomial.C_ne_zero.mpr contentNeZero) productNeZero,
      Polynomial.natDegree_C, zero_add,
      Polynomial.natDegree_prod indices branch branchNeZero]
  rw [← specializedDegree]
  exact Polynomial.natDegree_map_le

/-- If every specialized branch factor is nonconstant in `Y`, their number
is at most the global `Y`-degree. -/
theorem specialization_branch_count_le
    {K ι : Type*} [Field K] [DecidableEq ι]
    (parent : TrivariatePolynomial K) (x₀ : K)
    (indices : Finset ι) (content : Polynomial K)
    (branch : ι → BivariatePolynomial K)
    (contentNeZero : content ≠ 0)
    (branchNeZero : ∀ index ∈ indices, branch index ≠ 0)
    (branchPositiveDegree :
      ∀ index ∈ indices, 1 ≤ (branch index).natDegree)
    (factorization : specializeX x₀ parent = Polynomial.C content *
      ∏ index ∈ indices, branch index) :
    indices.card ≤ parent.natDegree := by
  rw [Finset.card_eq_sum_ones]
  exact (Finset.sum_le_sum branchPositiveDegree).trans
    (specialization_branch_yDegree_summation parent x₀ indices content
      branch contentNeZero branchNeZero factorization)

/-! ## Specialization content is visible in the derivative numerator -/

/-- Every unshifted `Y`-coefficient is divisible by the specialization
content. -/
theorem specialization_content_dvd_unshifted_coefficient
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ : K) (content : Polynomial K)
    (cofactor : BivariatePolynomial K)
    (factorization : specializeX x₀ parent =
      Polynomial.C content * cofactor) (yExponent : Nat) :
    content ∣ shiftedParentCoefficient x₀ 0 yExponent parent := by
  refine ⟨cofactor.coeff yExponent, ?_⟩
  rw [shiftedParentCoefficient_zero, factorization,
    Polynomial.coeff_C_mul]

/-- Equation (119) at the polynomial-representative level: the explicit
cleared derivative `W ξ` is divisible by the specialization content. -/
theorem specialization_content_dvd_clearedDerivativeRepresentative
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ : K) (content : Polynomial K)
    (cofactor : BivariatePolynomial K)
    (factorization : specializeX x₀ parent =
      Polynomial.C content * cofactor)
    (W : Polynomial K) (d : Nat) :
    Polynomial.C content ∣
      sourceClearedRepresentative parent x₀ 0 d 1
        (fun j ↦ (j : K)) W := by
  let witness : BivariatePolynomial K :=
    ∑ j ∈ Finset.Icc 1 d,
      Polynomial.monomial (j - 1)
        (Polynomial.C (j : K) * cofactor.coeff j * W ^ (d - j))
  refine ⟨witness, ?_⟩
  unfold sourceClearedRepresentative witness
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j jMem
  rw [Polynomial.C_mul_monomial,
    shiftedParentCoefficient_zero, factorization,
    Polynomial.coeff_C_mul]
  congr 1
  ring

/-- Consequently, at a root of the specialization content the literal
cleared derivative representative evaluates to zero for every generator
value `t`.  This is the algebraic content-root charge used before the
resultant root count. -/
theorem eval₂_clearedDerivativeRepresentative_eq_zero_of_content_root
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ : K) (content : Polynomial K)
    (cofactor : BivariatePolynomial K)
    (factorization : specializeX x₀ parent =
      Polynomial.C content * cofactor)
    (W : Polynomial K) (d : Nat) (z t : K)
    (contentRoot : content.eval z = 0) :
    (sourceClearedRepresentative parent x₀ 0 d 1
        (fun j ↦ (j : K)) W).eval₂ (Polynomial.evalRingHom z) t = 0 := by
  obtain ⟨witness, representativeEq⟩ :=
    specialization_content_dvd_clearedDerivativeRepresentative parent x₀
      content cofactor factorization W d
  rw [representativeEq, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  simp [contentRoot]

/-- All data attached to the pole/resultant exceptional polynomial of a
fixed specialized branch. -/
structure PoleResultantExceptionalData
    {K : Type*} [Field K]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (x₀ : K) (content : Polynomial K)
    (challenges : Finset K) where
  xi : RegularQuotient factor
  clearing : regularDerivativeElement parent factor x₀ parent.natDegree =
    AdjoinRoot.of (monicization factor) factor.leadingCoeff * xi
  xiNeZero : xi ≠ 0
  exceptional : Finset K
  exceptionalCard : exceptional.card <
    parent.natDegree * factor.natDegree * fullYZWeightedDegree 1 parent
  exceptionalSubset : exceptional ⊆ challenges
  contentIncluded : ∀ z ∈ challenges, content.eval z = 0 → z ∈ exceptional
  regularOutside : ∀ z ∈ challenges, z ∉ exceptional →
    factor.leadingCoeff.eval z ≠ 0 ∧
    (Polynomial.resultant
      (canonicalRepresentative factor factorNeZero xi)
      (monicization factor)).eval z ≠ 0

/-- Equation (120), with the degree estimate from (44), in its literal
form.  The returned finite set is the intersection of the supplied challenge
set with the roots of `W * Res_T(xi,Hhat)`.  Every specialization-content
root belongs to it, and outside it both clearing factors are nonzero. -/
theorem exists_pole_resultant_exceptional_set
    {K : Type*} [Field K]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (parentPositive : 1 ≤ parent.natDegree)
    (x₀ : K) (content : Polynomial K) (cofactor : BivariatePolynomial K)
    (factorization : specializeX x₀ parent =
      Polynomial.C content * cofactor)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (factorWeightLe : localBivariateWeight 1 factor ≤
      fullYZWeightedDegree 1 parent)
    (etaNeZero : regularDerivativeElement parent factor x₀
      parent.natDegree ≠ 0)
    (challenges : Finset K) :
    Nonempty (PoleResultantExceptionalData parent factor
      factorIrreducible.ne_zero x₀ content challenges) := by
  classical
  let G := fullYZWeightedDegree 1 parent
  let h := factor.natDegree
  let d := parent.natDegree
  let b := G - h
  let tau := b + 1
  let mu := sourceMu G 1 d b
  let w := factor.leadingCoeff.natDegree
  let sigma := sourceSigma G 1 d b w
  have factorNeZero : factor ≠ 0 := factorIrreducible.ne_zero
  have factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + 1 * exponent ≤ G := by
    intro exponent exponentMem
    simpa [G, Nat.mul_comm] using
      (coeff_weight_le_localBivariateWeight 1 factor exponent
        exponentMem).trans factorWeightLe
  have leadingMem : h ∈ factor.support :=
    Polynomial.natDegree_mem_support_of_nonzero factorNeZero
  have leadingBound : w + h ≤ G := by
    simpa [h, w] using factorCoefficientBound h leadingMem
  have hLeG : h ≤ G := by omega
  have GPositive : 1 ≤ G := by omega
  have wLeB : w ≤ b := by
    dsimp [b]
    omega
  have specializedDegreeLe : (specializeX x₀ parent).natDegree ≤ d :=
    Polynomial.natDegree_map_le
  obtain ⟨xiRepresentative, representativeEq, representativeWeight⟩ :=
    exists_sourceDerivativePolynomialNumerator parent factor x₀
      1 G d b tau factorNeZero
      (parentCoefficientBound_fullYZWeightedDegree 1 parent) rfl wLeB
      parentPositive factorDvd specializedDegreeLe
  let xi : RegularQuotient factor :=
    AdjoinRoot.mk (monicization factor) xiRepresentative
  have generatorEq : G + 1 - 1 * h = tau := by
    dsimp [tau, b]
    omega
  have clearing : regularDerivativeElement parent factor x₀ d =
      AdjoinRoot.of (monicization factor) factor.leadingCoeff * xi := by
    unfold regularDerivativeElement xi
    rw [representativeEq, map_mul]
    rfl
  have xiNeZero : xi ≠ 0 := by
    intro xiZero
    apply etaNeZero
    rw [clearing, xiZero, mul_zero]
  have xiBound : regularWeight factor factorNeZero tau xi ≤
      (sigma : WithBot Nat) := by
    have quotientBound := regularWeight_mk_le factor factorNeZero 1 G
      factorCoefficientBound xiRepresentative
    rw [generatorEq] at quotientBound
    exact quotientBound.trans representativeWeight
  have xiWeightLe : regularWeightNat factor factorNeZero tau xi ≤ sigma := by
    rw [regularWeight_eq_coe factor factorNeZero tau xiNeZero] at xiBound
    exact WithBot.coe_le_coe.mp xiBound
  let controllingResultant := Polynomial.resultant
    (canonicalRepresentative factor factorNeZero xi) (monicization factor)
  have resultantNeZero : controllingResultant ≠ 0 :=
    canonicalRepresentative_resultant_ne_zero factor factorIrreducible
      factorPositive xi xiNeZero
  let leadingRoots := challenges.filter fun z ↦ factor.leadingCoeff.eval z = 0
  let resultantRoots := challenges.filter fun z ↦ controllingResultant.eval z = 0
  let exceptional := leadingRoots ∪ resultantRoots
  have leadingCoefficientNeZero : factor.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr factorNeZero
  have leadingCard : leadingRoots.card ≤ w := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro z zMem
    rw [Polynomial.mem_roots leadingCoefficientNeZero, Polynomial.IsRoot]
    exact (Finset.mem_filter.mp zMem).2
  have resultantCard : resultantRoots.card ≤
      h * regularWeightNat factor factorNeZero tau xi := by
    calc
      resultantRoots.card ≤ controllingResultant.natDegree := by
        apply Polynomial.card_le_degree_of_subset_roots
        intro z zMem
        rw [Polynomial.mem_roots resultantNeZero, Polynomial.IsRoot]
        exact (Finset.mem_filter.mp zMem).2
      _ ≤ h * regularWeightNat factor factorNeZero tau xi := by
        have degreeBound := canonicalRepresentative_resultant_natDegree_le
          factor factorNeZero 1 G factorCoefficientBound xi
        change controllingResultant.natDegree ≤
          h * regularWeightNat factor factorNeZero (G + 1 - 1 * h) xi at degreeBound
        rw [generatorEq] at degreeBound
        exact degreeBound
  have wLeMu : w ≤ mu := by
    dsimp [mu, sourceMu]
    omega
  have muLt : mu < d * G :=
    sourceMu_lt_commonDegree G G G 1 h d mu le_rfl le_rfl
      (by omega) GPositive parentPositive (by simp [mu, b, sourceMu])
  have exceptionalCard : exceptional.card < h * d * G := by
    calc
      exceptional.card ≤ leadingRoots.card + resultantRoots.card :=
        Finset.card_union_le _ _
      _ ≤ w + h * regularWeightNat factor factorNeZero tau xi :=
        Nat.add_le_add leadingCard resultantCard
      _ < h * d * G :=
        sourcePoleBudget_lt_coarse h w
          (regularWeightNat factor factorNeZero tau xi) sigma mu d G
          (by omega) wLeMu rfl xiWeightLe muLt
  have contentIncluded : ∀ z ∈ challenges,
      content.eval z = 0 → z ∈ exceptional := by
    intro z zMem contentZero
    by_cases leadingZero : factor.leadingCoeff.eval z = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨zMem, leadingZero⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨zMem, ?_⟩
      have clearedMapZero :
          (sourceClearedRepresentative parent x₀ 0 d 1
            (fun j ↦ (j : K)) factor.leadingCoeff).map
              (Polynomial.evalRingHom z) = 0 := by
        obtain ⟨contentWitness, contentFactorization⟩ :=
          specialization_content_dvd_clearedDerivativeRepresentative
            parent x₀ content cofactor factorization factor.leadingCoeff d
        rw [contentFactorization, Polynomial.map_mul]
        simp [contentZero]
      have mappedRepresentativeEq := congrArg
        (Polynomial.map (Polynomial.evalRingHom z)) representativeEq
      rw [clearedMapZero, Polynomial.map_mul, Polynomial.map_C] at mappedRepresentativeEq
      have representativeMapZero :
          xiRepresentative.map (Polynomial.evalRingHom z) = 0 :=
        (mul_eq_zero.mp mappedRepresentativeEq.symm).resolve_left
          (Polynomial.C_ne_zero.mpr leadingZero)
      have canonicalMapZero :
          (canonicalRepresentative factor factorNeZero xi).map
              (Polynomial.evalRingHom z) = 0 := by
        change (xiRepresentative %ₘ monicization factor).map
            (Polynomial.evalRingHom z) = 0
        rw [Polynomial.map_modByMonic _
          (monicization_monic factor factorNeZero), representativeMapZero]
        simp
      change (Polynomial.evalRingHom z) controllingResultant = 0
      unfold controllingResultant
      rw [← Polynomial.resultant_map_map, canonicalMapZero,
        Polynomial.resultant_zero_left, monicization_natDegree]
      simp [factorPositive.ne']
  refine ⟨
    { xi := xi
      clearing := clearing
      xiNeZero := xiNeZero
      exceptional := exceptional
      exceptionalCard := ?_
      exceptionalSubset := ?_
      contentIncluded := contentIncluded
      regularOutside := ?_ }⟩
  · simpa [d, h, G, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      exceptionalCard
  · intro z zMem
    rcases Finset.mem_union.mp zMem with leadingMem | resultantMem
    · exact (Finset.mem_filter.mp leadingMem).1
    · exact (Finset.mem_filter.mp resultantMem).1
  · intro z zMem zNotExceptional
    have leadingValueNeZero : factor.leadingCoeff.eval z ≠ 0 := by
      intro leadingZero
      apply zNotExceptional
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨zMem, leadingZero⟩)
    have resultantValueNeZero : controllingResultant.eval z ≠ 0 := by
      intro resultantZero
      apply zNotExceptional
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨zMem, resultantZero⟩)
    exact ⟨leadingValueNeZero, resultantValueNeZero⟩

/-- Chosen pole/resultant data.  This is noncomputable only because the
polynomial numerator construction is existential; all of its mathematical
properties are fields of the returned structure. -/
noncomputable def poleResultantExceptionalData
    {K : Type*} [Field K]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (parentPositive : 1 ≤ parent.natDegree)
    (x₀ : K) (content : Polynomial K) (cofactor : BivariatePolynomial K)
    (factorization : specializeX x₀ parent =
      Polynomial.C content * cofactor)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (factorWeightLe : localBivariateWeight 1 factor ≤
      fullYZWeightedDegree 1 parent)
    (etaNeZero : regularDerivativeElement parent factor x₀
      parent.natDegree ≠ 0)
    (challenges : Finset K) :
    PoleResultantExceptionalData parent factor factorIrreducible.ne_zero x₀
      content challenges :=
  Classical.choice (exists_pole_resultant_exceptional_set parent factor
    factorIrreducible factorPositive parentPositive x₀ content cofactor
    factorization factorDvd factorWeightLe etaNeZero challenges)

/-- Equation (120), with the degree estimate from (44): content-root
specializations on a fixed branch are charged to the roots of `W` and the
weighted resultant of the nonzero regular derivative numerator `xi`.

The explicit hypothesis that the intrinsic regular derivative is nonzero is
the operative meaning of the paper's phrase that the chosen specialized
branch is simple. -/
theorem card_content_root_specializations_lt_pole_budget
    {K : Type*} [Field K]
    (parent : TrivariatePolynomial K) (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (parentPositive : 1 ≤ parent.natDegree)
    (x₀ : K) (content : Polynomial K) (cofactor : BivariatePolynomial K)
    (factorization : specializeX x₀ parent =
      Polynomial.C content * cofactor)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (factorWeightLe : localBivariateWeight 1 factor ≤
      fullYZWeightedDegree 1 parent)
    (etaNeZero : regularDerivativeElement parent factor x₀
      parent.natDegree ≠ 0)
    (challenges : Finset K)
    (contentRoot : ∀ z ∈ challenges, content.eval z = 0) :
    challenges.card <
      parent.natDegree * factor.natDegree * fullYZWeightedDegree 1 parent := by
  classical
  let G := fullYZWeightedDegree 1 parent
  let h := factor.natDegree
  let d := parent.natDegree
  let b := G - h
  let tau := b + 1
  let mu := sourceMu G 1 d b
  let w := factor.leadingCoeff.natDegree
  let sigma := sourceSigma G 1 d b w
  have factorNeZero : factor ≠ 0 := factorIrreducible.ne_zero
  have factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + 1 * exponent ≤ G := by
    intro exponent exponentMem
    simpa [G, Nat.mul_comm] using
      (coeff_weight_le_localBivariateWeight 1 factor exponent
        exponentMem).trans factorWeightLe
  have leadingMem : h ∈ factor.support := by
    exact Polynomial.natDegree_mem_support_of_nonzero factorNeZero
  have leadingBound : w + h ≤ G := by
    simpa [h, w] using factorCoefficientBound h leadingMem
  have hLeG : h ≤ G := by omega
  have GPositive : 1 ≤ G := by omega
  have wLeB : w ≤ b := by
    dsimp [b]
    omega
  have specializedDegreeLe : (specializeX x₀ parent).natDegree ≤ d := by
    exact Polynomial.natDegree_map_le
  obtain ⟨xiRepresentative, representativeEq, representativeWeight⟩ :=
    exists_sourceDerivativePolynomialNumerator parent factor x₀
      1 G d b tau factorNeZero
      (parentCoefficientBound_fullYZWeightedDegree 1 parent) rfl wLeB
      parentPositive factorDvd specializedDegreeLe
  let xi : RegularQuotient factor :=
    AdjoinRoot.mk (monicization factor) xiRepresentative
  have generatorEq : G + 1 - 1 * h = tau := by
    dsimp [tau, b]
    omega
  have clearing : regularDerivativeElement parent factor x₀ d =
      AdjoinRoot.of (monicization factor) factor.leadingCoeff * xi := by
    unfold regularDerivativeElement xi
    rw [representativeEq, map_mul]
    rfl
  have xiNeZero : xi ≠ 0 := by
    intro xiZero
    apply etaNeZero
    rw [clearing, xiZero, mul_zero]
  have xiBound : regularWeight factor factorNeZero tau xi ≤
      (sigma : WithBot Nat) := by
    have quotientBound := regularWeight_mk_le factor factorNeZero 1 G
      factorCoefficientBound xiRepresentative
    rw [generatorEq] at quotientBound
    exact quotientBound.trans representativeWeight
  have xiWeightLe : regularWeightNat factor factorNeZero tau xi ≤ sigma := by
    rw [regularWeight_eq_coe factor factorNeZero tau xiNeZero] at xiBound
    exact WithBot.coe_le_coe.mp xiBound
  let leadingRoots := challenges.filter fun z ↦ factor.leadingCoeff.eval z = 0
  let derivativeRoots := challenges.filter fun z ↦ factor.leadingCoeff.eval z ≠ 0
  have leadingCoefficientNeZero : factor.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr factorNeZero
  have leadingCard : leadingRoots.card ≤ w := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro z zMem
    rw [Polynomial.mem_roots leadingCoefficientNeZero, Polynomial.IsRoot]
    exact (Finset.mem_filter.mp zMem).2
  let controllingResultant := Polynomial.resultant
    (canonicalRepresentative factor factorNeZero xi) (monicization factor)
  have resultantNeZero : controllingResultant ≠ 0 :=
    canonicalRepresentative_resultant_ne_zero factor factorIrreducible
      factorPositive xi xiNeZero
  have derivativeCard : derivativeRoots.card ≤
      h * regularWeightNat factor factorNeZero tau xi := by
    calc
      derivativeRoots.card ≤ controllingResultant.natDegree := by
        apply Polynomial.card_le_degree_of_subset_roots
        intro z zMem
        have zMemChallenges : z ∈ challenges :=
          (Finset.mem_filter.mp zMem).1
        have leadingValueNeZero : factor.leadingCoeff.eval z ≠ 0 :=
          (Finset.mem_filter.mp zMem).2
        have clearedMapZero :
            (sourceClearedRepresentative parent x₀ 0 d 1
              (fun j ↦ (j : K)) factor.leadingCoeff).map
                (Polynomial.evalRingHom z) = 0 := by
          obtain ⟨contentWitness, contentFactorization⟩ :=
            specialization_content_dvd_clearedDerivativeRepresentative
              parent x₀ content cofactor factorization factor.leadingCoeff d
          rw [contentFactorization, Polynomial.map_mul]
          simp [contentRoot z zMemChallenges]
        have mappedRepresentativeEq := congrArg
          (Polynomial.map (Polynomial.evalRingHom z)) representativeEq
        rw [clearedMapZero, Polynomial.map_mul, Polynomial.map_C] at mappedRepresentativeEq
        have representativeMapZero :
            xiRepresentative.map (Polynomial.evalRingHom z) = 0 := by
          exact (mul_eq_zero.mp mappedRepresentativeEq.symm).resolve_left
            (Polynomial.C_ne_zero.mpr leadingValueNeZero)
        have canonicalMapZero :
            (canonicalRepresentative factor factorNeZero xi).map
                (Polynomial.evalRingHom z) = 0 := by
          change (xiRepresentative %ₘ monicization factor).map
              (Polynomial.evalRingHom z) = 0
          rw [Polynomial.map_modByMonic _
            (monicization_monic factor factorNeZero), representativeMapZero]
          simp
        rw [Polynomial.mem_roots resultantNeZero, Polynomial.IsRoot]
        change (Polynomial.evalRingHom z) controllingResultant = 0
        unfold controllingResultant
        rw [← Polynomial.resultant_map_map, canonicalMapZero,
          Polynomial.resultant_zero_left, monicization_natDegree]
        simp [factorPositive.ne']
      _ ≤ h * regularWeightNat factor factorNeZero tau xi := by
        have degreeBound := canonicalRepresentative_resultant_natDegree_le
          factor factorNeZero 1 G factorCoefficientBound xi
        change controllingResultant.natDegree ≤
          h * regularWeightNat factor factorNeZero (G + 1 - 1 * h) xi at degreeBound
        rw [generatorEq] at degreeBound
        exact degreeBound
  have wLeMu : w ≤ mu := by
    dsimp [mu, sourceMu]
    omega
  have muLt : mu < d * G := by
    exact sourceMu_lt_commonDegree G G G 1 h d mu le_rfl le_rfl
      (by omega) GPositive parentPositive (by simp [mu, b, sourceMu])
  have poleBudget : w + h * regularWeightNat factor factorNeZero tau xi <
      h * d * G := by
    exact sourcePoleBudget_lt_coarse h w
      (regularWeightNat factor factorNeZero tau xi) sigma mu d G
      (by omega) wLeMu rfl xiWeightLe muLt
  have partition := Finset.card_filter_add_card_filter_not
    (s := challenges) (fun z ↦ factor.leadingCoeff.eval z = 0)
  calc
    challenges.card = leadingRoots.card + derivativeRoots.card := by
      simpa [leadingRoots, derivativeRoots] using partition.symm
    _ ≤ w + h * regularWeightNat factor factorNeZero tau xi :=
      Nat.add_le_add leadingCard derivativeCard
    _ < h * d * G := poleBudget
    _ = parent.natDegree * factor.natDegree *
        fullYZWeightedDegree 1 parent := by
      simp only [d, h, G]
      ring

/-- Equation (110), weighted-degree half: the content and all full factor
degrees sum within the global weighted degree. -/
theorem fullFactor_weight_summation
    {K ι : Type*} [Field K] [DecidableEq ι]
    (indices : Finset ι) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (factor : ι → TrivariatePolynomial K) (multiplicity : ι → Nat)
    (contentNeZero : content ≠ 0)
    (factorNeZero : ∀ index ∈ indices, factor index ≠ 0)
    (factorization : Q = Polynomial.C content *
      ∏ index ∈ indices, factor index ^ multiplicity index)
    (DZ : Nat) (QDegree : fullYZWeightedDegree 1 Q ≤ DZ) :
    content.natDegree +
        ∑ index ∈ indices,
          multiplicity index * fullYZWeightedDegree 1 (factor index) ≤ DZ := by
  have productNeZero :
      ∏ index ∈ indices, factor index ^ multiplicity index ≠ 0 :=
    by
      apply (Finset.prod_ne_zero_iff
        (s := indices)
        (f := fun index ↦ factor index ^ multiplicity index)).mpr
      intro index indexMem
      exact pow_ne_zero _ (factorNeZero index indexMem)
  have exactDegree : fullYZWeightedDegree 1 Q = content.natDegree +
      ∑ index ∈ indices,
        multiplicity index * fullYZWeightedDegree 1 (factor index) := by
    rw [factorization]
    unfold fullYZWeightedDegree
    rw [localBivariateWeight_mul_eq 1 _ _ (Polynomial.C_ne_zero.mpr contentNeZero)
      productNeZero,
      localBivariateWeight_C_eq_natDegree 1 content contentNeZero,
      localBivariateWeight_finset_prod_eq 1 indices]
    · congr 1
      apply Finset.sum_congr rfl
      intro index indexMem
      exact localBivariateWeight_pow_eq 1 (factor index)
        (factorNeZero index indexMem) (multiplicity index)
    · intro index indexMem
      exact pow_ne_zero _ (factorNeZero index indexMem)
  rw [exactDegree] at QDegree
  exact QDegree

/-- Equation (110), ordinary `Y`-degree half. -/
theorem fullFactor_yDegree_summation
    {K ι : Type*} [Field K] [DecidableEq ι]
    (indices : Finset ι) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (factor : ι → TrivariatePolynomial K) (multiplicity : ι → Nat)
    (contentNeZero : content ≠ 0)
    (factorNeZero : ∀ index ∈ indices, factor index ≠ 0)
    (factorization : Q = Polynomial.C content *
      ∏ index ∈ indices, factor index ^ multiplicity index)
    (DY : Nat) (QDegree : Q.natDegree ≤ DY) :
    ∑ index ∈ indices, multiplicity index * (factor index).natDegree ≤ DY := by
  have productNeZero :
      ∏ index ∈ indices, factor index ^ multiplicity index ≠ 0 :=
    by
      apply (Finset.prod_ne_zero_iff
        (s := indices)
        (f := fun index ↦ factor index ^ multiplicity index)).mpr
      intro index indexMem
      exact pow_ne_zero _ (factorNeZero index indexMem)
  have exactDegree : Q.natDegree =
      ∑ index ∈ indices, multiplicity index * (factor index).natDegree := by
    rw [factorization, Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr contentNeZero) productNeZero,
      Polynomial.natDegree_C, zero_add,
      Polynomial.natDegree_prod]
    · apply Finset.sum_congr rfl
      intro index indexMem
      rw [Polynomial.natDegree_pow]
    · intro index indexMem
      exact pow_ne_zero _ (factorNeZero index indexMem)
  rw [exactDegree] at QDegree
  exact QDegree

/-- The active-factor `Y` budget and the content-charged weighted budget
follow from the literal global factorization (106), not from independent
numerical assumptions. -/
theorem activeFactor_degree_budgets
    {K ι κ : Type*} [Field K] [DecidableEq ι] [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (Q : TrivariatePolynomial K) (globalContent : BivariatePolynomial K)
    (parent : ι → TrivariatePolynomial K) (multiplicity : ι → Nat)
    (x₀ : K) (content : ι → Polynomial K)
    (branch : ι → κ → BivariatePolynomial K)
    (globalContentNeZero : globalContent ≠ 0)
    (parentNeZero : ∀ index ∈ indices, parent index ≠ 0)
    (multiplicityPositive : ∀ index ∈ indices, 1 ≤ multiplicity index)
    (globalFactorization : Q = Polynomial.C globalContent *
      ∏ index ∈ indices, parent index ^ multiplicity index)
    (contentNeZero : ∀ index ∈ indices, content index ≠ 0)
    (branchNeZero : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        branch index branchIndex ≠ 0)
    (specializationFactorization : ∀ index ∈ indices,
      specializeX x₀ (parent index) = Polynomial.C (content index) *
        ∏ branchIndex ∈ branchIndices index, branch index branchIndex)
    (DY DZ : Nat) (QYDegree : Q.natDegree ≤ DY)
    (QWeightedDegree : fullYZWeightedDegree 1 Q ≤ DZ) :
    (∑ index ∈ activeFactorIndices indices branchIndices,
        multiplicity index * (parent index).natDegree) ≤ DY ∧
      (globalContent.natDegree +
          ∑ index ∈ inactiveFactorIndices indices branchIndices,
            (content index).natDegree) +
        ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index * fullYZWeightedDegree 1 (parent index) ≤ DZ := by
  classical
  have allYBudget :
      ∑ index ∈ indices, multiplicity index * (parent index).natDegree ≤ DY :=
    fullFactor_yDegree_summation indices Q globalContent parent multiplicity
      globalContentNeZero parentNeZero globalFactorization DY QYDegree
  have allWeightedBudget : globalContent.natDegree +
      ∑ index ∈ indices,
        multiplicity index * fullYZWeightedDegree 1 (parent index) ≤ DZ :=
    fullFactor_weight_summation indices Q globalContent parent multiplicity
      globalContentNeZero parentNeZero globalFactorization DZ QWeightedDegree
  have activeYBudget :
      ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index * (parent index).natDegree ≤ DY :=
    (Finset.sum_le_sum_of_subset
      (Finset.filter_subset (fun index ↦ branchIndices index ≠ ∅) indices)).trans
        allYBudget
  have inactiveContentLe :
      ∑ index ∈ inactiveFactorIndices indices branchIndices,
          (content index).natDegree ≤
        ∑ index ∈ inactiveFactorIndices indices branchIndices,
          multiplicity index * fullYZWeightedDegree 1 (parent index) := by
    apply Finset.sum_le_sum
    intro index indexMem
    have indexInIndices : index ∈ indices := by
      rw [inactiveFactorIndices] at indexMem
      exact (Finset.mem_filter.mp indexMem).1
    have contentDegreeLe : (content index).natDegree ≤
        fullYZWeightedDegree 1 (parent index) := by
      have localBudget := specialization_content_branch_weight_summation
        (parent index) x₀ 1 (branchIndices index) (content index)
        (branch index) (contentNeZero index indexInIndices)
        (branchNeZero index indexInIndices)
        (specializationFactorization index indexInIndices)
      omega
    calc
      (content index).natDegree ≤
          fullYZWeightedDegree 1 (parent index) := contentDegreeLe
      _ = 1 * fullYZWeightedDegree 1 (parent index) := by omega
      _ ≤ multiplicity index * fullYZWeightedDegree 1 (parent index) :=
        Nat.mul_le_mul_right _ (multiplicityPositive index indexInIndices)
  have degreePartition :
      (∑ index ∈ inactiveFactorIndices indices branchIndices,
          multiplicity index * fullYZWeightedDegree 1 (parent index)) +
        ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index * fullYZWeightedDegree 1 (parent index) =
        ∑ index ∈ indices,
          multiplicity index * fullYZWeightedDegree 1 (parent index) := by
    simpa [inactiveFactorIndices, activeFactorIndices] using
      Finset.sum_filter_add_sum_filter_not indices
        (fun index ↦ branchIndices index = ∅)
        (fun index ↦
          multiplicity index * fullYZWeightedDegree 1 (parent index))
  refine ⟨activeYBudget, ?_⟩
  calc
    (globalContent.natDegree +
          ∑ index ∈ inactiveFactorIndices indices branchIndices,
            (content index).natDegree) +
        ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index * fullYZWeightedDegree 1 (parent index) ≤
      (globalContent.natDegree +
          ∑ index ∈ inactiveFactorIndices indices branchIndices,
            multiplicity index * fullYZWeightedDegree 1 (parent index)) +
        ∑ index ∈ activeFactorIndices indices branchIndices,
          multiplicity index * fullYZWeightedDegree 1 (parent index) :=
      Nat.add_le_add_right (Nat.add_le_add_left inactiveContentLe _) _
    _ = globalContent.natDegree +
        ∑ index ∈ indices,
          multiplicity index * fullYZWeightedDegree 1 (parent index) := by
      rw [Nat.add_assoc, degreePartition]
    _ ≤ DZ := allWeightedBudget

/-- Every successful challenge left after the explicit discard set admits
an active factor and a branch assignment.  A content root may be assigned to
any branch; otherwise the selected branch genuinely contains
`candidate(x₀)`. -/
theorem exists_active_factor_branch_assignment
    {K ι κ : Type*} [Field K] [DecidableEq K]
    [DecidableEq ι] [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (Q : TrivariatePolynomial K) (globalContent : BivariatePolynomial K)
    (parent : ι → TrivariatePolynomial K) (multiplicity : ι → Nat)
    (x₀ : K) (content : ι → Polynomial K)
    (branch : ι → κ → BivariatePolynomial K)
    (globalFactorization : Q = Polynomial.C globalContent *
      ∏ index ∈ indices, parent index ^ multiplicity index)
    (multiplicityPositive : ∀ index ∈ indices, 1 ≤ multiplicity index)
    (specializationFactorization : ∀ index ∈ indices,
      specializeX x₀ (parent index) = Polynomial.C (content index) *
        ∏ branchIndex ∈ branchIndices index, branch index branchIndex)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) Q = 0)
    (z : K) (zMem : z ∈ challenges)
    (zNotDiscarded : z ∉ factorTransferDiscarded indices branchIndices
      globalContent content challenges) :
    ∃ index ∈ activeFactorIndices indices branchIndices,
      ∃ branchIndex ∈ branchIndices index,
        challengeCandidatePolynomial z (candidate z) (parent index) = 0 ∧
          ((content index).eval z = 0 ∨
            (branch index branchIndex).eval₂ (Polynomial.evalRingHom z)
              ((candidate z).eval x₀) = 0) := by
  classical
  have globalContentValueNeZero :
      globalContent.eval (Polynomial.C z) ≠ 0 := by
    intro contentZero
    apply zNotDiscarded
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨zMem, contentZero⟩
  obtain ⟨index, indexMem, factorRoot⟩ :=
    exists_factor_root_of_fullFactorization indices Q globalContent parent
      multiplicity multiplicityPositive globalFactorization z (candidate z)
      (candidateRoot z zMem) globalContentValueNeZero
  have localAlternative := content_root_or_exists_branch_root
    (parent index) x₀ (branchIndices index) (content index) (branch index)
    (specializationFactorization index indexMem) z (candidate z) factorRoot
  rcases localAlternative with contentZero | ⟨branchIndex, branchIndexMem,
      branchRoot⟩
  · have branchNonempty : branchIndices index ≠ ∅ := by
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
  · have branchNonempty : branchIndices index ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨branchIndex, branchIndexMem⟩
    refine ⟨index, Finset.mem_filter.mpr ⟨indexMem, branchNonempty⟩,
      branchIndex, branchIndexMem, factorRoot, Or.inr branchRoot⟩

/-- Formal version of “make each choice once”: pointwise existence of an
active factor/branch assignment produces disjoint fiber sets whose
cardinalities sum exactly to the source set. -/
theorem exists_disjoint_factor_branch_assignment
    {K ι κ : Type*} [DecidableEq K] [DecidableEq ι] [DecidableEq κ]
    (source : Finset K) (active : Finset ι) (branches : ι → Finset κ)
    (property : K → ι → κ → Prop)
    (assignmentExists : ∀ z ∈ source,
      ∃ index ∈ active, ∃ branchIndex ∈ branches index,
        property z index branchIndex) :
    ∃ assigned : ι → κ → Finset K,
      source.card =
        ∑ index ∈ active,
          ∑ branchIndex ∈ branches index,
            (assigned index branchIndex).card ∧
      ∀ index ∈ active, ∀ branchIndex ∈ branches index,
        ∀ z ∈ assigned index branchIndex,
          z ∈ source ∧ property z index branchIndex := by
  classical
  let selection : K → Option (ι × κ) := fun z ↦
    if zMem : z ∈ source then
      let index := Classical.choose (assignmentExists z zMem)
      let indexSpec := Classical.choose_spec (assignmentExists z zMem)
      let branchIndex := Classical.choose indexSpec.2
      some (index, branchIndex)
    else none
  let assigned : ι → κ → Finset K := fun index branchIndex ↦
    source.filter fun z ↦ selection z = some (index, branchIndex)
  have selectionSpec : ∀ z ∈ source,
      ∃ index ∈ active, ∃ branchIndex ∈ branches index,
        selection z = some (index, branchIndex) ∧
          property z index branchIndex := by
    intro z zMem
    let index := Classical.choose (assignmentExists z zMem)
    let indexSpec := Classical.choose_spec (assignmentExists z zMem)
    let branchIndex := Classical.choose indexSpec.2
    let branchSpec := Classical.choose_spec indexSpec.2
    refine ⟨index, indexSpec.1, branchIndex, branchSpec.1, ?_, branchSpec.2⟩
    dsimp [selection]
    rw [dif_pos zMem]
  have selectionMem : ∀ z ∈ source,
      selection z ∈
        (active.sigma branches).image
          (fun pair ↦ some (pair.1, pair.2)) := by
    intro z zMem
    obtain ⟨index, indexMem, branchIndex, branchIndexMem,
      selectionEq, propertyHolds⟩ := selectionSpec z zMem
    apply Finset.mem_image.mpr
    exact ⟨⟨index, branchIndex⟩, Finset.mem_sigma.mpr
      ⟨indexMem, branchIndexMem⟩, selectionEq.symm⟩
  have fiberCount := Finset.card_eq_sum_card_fiberwise
    (s := source) (f := selection)
    (t := (active.sigma branches).image
      (fun pair ↦ some (pair.1, pair.2))) (by
        intro z zMem
        exact selectionMem z (by simpa using zMem))
  refine ⟨assigned, ?_, ?_⟩
  · rw [fiberCount, Finset.sum_image]
    · rw [Finset.sum_sigma]
    · intro left leftMem right rightMem equality
      simp only [Option.some.injEq, Prod.mk.injEq] at equality
      cases left with
      | mk leftIndex leftBranch =>
          cases right with
          | mk rightIndex rightBranch => simp_all
  · intro index indexMem branchIndex branchIndexMem z zMem
    have zMemSource : z ∈ source := (Finset.mem_filter.mp zMem).1
    have selectedPair : selection z = some (index, branchIndex) :=
      (Finset.mem_filter.mp zMem).2
    obtain ⟨chosenIndex, chosenIndexMem, chosenBranch, chosenBranchMem,
      chosenPair, chosenProperty⟩ := selectionSpec z zMemSource
    have pairEquality : (index, branchIndex) = (chosenIndex, chosenBranch) :=
      Option.some.inj (selectedPair.symm.trans chosenPair)
    have indexEquality : index = chosenIndex := congrArg Prod.fst pairEquality
    have branchEquality : branchIndex = chosenBranch := congrArg Prod.snd pairEquality
    subst chosenIndex
    subst chosenBranch
    exact ⟨zMemSource, chosenProperty⟩

/-! ## The pairwise summation ledger -/

/-- The key inequality in (116).  Multiplicities are retained in the global
budget, while each individual factor degree is at most `DY`. -/
theorem factor_square_weight_sum_le
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (multiplicity degree fullDegree : ι → Nat) (DY : Nat)
    (multiplicityPositive :
      ∀ index ∈ indices, 1 ≤ multiplicity index)
    (yDegreeBudget :
      ∑ index ∈ indices, multiplicity index * degree index ≤ DY) :
    ∑ index ∈ indices, degree index * degree index * fullDegree index ≤
      DY ^ 2 *
        ∑ index ∈ indices, multiplicity index * fullDegree index := by
  have degreeLe (index : ι) (indexMem : index ∈ indices) :
      degree index ≤ DY := by
    calc
      degree index = 1 * degree index := by omega
      _ ≤ multiplicity index * degree index :=
        Nat.mul_le_mul_right (degree index)
          (multiplicityPositive index indexMem)
      _ ≤ ∑ other ∈ indices, multiplicity other * degree other := by
        exact Finset.single_le_sum
          (f := fun other ↦ multiplicity other * degree other)
          (fun _ _ ↦ Nat.zero_le _) indexMem
      _ ≤ DY := yDegreeBudget
  calc
    ∑ index ∈ indices, degree index * degree index * fullDegree index ≤
        ∑ index ∈ indices,
          DY * DY * (multiplicity index * fullDegree index) := by
      apply Finset.sum_le_sum
      intro index indexMem
      calc
        degree index * degree index * fullDegree index ≤
            DY * DY * fullDegree index :=
          Nat.mul_le_mul_right (fullDegree index)
            (Nat.mul_le_mul (degreeLe index indexMem)
              (degreeLe index indexMem))
        _ ≤ DY * DY * (multiplicity index * fullDegree index) :=
          Nat.mul_le_mul_left (DY * DY) <| by
            calc
              fullDegree index = 1 * fullDegree index := by omega
              _ ≤ multiplicity index * fullDegree index :=
                Nat.mul_le_mul_right (fullDegree index)
                  (multiplicityPositive index indexMem)
    _ = DY ^ 2 *
          ∑ index ∈ indices,
            multiplicity index * fullDegree index := by
      rw [pow_two, Finset.mul_sum]

/-- The key inequality of (116) after applying the full weighted-degree
budget from (110). -/
theorem factor_square_weight_sum_le_global
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (multiplicity degree fullDegree : ι → Nat) (DY DZ : Nat)
    (multiplicityPositive :
      ∀ index ∈ indices, 1 ≤ multiplicity index)
    (yDegreeBudget :
      ∑ index ∈ indices, multiplicity index * degree index ≤ DY)
    (fullDegreeBudget :
      ∑ index ∈ indices, multiplicity index * fullDegree index ≤ DZ) :
    ∑ index ∈ indices, degree index * degree index * fullDegree index ≤
      DY ^ 2 * DZ := by
  exact (factor_square_weight_sum_le indices multiplicity degree fullDegree DY
    multiplicityPositive yDegreeBudget).trans
      (Nat.mul_le_mul_left (DY ^ 2) fullDegreeBudget)

/-- The number `r_i` of relevant specialized factors also obeys the second
inequality of (116). -/
theorem relevant_factor_count_sum_le
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (multiplicity degree relevantCount : ι → Nat) (DY : Nat)
    (multiplicityPositive :
      ∀ index ∈ indices, 1 ≤ multiplicity index)
    (relevantCountLe :
      ∀ index ∈ indices, relevantCount index ≤ degree index)
    (yDegreeBudget :
      ∑ index ∈ indices, multiplicity index * degree index ≤ DY) :
    ∑ index ∈ indices, relevantCount index ≤ DY := by
  calc
    ∑ index ∈ indices, relevantCount index ≤
        ∑ index ∈ indices, multiplicity index * degree index := by
      apply Finset.sum_le_sum
      intro index indexMem
      calc
        relevantCount index ≤ degree index :=
          relevantCountLe index indexMem
        _ = 1 * degree index := by omega
        _ ≤ multiplicity index * degree index :=
          Nat.mul_le_mul_right (degree index)
            (multiplicityPositive index indexMem)
    _ ≤ DY := yDegreeBudget

/-- Summing the degrees `h_{ij}` of the specialized branches first reduces
the pairwise budget to the square-weight sum. -/
theorem factor_branch_pair_weight_sum_le
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (degree branchDegreeSum fullDegree : ι → Nat)
    (branchDegreeSumLe :
      ∀ index ∈ indices, branchDegreeSum index ≤ degree index) :
    ∑ index ∈ indices,
        degree index * branchDegreeSum index * fullDegree index ≤
      ∑ index ∈ indices,
        degree index * degree index * fullDegree index := by
  apply Finset.sum_le_sum
  intro index indexMem
  exact Nat.mul_le_mul_right (fullDegree index)
    (Nat.mul_le_mul_left (degree index)
      (branchDegreeSumLe index indexMem))

/-- Equations (115)--(117), isolated as their exact finite-sum arithmetic
ledger.  The content/inactive-factor allowance is `discardedDegree`; the
hypothesis below is precisely (113). -/
theorem full_factor_global_allowance
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (multiplicity degree fullDegree branchDegreeSum relevantCount : ι → Nat)
    (DX DY DZ gammaN discardedDegree : Nat)
    (multiplicityPositive :
      ∀ index ∈ indices, 1 ≤ multiplicity index)
    (branchDegreeSumLe :
      ∀ index ∈ indices, branchDegreeSum index ≤ degree index)
    (relevantCountLe :
      ∀ index ∈ indices, relevantCount index ≤ degree index)
    (yDegreeBudget :
      ∑ index ∈ indices, multiplicity index * degree index ≤ DY)
    (weightedDegreeBudget : discardedDegree +
      ∑ index ∈ indices, multiplicity index * fullDegree index ≤ DZ)
    (globalMultiplierPositive : 1 ≤ 2 * DX * DY ^ 2) :
    discardedDegree +
        ∑ index ∈ indices,
          ((2 * DX) *
              (degree index * branchDegreeSum index * fullDegree index) +
            (gammaN + 1) * relevantCount index) ≤
      2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY := by
  have pairWeightBound :
      ∑ index ∈ indices,
          degree index * branchDegreeSum index * fullDegree index ≤
        DY ^ 2 *
          ∑ index ∈ indices, multiplicity index * fullDegree index :=
    (factor_branch_pair_weight_sum_le indices degree branchDegreeSum
      fullDegree branchDegreeSumLe).trans
      (factor_square_weight_sum_le indices multiplicity degree fullDegree DY
        multiplicityPositive yDegreeBudget)
  have countBound : ∑ index ∈ indices, relevantCount index ≤ DY :=
    relevant_factor_count_sum_le indices multiplicity degree relevantCount DY
      multiplicityPositive relevantCountLe yDegreeBudget
  have scaledDegreeBudget : discardedDegree +
      (2 * DX * DY ^ 2) *
        ∑ index ∈ indices, multiplicity index * fullDegree index ≤
      (2 * DX * DY ^ 2) * DZ := by
    calc
      discardedDegree +
          (2 * DX * DY ^ 2) *
            ∑ index ∈ indices, multiplicity index * fullDegree index ≤
          (2 * DX * DY ^ 2) * discardedDegree +
            (2 * DX * DY ^ 2) *
              ∑ index ∈ indices,
                multiplicity index * fullDegree index := by
        exact Nat.add_le_add_right
          (by
            calc
              discardedDegree = 1 * discardedDegree := by omega
              _ ≤ (2 * DX * DY ^ 2) * discardedDegree :=
                Nat.mul_le_mul_right discardedDegree globalMultiplierPositive)
          _
      _ = (2 * DX * DY ^ 2) *
          (discardedDegree +
            ∑ index ∈ indices,
              multiplicity index * fullDegree index) := by ring
      _ ≤ (2 * DX * DY ^ 2) * DZ :=
        Nat.mul_le_mul_left _ weightedDegreeBudget
  rw [Finset.sum_add_distrib]
  calc
    discardedDegree + (
          (∑ index ∈ indices,
            (2 * DX) *
              (degree index * branchDegreeSum index * fullDegree index)) +
          ∑ index ∈ indices, (gammaN + 1) * relevantCount index) =
        (discardedDegree +
          (2 * DX) *
            ∑ index ∈ indices,
              degree index * branchDegreeSum index * fullDegree index) +
          (gammaN + 1) *
            ∑ index ∈ indices, relevantCount index := by
      simp only [Finset.mul_sum, Nat.add_assoc]
    _ ≤ (discardedDegree +
          (2 * DX) *
            (DY ^ 2 *
              ∑ index ∈ indices,
                multiplicity index * fullDegree index)) +
          (gammaN + 1) * DY :=
      Nat.add_le_add
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left (2 * DX) pairWeightBound)
          discardedDegree)
        (Nat.mul_le_mul_left (gammaN + 1) countBound)
    _ ≤ 2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY := by
      apply Nat.add_le_add_right
      convert scaledDegreeBudget using 1
      ring

/-- If the global challenge set exceeds (117), some factor/branch pair
exceeds its preliminary allowance (118).  `assigned` records the disjoint
assignment made in the proof; `challengeCountLe` allows the explicitly
discarded content challenges as well. -/
theorem exists_factor_branch_above_preliminary_allowance
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (multiplicity degree fullDegree : ι → Nat)
    (branchDegree assigned : ι → κ → Nat)
    (DX DY DZ gammaN discardedDegree challengeCount : Nat)
    (multiplicityPositive :
      ∀ index ∈ indices, 1 ≤ multiplicity index)
    (branchDegreeSumLe : ∀ index ∈ indices,
      ∑ branchIndex ∈ branchIndices index,
        branchDegree index branchIndex ≤ degree index)
    (branchCountLe : ∀ index ∈ indices,
      (branchIndices index).card ≤ degree index)
    (yDegreeBudget :
      ∑ index ∈ indices, multiplicity index * degree index ≤ DY)
    (weightedDegreeBudget : discardedDegree +
      ∑ index ∈ indices, multiplicity index * fullDegree index ≤ DZ)
    (globalMultiplierPositive : 1 ≤ 2 * DX * DY ^ 2)
    (challengeCountLe : challengeCount ≤ discardedDegree +
      ∑ index ∈ indices,
        ∑ branchIndex ∈ branchIndices index,
          assigned index branchIndex)
    (challengeCountLarge :
      2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY < challengeCount) :
    ∃ index ∈ indices, ∃ branchIndex ∈ branchIndices index,
      2 * DX *
            (degree index * branchDegree index branchIndex *
              fullDegree index) +
          (gammaN + 1) < assigned index branchIndex := by
  by_contra noLargePair
  have everyPairBound (index : ι) (indexMem : index ∈ indices)
      (branchIndex : κ) (branchIndexMem : branchIndex ∈ branchIndices index) :
      assigned index branchIndex ≤
        2 * DX *
            (degree index * branchDegree index branchIndex *
              fullDegree index) +
          (gammaN + 1) := by
    apply Nat.le_of_not_gt
    intro pairLarge
    exact noLargePair
      ⟨index, indexMem, branchIndex, branchIndexMem, pairLarge⟩
  have assignedSumLe (index : ι) (indexMem : index ∈ indices) :
      ∑ branchIndex ∈ branchIndices index,
          assigned index branchIndex ≤
        (2 * DX) *
            (degree index *
              (∑ branchIndex ∈ branchIndices index,
                branchDegree index branchIndex) * fullDegree index) +
          (gammaN + 1) * (branchIndices index).card := by
    calc
      ∑ branchIndex ∈ branchIndices index,
          assigned index branchIndex ≤
          ∑ branchIndex ∈ branchIndices index,
            (2 * DX *
                (degree index * branchDegree index branchIndex *
                  fullDegree index) +
              (gammaN + 1)) := by
        apply Finset.sum_le_sum
        exact everyPairBound index indexMem
      _ = (2 * DX) *
              (degree index *
                (∑ branchIndex ∈ branchIndices index,
                  branchDegree index branchIndex) * fullDegree index) +
            (gammaN + 1) * (branchIndices index).card := by
        have weightedSum :
            ∑ branchIndex ∈ branchIndices index,
                2 * DX *
                  (degree index * branchDegree index branchIndex *
                    fullDegree index) =
              (2 * DX * degree index * fullDegree index) *
                ∑ branchIndex ∈ branchIndices index,
                  branchDegree index branchIndex := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro branchIndex branchIndexMem
          ring
        rw [Finset.sum_add_distrib]
        rw [weightedSum]
        simp only [Finset.sum_const_nat]
        ring
  have allAssignedLe :
      ∑ index ∈ indices,
          ∑ branchIndex ∈ branchIndices index,
            assigned index branchIndex ≤
        ∑ index ∈ indices,
          ((2 * DX) *
              (degree index *
                (∑ branchIndex ∈ branchIndices index,
                  branchDegree index branchIndex) * fullDegree index) +
            (gammaN + 1) * (branchIndices index).card) := by
    apply Finset.sum_le_sum
    exact assignedSumLe
  have globalBound := full_factor_global_allowance indices multiplicity
    degree fullDegree
    (fun index ↦ ∑ branchIndex ∈ branchIndices index,
      branchDegree index branchIndex)
    (fun index ↦ (branchIndices index).card)
    DX DY DZ gammaN discardedDegree multiplicityPositive branchDegreeSumLe
    branchCountLe yDegreeBudget weightedDegreeBudget globalMultiplierPositive
  have challengeCountBound :
      challengeCount ≤
        2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY := by
    exact challengeCountLe.trans <|
      (Nat.add_le_add_left allAssignedLe discardedDegree).trans globalBound
  omega

/-- Removing fewer than one local pole/resultant budget from the winning
pair changes the coefficient `2 DX` to `2 DX - 1`, as in (121). -/
theorem remove_local_exception_budget
    (DX localWeight gammaN assigned removed surviving : Nat)
    (DXPositive : 1 ≤ DX)
    (assignedLarge :
      2 * DX * localWeight + gammaN + 1 < assigned)
    (removedSmall : removed < localWeight)
    (partition : assigned = removed + surviving) :
    (2 * DX - 1) * localWeight + gammaN + 1 < surviving := by
  have multiplierPositive : 1 ≤ 2 * DX := by omega
  have multiplierSplit :
      2 * DX * localWeight =
        (2 * DX - 1) * localWeight + localWeight := by
    have split : 2 * DX = (2 * DX - 1) + 1 := by omega
    calc
      2 * DX * localWeight = ((2 * DX - 1) + 1) * localWeight := by
        exact congrArg (fun multiplier ↦ multiplier * localWeight) split
      _ = (2 * DX - 1) * localWeight + localWeight := by ring
  omega

/-- Numerical core of the full-factor transfer once each local exceptional
set has already been bounded.  The paper-facing theorem below derives that
bound from the actual content roots and regular derivative resultants. -/
theorem full_factor_degree_transfer_of_local_exception_bounds
    {K ι κ : Type*} [Field K] [DecidableEq ι] [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (parent : ι → TrivariatePolynomial K) (multiplicity : ι → Nat)
    (branchDegree assigned removed surviving : ι → κ → Nat)
    (DX DY DZ gammaN discardedDegree challengeCount : Nat)
    (multiplicityPositive :
      ∀ index ∈ indices, 1 ≤ multiplicity index)
    (branchDegreeSumLe : ∀ index ∈ indices,
      ∑ branchIndex ∈ branchIndices index,
        branchDegree index branchIndex ≤ (parent index).natDegree)
    (branchCountLe : ∀ index ∈ indices,
      (branchIndices index).card ≤ (parent index).natDegree)
    (yDegreeBudget : ∑ index ∈ indices,
      multiplicity index * (parent index).natDegree ≤ DY)
    (weightedDegreeBudget : discardedDegree +
      ∑ index ∈ indices,
        multiplicity index * fullYZWeightedDegree 1 (parent index) ≤ DZ)
    (globalMultiplierPositive : 1 ≤ 2 * DX * DY ^ 2)
    (challengeCountLe : challengeCount ≤ discardedDegree +
      ∑ index ∈ indices,
        ∑ branchIndex ∈ branchIndices index,
          assigned index branchIndex)
    (challengeCountLarge :
      2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY < challengeCount)
    (removalPartition : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        assigned index branchIndex =
          removed index branchIndex + surviving index branchIndex)
    (removedSmall : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        removed index branchIndex <
          (parent index).natDegree * branchDegree index branchIndex *
            fullYZWeightedDegree 1 (parent index)) :
    ∃ index ∈ indices, ∃ branchIndex ∈ branchIndices index,
      (∀ x₀ order yExponent,
        shiftedParentCoefficient x₀ order yExponent (parent index) ≠ 0 →
          (shiftedParentCoefficient x₀ order yExponent
              (parent index)).natDegree + yExponent ≤
            fullYZWeightedDegree 1 (parent index)) ∧
      (2 * DX - 1) *
            ((parent index).natDegree * branchDegree index branchIndex *
              fullYZWeightedDegree 1 (parent index)) +
          gammaN + 1 < surviving index branchIndex := by
  obtain ⟨index, indexMem, branchIndex, branchIndexMem, assignedLarge⟩ :=
    exists_factor_branch_above_preliminary_allowance indices branchIndices
      multiplicity (fun index ↦ (parent index).natDegree)
      (fun index ↦ fullYZWeightedDegree 1 (parent index)) branchDegree
      assigned DX DY DZ gammaN discardedDegree challengeCount
      multiplicityPositive branchDegreeSumLe branchCountLe yDegreeBudget
      weightedDegreeBudget globalMultiplierPositive challengeCountLe
      challengeCountLarge
  have DXPositive : 1 ≤ DX := by
    by_contra notPositive
    have DXZero : DX = 0 := Nat.eq_zero_of_not_pos notPositive
    simp [DXZero] at globalMultiplierPositive
  refine ⟨index, indexMem, branchIndex, branchIndexMem, ?_, ?_⟩
  · intro x₀ order yExponent coefficientNeZero
    simpa using shiftedCoefficient_fullDegree_le (parent index) x₀ 1 order
      yExponent coefficientNeZero
  · exact remove_local_exception_budget DX
      ((parent index).natDegree * branchDegree index branchIndex *
        fullYZWeightedDegree 1 (parent index))
      gammaN (assigned index branchIndex) (removed index branchIndex)
      (surviving index branchIndex) DXPositive assignedLarge
      (removedSmall index indexMem branchIndex branchIndexMem)
      (removalPartition index indexMem branchIndex branchIndexMem)

/-- Paper-facing full-factor transfer with the local removal sets represented
as actual field elements.  Their strict bounds are proved, rather than
assumed, by `card_content_root_specializations_lt_pole_budget`.

The assignment count is the explicit finite combinatorial ledger constructed
before equation (114).  For each assigned branch, `removedRoots` is precisely
the subset assigned only because the specialization content vanishes; the
surviving count is its complement as recorded by `removalPartition`. -/
theorem full_factor_degree_transfer_from_content_root_sets
    {K ι κ : Type*} [Field K] [DecidableEq K]
    [DecidableEq ι] [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (x₀ : K) (parent : ι → TrivariatePolynomial K)
    (multiplicity : ι → Nat) (content : ι → Polynomial K)
    (branch : ι → κ → BivariatePolynomial K)
    (assigned surviving : ι → κ → Nat)
    (removedRoots : ι → κ → Finset K)
    (DX DY DZ gammaN discardedDegree challengeCount : Nat)
    (multiplicityPositive :
      ∀ index ∈ indices, 1 ≤ multiplicity index)
    (parentPositive : ∀ index ∈ indices, 1 ≤ (parent index).natDegree)
    (contentNeZero : ∀ index ∈ indices, content index ≠ 0)
    (branchNeZero : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        branch index branchIndex ≠ 0)
    (branchPositive : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        0 < (branch index branchIndex).natDegree)
    (branchIrreducible : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        Irreducible (branch index branchIndex))
    (specializationFactorization : ∀ index ∈ indices,
      specializeX x₀ (parent index) = Polynomial.C (content index) *
        ∏ branchIndex ∈ branchIndices index, branch index branchIndex)
    (etaNeZero : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        regularDerivativeElement (parent index) (branch index branchIndex) x₀
          (parent index).natDegree ≠ 0)
    (removedContentRoot : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
      ∀ z ∈ removedRoots index branchIndex,
        (content index).eval z = 0)
    (yDegreeBudget : ∑ index ∈ indices,
      multiplicity index * (parent index).natDegree ≤ DY)
    (weightedDegreeBudget : discardedDegree +
      ∑ index ∈ indices,
        multiplicity index * fullYZWeightedDegree 1 (parent index) ≤ DZ)
    (globalMultiplierPositive : 1 ≤ 2 * DX * DY ^ 2)
    (challengeCountLe : challengeCount ≤ discardedDegree +
      ∑ index ∈ indices,
        ∑ branchIndex ∈ branchIndices index,
          assigned index branchIndex)
    (challengeCountLarge :
      2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY < challengeCount)
    (removalPartition : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        assigned index branchIndex =
          (removedRoots index branchIndex).card + surviving index branchIndex) :
    ∃ index ∈ indices, ∃ branchIndex ∈ branchIndices index,
      (∀ order yExponent,
        shiftedParentCoefficient x₀ order yExponent (parent index) ≠ 0 →
          (shiftedParentCoefficient x₀ order yExponent
              (parent index)).natDegree + yExponent ≤
            fullYZWeightedDegree 1 (parent index)) ∧
      (2 * DX - 1) *
            ((parent index).natDegree *
              (branch index branchIndex).natDegree *
                fullYZWeightedDegree 1 (parent index)) +
          gammaN + 1 < surviving index branchIndex := by
  classical
  have branchDegreeSumLe : ∀ index ∈ indices,
      ∑ branchIndex ∈ branchIndices index,
        (branch index branchIndex).natDegree ≤ (parent index).natDegree := by
    intro index indexMem
    exact specialization_branch_yDegree_summation (parent index) x₀
      (branchIndices index) (content index) (branch index)
      (contentNeZero index indexMem) (branchNeZero index indexMem)
      (specializationFactorization index indexMem)
  have branchCountLe : ∀ index ∈ indices,
      (branchIndices index).card ≤ (parent index).natDegree := by
    intro index indexMem
    exact specialization_branch_count_le (parent index) x₀
      (branchIndices index) (content index) (branch index)
      (contentNeZero index indexMem) (branchNeZero index indexMem)
      (fun branchIndex branchIndexMem ↦ by
        exact branchPositive index indexMem branchIndex branchIndexMem)
      (specializationFactorization index indexMem)
  have removedSmall : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        (removedRoots index branchIndex).card <
          (parent index).natDegree *
            (branch index branchIndex).natDegree *
              fullYZWeightedDegree 1 (parent index) := by
    intro index indexMem branchIndex branchIndexMem
    have branchWeightLe : localBivariateWeight 1
          (branch index branchIndex) ≤
        fullYZWeightedDegree 1 (parent index) := by
      have termLe : localBivariateWeight 1 (branch index branchIndex) ≤
          ∑ candidate ∈ branchIndices index,
            localBivariateWeight 1 (branch index candidate) := by
        exact Finset.single_le_sum
          (s := branchIndices index)
          (f := fun candidate ↦
            localBivariateWeight 1 (branch index candidate))
          (fun _ _ ↦ Nat.zero_le _) branchIndexMem
      have sumBound := specialization_content_branch_weight_summation
        (parent index) x₀ 1 (branchIndices index) (content index)
        (branch index) (contentNeZero index indexMem)
        (branchNeZero index indexMem)
        (specializationFactorization index indexMem)
      omega
    have factorDvd : branch index branchIndex ∣
        specializeX x₀ (parent index) := by
      rw [specializationFactorization index indexMem]
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem (branch index) branchIndexMem)
        (Polynomial.C (content index))
    exact card_content_root_specializations_lt_pole_budget
      (parent index) (branch index branchIndex)
      (branchIrreducible index indexMem branchIndex branchIndexMem)
      (branchPositive index indexMem branchIndex branchIndexMem)
      (parentPositive index indexMem) x₀ (content index)
      (∏ candidate ∈ branchIndices index, branch index candidate)
      (specializationFactorization index indexMem) factorDvd branchWeightLe
      (etaNeZero index indexMem branchIndex branchIndexMem)
      (removedRoots index branchIndex)
      (removedContentRoot index indexMem branchIndex branchIndexMem)
  obtain ⟨index, indexMem, branchIndex, branchIndexMem,
      coefficientBound, survivingLarge⟩ :=
    full_factor_degree_transfer_of_local_exception_bounds
      indices branchIndices parent multiplicity
      (fun index branchIndex ↦ (branch index branchIndex).natDegree)
      assigned (fun index branchIndex ↦ (removedRoots index branchIndex).card)
      surviving DX DY DZ gammaN discardedDegree challengeCount
      multiplicityPositive branchDegreeSumLe branchCountLe yDegreeBudget
      weightedDegreeBudget globalMultiplierPositive challengeCountLe
      challengeCountLarge removalPartition removedSmall
  refine ⟨index, indexMem, branchIndex, branchIndexMem, ?_, survivingLarge⟩
  intro order yExponent coefficientNeZero
  exact coefficientBound x₀ order yExponent coefficientNeZero

/-- Proposition 7.10 from its polynomial factorization and successful
challenge hypotheses. The `specializedSeparable` hypothesis is exactly the
choice made in Step 2 of BCHKS26: every positive-`Y`-degree specialization
`Rᵢ(x₀,Y,Z)` remains separable over `K(Z)`. The proof derives nonvanishing of
the intrinsic regular derivative on every irreducible branch, constructs the
discard set, the disjoint factor/branch assignment, every local
pole/resultant set, and the final genuine simple surviving branch. -/
theorem full_factor_degree_transfer
    {K ι κ : Type*} [Field K] [DecidableEq K]
    [DecidableEq ι] [DecidableEq κ]
    (indices : Finset ι) (branchIndices : ι → Finset κ)
    (Q : TrivariatePolynomial K) (globalContent : BivariatePolynomial K)
    (parent : ι → TrivariatePolynomial K) (multiplicity : ι → Nat)
    (x₀ : K) (content : ι → Polynomial K)
    (branch : ι → κ → BivariatePolynomial K)
    (challenges : Finset K) (candidate : K → Polynomial K)
    (DX DY DZ gammaN : Nat)
    (globalContentNeZero : globalContent ≠ 0)
    (parentNeZero : ∀ index ∈ indices, parent index ≠ 0)
    (parentPositive : ∀ index ∈ indices, 1 ≤ (parent index).natDegree)
    (multiplicityPositive : ∀ index ∈ indices, 1 ≤ multiplicity index)
    (globalFactorization : Q = Polynomial.C globalContent *
      ∏ index ∈ indices, parent index ^ multiplicity index)
    (contentNeZero : ∀ index ∈ indices, content index ≠ 0)
    (branchNeZero : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        branch index branchIndex ≠ 0)
    (branchPositive : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        0 < (branch index branchIndex).natDegree)
    (branchIrreducible : ∀ index ∈ indices,
      ∀ branchIndex ∈ branchIndices index,
        Irreducible (branch index branchIndex))
    (specializationFactorization : ∀ index ∈ indices,
      specializeX x₀ (parent index) = Polynomial.C (content index) *
        ∏ branchIndex ∈ branchIndices index, branch index branchIndex)
    (specializedSeparable : ∀ index ∈ indices,
      (branchPolynomial (specializeX x₀ (parent index))).Separable)
    (QYDegree : Q.natDegree ≤ DY)
    (QWeightedDegree : fullYZWeightedDegree 1 Q ≤ DZ)
    (globalMultiplierPositive : 1 ≤ 2 * DX * DY ^ 2)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidatePolynomial z (candidate z) Q = 0)
    (challengeCountLarge :
      2 * DX * DY ^ 2 * DZ + (gammaN + 1) * DY < challenges.card) :
    ∃ index ∈ activeFactorIndices indices branchIndices,
      ∃ branchIndex ∈ branchIndices index,
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
            gammaN + 1 < surviving.card ∧
        ∀ z ∈ surviving,
          z ∈ challenges ∧
          challengeCandidatePolynomial z (candidate z) (parent index) = 0 ∧
          (content index).eval z ≠ 0 ∧
          ∃ _localRoot : (branch index branchIndex).eval₂
              (Polynomial.evalRingHom z) ((candidate z).eval x₀) = 0,
            (branch index branchIndex).leadingCoeff.eval z ≠ 0 ∧
            specializedDerivativeValue (parent index) x₀ z
              (shiftedCandidateSeries x₀ (candidate z))
                (parent index).natDegree ≠ 0 := by
  classical
  let active := activeFactorIndices indices branchIndices
  let discarded := factorTransferDiscarded indices branchIndices
    globalContent content challenges
  let source := challenges \ discarded
  let assignmentProperty : K → ι → κ → Prop :=
    fun z index branchIndex ↦
      challengeCandidatePolynomial z (candidate z) (parent index) = 0 ∧
        ((content index).eval z = 0 ∨
          (branch index branchIndex).eval₂ (Polynomial.evalRingHom z)
            ((candidate z).eval x₀) = 0)
  have assignmentExists : ∀ z ∈ source,
      ∃ index ∈ active, ∃ branchIndex ∈ branchIndices index,
        assignmentProperty z index branchIndex := by
    intro z zMem
    have zMemChallenges : z ∈ challenges := (Finset.mem_sdiff.mp zMem).1
    have zNotDiscarded : z ∉ discarded := (Finset.mem_sdiff.mp zMem).2
    exact exists_active_factor_branch_assignment indices branchIndices Q
      globalContent parent multiplicity x₀ content branch globalFactorization
      multiplicityPositive specializationFactorization challenges candidate
      candidateRoot z zMemChallenges zNotDiscarded
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
    · obtain ⟨index, indexMem, localMem⟩ := Finset.mem_biUnion.mp inactiveMem
      exact (Finset.mem_filter.mp localMem).1
  have discardedCard : discarded.card ≤ discardedDegree := by
    exact factorTransferDiscarded_card_le indices branchIndices globalContent
      content challenges globalContentNeZero contentNeZero
  have challengeCountLe : challenges.card ≤ discardedDegree +
      ∑ index ∈ active,
        ∑ branchIndex ∈ branchIndices index,
          (assigned index branchIndex).card := by
    have partition := Finset.card_sdiff_add_card_eq_card discardedSubset
    dsimp [source] at assignmentCount
    omega
  obtain ⟨yDegreeBudget, weightedDegreeBudget⟩ :=
    activeFactor_degree_budgets indices branchIndices Q globalContent parent
      multiplicity x₀ content branch globalContentNeZero parentNeZero
      multiplicityPositive globalFactorization contentNeZero branchNeZero
      specializationFactorization DY DZ QYDegree QWeightedDegree
  have branchDegreeSumLe : ∀ index ∈ active,
      ∑ branchIndex ∈ branchIndices index,
        (branch index branchIndex).natDegree ≤ (parent index).natDegree := by
    intro index indexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    exact specialization_branch_yDegree_summation (parent index) x₀
      (branchIndices index) (content index) (branch index)
      (contentNeZero index indexInIndices) (branchNeZero index indexInIndices)
      (specializationFactorization index indexInIndices)
  have branchCountLe : ∀ index ∈ active,
      (branchIndices index).card ≤ (parent index).natDegree := by
    intro index indexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    exact specialization_branch_count_le (parent index) x₀
      (branchIndices index) (content index) (branch index)
      (contentNeZero index indexInIndices) (branchNeZero index indexInIndices)
      (branchPositive index indexInIndices)
      (specializationFactorization index indexInIndices)
  have branchWeightLe : ∀ index ∈ active,
      ∀ branchIndex ∈ branchIndices index,
        localBivariateWeight 1 (branch index branchIndex) ≤
          fullYZWeightedDegree 1 (parent index) := by
    intro index indexMem branchIndex branchIndexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    have termLe : localBivariateWeight 1 (branch index branchIndex) ≤
        ∑ candidate ∈ branchIndices index,
          localBivariateWeight 1 (branch index candidate) :=
      Finset.single_le_sum
        (f := fun candidate ↦ localBivariateWeight 1 (branch index candidate))
        (fun _ _ ↦ Nat.zero_le _) branchIndexMem
    have sumBound := specialization_content_branch_weight_summation
      (parent index) x₀ 1 (branchIndices index) (content index)
      (branch index) (contentNeZero index indexInIndices)
      (branchNeZero index indexInIndices)
      (specializationFactorization index indexInIndices)
    omega
  have factorDvd : ∀ index ∈ active,
      ∀ branchIndex ∈ branchIndices index,
        branch index branchIndex ∣ specializeX x₀ (parent index) := by
    intro index indexMem branchIndex branchIndexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    rw [specializationFactorization index indexInIndices]
    exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (branch index) branchIndexMem)
      (Polynomial.C (content index))
  have etaNeZero : ∀ index ∈ active,
      ∀ branchIndex ∈ branchIndices index,
        regularDerivativeElement (parent index) (branch index branchIndex) x₀
          (parent index).natDegree ≠ 0 := by
    intro index indexMem branchIndex branchIndexMem
    have indexInIndices : index ∈ indices :=
      (Finset.mem_filter.mp indexMem).1
    exact regularDerivativeElement_ne_zero_of_specialized_separable
      (parent index) (branch index branchIndex)
      (branchIrreducible index indexInIndices branchIndex branchIndexMem)
      (branchPositive index indexInIndices branchIndex branchIndexMem)
      x₀ (parent index).natDegree le_rfl
      (factorDvd index indexMem branchIndex branchIndexMem)
      (specializedSeparable index indexInIndices)
  let localData (index : ι) (indexMem : index ∈ active)
      (branchIndex : κ) (branchIndexMem : branchIndex ∈ branchIndices index) :=
    poleResultantExceptionalData (parent index)
      (branch index branchIndex)
      (branchIrreducible index (Finset.mem_filter.mp indexMem).1
        branchIndex branchIndexMem)
      (branchPositive index (Finset.mem_filter.mp indexMem).1
        branchIndex branchIndexMem)
      (parentPositive index (Finset.mem_filter.mp indexMem).1)
      x₀ (content index)
      (∏ candidate ∈ branchIndices index, branch index candidate)
      (specializationFactorization index (Finset.mem_filter.mp indexMem).1)
      (factorDvd index indexMem branchIndex branchIndexMem)
      (branchWeightLe index indexMem branchIndex branchIndexMem)
      (etaNeZero index indexMem branchIndex branchIndexMem)
      (assigned index branchIndex)
  let removed : ι → κ → Finset K := fun index branchIndex ↦
    if indexMem : index ∈ active then
      if branchIndexMem : branchIndex ∈ branchIndices index then
        (localData index indexMem branchIndex branchIndexMem).exceptional
      else ∅
    else ∅
  let surviving : ι → κ → Finset K := fun index branchIndex ↦
    assigned index branchIndex \ removed index branchIndex
  have removedSmall : ∀ index ∈ active,
      ∀ branchIndex ∈ branchIndices index,
        (removed index branchIndex).card <
          (parent index).natDegree * (branch index branchIndex).natDegree *
            fullYZWeightedDegree 1 (parent index) := by
    intro index indexMem branchIndex branchIndexMem
    simpa [removed, indexMem, branchIndexMem] using
      (localData index indexMem branchIndex branchIndexMem).exceptionalCard
  have removedSubset : ∀ index ∈ active,
      ∀ branchIndex ∈ branchIndices index,
        removed index branchIndex ⊆ assigned index branchIndex := by
    intro index indexMem branchIndex branchIndexMem
    simpa [removed, indexMem, branchIndexMem] using
      (localData index indexMem branchIndex branchIndexMem).exceptionalSubset
  have removalPartition : ∀ index ∈ active,
      ∀ branchIndex ∈ branchIndices index,
        (assigned index branchIndex).card =
          (removed index branchIndex).card + (surviving index branchIndex).card := by
    intro index indexMem branchIndex branchIndexMem
    have partition := Finset.card_sdiff_add_card_eq_card
      (removedSubset index indexMem branchIndex branchIndexMem)
    dsimp [surviving]
    omega
  obtain ⟨index, indexMem, branchIndex, branchIndexMem,
      coefficientBound, survivingLarge⟩ :=
    full_factor_degree_transfer_of_local_exception_bounds active branchIndices
      parent multiplicity
      (fun index branchIndex ↦ (branch index branchIndex).natDegree)
      (fun index branchIndex ↦ (assigned index branchIndex).card)
      (fun index branchIndex ↦ (removed index branchIndex).card)
      (fun index branchIndex ↦ (surviving index branchIndex).card)
      DX DY DZ gammaN discardedDegree challenges.card
      (fun index indexMem ↦ multiplicityPositive index
        (Finset.mem_filter.mp indexMem).1)
      branchDegreeSumLe branchCountLe yDegreeBudget weightedDegreeBudget
      globalMultiplierPositive challengeCountLe challengeCountLarge
      removalPartition removedSmall
  refine ⟨index, indexMem, branchIndex, branchIndexMem,
    surviving index branchIndex, ?_, survivingLarge, ?_⟩
  · intro order yExponent coefficientNeZero
    exact coefficientBound x₀ order yExponent coefficientNeZero
  · intro z zMem
    have zMemAssigned : z ∈ assigned index branchIndex :=
      (Finset.mem_sdiff.mp zMem).1
    have zNotRemoved : z ∉ removed index branchIndex :=
      (Finset.mem_sdiff.mp zMem).2
    obtain ⟨zMemSource, factorRoot, localAlternative⟩ :=
      assignedProperty index indexMem branchIndex branchIndexMem z zMemAssigned
    have zMemChallenges : z ∈ challenges := (Finset.mem_sdiff.mp zMemSource).1
    have zNotExceptional : z ∉
        (localData index indexMem branchIndex branchIndexMem).exceptional := by
      simpa [removed, indexMem, branchIndexMem] using zNotRemoved
    obtain ⟨leadingValueNeZero, resultantValueNeZero⟩ :=
      (localData index indexMem branchIndex branchIndexMem).regularOutside
        z zMemAssigned zNotExceptional
    have contentValueNeZero : (content index).eval z ≠ 0 := by
      intro contentZero
      apply zNotExceptional
      exact (localData index indexMem branchIndex branchIndexMem).contentIncluded
        z zMemAssigned contentZero
    have localRoot : (branch index branchIndex).eval₂
        (Polynomial.evalRingHom z) ((candidate z).eval x₀) = 0 :=
      localAlternative.resolve_left contentValueNeZero
    let rootPair := branchRootPair (branch index branchIndex)
      (branchPositive index (Finset.mem_filter.mp indexMem).1
        branchIndex branchIndexMem) x₀ z (candidate z) localRoot
    let specialization := branchSpecialization (branch index branchIndex)
      (branchPositive index (Finset.mem_filter.mp indexMem).1
        branchIndex branchIndexMem) x₀ z (candidate z) localRoot
    have xiSpecializationNeZero : specialization
        (localData index indexMem branchIndex branchIndexMem).xi ≠ 0 := by
      intro xiZero
      apply resultantValueNeZero
      exact eval_canonicalRepresentative_resultant_eq_zero
        (branch index branchIndex)
        (branchIrreducible index (Finset.mem_filter.mp indexMem).1
          branchIndex branchIndexMem).ne_zero
        (branchPositive index (Finset.mem_filter.mp indexMem).1
          branchIndex branchIndexMem)
        (localData index indexMem branchIndex branchIndexMem).xi z
        (branchRootValue (branch index branchIndex) x₀ z (candidate z))
        rootPair xiZero
    have mappedClearing := congrArg specialization
      (localData index indexMem branchIndex branchIndexMem).clearing
    rw [map_mul, branchSpecialization_of] at mappedClearing
    have etaSpecializationNeZero : specialization
        (regularDerivativeElement (parent index) (branch index branchIndex) x₀
          (parent index).natDegree) ≠ 0 := by
      rw [mappedClearing]
      exact mul_ne_zero leadingValueNeZero xiSpecializationNeZero
    have derivativeValueNeZero : specializedDerivativeValue (parent index)
        x₀ z (shiftedCandidateSeries x₀ (candidate z))
          (parent index).natDegree ≠ 0 := by
      intro derivativeZero
      apply etaSpecializationNeZero
      rw [branchSpecialization_regularDerivativeElement (parent index)
        (branch index branchIndex)
        (branchPositive index (Finset.mem_filter.mp indexMem).1
          branchIndex branchIndexMem)
        x₀ z (candidate z) localRoot (parent index).natDegree,
        derivativeZero, mul_zero]
    exact ⟨zMemChallenges, factorRoot, contentValueNeZero, localRoot,
      leadingValueNeZero, derivativeValueNeZero⟩

#print axioms shiftedCoefficient_fullDegree_le
#print axioms eval_challengeCandidatePolynomial
#print axioms exists_factor_root_of_fullFactorization
#print axioms content_root_or_exists_branch_root
#print axioms global_content_root_card_le
#print axioms factorTransferDiscarded_card_le
#print axioms fullDegreeCounterexample_specialized_zDegree
#print axioms fullDegreeCounterexample_shifted_zDegree
#print axioms localBivariateWeight_pow_eq
#print axioms localBivariateWeight_finset_prod_eq
#print axioms fullFactor_weight_summation
#print axioms fullFactor_yDegree_summation
#print axioms activeFactor_degree_budgets
#print axioms exists_active_factor_branch_assignment
#print axioms exists_disjoint_factor_branch_assignment
#print axioms specializeX_fullYZWeightedDegree_le
#print axioms specialization_content_branch_weight_summation
#print axioms specialization_branch_yDegree_summation
#print axioms specialization_content_dvd_clearedDerivativeRepresentative
#print axioms eval₂_clearedDerivativeRepresentative_eq_zero_of_content_root
#print axioms exists_pole_resultant_exceptional_set
#print axioms poleResultantExceptionalData
#print axioms card_content_root_specializations_lt_pole_budget
#print axioms factor_square_weight_sum_le_global
#print axioms full_factor_global_allowance
#print axioms exists_factor_branch_above_preliminary_allowance
#print axioms remove_local_exception_budget
#print axioms full_factor_degree_transfer_of_local_exception_bounds
#print axioms full_factor_degree_transfer_from_content_root_sets
#print axioms full_factor_degree_transfer

end

end WeightedHensel

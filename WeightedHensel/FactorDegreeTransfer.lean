/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.CoarseBounds
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

/-- Paper-facing full-factor transfer.  The assignment and removal data are
the explicit finite sets/counts constructed in Proposition 7.10: unlike a
prose phrase such as “genuine specializations”, every discarded and surviving
cardinality is visible in the hypotheses.  The conclusion includes both the
full shifted-coefficient bound (111) and the strict surviving allowance
(121). -/
theorem full_factor_degree_transfer
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

#print axioms shiftedCoefficient_fullDegree_le
#print axioms fullDegreeCounterexample_specialized_zDegree
#print axioms fullDegreeCounterexample_shifted_zDegree
#print axioms localBivariateWeight_pow_eq
#print axioms localBivariateWeight_finset_prod_eq
#print axioms fullFactor_weight_summation
#print axioms fullFactor_yDegree_summation
#print axioms specializeX_fullYZWeightedDegree_le
#print axioms specialization_content_branch_weight_summation
#print axioms specialization_branch_yDegree_summation
#print axioms specialization_content_dvd_clearedDerivativeRepresentative
#print axioms eval₂_clearedDerivativeRepresentative_eq_zero_of_content_root
#print axioms factor_square_weight_sum_le_global
#print axioms full_factor_global_allowance
#print axioms exists_factor_branch_above_preliminary_allowance
#print axioms remove_local_exception_budget
#print axioms full_factor_degree_transfer

end

end WeightedHensel

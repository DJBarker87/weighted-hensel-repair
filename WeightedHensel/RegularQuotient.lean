/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.Monicization
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The regular quotient and its fixed function-field embedding

For an outer-positive branch polynomial `H ∈ K[Z][Y]`, this file defines
the monic regular quotient `O = K[Z][T]/(Hhat)`, canonical representatives of
`T`-degree below `deg_Y H`, and the map to `K(Z)[Y]/(H)` sending `T` to
`W Y`.  The map is proved injective by a direct degree argument.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-- The rational function field `K(Z)`. -/
abbrev RationalFunctionField (K : Type*) [Field K] :=
  FractionRing (Polynomial K)

/-- A bivariate branch, regarded as a polynomial in `Y` over `K(Z)`. -/
def branchPolynomial
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    Polynomial (RationalFunctionField K) :=
  factor.map (algebraMap (Polynomial K) (RationalFunctionField K))

/-- Passage from `K[Z]` to `K(Z)` preserves outer degree. -/
@[simp] theorem branchPolynomial_natDegree
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    (branchPolynomial factor).natDegree = factor.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective (Polynomial K) (RationalFunctionField K)) factor

/-- A positive-degree irreducible branch stays irreducible over `K(Z)`.
This is Gauss's lemma, with primitivity derived rather than assumed. -/
theorem branchPolynomial_irreducible
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree) :
    Irreducible (branchPolynomial factor) := by
  have factorPrimitive : factor.IsPrimitive :=
    factorIrreducible.isPrimitive (Nat.ne_of_gt factorPositive)
  exact (factorPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
    factorIrreducible

/-- The selected algebraic function-field extension `L = K(Z)[Y]/(H)`. -/
abbrev BranchFunctionField
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :=
  AdjoinRoot (branchPolynomial factor)

/-- The regular quotient `O = K[Z][T]/(Hhat)`. -/
abbrev RegularQuotient
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :=
  AdjoinRoot (monicization factor)

/-- Embed coefficient polynomials `K[Z]` into the selected branch
extension. -/
def regularCoefficientMap
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    Polynomial K →+* BranchFunctionField factor :=
  (AdjoinRoot.of (branchPolynomial factor)).comp
    (algebraMap (Polynomial K) (RationalFunctionField K))

/-- The coefficient map is injective as soon as the branch has positive
outer degree. -/
theorem regularCoefficientMap_injective
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) :
    Function.Injective (regularCoefficientMap factor) := by
  have mappedDegreeNeZero : (branchPolynomial factor).degree ≠ 0 := by
    have mappedNeZero : branchPolynomial factor ≠ 0 := by
      intro mappedZero
      have degreeZero := congrArg Polynomial.natDegree mappedZero
      simp only [branchPolynomial_natDegree, Polynomial.natDegree_zero] at degreeZero
      omega
    rw [Polynomial.degree_eq_natDegree mappedNeZero, branchPolynomial_natDegree]
    exact_mod_cast (Nat.ne_of_gt factorPositive)
  exact (AdjoinRoot.of.injective_of_degree_ne_zero mappedDegreeNeZero).comp
      (IsFractionRing.injective (Polynomial K) (RationalFunctionField K))

/-- The integral generator `T = W Y` inside the selected branch
extension. -/
def regularGenerator
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    BranchFunctionField factor :=
  regularCoefficientMap factor factor.leadingCoeff *
    AdjoinRoot.root (branchPolynomial factor)

/-- The adjoined element `Y` is a root of the original branch. -/
theorem branchPolynomial_eval₂_root
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    factor.eval₂ (regularCoefficientMap factor)
        (AdjoinRoot.root (branchPolynomial factor)) = 0 := by
  unfold regularCoefficientMap
  rw [← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root (branchPolynomial factor)

/-- The integral generator is a root of the monicized branch equation. -/
theorem regularGenerator_isRoot
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) :
    (monicization factor).eval₂ (regularCoefficientMap factor)
        (regularGenerator factor) = 0 := by
  exact Polynomial.integralNormalization_eval₂_eq_zero
    (f := regularCoefficientMap factor)
    (z := AdjoinRoot.root (branchPolynomial factor))
    (branchPolynomial_eval₂_root factor)
    (fun coefficient coefficientZero ↦ by
      apply regularCoefficientMap_injective factor factorPositive
      simpa only [map_zero] using coefficientZero)

/-- The literal map `O → L`, sending `T` to `W Y`. -/
def regularToFunctionField
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) :
    RegularQuotient factor →+* BranchFunctionField factor :=
  AdjoinRoot.lift (regularCoefficientMap factor)
    (regularGenerator factor) (regularGenerator_isRoot factor factorPositive)

@[simp] theorem regularToFunctionField_root
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) :
    regularToFunctionField factor factorPositive
        (AdjoinRoot.root (monicization factor)) = regularGenerator factor := by
  exact AdjoinRoot.lift_root (regularGenerator_isRoot factor factorPositive)

@[simp] theorem regularToFunctionField_of
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) (coefficient : Polynomial K) :
    regularToFunctionField factor factorPositive
        (AdjoinRoot.of (monicization factor) coefficient) =
      regularCoefficientMap factor coefficient := by
  exact AdjoinRoot.lift_of (regularGenerator_isRoot factor factorPositive)

/-! ## Canonical regular representatives -/

/-- The canonical representative of outer degree below `deg_Y H`. -/
def canonicalRepresentative
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) :
    RegularQuotient factor →ₗ[Polynomial K] BivariatePolynomial K :=
  AdjoinRoot.modByMonicHom (monicization_monic factor factorNeZero)

/-- Canonical representatives represent their quotient class. -/
theorem mk_canonicalRepresentative
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (element : RegularQuotient factor) :
    AdjoinRoot.mk (monicization factor)
        (canonicalRepresentative factor factorNeZero element) = element := by
  exact AdjoinRoot.mk_leftInverse (monicization_monic factor factorNeZero) element

/-- The canonical representative has outer degree strictly below the branch
degree. -/
theorem canonicalRepresentative_natDegree_lt
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (element : RegularQuotient factor) :
    (canonicalRepresentative factor factorNeZero element).natDegree <
      factor.natDegree := by
  induction element using AdjoinRoot.induction_on with
  | ih representative =>
      change (representative %ₘ monicization factor).natDegree < factor.natDegree
      rw [← monicization_natDegree factor]
      apply Polynomial.natDegree_modByMonic_lt representative
        (monicization_monic factor factorNeZero)
      intro normalizedOne
      have degreeOne := congrArg Polynomial.natDegree normalizedOne
      simp only [monicization_natDegree, Polynomial.natDegree_one] at degreeOne
      omega

/-- Canonical representation of a product is monic reduction of the
product of canonical representatives. -/
theorem canonicalRepresentative_mul
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (left right : RegularQuotient factor) :
    canonicalRepresentative factor factorNeZero (left * right) =
      (canonicalRepresentative factor factorNeZero left *
        canonicalRepresentative factor factorNeZero right) %ₘ
          monicization factor := by
  induction left using AdjoinRoot.induction_on with
  | ih leftRepresentative =>
      induction right using AdjoinRoot.induction_on with
      | ih rightRepresentative =>
          change (leftRepresentative * rightRepresentative) %ₘ
              monicization factor =
            (leftRepresentative %ₘ monicization factor) *
              (rightRepresentative %ₘ monicization factor) %ₘ
                monicization factor
          exact Polynomial.mul_modByMonic leftRepresentative rightRepresentative
            (monicization factor)

/-! ## Specialization of regular elements -/

/-- A root pair `(z,t)` of the monicized branch defines evaluation directly
on the regular quotient. No evaluation map from the full function field is
used. -/
def regularSpecialization
    {K : Type*} [Field K] (factor : BivariatePolynomial K) (z t : K)
    (rootPair : (monicization factor).eval₂ (Polynomial.evalRingHom z) t = 0) :
    RegularQuotient factor →+* K :=
  AdjoinRoot.lift (Polynomial.evalRingHom z) t rootPair

@[simp] theorem regularSpecialization_root
    {K : Type*} [Field K] (factor : BivariatePolynomial K) (z t : K)
    (rootPair : (monicization factor).eval₂ (Polynomial.evalRingHom z) t = 0) :
    regularSpecialization factor z t rootPair
        (AdjoinRoot.root (monicization factor)) = t := by
  exact AdjoinRoot.lift_root rootPair

@[simp] theorem regularSpecialization_of
    {K : Type*} [Field K] (factor : BivariatePolynomial K) (z t : K)
    (rootPair : (monicization factor).eval₂ (Polynomial.evalRingHom z) t = 0)
    (coefficient : Polynomial K) :
    regularSpecialization factor z t rootPair
        (AdjoinRoot.of (monicization factor) coefficient) = coefficient.eval z := by
  exact AdjoinRoot.lift_of rootPair

/-- Specialization is evaluation of the canonical representative. -/
theorem regularSpecialization_eq_eval_canonical
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (z t : K)
    (rootPair : (monicization factor).eval₂ (Polynomial.evalRingHom z) t = 0)
    (element : RegularQuotient factor) :
    regularSpecialization factor z t rootPair element =
      (canonicalRepresentative factor factorNeZero element).eval₂
        (Polynomial.evalRingHom z) t := by
  conv_lhs => rw [← mk_canonicalRepresentative factor factorNeZero element]
  exact AdjoinRoot.lift_mk rootPair _

/-! ## Weight in the regular quotient -/

/-- Natural-valued weight of the canonical representative. This helper is
used to prove bounds; `regularWeight` below records zero as `⊥`. -/
def regularWeightNat
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (element : RegularQuotient factor) : Nat :=
  iteratedBivariateWeight generatorWeight
    (canonicalRepresentative factor factorNeZero element)

/-- The paper's weight on regular quotient classes, with `Λ(0) = -∞`. -/
def regularWeight
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (element : RegularQuotient factor) : WithBot Nat :=
  if element = 0 then ⊥ else regularWeightNat factor factorNeZero generatorWeight element

@[simp] theorem regularWeight_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat) :
    regularWeight factor factorNeZero generatorWeight 0 = ⊥ := by
  simp [regularWeight]

theorem regularWeight_eq_coe
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    {element : RegularQuotient factor} (elementNeZero : element ≠ 0) :
    regularWeight factor factorNeZero generatorWeight element =
      (regularWeightNat factor factorNeZero generatorWeight element : WithBot Nat) := by
  simp [regularWeight, elementNeZero]

/-- Monic reduction does not increase the declared weight. -/
theorem regularWeightNat_mk_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (representative : BivariatePolynomial K) :
    regularWeightNat factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (AdjoinRoot.mk (monicization factor) representative) ≤
      iteratedBivariateWeight
        (totalBound + ell - ell * factor.natDegree) representative := by
  let generatorWeight := totalBound + ell - ell * factor.natDegree
  have modulusWeight : iteratedBivariateWeight generatorWeight
      (monicization factor) ≤ (monicization factor).natDegree * generatorWeight := by
    rw [monicization_natDegree]
    exact monicization_iteratedWeight_le factor factorNeZero ell totalBound
      coefficientBound
  change iteratedBivariateWeight generatorWeight
      (representative %ₘ monicization factor) ≤
    iteratedBivariateWeight generatorWeight representative
  exact iteratedBivariateWeight_modByMonic_le generatorWeight
    (monicization factor) (monicization_monic factor factorNeZero)
    modulusWeight representative

/-- Paper-valued form of `regularWeightNat_mk_le`: canonical reduction
does not increase `Λ`, including the zero case. -/
theorem regularWeight_mk_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (representative : BivariatePolynomial K) :
    regularWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (AdjoinRoot.mk (monicization factor) representative) ≤
      weight (totalBound + ell - ell * factor.natDegree) representative := by
  let element := AdjoinRoot.mk (monicization factor) representative
  by_cases elementZero : element = 0
  · have mkZero : AdjoinRoot.mk (monicization factor) representative = 0 := by
      simpa [element] using elementZero
    rw [regularWeight, if_pos mkZero]
    exact bot_le
  have representativeNeZero : representative ≠ 0 := by
    intro representativeZero
    apply elementZero
    simp [element, representativeZero]
  rw [regularWeight_eq_coe factor factorNeZero _ elementZero,
    weight_eq_coe _ representativeNeZero,
    localBivariateWeight_eq_iteratedBivariateWeight]
  exact WithBot.coe_le_coe.mpr
    (regularWeightNat_mk_le factor factorNeZero ell totalBound
      coefficientBound representative)

/-- Multiplication in the quotient is subadditive. -/
theorem regularWeightNat_mul_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (left right : RegularQuotient factor) :
    regularWeightNat factor factorNeZero
        (totalBound + ell - ell * factor.natDegree) (left * right) ≤
      regularWeightNat factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) left +
        regularWeightNat factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) right := by
  let generatorWeight := totalBound + ell - ell * factor.natDegree
  let leftRep := canonicalRepresentative factor factorNeZero left
  let rightRep := canonicalRepresentative factor factorNeZero right
  have modulusWeight : iteratedBivariateWeight generatorWeight
      (monicization factor) ≤ (monicization factor).natDegree * generatorWeight := by
    rw [monicization_natDegree]
    exact monicization_iteratedWeight_le factor factorNeZero ell totalBound
      coefficientBound
  change iteratedBivariateWeight generatorWeight
      (canonicalRepresentative factor factorNeZero (left * right)) ≤
    iteratedBivariateWeight generatorWeight leftRep +
      iteratedBivariateWeight generatorWeight rightRep
  rw [canonicalRepresentative_mul factor factorNeZero]
  exact (iteratedBivariateWeight_modByMonic_le generatorWeight
      (monicization factor) (monicization_monic factor factorNeZero)
      modulusWeight (leftRep * rightRep)).trans
    (iteratedBivariateWeight_mul_le generatorWeight leftRep rightRep)

/-- Addition in the quotient is max-bounded. -/
theorem regularWeightNat_add_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (left right : RegularQuotient factor) :
    regularWeightNat factor factorNeZero generatorWeight (left + right) ≤
      max (regularWeightNat factor factorNeZero generatorWeight left)
        (regularWeightNat factor factorNeZero generatorWeight right) := by
  unfold regularWeightNat canonicalRepresentative
  rw [map_add]
  exact iteratedBivariateWeight_add_le generatorWeight _ _

@[simp] theorem regularWeightNat_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat) :
    regularWeightNat factor factorNeZero generatorWeight 0 = 0 := by
  unfold regularWeightNat canonicalRepresentative
  rw [map_zero]
  exact iteratedBivariateWeight_zero generatorWeight

@[simp] theorem regularWeightNat_one
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat) :
    regularWeightNat factor factorNeZero generatorWeight 1 = 0 := by
  unfold regularWeightNat canonicalRepresentative
  change iteratedBivariateWeight generatorWeight (1 %ₘ monicization factor) = 0
  by_cases degreeZero : (monicization factor).natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero
      (monicization_monic factor factorNeZero) degreeZero,
      Polynomial.modByMonic_one]
    exact iteratedBivariateWeight_zero generatorWeight
  · have degreePositive : 0 < (monicization factor).natDegree :=
      Nat.pos_of_ne_zero degreeZero
    rw [(Polynomial.modByMonic_eq_self_iff
      (monicization_monic factor factorNeZero)).mpr]
    · apply Nat.eq_zero_of_le_zero
      apply iteratedBivariateWeight_le_of_coeff generatorWeight 0 1
      intro exponent exponentMem
      have exponentZero : exponent = 0 := by
        by_contra exponentNeZero
        exact (Polynomial.mem_support_iff.mp exponentMem)
          (by simp [Polynomial.coeff_one, exponentNeZero])
      subst exponent
      simp
    · rw [Polynomial.degree_one,
        Polynomial.degree_eq_natDegree
          (monicization_monic factor factorNeZero).ne_zero]
      exact_mod_cast degreePositive

@[simp] theorem regularWeightNat_neg
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (element : RegularQuotient factor) :
    regularWeightNat factor factorNeZero generatorWeight (-element) =
      regularWeightNat factor factorNeZero generatorWeight element := by
  unfold regularWeightNat canonicalRepresentative
  rw [map_neg]
  exact iteratedBivariateWeight_neg generatorWeight _

/-- Powers of a regular element have at most the corresponding multiple of
its weight. -/
theorem regularWeightNat_pow_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (element : RegularQuotient factor) (power : Nat) :
    regularWeightNat factor factorNeZero
        (totalBound + ell - ell * factor.natDegree) (element ^ power) ≤
      power * regularWeightNat factor factorNeZero
        (totalBound + ell - ell * factor.natDegree) element := by
  induction power with
  | zero => simp
  | succ power induction =>
      rw [pow_succ, Nat.succ_mul]
      exact (regularWeightNat_mul_le factor factorNeZero ell totalBound
        coefficientBound _ _).trans (Nat.add_le_add induction le_rfl)

/-- A finite sum with a common ceiling retains that ceiling. -/
theorem regularWeightNat_finset_sum_le
    {K ι : Type*} [Field K]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (generatorWeight bound : Nat) (indices : Finset ι)
    (element : ι → RegularQuotient factor)
    (elementBound : ∀ index ∈ indices,
      regularWeightNat factor factorNeZero generatorWeight (element index) ≤ bound) :
    regularWeightNat factor factorNeZero generatorWeight
        (∑ index ∈ indices, element index) ≤ bound := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices indexNotMem induction =>
      rw [Finset.sum_insert indexNotMem]
      exact (regularWeightNat_add_le factor factorNeZero generatorWeight _ _).trans <|
        max_le (elementBound index (Finset.mem_insert_self index indices))
          (induction (fun other otherMem ↦ elementBound other
            (Finset.mem_insert_of_mem otherMem)))

/-- A finite product is bounded by the sum of the factor weights. -/
theorem regularWeightNat_finset_prod_le
    {K ι : Type*} [Field K]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (indices : Finset ι) (element : ι → RegularQuotient factor) :
    regularWeightNat factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (∏ index ∈ indices, element index) ≤
      ∑ index ∈ indices,
        regularWeightNat factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) (element index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices indexNotMem induction =>
      rw [Finset.prod_insert indexNotMem, Finset.sum_insert indexNotMem]
      exact (regularWeightNat_mul_le factor factorNeZero ell totalBound
        coefficientBound _ _).trans (Nat.add_le_add le_rfl induction)

/-- An embedded coefficient polynomial costs at most its `Z`-degree. -/
theorem regularWeightNat_of_le_natDegree
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (coefficient : Polynomial K) :
    regularWeightNat factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (AdjoinRoot.of (monicization factor) coefficient) ≤
      coefficient.natDegree := by
  unfold AdjoinRoot.of
  have reduced := regularWeightNat_mk_le factor factorNeZero ell totalBound
    coefficientBound (Polynomial.C coefficient)
  exact reduced.trans <| by
    rw [← Polynomial.monomial_zero_left]
    simpa using iteratedBivariateWeight_monomial_le
      (totalBound + ell - ell * factor.natDegree) 0 coefficient

/-- The regular generator `T` costs at most its declared weight. -/
theorem regularWeightNat_root_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound) :
    regularWeightNat factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (AdjoinRoot.root (monicization factor)) ≤
      totalBound + ell - ell * factor.natDegree := by
  have reduced := regularWeightNat_mk_le factor factorNeZero ell totalBound
    coefficientBound Polynomial.X
  exact reduced.trans <| by
    rw [show (Polynomial.X : BivariatePolynomial K) =
      Polynomial.monomial 1 1 by rfl]
    simpa using iteratedBivariateWeight_monomial_le
      (totalBound + ell - ell * factor.natDegree) 1 (1 : Polynomial K)

/-- The `WithBot` quotient weight is max-bounded under addition. -/
theorem regularWeight_add_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (left right : RegularQuotient factor) :
    regularWeight factor factorNeZero generatorWeight (left + right) ≤
      max (regularWeight factor factorNeZero generatorWeight left)
        (regularWeight factor factorNeZero generatorWeight right) := by
  by_cases leftZero : left = 0
  · subst left
    simp
  by_cases rightZero : right = 0
  · subst right
    simp
  by_cases sumZero : left + right = 0
  · simp [regularWeight, sumZero]
  simp only [regularWeight_eq_coe factor factorNeZero generatorWeight sumZero,
    regularWeight_eq_coe factor factorNeZero generatorWeight leftZero,
    regularWeight_eq_coe factor factorNeZero generatorWeight rightZero]
  change (regularWeightNat factor factorNeZero generatorWeight (left + right) :
      WithBot Nat) ≤
    (max (regularWeightNat factor factorNeZero generatorWeight left)
      (regularWeightNat factor factorNeZero generatorWeight right) : Nat)
  exact WithBot.coe_le_coe.mpr
    (regularWeightNat_add_le factor factorNeZero generatorWeight left right)

/-- The `WithBot` quotient weight is subadditive under multiplication. -/
theorem regularWeight_mul_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (left right : RegularQuotient factor) :
    regularWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree) (left * right) ≤
      regularWeight factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) left +
        regularWeight factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) right := by
  by_cases leftZero : left = 0
  · subst left
    simp
  by_cases rightZero : right = 0
  · subst right
    simp
  by_cases productZero : left * right = 0
  · simp [regularWeight, productZero]
  simp only [regularWeight_eq_coe factor factorNeZero _ productZero,
    regularWeight_eq_coe factor factorNeZero _ leftZero,
    regularWeight_eq_coe factor factorNeZero _ rightZero]
  exact_mod_cast regularWeightNat_mul_le factor factorNeZero ell totalBound
    coefficientBound left right

/-! ## Faithfulness and domain structure -/

/-- The regular quotient embeds injectively into the branch extension.
The proof rescales a hypothetical relation back to `Y`, where its degree is
strictly below `deg H`. -/
theorem regularToFunctionField_injective
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree) :
    Function.Injective (regularToFunctionField factor factorPositive) := by
  intro left right mappedEquality
  suffices left - right = 0 by exact sub_eq_zero.mp this
  let element := left - right
  let representative := canonicalRepresentative factor factorNeZero element
  let rationalMap : Polynomial K →+* RationalFunctionField K :=
    algebraMap (Polynomial K) (RationalFunctionField K)
  let mappedRepresentative := representative.map rationalMap
  let mappedFactor := branchPolynomial factor
  let leading := rationalMap factor.leadingCoeff
  let unscaledRepresentative := mappedRepresentative.scaleRoots leading⁻¹
  have elementMappedZero : regularToFunctionField factor factorPositive element = 0 := by
    change regularToFunctionField factor factorPositive (left - right) = 0
    rw [map_sub, mappedEquality, sub_self]
  have representativeRoot : representative.eval₂ (regularCoefficientMap factor)
      (regularGenerator factor) = 0 := by
    have elementMappedZero' := elementMappedZero
    rw [← mk_canonicalRepresentative factor factorNeZero element]
      at elementMappedZero'
    unfold regularToFunctionField at elementMappedZero'
    rw [AdjoinRoot.lift_mk] at elementMappedZero'
    exact elementMappedZero'
  have leadingNeZero : leading ≠ 0 := by
    intro leadingZero
    apply Polynomial.leadingCoeff_ne_zero.mpr factorNeZero
    apply (IsFractionRing.injective (Polynomial K) (RationalFunctionField K))
    simpa [leading, rationalMap] using leadingZero
  have mappedRepresentativeRoot : mappedRepresentative.eval₂
      (AdjoinRoot.of mappedFactor)
      ((AdjoinRoot.of mappedFactor) leading * AdjoinRoot.root mappedFactor) = 0 := by
    change (representative.map rationalMap).eval₂ (AdjoinRoot.of mappedFactor)
      ((AdjoinRoot.of mappedFactor) leading * AdjoinRoot.root mappedFactor) = 0
    rw [Polynomial.eval₂_map]
    change representative.eval₂ (regularCoefficientMap factor)
      (regularGenerator factor) = 0
    exact representativeRoot
  have inverseMul :
      (AdjoinRoot.of mappedFactor) leading⁻¹ *
          ((AdjoinRoot.of mappedFactor) leading * AdjoinRoot.root mappedFactor) =
        AdjoinRoot.root mappedFactor := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ leadingNeZero, map_one, one_mul]
  have unscaledRoot : unscaledRepresentative.eval₂
      (AdjoinRoot.of mappedFactor) (AdjoinRoot.root mappedFactor) = 0 := by
    rw [← inverseMul]
    change (mappedRepresentative.scaleRoots leading⁻¹).eval₂
      (AdjoinRoot.of mappedFactor)
      ((AdjoinRoot.of mappedFactor) leading⁻¹ *
        ((AdjoinRoot.of mappedFactor) leading * AdjoinRoot.root mappedFactor)) = 0
    rw [Polynomial.scaleRoots_eval₂_mul]
    rw [mappedRepresentativeRoot, mul_zero]
  have mappedFactorDvd : mappedFactor ∣ unscaledRepresentative := by
    apply AdjoinRoot.mk_eq_zero.mp
    rw [← AdjoinRoot.aeval_eq]
    simpa [Polynomial.aeval_def] using unscaledRoot
  have representativeDegreeLt : representative.natDegree < factor.natDegree :=
    canonicalRepresentative_natDegree_lt factor factorNeZero factorPositive element
  have rationalMapInjective : Function.Injective rationalMap :=
    IsFractionRing.injective (Polynomial K) (RationalFunctionField K)
  have unscaledDegreeLt : unscaledRepresentative.natDegree < mappedFactor.natDegree := by
    simp only [unscaledRepresentative, Polynomial.natDegree_scaleRoots,
      mappedRepresentative, Polynomial.natDegree_map_eq_of_injective
        rationalMapInjective, mappedFactor, branchPolynomial_natDegree]
    exact representativeDegreeLt
  have unscaledZero : unscaledRepresentative = 0 := by
    by_contra unscaledNeZero
    exact (Polynomial.not_dvd_of_natDegree_lt unscaledNeZero unscaledDegreeLt)
      mappedFactorDvd
  have mappedRepresentativeZero : mappedRepresentative = 0 := by
    by_contra mappedRepresentativeNeZero
    exact Polynomial.scaleRoots_ne_zero mappedRepresentativeNeZero leading⁻¹
      unscaledZero
  have representativeZero : representative = 0 := by
    exact (Polynomial.map_eq_zero_iff rationalMapInjective).mp mappedRepresentativeZero
  change element = 0
  rw [← mk_canonicalRepresentative factor factorNeZero element]
  have canonicalZero : canonicalRepresentative factor factorNeZero element = 0 := by
    simpa [representative] using representativeZero
  rw [canonicalZero, map_zero]

/-- Under the paper's irreducibility hypothesis, the regular quotient is an
integral domain. -/
theorem regularQuotient_isDomain
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree) :
    IsDomain (RegularQuotient factor) := by
  letI : Fact (Irreducible (branchPolynomial factor)) :=
    ⟨branchPolynomial_irreducible factor factorIrreducible factorPositive⟩
  exact Function.Injective.isDomain
    (regularToFunctionField factor factorPositive)
    (regularToFunctionField_injective factor factorIrreducible.ne_zero factorPositive)

/-- Any nonzero regular branch factor remains nonzero in the function-field
extension. -/
theorem regularToFunctionField_ne_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    {element : RegularQuotient factor} (elementNeZero : element ≠ 0) :
    regularToFunctionField factor factorPositive element ≠ 0 := by
  intro mappedZero
  apply elementNeZero
  apply regularToFunctionField_injective factor factorNeZero factorPositive
  simpa using mappedZero

#print axioms branchPolynomial_irreducible
#print axioms regularGenerator_isRoot
#print axioms canonicalRepresentative_natDegree_lt
#print axioms canonicalRepresentative_mul
#print axioms regularSpecialization_eq_eval_canonical
#print axioms regularWeight_zero
#print axioms regularWeightNat_mk_le
#print axioms regularWeight_mk_le
#print axioms regularWeightNat_mul_le
#print axioms regularWeightNat_add_le
#print axioms regularWeightNat_pow_le
#print axioms regularWeightNat_finset_sum_le
#print axioms regularWeightNat_finset_prod_le
#print axioms regularWeightNat_of_le_natDegree
#print axioms regularWeightNat_root_le
#print axioms regularWeight_add_le
#print axioms regularWeight_mul_le
#print axioms regularToFunctionField_injective
#print axioms regularQuotient_isDomain
#print axioms regularToFunctionField_ne_zero

end

end WeightedHensel

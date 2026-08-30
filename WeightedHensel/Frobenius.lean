/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.Specialization
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Perfect

/-!
# Frobenius powers and sparse translated polynomials

This file contains the characteristic-`p` algebra used in the inseparable
extension of the factor-transfer theorem.  If `q = p ^ f`, a `q`-th
power polynomial has translated coefficients only in indices divisible by
`q`.  Over a finite field, coefficientwise inverse Frobenius recovers the
unique polynomial root without changing its degree.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- The Frobenius exponent `q = p^f`. -/
def frobeniusPower (p f : Nat) : Nat := p ^ f

theorem frobeniusPower_pos
    (p f : Nat) [Fact p.Prime] :
    0 < frobeniusPower p f := by
  unfold frobeniusPower
  exact pow_pos (Fact.out : p.Prime).pos f

theorem frobeniusPower_ne_zero
    (p f : Nat) [Fact p.Prime] :
    frobeniusPower p f ≠ 0 :=
  Nat.ne_of_gt (frobeniusPower_pos p f)

/-- Coefficientwise inverse Frobenius on a univariate polynomial. -/
def polynomialFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : Polynomial K) : Polynomial K :=
  polynomial.map (iterateFrobeniusEquiv K p f).symm

@[simp] theorem coeff_polynomialFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : Polynomial K) (order : Nat) :
    (polynomialFrobeniusRoot p f polynomial).coeff order =
      (iterateFrobeniusEquiv K p f).symm (polynomial.coeff order) := by
  simp [polynomialFrobeniusRoot]

@[simp] theorem support_polynomialFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : Polynomial K) :
    (polynomialFrobeniusRoot p f polynomial).support =
      polynomial.support := by
  exact Polynomial.support_map_of_injective polynomial
    (iterateFrobeniusEquiv K p f).symm.injective

@[simp] theorem natDegree_polynomialFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : Polynomial K) :
    (polynomialFrobeniusRoot p f polynomial).natDegree =
      polynomial.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (iterateFrobeniusEquiv K p f).symm.injective polynomial
/-- The unique inverse-Frobenius root in a finite field raises back to the
original scalar. -/
@[simp] theorem frobeniusRoot_pow
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p] (value : K) :
    ((iterateFrobeniusEquiv K p f).symm value) ^ frobeniusPower p f =
      value := by
  unfold frobeniusPower
  change iterateFrobenius K p f
      ((iterateFrobeniusEquiv K p f).symm value) = value
  exact (iterateFrobeniusEquiv K p f).apply_symm_apply value

/-- Inverse Frobenius followed by the `q`-th power gives the sparse
expansion of the original polynomial. -/
theorem polynomialFrobeniusRoot_pow
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : Polynomial K) :
    polynomialFrobeniusRoot p f polynomial ^ frobeniusPower p f =
      Polynomial.expand K (frobeniusPower p f) polynomial := by
  let inverse : K →+* K := (iterateFrobeniusEquiv K p f).symm
  have mapped :=
    Polynomial.map_iterateFrobenius_expand
      p (polynomial.map inverse) f
  rw [Polynomial.map_expand, Polynomial.map_map] at mapped
  have composition :
      (iterateFrobenius K p f).comp inverse = RingHom.id K := by
    ext value
    exact (iterateFrobeniusEquiv K p f).apply_symm_apply value
  rw [composition, Polynomial.map_id] at mapped
  exact mapped.symm

/-- Evaluation commutes with taking the coefficientwise inverse-Frobenius
root, provided the evaluation point is also raised to the Frobenius power. -/
theorem eval_polynomialFrobeniusRoot_pow
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : Polynomial K) (value : K) :
    (polynomialFrobeniusRoot p f polynomial).eval value ^
        frobeniusPower p f =
      polynomial.eval (value ^ frobeniusPower p f) := by
  rw [← Polynomial.eval_pow, polynomialFrobeniusRoot_pow,
    Polynomial.expand_eval]

/-- Coefficientwise inverse Frobenius as an automorphism of the univariate
polynomial ring. -/
def polynomialFrobeniusRootEquiv
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p] :
    Polynomial K ≃+* Polynomial K :=
  Polynomial.mapEquiv (iterateFrobeniusEquiv K p f).symm

@[simp] theorem polynomialFrobeniusRootEquiv_apply
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : Polynomial K) :
    polynomialFrobeniusRootEquiv p f polynomial =
      polynomialFrobeniusRoot p f polynomial := by
  rfl

/-- Apply inverse Frobenius to every scalar coefficient of a bivariate
polynomial, leaving both variable exponents unchanged. -/
def bivariateFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : BivariatePolynomial K) : BivariatePolynomial K :=
  polynomial.map (polynomialFrobeniusRootEquiv p f).toRingHom

@[simp] theorem coeff_bivariateFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : BivariatePolynomial K) (exponent : Nat) :
    (bivariateFrobeniusRoot p f polynomial).coeff exponent =
      polynomialFrobeniusRoot p f (polynomial.coeff exponent) := by
  simp [bivariateFrobeniusRoot]

@[simp] theorem support_bivariateFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : BivariatePolynomial K) :
    (bivariateFrobeniusRoot p f polynomial).support =
      polynomial.support := by
  exact Polynomial.support_map_of_injective polynomial
    (polynomialFrobeniusRootEquiv p f).injective

@[simp] theorem natDegree_bivariateFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : BivariatePolynomial K) :
    (bivariateFrobeniusRoot p f polynomial).natDegree =
      polynomial.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (polynomialFrobeniusRootEquiv p f).injective polynomial

/-- Inverse Frobenius does not change any monomial exponent, hence it
preserves every local weighted degree. -/
theorem localBivariateWeight_bivariateFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f tWeight : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : BivariatePolynomial K) :
    localBivariateWeight tWeight
        (bivariateFrobeniusRoot p f polynomial) =
      localBivariateWeight tWeight polynomial := by
  rw [localBivariateWeight_eq_iteratedBivariateWeight,
    localBivariateWeight_eq_iteratedBivariateWeight]
  simp [iteratedBivariateWeight]

/-- Bivariate evaluation after inverse Frobenius becomes the original
evaluation after raising both inputs to the Frobenius power. -/
theorem eval₂_bivariateFrobeniusRoot_pow
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : BivariatePolynomial K) (z y : K) :
    (bivariateFrobeniusRoot p f polynomial).eval₂
          (Polynomial.evalRingHom z) y ^ frobeniusPower p f =
      polynomial.eval₂
        (Polynomial.evalRingHom (z ^ frobeniusPower p f))
        (y ^ frobeniusPower p f) := by
  unfold bivariateFrobeniusRoot
  rw [Polynomial.eval₂_map]
  unfold frobeniusPower
  change iterateFrobenius K p f
      (polynomial.eval₂
        ((Polynomial.evalRingHom z).comp
          (polynomialFrobeniusRootEquiv p f).toRingHom) y) =
    polynomial.eval₂ (Polynomial.evalRingHom (z ^ p ^ f)) (y ^ p ^ f)
  rw [Polynomial.hom_eval₂]
  congr 1
  ext coefficient
  · simp only [RingHom.comp_apply]
    rw [show (polynomialFrobeniusRootEquiv p f).toRingHom
          (Polynomial.C coefficient) =
        Polynomial.C ((iterateFrobeniusEquiv K p f).symm coefficient) by
          simp [polynomialFrobeniusRootEquiv]]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C]
    exact (iterateFrobeniusEquiv K p f).apply_symm_apply coefficient
  · simp [polynomialFrobeniusRootEquiv, iterateFrobenius_def]

/-- A `q`-th power polynomial has no translated coefficient outside the
indices divisible by `q`. -/
theorem coeff_taylor_frobeniusPower_eq_zero_of_not_dvd
    {K : Type*} [Field K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (x₀ : K) (polynomial : Polynomial K) (order : Nat)
    (notDivisible : ¬frobeniusPower p f ∣ order) :
    ((polynomial ^ frobeniusPower p f).taylor x₀).coeff order = 0 := by
  unfold frobeniusPower at *
  rw [Polynomial.taylor_pow,
    ← Polynomial.map_iterateFrobenius_expand p (polynomial.taylor x₀) f,
    Polynomial.coeff_map,
    Polynomial.coeff_expand (pow_pos (Fact.out : p.Prime).pos f),
    if_neg notDivisible, map_zero]

/-- At a divisible index, the translated coefficient of a `q`-th power
is the `q`-th power of the corresponding original coefficient. -/
theorem coeff_taylor_frobeniusPower_mul
    {K : Type*} [Field K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (x₀ : K) (polynomial : Polynomial K) (order : Nat) :
    ((polynomial ^ frobeniusPower p f).taylor x₀).coeff
        (order * frobeniusPower p f) =
      ((polynomial.taylor x₀).coeff order) ^ frobeniusPower p f := by
  unfold frobeniusPower
  rw [Polynomial.taylor_pow,
    ← Polynomial.map_iterateFrobenius_expand p (polynomial.taylor x₀) f,
    Polynomial.coeff_map,
    Polynomial.coeff_expand_mul (pow_pos (Fact.out : p.Prime).pos f)]
  rfl

/-- Power-series form of translated Frobenius sparsity. -/
theorem coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_not_dvd
    {K : Type*} [Field K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (x₀ : K) (candidate : Polynomial K) (order : Nat)
    (notDivisible : ¬frobeniusPower p f ∣ order) :
    PowerSeries.coeff order
        (shiftedCandidateSeries x₀
          (candidate ^ frobeniusPower p f)) = 0 := by
  rw [shiftedCandidateSeries, shiftedEvaluationHom_eq_coe_taylor,
    Polynomial.coeff_coe]
  exact coeff_taylor_frobeniusPower_eq_zero_of_not_dvd
    p f x₀ candidate order notDivisible

/-- Raising a degree-`k` candidate to its Frobenius power gives degree at
most `qk`. -/
theorem natDegree_frobeniusPower_le
    {K : Type*} [Field K]
    (p f k : Nat) (candidate : Polynomial K)
    (degreeLe : candidate.natDegree ≤ k) :
    (candidate ^ frobeniusPower p f).natDegree ≤
      frobeniusPower p f * k := by
  exact Polynomial.natDegree_pow_le_of_le _ degreeLe

/-- The power of a line in the challenge has only its constant and
`q`-th challenge terms. -/
theorem linearChallenge_frobeniusPower
    {K : Type*} [Field K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (constant linear : K) :
    (Polynomial.C constant + Polynomial.C linear * Polynomial.X) ^
        frobeniusPower p f =
      Polynomial.C (constant ^ frobeniusPower p f) +
        Polynomial.C (linear ^ frobeniusPower p f) *
          Polynomial.X ^ frobeniusPower p f := by
  unfold frobeniusPower
  rw [← Polynomial.map_iterateFrobenius_expand p _ f]
  simp only [map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, iterateFrobenius_def]

/-- Frobenius powers are injective in the polynomial domain. -/
theorem polynomial_frobeniusPower_injective
    {K : Type*} [Field K]
    (p f : Nat) [Fact p.Prime] [CharP K p] :
    Function.Injective
      (fun polynomial : Polynomial K ↦
        polynomial ^ frobeniusPower p f) := by
  exact iterateFrobenius_inj (Polynomial K) p f

#print axioms polynomialFrobeniusRoot_pow
#print axioms coeff_taylor_frobeniusPower_eq_zero_of_not_dvd
#print axioms coeff_shiftedCandidateSeries_frobeniusPower_eq_zero_of_not_dvd
#print axioms natDegree_frobeniusPower_le
#print axioms linearChallenge_frobeniusPower
#print axioms polynomial_frobeniusPower_injective

end

end WeightedHensel

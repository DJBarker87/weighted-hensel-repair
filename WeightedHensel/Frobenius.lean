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


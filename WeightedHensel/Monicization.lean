/- Copyright (c) 2026 Dominic Barker. All rights reserved. -/

import WeightedHensel.WeightedDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# The integral local branch used by the weighted Hensel argument

The paper Appendix A replaces a local factor `H(Y,Z)`, with leading coefficient
`W(Z)`, by

`H̃(T,Z) = W(Z)^(deg H - 1) * H(T / W(Z), Z)`.

Mathlib's `Polynomial.integralNormalization` is exactly this coefficientwise
construction.  This file uses that Mathlib definition, proves the scaled
branch root satisfies the monic polynomial, and constructs the literal map
from the resulting finite `K[Z]`-algebra into the fixed function field.  No
division by a possibly vanishing specialization of `W` occurs here.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-- The paper's integral normalization of a fixed local factor. -/
def monicization
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    BivariatePolynomial K :=
  factor.integralNormalization

/-- A nonzero local factor has a monic integral normalization. -/
theorem monicization_monic
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) :
    (monicization factor).Monic := by
  exact Polynomial.monic_integralNormalization factorNeZero

/-- Monicization preserves the exact outer (`Y`/`T`) degree. -/
@[simp] theorem monicization_natDegree
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    (monicization factor).natDegree = factor.natDegree := by
  exact Polynomial.natDegree_integralNormalization

/-- The division-free coefficient formula defining the paper's
`W^(h-1) H(T/W,Z)`. In particular, this definition contains no
substitution into a fraction field. -/
theorem monicization_coeff
    {K : Type*} [Field K] (factor : BivariatePolynomial K) (i : Nat) :
    (monicization factor).coeff i =
      if factor.degree = i then 1 else
        factor.coeff i * factor.leadingCoeff ^ (factor.natDegree - 1 - i) := by
  exact Polynomial.integralNormalization_coeff

/-- Below the leading term, monicization multiplies the coefficient of
`T^i` by the explicit nonnegative power `W^(h-1-i)`. -/
theorem monicization_coeff_of_lt
    {K : Type*} [Field K] (factor : BivariatePolynomial K) (i : Nat)
    (hi : i < factor.natDegree) :
    (monicization factor).coeff i =
      factor.coeff i * factor.leadingCoeff ^ (factor.natDegree - 1 - i) := by
  exact Polynomial.integralNormalization_coeff_ne_natDegree (Nat.ne_of_lt hi)

/-- The polynomial identity behind the notation
`Hhat(T,Z) = W^(h-1) H(T/W,Z)`, stated without division. -/
theorem monicization_eval₂_leadingCoeff_mul
    {K S : Type*} [Field K] [CommSemiring S]
    (factor : BivariatePolynomial K) (factorPositive : 0 < factor.natDegree)
    (f : Polynomial K →+* S) (y : S) :
    (monicization factor).eval₂ f (f factor.leadingCoeff * y) =
      f factor.leadingCoeff ^ (factor.natDegree - 1) * factor.eval₂ f y := by
  simpa [monicization] using
    (Polynomial.integralNormalization_eval₂_leadingCoeff_mul
      factorPositive f y)

theorem monicization_root_of_localFactor_root
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) (z y : K)
    (root : factor.eval₂ (Polynomial.evalRingHom z) y = 0) :
    (monicization factor).eval₂ (Polynomial.evalRingHom z)
        ((factor.leadingCoeff).eval z * y) = 0 := by
  calc
    (monicization factor).eval₂ (Polynomial.evalRingHom z)
        ((factor.leadingCoeff).eval z * y) =
        (Polynomial.evalRingHom z factor.leadingCoeff) ^
            (factor.natDegree - 1) *
          factor.eval₂ (Polynomial.evalRingHom z) y := by
      exact monicization_eval₂_leadingCoeff_mul factor factorPositive
        (Polynomial.evalRingHom z) y
    _ = 0 := by rw [root, mul_zero]

/-- The literal map from the integral branch algebra into its rational
function field, sending the quotient generator to `T = W Y`. -/
theorem monicization_coefficientWeight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound) :
    ∀ exponent ∈ (monicization factor).support,
      ((monicization factor).coeff exponent).natDegree +
          exponent * (totalBound + ell - ell * factor.natDegree) ≤
        factor.natDegree *
          (totalBound + ell - ell * factor.natDegree) := by
  let degree := factor.natDegree
  let coefficientBudget := totalBound - ell * degree
  have leadingMem : degree ∈ factor.support := by
    exact Polynomial.natDegree_mem_support_of_nonzero factorNeZero
  have leadingBound := coefficientBound degree leadingMem
  have degreeWeightLe : ell * degree ≤ totalBound := by omega
  have generatorWeight : totalBound + ell - ell * degree =
      coefficientBudget + ell := by
    dsimp [coefficientBudget]
    omega
  intro exponent exponentMem
  rw [generatorWeight]
  have originalMem : exponent ∈ factor.support :=
    Polynomial.support_integralNormalization_subset exponentMem
  have exponentLe : exponent ≤ degree :=
    Polynomial.le_natDegree_of_mem_supp exponent originalMem
  rcases exponentLe.eq_or_lt with exponentEq | exponentLt
  · subst exponent
    have leadingCoefficient :
        (monicization factor).coeff degree = 1 := by
      exact Polynomial.integralNormalization_coeff_natDegree factorNeZero
    rw [leadingCoefficient]
    simp [degree]
  · have exponentNe : exponent ≠ degree := Nat.ne_of_lt exponentLt
    have normalizedCoefficient :
        (monicization factor).coeff exponent =
          factor.coeff exponent *
            factor.leadingCoeff ^ (degree - 1 - exponent) := by
      exact Polynomial.integralNormalization_coeff_ne_natDegree exponentNe
    rw [normalizedCoefficient]
    have originalBound := coefficientBound exponent originalMem
    have leadingDegree : factor.leadingCoeff.natDegree =
        (factor.coeff degree).natDegree := by
      rfl
    have leadingBudget : factor.leadingCoeff.natDegree ≤
        coefficientBudget := by
      rw [leadingDegree]
      dsimp [coefficientBudget]
      omega
    have coefficientDegree : (factor.coeff exponent).natDegree ≤
        coefficientBudget + ell * (degree - exponent) := by
      have totalDecomposition : totalBound =
          coefficientBudget + ell * degree := by
        dsimp [coefficientBudget]
        omega
      have degreeDecomposition : degree =
          exponent + (degree - exponent) := by omega
      have totalDecomposition' : totalBound =
          coefficientBudget + ell * exponent +
            ell * (degree - exponent) := by
        calc
          totalBound = coefficientBudget + ell * degree :=
            totalDecomposition
          _ = coefficientBudget +
              ell * (exponent + (degree - exponent)) := by
            exact congrArg (fun value => coefficientBudget + ell * value)
              degreeDecomposition
          _ = coefficientBudget + ell * exponent +
              ell * (degree - exponent) := by
            rw [Nat.mul_add, Nat.add_assoc]
      omega
    have normalizedDegree :
        (factor.coeff exponent *
          factor.leadingCoeff ^ (degree - 1 - exponent)).natDegree ≤
        (factor.coeff exponent).natDegree +
          (degree - 1 - exponent) * factor.leadingCoeff.natDegree :=
      Polynomial.natDegree_mul_le.trans <|
        Nat.add_le_add_left Polynomial.natDegree_pow_le _
    calc
      (factor.coeff exponent *
            factor.leadingCoeff ^ (degree - 1 - exponent)).natDegree +
          exponent * (coefficientBudget + ell) ≤
          ((factor.coeff exponent).natDegree +
            (degree - 1 - exponent) *
              factor.leadingCoeff.natDegree) +
            exponent * (coefficientBudget + ell) :=
        Nat.add_le_add_right normalizedDegree _
      _ ≤ (coefficientBudget + ell * (degree - exponent) +
            (degree - 1 - exponent) * coefficientBudget) +
          exponent * (coefficientBudget + ell) := by
        gcongr
      _ = degree * (coefficientBudget + ell) := by
        have decomposition : degree = exponent + 1 +
            (degree - 1 - exponent) := by omega
        have subtractDecomposition : degree - exponent =
            1 + (degree - 1 - exponent) := by omega
        rw [subtractDecomposition]
        conv_rhs => rw [decomposition]
        ring

/-- If `H` obeys the source weighted-degree bound
`deg_Z H_j + ell*j ≤ D`, then its integral normalization has weight at
most `d_H * (D + ell - ell*d_H)`. -/
theorem monicization_weight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound) :
    localBivariateWeight
        (totalBound + ell - ell * factor.natDegree)
        (monicization factor) ≤
      factor.natDegree *
        (totalBound + ell - ell * factor.natDegree) := by
  apply localBivariateWeight_le_of_coeff
  exact monicization_coefficientWeight_le factor factorNeZero ell
    totalBound coefficientBound

/-- The same monicization bound in the iterated-support presentation used
by the literal division proof. -/
theorem monicization_iteratedWeight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound) :
    iteratedBivariateWeight
        (totalBound + ell - ell * factor.natDegree)
        (monicization factor) ≤
      factor.natDegree *
        (totalBound + ell - ell * factor.natDegree) := by
  apply iteratedBivariateWeight_le_of_coeff
  exact monicization_coefficientWeight_le factor factorNeZero ell
    totalBound coefficientBound

#print axioms monicization_coeff
#print axioms monicization_coeff_of_lt
#print axioms monicization_eval₂_leadingCoeff_mul
#print axioms monicization_monic
#print axioms monicization_root_of_localFactor_root
#print axioms monicization_coefficientWeight_le
#print axioms monicization_weight_le

end

end WeightedHensel

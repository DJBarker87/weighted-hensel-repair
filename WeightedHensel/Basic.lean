/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Basic notation for the weighted Hensel repair

The iterated polynomial convention throughout the development is:

* `K[Z,T] = Polynomial (Polynomial K)`, with inner variable `Z` and outer
  variable `T`;
* `K[X,Z,Y] = Polynomial (Polynomial (Polynomial K))`, with innermost
  variable `X`, middle variable `Z`, and outer variable `Y`.

These are plain Mathlib polynomial rings. No application-specific Aspis type
is part of the standalone interface.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

/-- The polynomial ring `K[Z,T]`, represented with `Z` inner and `T` outer. -/
abbrev BivariatePolynomial (K : Type*) [Semiring K] :=
  Polynomial (Polynomial K)

/-- The polynomial ring `K[X,Z,Y]`, represented with `X` innermost. -/
abbrev TrivariatePolynomial (K : Type*) [Semiring K] :=
  Polynomial (Polynomial (Polynomial K))

/-- The Hensel denominator exponent: `e 0 = 0` and `e t = 2t-1` for `t>0`. -/
def henselExponent (t : Nat) : Nat := 2 * t - 1

@[simp] theorem henselExponent_zero : henselExponent 0 = 0 := by
  rfl

theorem henselExponent_of_pos {t : Nat} (_positive : 0 < t) :
    henselExponent t = 2 * t - 1 := by
  rfl

@[simp] theorem henselExponent_succ (t : Nat) :
    henselExponent (t + 1) = 2 * t + 1 := by
  simp [henselExponent]
  omega

theorem henselExponent_monotone : Monotone henselExponent := by
  intro a b hab
  simp only [henselExponent]
  omega

/-- The source recurrence indicator `ε_s`, equal to one exactly at `s=0`. -/
def sourceEpsilon (s : Nat) : Nat := if s = 0 then 1 else 0

@[simp] theorem sourceEpsilon_zero : sourceEpsilon 0 = 1 := by
  simp [sourceEpsilon]

@[simp] theorem sourceEpsilon_of_pos {s : Nat} (positive : 0 < s) :
    sourceEpsilon s = 0 := by
  simp [sourceEpsilon, Nat.ne_of_gt positive]

theorem sourceEpsilon_le_one (s : Nat) : sourceEpsilon s ≤ 1 := by
  unfold sourceEpsilon
  split <;> omega

#print axioms henselExponent_of_pos
#print axioms henselExponent_monotone

end WeightedHensel

/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.Frobenius

/-!
# Compatible Frobenius roots of a regular branch

For a finite field of characteristic `p` and `q = p^f`, this file
constructs the coefficientwise inverse-Frobenius branch `Hroot`.  Its
regular quotient is canonically equivalent to the original quotient after
applying inverse Frobenius to coefficients.  Canonical representatives keep
exactly the same monomial support, so their regular weights are equal.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Inverse Frobenius preserves nonzeroness of a bivariate polynomial. -/
theorem bivariateFrobeniusRoot_ne_zero
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    {polynomial : BivariatePolynomial K} (polynomialNeZero : polynomial ≠ 0) :
    bivariateFrobeniusRoot p f polynomial ≠ 0 := by
  simpa [bivariateFrobeniusRoot] using
    (Polynomial.mapEquiv
      (polynomialFrobeniusRootEquiv p f)).injective.ne polynomialNeZero

/-- Inverse Frobenius preserves irreducibility. -/
theorem bivariateFrobeniusRoot_irreducible
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    {polynomial : BivariatePolynomial K}
    (polynomialIrreducible : Irreducible polynomial) :
    Irreducible (bivariateFrobeniusRoot p f polynomial) := by
  exact polynomialIrreducible.map
    (Polynomial.mapEquiv (polynomialFrobeniusRootEquiv p f))

/-- The leading coefficient is transformed by the inner polynomial
inverse-Frobenius equivalence. -/
theorem leadingCoeff_bivariateFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (polynomial : BivariatePolynomial K) :
    (bivariateFrobeniusRoot p f polynomial).leadingCoeff =
      polynomialFrobeniusRoot p f polynomial.leadingCoeff := by
  exact Polynomial.leadingCoeff_map_of_injective
    (polynomialFrobeniusRootEquiv p f).injective polynomial

/-- Integral monicization commutes with coefficientwise inverse Frobenius. -/
theorem monicization_bivariateFrobeniusRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0) :
    monicization (bivariateFrobeniusRoot p f factor) =
      (monicization factor).map
        (polynomialFrobeniusRootEquiv p f).toRingHom := by
  unfold monicization bivariateFrobeniusRoot
  exact Polynomial.integralNormalization_map
    (polynomialFrobeniusRootEquiv p f).toRingHom factor
    (by
      intro mappedZero
      apply Polynomial.leadingCoeff_ne_zero.mpr factorNeZero
      apply (polynomialFrobeniusRootEquiv p f).injective
      change polynomialFrobeniusRoot p f factor.leadingCoeff =
        polynomialFrobeniusRoot p f 0
      simpa [polynomialFrobeniusRoot] using mappedZero)

/-- The regular quotients of a branch and its coefficientwise
inverse-Frobenius transform are canonically equivalent. -/
def regularFrobeniusRootEquiv
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0) :
    RegularQuotient factor ≃+*
      RegularQuotient (bivariateFrobeniusRoot p f factor) :=
  AdjoinRoot.mapRingEquiv (polynomialFrobeniusRootEquiv p f)
    (monicization factor)
    (monicization (bivariateFrobeniusRoot p f factor)) (by
      rw [monicization_bivariateFrobeniusRoot p f factor factorNeZero]
      change Associated
        ((monicization factor).map
          (polynomialFrobeniusRootEquiv p f).toRingHom)
        ((monicization factor).map
          (polynomialFrobeniusRootEquiv p f).toRingHom)
      exact Associated.refl _)

@[simp] theorem regularFrobeniusRootEquiv_root
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0) :
    regularFrobeniusRootEquiv p f factor factorNeZero
        (AdjoinRoot.root (monicization factor)) =
      AdjoinRoot.root
        (monicization (bivariateFrobeniusRoot p f factor)) := by
  simp [regularFrobeniusRootEquiv]

@[simp] theorem regularFrobeniusRootEquiv_of
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (coefficient : Polynomial K) :
    regularFrobeniusRootEquiv p f factor factorNeZero
        (AdjoinRoot.of (monicization factor) coefficient) =
      AdjoinRoot.of (monicization (bivariateFrobeniusRoot p f factor))
        (polynomialFrobeniusRoot p f coefficient) := by
  simp [regularFrobeniusRootEquiv]

/-- The quotient equivalence maps an arbitrary polynomial representative
coefficientwise. -/
theorem regularFrobeniusRootEquiv_mk
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (representative : BivariatePolynomial K) :
    regularFrobeniusRootEquiv p f factor factorNeZero
        (AdjoinRoot.mk (monicization factor) representative) =
      AdjoinRoot.mk (monicization (bivariateFrobeniusRoot p f factor))
        (representative.map
          (polynomialFrobeniusRootEquiv p f).toRingHom) := by
  induction representative using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      simp only [map_add, Polynomial.map_add, leftIH, rightIH]
  | monomial exponent coefficient =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp

/-- Canonical representatives commute with the regular inverse-Frobenius
equivalence. -/
theorem canonicalRepresentative_regularFrobeniusRootEquiv
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (element : RegularQuotient factor) :
    canonicalRepresentative
        (bivariateFrobeniusRoot p f factor)
        (bivariateFrobeniusRoot_ne_zero p f factorNeZero)
        (regularFrobeniusRootEquiv p f factor factorNeZero element) =
      bivariateFrobeniusRoot p f
        (canonicalRepresentative factor factorNeZero element) := by
  induction element using AdjoinRoot.induction_on with
  | ih representative =>
      rw [regularFrobeniusRootEquiv_mk]
      change (representative.map
            (polynomialFrobeniusRootEquiv p f).toRingHom %ₘ
          monicization (bivariateFrobeniusRoot p f factor)) =
        (representative %ₘ monicization factor).map
          (polynomialFrobeniusRootEquiv p f).toRingHom
      rw [monicization_bivariateFrobeniusRoot p f factor factorNeZero,
        ← Polynomial.map_modByMonic
          (polynomialFrobeniusRootEquiv p f).toRingHom
          (monicization_monic factor factorNeZero)]

/-- The inverse-Frobenius regular equivalence preserves the exact natural
weight of canonical representatives. -/
theorem regularWeightNat_regularFrobeniusRootEquiv
    {K : Type*} [Field K] [Finite K]
    (p f tWeight : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (element : RegularQuotient factor) :
    regularWeightNat
        (bivariateFrobeniusRoot p f factor)
        (bivariateFrobeniusRoot_ne_zero p f factorNeZero) tWeight
        (regularFrobeniusRootEquiv p f factor factorNeZero element) =
      regularWeightNat factor factorNeZero tWeight element := by
  unfold regularWeightNat
  rw [canonicalRepresentative_regularFrobeniusRootEquiv]
  rw [← localBivariateWeight_eq_iteratedBivariateWeight,
    localBivariateWeight_bivariateFrobeniusRoot,
    localBivariateWeight_eq_iteratedBivariateWeight]
/-- The leading coefficient evaluation obeys the same compatible-root
identity as every coefficient polynomial. -/
theorem eval_leadingCoeff_bivariateFrobeniusRoot_pow
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (z : K) :
    ((bivariateFrobeniusRoot p f factor).leadingCoeff.eval z) ^
        frobeniusPower p f =
      factor.leadingCoeff.eval (z ^ frobeniusPower p f) := by
  rw [leadingCoeff_bivariateFrobeniusRoot,
    eval_polynomialFrobeniusRoot_pow]

/-- The scaled regular branch root is compatible with Frobenius. -/
theorem branchRootValue_bivariateFrobeniusRoot_pow
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K)
    (x₀ z : K) (candidate : Polynomial K) :
    branchRootValue (bivariateFrobeniusRoot p f factor) x₀ z candidate ^
        frobeniusPower p f =
      branchRootValue factor x₀ (z ^ frobeniusPower p f)
        (candidate ^ frobeniusPower p f) := by
  unfold branchRootValue
  rw [mul_pow, eval_leadingCoeff_bivariateFrobeniusRoot_pow,
    Polynomial.eval_pow]

/-- A source branch root for the powered candidate transports to a root of
the inverse-Frobenius branch for the original candidate. -/
theorem bivariateFrobeniusRoot_localRoot
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K)
    (x₀ z : K) (candidate : Polynomial K)
    (sourceLocalRoot :
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          ((candidate ^ frobeniusPower p f).eval x₀) = 0) :
    (bivariateFrobeniusRoot p f factor).eval₂
        (Polynomial.evalRingHom z) (candidate.eval x₀) = 0 := by
  have powered := eval₂_bivariateFrobeniusRoot_pow p f factor z
    (candidate.eval x₀)
  rw [Polynomial.eval_pow] at sourceLocalRoot
  rw [sourceLocalRoot] at powered
  exact (pow_eq_zero_iff (frobeniusPower_ne_zero p f)).mp powered

/-- The regular specialization diagram commutes after raising the target
value to the Frobenius power.  This is the formal compatible-root statement:
the target specialization is at `z`, while the source specialization is at
`z^q` and uses the powered candidate. -/
theorem branchSpecialization_regularFrobeniusRootEquiv_pow
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (sourceLocalRoot :
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          ((candidate ^ frobeniusPower p f).eval x₀) = 0)
    (element : RegularQuotient factor) :
    branchSpecialization
          (bivariateFrobeniusRoot p f factor)
          (by simpa using factorPositive)
          x₀ z candidate
          (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
            sourceLocalRoot)
          (regularFrobeniusRootEquiv p f factor factorNeZero element) ^
        frobeniusPower p f =
      branchSpecialization factor factorPositive x₀
        (z ^ frobeniusPower p f)
        (candidate ^ frobeniusPower p f) sourceLocalRoot element := by
  let rootedFactor := bivariateFrobeniusRoot p f factor
  let rootedFactorNeZero :=
    bivariateFrobeniusRoot_ne_zero p f factorNeZero
  let rootedLocalRoot :=
    bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
      sourceLocalRoot
  calc
    branchSpecialization rootedFactor (by simpa [rootedFactor] using factorPositive)
          x₀ z candidate rootedLocalRoot
          (regularFrobeniusRootEquiv p f factor factorNeZero element) ^
        frobeniusPower p f =
      ((canonicalRepresentative rootedFactor rootedFactorNeZero
          (regularFrobeniusRootEquiv p f factor factorNeZero element)).eval₂
        (Polynomial.evalRingHom z)
        (branchRootValue rootedFactor x₀ z candidate)) ^
          frobeniusPower p f := by
            unfold branchSpecialization
            rw [regularSpecialization_eq_eval_canonical]
    _ = (canonicalRepresentative factor factorNeZero element).eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          ((branchRootValue rootedFactor x₀ z candidate) ^
            frobeniusPower p f) := by
            rw [canonicalRepresentative_regularFrobeniusRootEquiv]
            exact eval₂_bivariateFrobeniusRoot_pow p f
              (canonicalRepresentative factor factorNeZero element) z
              (branchRootValue rootedFactor x₀ z candidate)
    _ = (canonicalRepresentative factor factorNeZero element).eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          (branchRootValue factor x₀ (z ^ frobeniusPower p f)
            (candidate ^ frobeniusPower p f)) := by
            rw [branchRootValue_bivariateFrobeniusRoot_pow]
    _ = branchSpecialization factor factorPositive x₀
          (z ^ frobeniusPower p f)
          (candidate ^ frobeniusPower p f) sourceLocalRoot element := by
            unfold branchSpecialization
            rw [regularSpecialization_eq_eval_canonical]

/-- Nonvanishing of a source regular specialization therefore implies
nonvanishing of its compatible inverse-Frobenius specialization. -/
theorem branchSpecialization_regularFrobeniusRootEquiv_ne_zero
    {K : Type*} [Field K] [Finite K]
    (p f : Nat) [Fact p.Prime] [CharP K p]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (sourceLocalRoot :
      factor.eval₂
          (Polynomial.evalRingHom (z ^ frobeniusPower p f))
          ((candidate ^ frobeniusPower p f).eval x₀) = 0)
    (element : RegularQuotient factor)
    (sourceNeZero :
      branchSpecialization factor factorPositive x₀
        (z ^ frobeniusPower p f)
        (candidate ^ frobeniusPower p f) sourceLocalRoot element ≠ 0) :
    branchSpecialization
        (bivariateFrobeniusRoot p f factor)
        (by simpa using factorPositive)
        x₀ z candidate
        (bivariateFrobeniusRoot_localRoot p f factor x₀ z candidate
          sourceLocalRoot)
        (regularFrobeniusRootEquiv p f factor factorNeZero element) ≠ 0 := by
  intro rootedZero
  have compatibility :=
    branchSpecialization_regularFrobeniusRootEquiv_pow p f factor
      factorNeZero factorPositive x₀ z candidate sourceLocalRoot element
  rw [rootedZero, zero_pow (frobeniusPower_ne_zero p f)] at compatibility
  exact sourceNeZero compatibility.symm


#print axioms bivariateFrobeniusRoot_irreducible
#print axioms monicization_bivariateFrobeniusRoot
#print axioms regularFrobeniusRootEquiv
#print axioms regularWeightNat_regularFrobeniusRootEquiv
#print axioms bivariateFrobeniusRoot_localRoot
#print axioms branchSpecialization_regularFrobeniusRootEquiv_pow
#print axioms branchSpecialization_regularFrobeniusRootEquiv_ne_zero

end

end WeightedHensel

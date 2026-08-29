/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.DirectRepair
import Mathlib.Algebra.Field.ZMod

/-!
# Counterexamples to the printed source estimates

The declarations in this file are propositions, not executable examples.
They check the three explicit examples in Section 3 of the paper.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ## Common coordinate polynomials -/

/-- `Z` in `K[Z,Y]`. -/
def counterexampleZ {K : Type*} [Field K] : BivariatePolynomial K :=
  Polynomial.C Polynomial.X

/-- `Y` in `K[Z,Y]`. -/
def counterexampleY {K : Type*} [Field K] : BivariatePolynomial K :=
  Polynomial.X

/-- `X` in `K[X,Z,Y]`. -/
def counterexampleChallenge {K : Type*} [Field K] : TrivariatePolynomial K :=
  Polynomial.C (Polynomial.C Polynomial.X)

/-- `Z` in `K[X,Z,Y]`. -/
def counterexampleTrivariateZ {K : Type*} [Field K] : TrivariatePolynomial K :=
  Polynomial.C Polynomial.X

/-- `Y` in `K[X,Z,Y]`. -/
def counterexampleTrivariateY {K : Type*} [Field K] : TrivariatePolynomial K :=
  Polynomial.X

/-- The selected linear branch `Y+Z^2`. -/
def counterexampleFactor (K : Type*) [Field K] : BivariatePolynomial K :=
  Polynomial.X + Polynomial.C (Polynomial.X ^ 2)

@[simp] theorem counterexampleFactor_ne_zero
    {K : Type*} [Field K] : counterexampleFactor K ≠ 0 := by
  have monic : (counterexampleFactor K).Monic := by
    change (Polynomial.X + Polynomial.C (Polynomial.X ^ 2 : Polynomial K)).Monic
    exact Polynomial.monic_X_add_C (Polynomial.X ^ 2)
  exact monic.ne_zero

@[simp] theorem counterexampleFactor_natDegree
    {K : Type*} [Field K] : (counterexampleFactor K).natDegree = 1 := by
  change (Polynomial.X + Polynomial.C (Polynomial.X ^ 2 : Polynomial K)).natDegree = 1
  exact Polynomial.natDegree_X_add_C (Polynomial.X ^ 2)

@[simp] theorem counterexampleFactor_leadingCoeff
    {K : Type*} [Field K] : (counterexampleFactor K).leadingCoeff = 1 := by
  have monic : (counterexampleFactor K).Monic := by
    change (Polynomial.X + Polynomial.C (Polynomial.X ^ 2 : Polynomial K)).Monic
    exact Polynomial.monic_X_add_C (Polynomial.X ^ 2)
  exact monic.leadingCoeff

/-- The branch root `-Z^2`. -/
def counterexampleRoot {K : Type*} [Field K] : Polynomial K :=
  -(Polynomial.X ^ 2)

theorem counterexampleRoot_is_root
    {K : Type*} [Field K] :
    (counterexampleFactor K).eval₂ (RingHom.id (Polynomial K))
      (counterexampleRoot : Polynomial K) = 0 := by
  simp [counterexampleFactor, counterexampleRoot]

/-! ## Saturation/base-case example -/

/-- The specialized parent `(Y+Z^2)(Y+Z+1)`. -/
def saturationSpecializedParent
    (K : Type*) [Field K] : BivariatePolynomial K :=
  counterexampleFactor K *
    (Polynomial.X + Polynomial.C (Polynomial.X + 1))

/-- The full saturation example
`R=(Y+Z^2)(Y+Z+1)+X`. -/
def saturationParent (K : Type*) [Field K] : TrivariatePolynomial K :=
  (counterexampleTrivariateY + counterexampleTrivariateZ ^ 2) *
      (counterexampleTrivariateY + counterexampleTrivariateZ + 1) +
    counterexampleChallenge

theorem saturationParent_specialize_zero
    {K : Type*} [Field K] :
    specializeX 0 (saturationParent K) = saturationSpecializedParent K := by
  simp [specializeX, saturationParent, saturationSpecializedParent,
    counterexampleChallenge, counterexampleTrivariateY,
    counterexampleTrivariateZ, counterexampleFactor]
  exact Or.inl (by ring)

theorem saturation_factor_divides
    {K : Type*} [Field K] :
    counterexampleFactor K ∣ saturationSpecializedParent K := by
  exact dvd_mul_right _ _

theorem saturationParent_branch_divides
    {K : Type*} [Field K] :
    counterexampleFactor K ∣ specializeX 0 (saturationParent K) := by
  rw [saturationParent_specialize_zero]
  exact saturation_factor_divides

@[simp] theorem saturation_parent_yDegree
    {K : Type*} [Field K] :
    (saturationSpecializedParent K).natDegree = 2 := by
  have factorMonic : (counterexampleFactor K).Monic := by
    change (Polynomial.X + Polynomial.C (Polynomial.X ^ 2 : Polynomial K)).Monic
    exact Polynomial.monic_X_add_C (Polynomial.X ^ 2)
  have otherMonic :
      (Polynomial.X + Polynomial.C (Polynomial.X + 1 : Polynomial K)).Monic :=
    Polynomial.monic_X_add_C (Polynomial.X + 1)
  rw [saturationSpecializedParent, factorMonic.natDegree_mul otherMonic,
    counterexampleFactor_natDegree,
    Polynomial.natDegree_X_add_C (Polynomial.X + 1 : Polynomial K)]

/-- In this branch `D_H=2`, `ell=1`, `h=1`, hence `b=1`, `tau=2`,
whereas `W=1` has degree zero. -/
theorem saturation_tau_strictly_exceeds_printed_base :
    let DH := 2
    let ell := 1
    let h := 1
    let b := DH - ell * h
    let tau := b + ell
    let w := (1 : Polynomial ℚ).natDegree
    tau > w + 1 := by
  norm_num

/-! ## Failure at the first positive Hensel order -/

/-- The full sharp example `R=Y+Z^2+XY^2`. -/
def positiveOrderParent (K : Type*) [Field K] : TrivariatePolynomial K :=
  Polynomial.C (Polynomial.X ^ 2 : Polynomial (Polynomial K)) +
    Polynomial.X + Polynomial.monomial 2 (Polynomial.C Polynomial.X)

theorem positiveOrderParent_coordinate_formula
    {K : Type*} [Field K] :
    positiveOrderParent K =
      counterexampleTrivariateY + counterexampleTrivariateZ ^ 2 +
        counterexampleChallenge * counterexampleTrivariateY ^ 2 := by
  simp [positiveOrderParent, counterexampleChallenge,
    counterexampleTrivariateY, counterexampleTrivariateZ,
    Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem positiveOrderParent_specialize_zero
    {K : Type*} [Field K] :
    specializeX 0 (positiveOrderParent K) = counterexampleFactor K := by
  simp [specializeX, positiveOrderParent, counterexampleFactor]
  ring

theorem positiveOrderParent_branch_divides
    {K : Type*} [Field K] :
    counterexampleFactor K ∣ specializeX 0 (positiveOrderParent K) := by
  rw [positiveOrderParent_specialize_zero]

@[simp] theorem positiveOrderParent_yDegree
    {K : Type*} [Field K] : (positiveOrderParent K).natDegree = 2 := by
  unfold positiveOrderParent
  compute_degree
  all_goals simp

theorem positiveOrderParent_coeff
    {K : Type*} [Field K] (exponent : Nat) :
    (positiveOrderParent K).coeff exponent =
      if exponent = 0 then Polynomial.X ^ 2
      else if exponent = 1 then 1
      else if exponent = 2 then Polynomial.C Polynomial.X
      else 0 := by
  unfold positiveOrderParent
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X,
    Polynomial.coeff_monomial]
  by_cases exponentZero : exponent = 0
  · subst exponent
    norm_num
  by_cases exponentOne : exponent = 1
  · subst exponent
    norm_num
  by_cases exponentTwo : exponent = 2
  · subst exponent
    norm_num
  have oneNe : 1 ≠ exponent := Ne.symm exponentOne
  have twoNe : 2 ≠ exponent := Ne.symm exponentTwo
  simp only [exponentZero, exponentOne, exponentTwo, oneNe, twoNe,
    ↓reduceIte, add_zero]

theorem positiveOrderParent_coefficient_bound
    {K : Type*} [Field K] :
    ParentCoefficientBound (positiveOrderParent K) 1 2 := by
  intro exponent exponentMem
  have coefficientNeZero := Polynomial.mem_support_iff.mp exponentMem
  have exponentLe : exponent ≤ 2 := by
    rw [← positiveOrderParent_yDegree (K := K)]
    exact Polynomial.le_natDegree_of_ne_zero coefficientNeZero
  rw [positiveOrderParent_coeff]
  interval_cases exponent <;> norm_num

/-- The first coefficient forced by
`alpha(U)+Z^2+U alpha(U)^2=0`. -/
def positiveOrderAlphaOne (K : Type*) [Field K] : Polynomial K :=
  -((counterexampleRoot : Polynomial K) ^ 2)

/-- The constant and linear coefficient equations of the Hensel identity. -/
theorem positive_order_hensel_coefficients
    {K : Type*} [Field K] :
    (counterexampleRoot : Polynomial K) + Polynomial.X ^ 2 = 0 ∧
      positiveOrderAlphaOne K + (counterexampleRoot : Polynomial K) ^ 2 = 0 := by
  constructor <;> simp [counterexampleRoot, positiveOrderAlphaOne]

theorem positiveOrderAlphaOne_eq
    {K : Type*} [Field K] :
    positiveOrderAlphaOne K = -(Polynomial.X ^ 4) := by
  simp [positiveOrderAlphaOne, counterexampleRoot]
  ring

/-- Since `W=xi=1`, the source numerator `beta_1` is the Hensel
coefficient itself. -/
def positiveOrderBetaOne (K : Type*) [Field K] : Polynomial K :=
  positiveOrderAlphaOne K

theorem positive_order_beta_one
    {K : Type*} [Field K] :
    positiveOrderBetaOne K = -(Polynomial.X ^ 4) :=
  positiveOrderAlphaOne_eq

theorem positive_order_beta_one_weight
    {K : Type*} [Field K] :
    weight 2 (Polynomial.C (positiveOrderBetaOne K)) = (4 : Nat) := by
  have betaNeZero : positiveOrderBetaOne K ≠ 0 := by
    rw [positive_order_beta_one]
    exact neg_ne_zero.mpr (pow_ne_zero 4 Polynomial.X_ne_zero)
  rw [weight_C_of_ne_zero 2 betaNeZero, Polynomial.degree_eq_natDegree betaNeZero]
  simp [positiveOrderBetaOne, positiveOrderAlphaOne, counterexampleRoot]

/-- `beta_1` as an element of the regular quotient for the selected branch. -/
def positiveOrderBetaOneRegular
    (K : Type*) [Field K] : RegularQuotient (counterexampleFactor K) :=
  AdjoinRoot.of (monicization (counterexampleFactor K)) (positiveOrderBetaOne K)

/-- The paper's quotient weight of `beta_1` is exactly four. -/
theorem positive_order_beta_one_regular_weight
    {K : Type*} [Field K] :
    regularWeight (counterexampleFactor K) counterexampleFactor_ne_zero 2
        (positiveOrderBetaOneRegular K) = (4 : Nat) := by
  have betaNeZero : positiveOrderBetaOne K ≠ 0 := by
    rw [positive_order_beta_one]
    exact neg_ne_zero.mpr (pow_ne_zero 4 Polynomial.X_ne_zero)
  have elementNeZero : positiveOrderBetaOneRegular K ≠ 0 := by
    intro elementZero
    have canonicalZero := congrArg
      (canonicalRepresentative (counterexampleFactor K)
        counterexampleFactor_ne_zero) elementZero
    simp only [positiveOrderBetaOneRegular] at canonicalZero
    rw [canonicalRepresentative_of_coefficient (counterexampleFactor K)
      counterexampleFactor_ne_zero (by simp) (positiveOrderBetaOne K), map_zero]
      at canonicalZero
    exact (Polynomial.C_ne_zero.mpr betaNeZero) canonicalZero
  rw [regularWeight_eq_coe (counterexampleFactor K)
    counterexampleFactor_ne_zero 2 elementNeZero]
  unfold regularWeightNat positiveOrderBetaOneRegular
  rw [canonicalRepresentative_of_coefficient (counterexampleFactor K)
    counterexampleFactor_ne_zero (by simp) (positiveOrderBetaOne K),
    ← localBivariateWeight_eq_iteratedBivariateWeight,
    rawWeight_C_eq_natDegree]
  norm_num [positiveOrderBetaOne, positiveOrderAlphaOne, counterexampleRoot]

/-- Equation (16) in the printed claim gives `1` at `t=1`. -/
def printedSourceCeiling (w xiWeight t : Nat) : Nat :=
  1 + (t + 1) * w + henselExponent t * xiWeight

/-- Repairing only the base term replaces the initial `1` by `tau`. -/
def baseOnlyRepairedCeiling (tau w xiWeight t : Nat) : Nat :=
  tau + (t + 1) * w + henselExponent t * xiWeight

theorem positive_order_printed_ceiling :
    printedSourceCeiling 0 0 1 = 1 := by
  norm_num [printedSourceCeiling, henselExponent]

theorem positive_order_base_only_ceiling :
    baseOnlyRepairedCeiling 2 0 0 1 = 2 := by
  norm_num [baseOnlyRepairedCeiling, henselExponent]

theorem positive_order_both_ceilings_fail :
    printedSourceCeiling 0 0 1 < 4 ∧
      baseOnlyRepairedCeiling 2 0 0 1 < 4 := by
  norm_num [printedSourceCeiling, baseOnlyRepairedCeiling, henselExponent]

/-! ## Failure of the derivative-numerator ceiling -/

/-- The specialized parent `(Y+Z^2)(Y^2+1)` over `F_5`. -/
def derivativeSpecializedParent : BivariatePolynomial (ZMod 5) :=
  counterexampleFactor (ZMod 5) * (Polynomial.X ^ 2 + 1)

/-- The full derivative example
`R=(Y+Z^2)(Y^2+1)+X` over `F_5`. -/
def derivativeCounterexampleParent : TrivariatePolynomial (ZMod 5) :=
  (counterexampleTrivariateY + counterexampleTrivariateZ ^ 2) *
      (counterexampleTrivariateY ^ 2 + 1) + counterexampleChallenge

theorem derivativeCounterexampleParent_specialize_zero :
    specializeX 0 derivativeCounterexampleParent = derivativeSpecializedParent := by
  simp [specializeX, derivativeCounterexampleParent, derivativeSpecializedParent,
    counterexampleChallenge, counterexampleTrivariateY,
    counterexampleTrivariateZ, counterexampleFactor]

theorem derivativeCounterexampleParent_branch_divides :
    counterexampleFactor (ZMod 5) ∣
      specializeX 0 derivativeCounterexampleParent := by
  rw [derivativeCounterexampleParent_specialize_zero]
  exact dvd_mul_right _ _

/-- Direct differentiation at the selected root gives `Z^4+1`. -/
theorem derivative_at_selected_branch :
    derivativeSpecializedParent.derivative.eval₂
        (RingHom.id (Polynomial (ZMod 5)))
        (counterexampleRoot : Polynomial (ZMod 5)) =
      Polynomial.X ^ 4 + 1 := by
  simp [derivativeSpecializedParent, counterexampleFactor, counterexampleRoot,
    Polynomial.derivative_pow]
  ring_nf

def derivativeCounterexampleXi : Polynomial (ZMod 5) :=
  Polynomial.X ^ 4 + 1

theorem derivative_counterexample_xi :
    derivativeCounterexampleXi = Polynomial.X ^ 4 + 1 := rfl

theorem derivative_counterexample_xi_weight :
    weight 2 (Polynomial.C derivativeCounterexampleXi) = (4 : Nat) := by
  have xiNeZero : derivativeCounterexampleXi ≠ 0 := by
    intro xiZero
    have coefficientZero := congrArg
      (fun polynomial : Polynomial (ZMod 5) ↦ polynomial.coeff 4) xiZero
    simp [derivativeCounterexampleXi, Polynomial.coeff_one] at coefficientZero
  have xiDegree : derivativeCounterexampleXi.natDegree = 4 := by
    unfold derivativeCounterexampleXi
    calc
      (Polynomial.X ^ 4 + 1 : Polynomial (ZMod 5)).natDegree =
          (Polynomial.X ^ 4 : Polynomial (ZMod 5)).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp)
      _ = 4 := by simp
  rw [weight_C_of_ne_zero 2 xiNeZero, Polynomial.degree_eq_natDegree xiNeZero]
  rw [xiDegree]

def derivativeCounterexampleXiRegular :
    RegularQuotient (counterexampleFactor (ZMod 5)) :=
  AdjoinRoot.of (monicization (counterexampleFactor (ZMod 5)))
    derivativeCounterexampleXi

theorem derivative_counterexample_xi_regular_weight :
    regularWeight (counterexampleFactor (ZMod 5))
        counterexampleFactor_ne_zero 2 derivativeCounterexampleXiRegular =
      (4 : Nat) := by
  have xiNeZero : derivativeCounterexampleXi ≠ 0 := by
    intro xiZero
    have coefficientZero := congrArg
      (fun polynomial : Polynomial (ZMod 5) ↦ polynomial.coeff 4) xiZero
    simp [derivativeCounterexampleXi, Polynomial.coeff_one] at coefficientZero
  have elementNeZero : derivativeCounterexampleXiRegular ≠ 0 := by
    intro elementZero
    have canonicalZero := congrArg
      (canonicalRepresentative (counterexampleFactor (ZMod 5))
        counterexampleFactor_ne_zero) elementZero
    simp only [derivativeCounterexampleXiRegular] at canonicalZero
    rw [canonicalRepresentative_of_coefficient
      (counterexampleFactor (ZMod 5)) counterexampleFactor_ne_zero
      (by simp) derivativeCounterexampleXi, map_zero] at canonicalZero
    exact (Polynomial.C_ne_zero.mpr xiNeZero) canonicalZero
  rw [regularWeight_eq_coe (counterexampleFactor (ZMod 5))
    counterexampleFactor_ne_zero 2 elementNeZero]
  unfold regularWeightNat derivativeCounterexampleXiRegular
  rw [canonicalRepresentative_of_coefficient
    (counterexampleFactor (ZMod 5)) counterexampleFactor_ne_zero
    (by simp) derivativeCounterexampleXi,
    ← localBivariateWeight_eq_iteratedBivariateWeight,
    rawWeight_C_eq_natDegree]
  have xiDegree : derivativeCounterexampleXi.natDegree = 4 := by
    unfold derivativeCounterexampleXi
    calc
      (Polynomial.X ^ 4 + 1 : Polynomial (ZMod 5)).natDegree =
          (Polynomial.X ^ 4 : Polynomial (ZMod 5)).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp)
      _ = 4 := by simp
  rw [xiDegree]

/-- The first printed derivative ceiling, equation (14) with `s=0,q=1`,
is `(D-1)+(d-2)w`. -/
def printedDerivativeCeiling (D d w : Nat) : Nat :=
  (D - 1) + (d - 2) * w

theorem derivative_printed_ceiling :
    printedDerivativeCeiling 4 3 0 = 3 := by
  norm_num [printedDerivativeCeiling]

theorem derivative_printed_ceiling_fails :
    printedDerivativeCeiling 4 3 0 < 4 := by
  norm_num [printedDerivativeCeiling]

#print axioms saturation_tau_strictly_exceeds_printed_base
#print axioms saturationParent_specialize_zero
#print axioms saturationParent_branch_divides
#print axioms positiveOrderParent_specialize_zero
#print axioms positiveOrderParent_coefficient_bound
#print axioms positive_order_beta_one
#print axioms positive_order_beta_one_weight
#print axioms positive_order_beta_one_regular_weight
#print axioms positive_order_printed_ceiling
#print axioms positive_order_base_only_ceiling
#print axioms positive_order_both_ceilings_fail
#print axioms derivative_at_selected_branch
#print axioms derivative_counterexample_xi_weight
#print axioms derivative_counterexample_xi_regular_weight
#print axioms derivative_printed_ceiling
#print axioms derivative_printed_ceiling_fails

end

end WeightedHensel

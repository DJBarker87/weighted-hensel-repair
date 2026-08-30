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

@[simp] theorem counterexampleFactor_coeff_zero
    {K : Type*} [Field K] :
    (counterexampleFactor K).coeff 0 = Polynomial.X ^ 2 := by
  simp only [counterexampleFactor, Polynomial.coeff_add,
    Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_add]

@[simp] theorem counterexampleFactor_coeff_one
    {K : Type*} [Field K] : (counterexampleFactor K).coeff 1 = 1 := by
  simp only [counterexampleFactor, Polynomial.coeff_add,
    Polynomial.coeff_X_one, Polynomial.coeff_C]
  norm_num

/-- The selected branch has the paper's coefficient bound `D_H=2` when
`ell=1`. -/
theorem counterexampleFactor_coefficient_bound
    {K : Type*} [Field K] :
    ∀ exponent ∈ (counterexampleFactor K).support,
      ((counterexampleFactor K).coeff exponent).natDegree + exponent ≤ 2 := by
  intro exponent exponentMem
  have exponentLe : exponent ≤ 1 := by
    rw [← counterexampleFactor_natDegree (K := K)]
    exact Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp exponentMem)
  interval_cases exponent
  · rw [counterexampleFactor_coeff_zero]
    simp
  · rw [counterexampleFactor_coeff_one]
    norm_num

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
  simp only [specializeX, saturationParent, counterexampleTrivariateY,
    counterexampleTrivariateZ, counterexampleChallenge, Polynomial.map_add,
    Polynomial.map_mul, map_X, Polynomial.map_pow, map_C, coe_mapRingHom,
    Polynomial.map_one, coe_evalRingHom, eval_X, map_zero, add_zero,
    saturationSpecializedParent, counterexampleFactor, map_pow, map_add,
    map_one, mul_eq_mul_left_iff]
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

/-! ## Admissibility of the three examples

The numerical failures above are not artifacts of reducible or inseparable
parents.  The following declarations check the irreducibility, separability,
and square-freeness assertions made in Section 3 of the paper.  Separability
in the response variable is stated after mapping the coefficient ring
`K[X,Z]` to its fraction field.
-/

/-- Ring equivalence interchanging the challenge variable `X` and the
response variable `Y`, while fixing `Z`. -/
def swapChallengeResponse
    (K : Type*) [Field K] :
    TrivariatePolynomial K ≃+* TrivariatePolynomial K :=
  (Polynomial.Bivariate.swap (R := Polynomial K)).toRingEquiv |>.trans
    ((Polynomial.mapAlgEquiv
      (Polynomial.Bivariate.swap (R := K))).toRingEquiv |>.trans
        (Polynomial.Bivariate.swap (R := Polynomial K)).toRingEquiv)

/-- The positive-order parent, viewed as a degree-one polynomial in the
challenge variable. -/
def positiveOrderParentByChallenge
    (K : Type*) [Field K] : Polynomial (BivariatePolynomial K) :=
  Polynomial.C ((Polynomial.C Polynomial.X : BivariatePolynomial K) ^ 2) *
      Polynomial.X +
    Polynomial.C
      (Polynomial.C Polynomial.X + (Polynomial.X : BivariatePolynomial K) ^ 2)

theorem positiveOrderParentByChallenge_irreducible
    {K : Type*} [Field K] :
    Irreducible (positiveOrderParentByChallenge K) := by
  apply Polynomial.irreducible_C_mul_X_add_C
  · exact pow_ne_zero 2 (Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero)
  · apply IsRelPrime.pow_left
    have innerPrime : Prime
        (Polynomial.C Polynomial.X : BivariatePolynomial K) :=
      Polynomial.prime_C_iff.mpr Polynomial.prime_X
    apply innerPrime.irreducible.isRelPrime_iff_not_dvd.mpr
    intro divides
    have coefficientDivides :=
      (Polynomial.C_dvd_iff_dvd_coeff Polynomial.X
        (Polynomial.C Polynomial.X +
          (Polynomial.X : BivariatePolynomial K) ^ 2)).mp divides 2
    have xDvdOne : (Polynomial.X : Polynomial K) ∣ 1 := by
      simpa using coefficientDivides
    exact Polynomial.not_isUnit_X (isUnit_iff_dvd_one.mpr xDvdOne)

theorem swapChallengeResponse_positiveOrderParent
    {K : Type*} [Field K] :
    swapChallengeResponse K (positiveOrderParent K) =
      positiveOrderParentByChallenge K := by
  simp [swapChallengeResponse, positiveOrderParent,
    positiveOrderParentByChallenge,
    Polynomial.Bivariate.swap_apply]
  ring

/-- The full positive-order counterexample parent is irreducible in
`K[X,Z,Y]`. -/
theorem positiveOrderParent_irreducible
    {K : Type*} [Field K] : Irreducible (positiveOrderParent K) := by
  have mappedIrreducible :
      Irreducible (swapChallengeResponse K (positiveOrderParent K)) := by
    rw [swapChallengeResponse_positiveOrderParent]
    exact positiveOrderParentByChallenge_irreducible
  exact mappedIrreducible.of_map

/-- The chosen linear branch is irreducible over `K[Z]`. -/
theorem counterexampleFactor_irreducible
    {K : Type*} [Field K] : Irreducible (counterexampleFactor K) := by
  have factorEq : counterexampleFactor K =
      Polynomial.X - Polynomial.C (-(Polynomial.X ^ 2 : Polynomial K)) := by
    simp [counterexampleFactor]
  rw [factorEq]
  exact Polynomial.irreducible_X_sub_C _

theorem counterexampleFactor_eq_X_sub_C
    {K : Type*} [Field K] : counterexampleFactor K =
      Polynomial.X - Polynomial.C (-(Polynomial.X ^ 2 : Polynomial K)) := by
  simp [counterexampleFactor]

/-- The chosen branch is simple: its response derivative is one. -/
theorem counterexampleFactor_derivative
    {K : Type*} [Field K] : (counterexampleFactor K).derivative = 1 := by
  unfold counterexampleFactor
  rw [Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C]
  simp

/-- The saturation parent, viewed as a monic linear polynomial in the
challenge variable. -/
def saturationParentByChallenge
    (K : Type*) [Field K] : Polynomial (BivariatePolynomial K) :=
  Polynomial.X + Polynomial.C
    (Polynomial.Bivariate.swap (saturationSpecializedParent K))

theorem saturationParentByChallenge_irreducible
    {K : Type*} [Field K] :
    Irreducible (saturationParentByChallenge K) := by
  simpa [saturationParentByChallenge, sub_eq_add_neg] using
    (Polynomial.irreducible_X_sub_C
      (-(Polynomial.Bivariate.swap (saturationSpecializedParent K))))

theorem swapChallengeResponse_saturationParent
    {K : Type*} [Field K] :
    swapChallengeResponse K (saturationParent K) =
      saturationParentByChallenge K := by
  simp [swapChallengeResponse, saturationParent, saturationParentByChallenge,
    saturationSpecializedParent, counterexampleFactor,
    counterexampleChallenge, counterexampleTrivariateY,
    counterexampleTrivariateZ, Polynomial.Bivariate.swap_apply]
  ring

/-- The full saturation parent is irreducible in `K[X,Z,Y]`. -/
theorem saturationParent_irreducible
    {K : Type*} [Field K] : Irreducible (saturationParent K) := by
  have mappedIrreducible :
      Irreducible (swapChallengeResponse K (saturationParent K)) := by
    rw [swapChallengeResponse_saturationParent]
    exact saturationParentByChallenge_irreducible
  exact mappedIrreducible.of_map

/-- The derivative example parent, viewed as a monic linear polynomial in
the challenge variable. -/
def derivativeCounterexampleParentByChallenge :
    Polynomial (BivariatePolynomial (ZMod 5)) :=
  Polynomial.X + Polynomial.C
    (Polynomial.Bivariate.swap derivativeSpecializedParent)

theorem derivativeCounterexampleParentByChallenge_irreducible :
    Irreducible derivativeCounterexampleParentByChallenge := by
  simpa [derivativeCounterexampleParentByChallenge, sub_eq_add_neg] using
    (Polynomial.irreducible_X_sub_C
      (-(Polynomial.Bivariate.swap derivativeSpecializedParent)))

theorem swapChallengeResponse_derivativeCounterexampleParent :
    swapChallengeResponse (ZMod 5) derivativeCounterexampleParent =
      derivativeCounterexampleParentByChallenge := by
  simp [swapChallengeResponse, derivativeCounterexampleParent,
    derivativeCounterexampleParentByChallenge, derivativeSpecializedParent,
    counterexampleFactor, counterexampleChallenge, counterexampleTrivariateY,
    counterexampleTrivariateZ, Polynomial.Bivariate.swap_apply]
  ring

/-- The derivative-counterexample parent is irreducible in
`F₅[X,Z,Y]`. -/
theorem derivativeCounterexampleParent_irreducible :
    Irreducible derivativeCounterexampleParent := by
  have mappedIrreducible : Irreducible
      (swapChallengeResponse (ZMod 5) derivativeCounterexampleParent) := by
    rw [swapChallengeResponse_derivativeCounterexampleParent]
    exact derivativeCounterexampleParentByChallenge_irreducible
  exact mappedIrreducible.of_map

/-- The coefficient field used to state separability in the response
variable. -/
abbrev CounterexampleResponseFunctionField
    (K : Type*) [Field K] := FractionRing (BivariatePolynomial K)

def parentInResponseFunctionField
    {K : Type*} [Field K] (parent : TrivariatePolynomial K) :
    Polynomial (CounterexampleResponseFunctionField K) :=
  parent.map (algebraMap (BivariatePolynomial K)
    (CounterexampleResponseFunctionField K))

theorem parentInResponseFunctionField_irreducible
    {K : Type*} [Field K] {parent : TrivariatePolynomial K}
    (parentIrreducible : Irreducible parent)
    (coefficientOneNeZero : parent.coeff 1 ≠ 0) :
    Irreducible (parentInResponseFunctionField parent) := by
  have parentDegreeNeZero : parent.natDegree ≠ 0 := by
    intro degreeZero
    apply coefficientOneNeZero
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  have primitive := parentIrreducible.isPrimitive parentDegreeNeZero
  exact primitive.irreducible_iff_irreducible_map_fraction_map.mp
    parentIrreducible

theorem parentInResponseFunctionField_derivative_ne_zero
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (coefficientOneNeZero : parent.coeff 1 ≠ 0) :
    (parentInResponseFunctionField parent).derivative ≠ 0 := by
  intro derivativeZero
  have coefficientZero := congrArg
    (fun polynomial : Polynomial (CounterexampleResponseFunctionField K) ↦
      polynomial.coeff 0) derivativeZero
  rw [Polynomial.coeff_derivative] at coefficientZero
  norm_num at coefficientZero
  rw [parentInResponseFunctionField, Polynomial.coeff_map] at coefficientZero
  have mappedCoefficientZero :
      algebraMap (BivariatePolynomial K)
          (CounterexampleResponseFunctionField K) (parent.coeff 1) = 0 :=
    coefficientZero
  have mappedCoefficientZero' :
      algebraMap (BivariatePolynomial K)
          (CounterexampleResponseFunctionField K) (parent.coeff 1) =
        algebraMap (BivariatePolynomial K)
          (CounterexampleResponseFunctionField K) 0 := by
    simpa using mappedCoefficientZero
  exact coefficientOneNeZero
    (IsFractionRing.injective (BivariatePolynomial K)
      (CounterexampleResponseFunctionField K) mappedCoefficientZero')

/-- Separability of a trivariate parent in the response variable, over the
fraction field `Frac(K[X,Z])`. -/
def SeparableInResponse
    {K : Type*} [Field K] (parent : TrivariatePolynomial K) : Prop :=
  (parentInResponseFunctionField parent).Separable

theorem separableInResponse_of_irreducible_of_coeff_one_ne_zero
    {K : Type*} [Field K] {parent : TrivariatePolynomial K}
    (parentIrreducible : Irreducible parent)
    (coefficientOneNeZero : parent.coeff 1 ≠ 0) :
    SeparableInResponse parent := by
  rw [SeparableInResponse, Polynomial.separable_iff_derivative_ne_zero
    (parentInResponseFunctionField_irreducible parentIrreducible
      coefficientOneNeZero)]
  exact parentInResponseFunctionField_derivative_ne_zero parent
    coefficientOneNeZero

/-- The positive-order counterexample is separable in `Y` over
`Frac(K[X,Z])`. -/
theorem positiveOrderParent_separableInResponse
    {K : Type*} [Field K] : SeparableInResponse (positiveOrderParent K) := by
  apply separableInResponse_of_irreducible_of_coeff_one_ne_zero
    positiveOrderParent_irreducible
  rw [positiveOrderParent_coeff]
  norm_num

@[simp] theorem counterexample_coeff_C_pow_zero
    {R : Type*} [Semiring R] (coefficient : R) (exponent : Nat) :
    ((Polynomial.C coefficient : Polynomial R) ^ exponent).coeff 0 =
      coefficient ^ exponent := by
  calc
    ((Polynomial.C coefficient : Polynomial R) ^ exponent).coeff 0 =
        (Polynomial.C (coefficient ^ exponent) : Polynomial R).coeff 0 :=
      congrArg (fun polynomial : Polynomial R ↦ polynomial.coeff 0)
        (Polynomial.C_pow (R := R) (a := coefficient)
          (n := exponent)).symm
    _ = coefficient ^ exponent := Polynomial.coeff_C_zero

@[simp] theorem counterexample_coeff_C_pow_succ
    {R : Type*} [Semiring R] (coefficient : R)
    (exponent coefficientIndex : Nat) :
    ((Polynomial.C coefficient : Polynomial R) ^ exponent).coeff
        (coefficientIndex + 1) = 0 := by
  calc
    ((Polynomial.C coefficient : Polynomial R) ^ exponent).coeff
          (coefficientIndex + 1) =
        (Polynomial.C (coefficient ^ exponent) : Polynomial R).coeff
          (coefficientIndex + 1) :=
      congrArg (fun polynomial : Polynomial R ↦
        polynomial.coeff (coefficientIndex + 1))
        (Polynomial.C_pow (R := R) (a := coefficient)
          (n := exponent)).symm
    _ = 0 := Polynomial.coeff_C_succ

/-- The full saturation parent written by response degree. -/
theorem saturationParent_expansion
    {K : Type*} [Field K] :
    saturationParent K =
      Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.X ^ 2 + Polynomial.X + 1) *
          Polynomial.X +
        Polynomial.C
          (Polynomial.X ^ 3 + Polynomial.X ^ 2 +
            Polynomial.C Polynomial.X) := by
  unfold saturationParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp only [Polynomial.C_add, Polynomial.C_pow, Polynomial.C_1]
  ring

theorem saturationParent_coeff_zero
    {K : Type*} [Field K] :
    (saturationParent K).coeff 0 =
      Polynomial.X ^ 3 + Polynomial.X ^ 2 +
        Polynomial.C Polynomial.X := by
  unfold saturationParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp [Polynomial.coeff_mul]
  ring

/-- The response-linear coefficient of the saturation parent. -/
theorem saturationParent_coeff_one
    {K : Type*} [Field K] :
    (saturationParent K).coeff 1 = Polynomial.X ^ 2 + Polynomial.X + 1 := by
  have antiOne : (Finset.antidiagonal 1 : Finset (Nat × Nat)) =
      {(0, 1), (1, 0)} := by decide
  unfold saturationParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp [Polynomial.coeff_mul, antiOne, Polynomial.coeff_one,
    Polynomial.coeff_X]
  ring

theorem saturationParent_coeff_two
    {K : Type*} [Field K] :
    (saturationParent K).coeff 2 = 1 := by
  have antiTwo : (Finset.antidiagonal 2 : Finset (Nat × Nat)) =
      {(0, 2), (1, 1), (2, 0)} := by decide
  unfold saturationParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp [Polynomial.coeff_mul, antiTwo, Polynomial.coeff_one,
    Polynomial.coeff_X]

@[simp] theorem saturationParent_coeff_zero_degree
    {K : Type*} [Field K] :
    ((saturationParent K).coeff 0).natDegree = 3 := by
  rw [saturationParent_coeff_zero]
  compute_degree
  all_goals simp

@[simp] theorem saturationParent_coeff_one_degree
    {K : Type*} [Field K] :
    ((saturationParent K).coeff 1).natDegree = 2 := by
  rw [saturationParent_coeff_one]
  compute_degree
  all_goals simp

@[simp] theorem saturationParent_coeff_two_degree
    {K : Type*} [Field K] :
    ((saturationParent K).coeff 2).natDegree = 0 := by
  rw [saturationParent_coeff_two]
  simp

@[simp] theorem saturationParent_yDegree
    {K : Type*} [Field K] : (saturationParent K).natDegree = 2 := by
  rw [saturationParent_expansion]
  compute_degree
  all_goals simp

/-- The saturation parent has the paper's full weighted coefficient bound
`D_R=3` for response weight `ell=1`. -/
theorem saturationParent_coefficient_bound
    {K : Type*} [Field K] :
    ParentCoefficientBound (saturationParent K) 1 3 := by
  intro exponent exponentMem
  have exponentLe : exponent ≤ 2 := by
    rw [← saturationParent_yDegree (K := K)]
    exact Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp exponentMem)
  interval_cases exponent <;> norm_num

/-- The saturation parent is separable in `Y` over `Frac(K[X,Z])`. -/
theorem saturationParent_separableInResponse
    {K : Type*} [Field K] : SeparableInResponse (saturationParent K) := by
  apply separableInResponse_of_irreducible_of_coeff_one_ne_zero
    saturationParent_irreducible
  rw [saturationParent_coeff_one]
  intro coefficientZero
  have topCoefficientZero := congrArg
    (fun polynomial : Polynomial (Polynomial K) ↦ polynomial.coeff 2)
    coefficientZero
  norm_num [Polynomial.coeff_add, Polynomial.coeff_X,
    Polynomial.coeff_one] at topCoefficientZero

/-- The derivative-counterexample parent written by response degree. -/
theorem derivativeCounterexampleParent_expansion :
    derivativeCounterexampleParent =
      Polynomial.X ^ 3 +
        Polynomial.C (Polynomial.X ^ 2) * Polynomial.X ^ 2 +
        Polynomial.X +
        Polynomial.C
          (Polynomial.X ^ 2 + Polynomial.C Polynomial.X) := by
  unfold derivativeCounterexampleParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp only [Polynomial.C_add, Polynomial.C_pow]
  ring

theorem derivativeCounterexampleParent_coeff_zero :
    derivativeCounterexampleParent.coeff 0 =
      Polynomial.X ^ 2 + Polynomial.C Polynomial.X := by
  unfold derivativeCounterexampleParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp [Polynomial.coeff_mul]

/-- The response-linear coefficient of the derivative parent is one. -/
theorem derivativeCounterexampleParent_coeff_one :
    derivativeCounterexampleParent.coeff 1 = 1 := by
  have antiOne : (Finset.antidiagonal 1 : Finset (Nat × Nat)) =
      {(0, 1), (1, 0)} := by decide
  unfold derivativeCounterexampleParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp [Polynomial.coeff_mul, antiOne, Polynomial.coeff_one,
    Polynomial.coeff_X]

theorem derivativeCounterexampleParent_coeff_two :
    derivativeCounterexampleParent.coeff 2 = Polynomial.X ^ 2 := by
  have antiTwo : (Finset.antidiagonal 2 : Finset (Nat × Nat)) =
      {(0, 2), (1, 1), (2, 0)} := by decide
  unfold derivativeCounterexampleParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp [Polynomial.coeff_mul, antiTwo, Polynomial.coeff_one,
    Polynomial.coeff_X]

theorem derivativeCounterexampleParent_coeff_three :
    derivativeCounterexampleParent.coeff 3 = 1 := by
  have antiThree : (Finset.antidiagonal 3 : Finset (Nat × Nat)) =
      {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide
  unfold derivativeCounterexampleParent counterexampleTrivariateY
    counterexampleTrivariateZ counterexampleChallenge
  simp [Polynomial.coeff_mul, antiThree, Polynomial.coeff_one,
    Polynomial.coeff_X]

@[simp] theorem derivativeCounterexampleParent_coeff_zero_degree :
    (derivativeCounterexampleParent.coeff 0).natDegree = 2 := by
  rw [derivativeCounterexampleParent_coeff_zero]
  compute_degree
  all_goals simp

@[simp] theorem derivativeCounterexampleParent_coeff_one_degree :
    (derivativeCounterexampleParent.coeff 1).natDegree = 0 := by
  rw [derivativeCounterexampleParent_coeff_one]
  simp

@[simp] theorem derivativeCounterexampleParent_coeff_two_degree :
    (derivativeCounterexampleParent.coeff 2).natDegree = 2 := by
  rw [derivativeCounterexampleParent_coeff_two]
  simp

@[simp] theorem derivativeCounterexampleParent_coeff_three_degree :
    (derivativeCounterexampleParent.coeff 3).natDegree = 0 := by
  rw [derivativeCounterexampleParent_coeff_three]
  simp

@[simp] theorem derivativeCounterexampleParent_yDegree :
    derivativeCounterexampleParent.natDegree = 3 := by
  rw [derivativeCounterexampleParent_expansion]
  compute_degree
  all_goals simp

/-- The derivative counterexample has the paper's full weighted coefficient
bound `D_R=4` for response weight `ell=1`. -/
theorem derivativeCounterexampleParent_coefficient_bound :
    ParentCoefficientBound derivativeCounterexampleParent 1 4 := by
  intro exponent exponentMem
  have exponentLe : exponent ≤ 3 := by
    rw [← derivativeCounterexampleParent_yDegree]
    exact Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp exponentMem)
  interval_cases exponent <;> norm_num

/-- The derivative counterexample is separable in `Y` over
`Frac(F₅[X,Z])`. -/
theorem derivativeCounterexampleParent_separableInResponse :
    SeparableInResponse derivativeCounterexampleParent := by
  apply separableInResponse_of_irreducible_of_coeff_one_ne_zero
    derivativeCounterexampleParent_irreducible
  rw [derivativeCounterexampleParent_coeff_one]
  exact one_ne_zero

def derivativeQuadratic : BivariatePolynomial (ZMod 5) :=
  Polynomial.X ^ 2 + 1

def derivativeLinearMinus : BivariatePolynomial (ZMod 5) :=
  Polynomial.X - Polynomial.C 2

def derivativeLinearPlus : BivariatePolynomial (ZMod 5) :=
  Polynomial.X + Polynomial.C 2

theorem polynomial_two_sq_eq_neg_one :
    (2 : Polynomial (ZMod 5)) ^ 2 = -1 := by
  have fourEqNegOne : (4 : ZMod 5) = -1 := by decide
  calc
    (2 : Polynomial (ZMod 5)) ^ 2 = 4 := by ring
    _ = Polynomial.C (4 : ZMod 5) := by
      exact (Polynomial.C_eq_natCast 4).symm
    _ = Polynomial.C (-1 : ZMod 5) := congrArg Polynomial.C fourEqNegOne
    _ = -1 := by simp

/-- Over `F₅`, `Y²+1=(Y-2)(Y+2)`. -/
theorem derivativeQuadratic_factorization :
    derivativeQuadratic = derivativeLinearMinus * derivativeLinearPlus := by
  unfold derivativeQuadratic derivativeLinearMinus derivativeLinearPlus
  calc
    Polynomial.X ^ 2 + 1 =
        Polynomial.X ^ 2 -
          Polynomial.C (2 : Polynomial (ZMod 5)) ^ 2 := by
      rw [← Polynomial.C_pow, polynomial_two_sq_eq_neg_one]
      simp
    _ = (Polynomial.X - Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2) := by ring

theorem derivativeLinearMinus_irreducible :
    Irreducible derivativeLinearMinus := by
  exact Polynomial.irreducible_X_sub_C 2

theorem derivativeLinearPlus_irreducible :
    Irreducible derivativeLinearPlus := by
  have linearEq : derivativeLinearPlus =
      Polynomial.X - Polynomial.C (-2) := by
    simp [derivativeLinearPlus]
  rw [linearEq]
  exact Polynomial.irreducible_X_sub_C _

theorem derivativeLinear_relPrime :
    IsRelPrime derivativeLinearMinus derivativeLinearPlus := by
  apply derivativeLinearMinus_irreducible.isRelPrime_iff_not_dvd.mpr
  intro divides
  have root := Polynomial.dvd_iff_isRoot.mp divides
  have valueZero : (2 : Polynomial (ZMod 5)) + 2 = 0 := by
    simpa [derivativeLinearMinus, derivativeLinearPlus,
      Polynomial.IsRoot] using root
  have constantZero : (2 : ZMod 5) + 2 = 0 := by
    simpa using congrArg (Polynomial.eval (0 : ZMod 5)) valueZero
  have fourNeZero : (4 : ZMod 5) ≠ 0 := by decide
  apply fourNeZero
  calc
    (4 : ZMod 5) = 2 + 2 := by ring
    _ = 0 := constantZero

theorem derivativeQuadratic_squarefree : Squarefree derivativeQuadratic := by
  rw [derivativeQuadratic_factorization]
  exact squarefree_mul_iff.mpr
    ⟨derivativeLinear_relPrime, derivativeLinearMinus_irreducible.squarefree,
      derivativeLinearPlus_irreducible.squarefree⟩

theorem derivativeCounterexampleXi_ne_zero : derivativeCounterexampleXi ≠ 0 := by
  intro xiZero
  have coefficientZero := congrArg
    (fun polynomial : Polynomial (ZMod 5) ↦ polynomial.coeff 4) xiZero
  simp [derivativeCounterexampleXi, Polynomial.coeff_one] at coefficientZero

theorem counterexampleFactor_relPrime_derivativeQuadratic :
    IsRelPrime (counterexampleFactor (ZMod 5)) derivativeQuadratic := by
  apply counterexampleFactor_irreducible.isRelPrime_iff_not_dvd.mpr
  intro divides
  rw [counterexampleFactor_eq_X_sub_C] at divides
  have root := Polynomial.dvd_iff_isRoot.mp divides
  rw [Polynomial.IsRoot, derivativeQuadratic] at root
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at root
  apply derivativeCounterexampleXi_ne_zero
  rw [derivativeCounterexampleXi]
  calc
    Polynomial.X ^ 4 + 1 =
        (-(Polynomial.X ^ 2 : Polynomial (ZMod 5))) ^ 2 + 1 := by ring
    _ = 0 := root

/-- The specialized derivative parent is square-free in `F₅[Z][Y]`. -/
theorem derivativeSpecializedParent_squarefree :
    Squarefree derivativeSpecializedParent := by
  rw [derivativeSpecializedParent]
  exact squarefree_mul_iff.mpr
    ⟨counterexampleFactor_relPrime_derivativeQuadratic,
      counterexampleFactor_irreducible.squarefree,
      derivativeQuadratic_squarefree⟩

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
#print axioms counterexampleFactor_irreducible
#print axioms counterexampleFactor_derivative
#print axioms counterexampleFactor_coefficient_bound
#print axioms saturationParent_coefficient_bound
#print axioms saturationParent_irreducible
#print axioms saturationParent_separableInResponse
#print axioms positiveOrderParent_irreducible
#print axioms positiveOrderParent_separableInResponse
#print axioms derivativeCounterexampleParent_irreducible
#print axioms derivativeCounterexampleParent_coefficient_bound
#print axioms derivativeCounterexampleParent_separableInResponse
#print axioms derivativeSpecializedParent_squarefree

end

end WeightedHensel

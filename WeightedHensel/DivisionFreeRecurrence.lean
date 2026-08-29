/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.Counterexamples

/-!
# Division-free Hensel recurrence

This file implements the tuple bookkeeping of equations (60)--(67).  A
tuple has exactly `j` entries, records total order `t-s`, and, at shifted
order zero, excludes precisely the terms with one positive entry.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-! ## Tuple combinatorics -/

/-- Total order of a `j`-tuple. -/
def tupleOrder {j : Nat} (parts : Fin j → Nat) : Nat :=
  ∑ index, parts index

/-- Number of positive entries of a `j`-tuple. -/
def positivePartCount {j : Nat} (parts : Fin j → Nat) : Nat :=
  (Finset.univ.filter fun index ↦ parts index ≠ 0).card

/-- Sum of Hensel denominator exponents over a tuple. -/
def tupleHenselExponent {j : Nat} (parts : Fin j → Nat) : Nat :=
  ∑ index, henselExponent (parts index)

/-- Exact identity `sum e_{u_i} + r(u) = 2 sum u_i`. -/
theorem tupleHenselExponent_add_positivePartCount
    {j : Nat} (parts : Fin j → Nat) :
    tupleHenselExponent parts + positivePartCount parts =
      2 * tupleOrder parts := by
  classical
  unfold tupleHenselExponent positivePartCount tupleOrder
  rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  by_cases partZero : parts index = 0
  · simp [partZero]
  · rw [if_pos partZero]
    unfold henselExponent
    omega

/-- A retained tuple in `P̊_{s,j,t}`. -/
structure DivisionFreeTermIndex (t : Nat) (tPositive : 0 < t) where
  s : Nat
  s_le : s ≤ t
  j : Nat
  parts : Fin j → Nat
  order_eq : tupleOrder parts = t - s
  notLinear : ¬ (s = 0 ∧ positivePartCount parts = 1)

namespace DivisionFreeTermIndex

variable {t : Nat} {tPositive : 0 < t}

/-- The extra exponent `nu(u)=e_t-1-sum e_{u_i}`. -/
def nu (index : DivisionFreeTermIndex t tPositive) : Nat :=
  henselExponent t - 1 - tupleHenselExponent index.parts

theorem positivePartCount_pos_of_s_eq_zero
    (index : DivisionFreeTermIndex t tPositive) (sZero : index.s = 0) :
    0 < positivePartCount index.parts := by
  by_contra countNotPositive
  have countZero : positivePartCount index.parts = 0 := by omega
  have allZero : ∀ partIndex, index.parts partIndex = 0 := by
    intro partIndex
    by_contra partNeZero
    have filteredMem : partIndex ∈
        Finset.univ.filter (fun candidate ↦ index.parts candidate ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, partNeZero⟩
    have cardPositive : 0 <
        (Finset.univ.filter
          (fun candidate ↦ index.parts candidate ≠ 0)).card :=
      Finset.card_pos.mpr ⟨partIndex, filteredMem⟩
    exact (Nat.ne_of_gt cardPositive) countZero
  have orderZero : tupleOrder index.parts = 0 := by
    unfold tupleOrder
    exact Finset.sum_eq_zero fun partIndex _ ↦ allZero partIndex
  rw [index.order_eq, sZero, Nat.sub_zero] at orderZero
  omega

/-- At shifted order zero every retained tuple has at least two positive
entries. -/
theorem two_le_positivePartCount_of_s_eq_zero
    (index : DivisionFreeTermIndex t tPositive) (sZero : index.s = 0) :
    2 ≤ positivePartCount index.parts := by
  have countPositive := index.positivePartCount_pos_of_s_eq_zero sZero
  have countNotOne : positivePartCount index.parts ≠ 1 := by
    intro countOne
    exact index.notLinear ⟨sZero, countOne⟩
  omega

/-- The tuple denominator exponents fit below `e_t-1`, so `nu` is an
honest natural exponent. -/
theorem tupleHenselExponent_le_target_sub_one
    (index : DivisionFreeTermIndex t tPositive) :
    tupleHenselExponent index.parts ≤ henselExponent t - 1 := by
  have identity := tupleHenselExponent_add_positivePartCount index.parts
  have targetExponent : henselExponent t - 1 = 2 * t - 2 := by
    unfold henselExponent
    omega
  rw [targetExponent]
  by_cases sZero : index.s = 0
  · have countTwo := index.two_le_positivePartCount_of_s_eq_zero sZero
    rw [index.order_eq, sZero, Nat.sub_zero] at identity
    omega
  · have sPositive : 0 < index.s := Nat.pos_of_ne_zero sZero
    have orderLt : tupleOrder index.parts < t := by
      rw [index.order_eq]
      omega
    omega

theorem nu_add_tupleHenselExponent
    (index : DivisionFreeTermIndex t tPositive) :
    index.nu + tupleHenselExponent index.parts = henselExponent t - 1 := by
  unfold nu
  exact Nat.sub_add_cancel index.tupleHenselExponent_le_target_sub_one

/-- Every coefficient index occurring in a retained tuple is earlier than
the target order. -/
theorem part_lt
    (index : DivisionFreeTermIndex t tPositive) (partIndex : Fin index.j) :
    index.parts partIndex < t := by
  have partLeOrder : index.parts partIndex ≤ tupleOrder index.parts := by
    unfold tupleOrder
    exact Finset.single_le_sum (fun candidate _ ↦ Nat.zero_le (index.parts candidate))
      (Finset.mem_univ partIndex)
  have partLeTarget : index.parts partIndex ≤ t := by
    rw [index.order_eq] at partLeOrder
    exact partLeOrder.trans (Nat.sub_le t index.s)
  by_contra partNotLt
  have partEq : index.parts partIndex = t := by omega
  have exponentTermLe : henselExponent (index.parts partIndex) ≤
      tupleHenselExponent index.parts := by
    unfold tupleHenselExponent
    exact Finset.single_le_sum
      (fun candidate _ ↦ Nat.zero_le (henselExponent (index.parts candidate)))
      (Finset.mem_univ partIndex)
  rw [partEq] at exponentTermLe
  have exponentBound := index.tupleHenselExponent_le_target_sub_one
  have exponentPositive : 0 < henselExponent t := by
    unfold henselExponent
    omega
  omega

end DivisionFreeTermIndex

/-! ## Intrinsic cleared coefficients -/

/-- The regular derivative element `eta` of equation (56), defined directly
inside `O` rather than through its function-field image. -/
def regularDerivativeElement
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K) (d : Nat) :
    RegularQuotient factor :=
  AdjoinRoot.mk (monicization factor)
    (sourceClearedRepresentative parent x₀ 0 d 1
      (fun j ↦ (j : K)) factor.leadingCoeff)

/-- The cleared coefficient `rho_{s,j}=c_{s,j}W^{d-j}` embedded in `O`. -/
def regularClearedCoefficient
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K) (s d j : Nat) :
    RegularQuotient factor :=
  AdjoinRoot.of (monicization factor)
    (shiftedParentCoefficient x₀ s j parent *
      factor.leadingCoeff ^ (d - j))

/-- Intrinsic derivative bound `Lambda(eta) ≤ mu`. -/
theorem regularDerivativeElement_weight_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K)
    (ell DH DR d b tau : Nat)
    (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (dPositive : 1 ≤ d) :
    regularWeightNat factor factorNeZero tau
        (regularDerivativeElement parent factor x₀ d) ≤
      sourceMu DR ell d b := by
  let representative := sourceClearedRepresentative parent x₀ 0 d 1
    (fun j ↦ (j : K)) factor.leadingCoeff
  have representativeWeight : weight tau representative ≤
      (sourceMu DR ell d b : Nat) := by
    simpa [representative, sourceMu] using
      sourceClearedRepresentative_weight_le parent x₀ ell DR d b tau 0 1
        (fun j ↦ (j : K)) factor.leadingCoeff globalBound tauEq wLeB dPositive
  have representativeRaw : iteratedBivariateWeight tau representative ≤
      sourceMu DR ell d b := by
    by_cases representativeZero : representative = 0
    · simp [representativeZero]
    · rw [weight_eq_coe tau representativeZero,
        localBivariateWeight_eq_iteratedBivariateWeight] at representativeWeight
      exact WithBot.coe_le_coe.mp representativeWeight
  have quotientBound := regularWeightNat_mk_le factor factorNeZero ell DH
    factorCoefficientBound representative
  rw [generatorWeightEq] at quotientBound
  change regularWeightNat factor factorNeZero tau
      (regularDerivativeElement parent factor x₀ d) ≤ sourceMu DR ell d b
  exact quotientBound.trans representativeRaw

/-- The intrinsic cleared derivative is `eta=W xi` for the source
derivative numerator constructed from the actual polynomial divisibility
hypothesis. -/
theorem exists_sourceDerivative_for_regularDerivative
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K)
    (ell DH DR d b tau : Nat)
    (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (ellDegreeLe : ell * factor.natDegree ≤ DH)
    (bEq : b = DH - ell * factor.natDegree)
    (tauEq : tau = b + ell)
    (globalBound : ParentCoefficientBound parent ell DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (dPositive : 1 ≤ d)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (specializedDegreeLe : (specializeX x₀ parent).natDegree ≤ d) :
    ∃ xi : RegularQuotient factor,
      regularDerivativeElement parent factor x₀ d =
          AdjoinRoot.of (monicization factor) factor.leadingCoeff * xi ∧
        regularWeight factor factorNeZero tau xi ≤
          (sourceSigma DR ell d b factor.leadingCoeff.natDegree : Nat) := by
  obtain ⟨xi, clearing, xiBound⟩ := exists_sourceDerivativeNumerator
    parent factor x₀ ell DH DR d b tau (fun j ↦ (j : K)) factorNeZero
    factorCoefficientBound ellDegreeLe bEq tauEq globalBound wLeB dPositive
    factorDvd specializedDegreeLe
  refine ⟨xi, ?_, xiBound⟩
  simpa [regularDerivativeElement] using clearing

/-- Cleared coefficient estimate (59):
`Lambda(rho_{s,j}) + j*tau ≤ tau+mu`. -/
theorem regularClearedCoefficient_weight_add_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K)
    (ell DH DR d b tau s j : Nat)
    (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR) (jLeD : j ≤ d)
    (wLeB : factor.leadingCoeff.natDegree ≤ b) :
    regularWeightNat factor factorNeZero tau
          (regularClearedCoefficient parent factor x₀ s d j) + j * tau ≤
      tau + sourceMu DR ell d b := by
  let shifted := shiftedParentCoefficient x₀ s j parent
  let coefficient := shifted * factor.leadingCoeff ^ (d - j)
  have quotientBound := regularWeightNat_of_le_natDegree factor factorNeZero
    ell DH factorCoefficientBound coefficient
  rw [generatorWeightEq] at quotientBound
  have parameterEq : tau + sourceMu DR ell d b = DR + d * b := by
    simpa [sourceMu] using source_parameter_ledger DR ell d b tau
      (sourceMu DR ell d b) (sourceMu DR ell d b) 0 ellLeDR dPositive
      (Nat.zero_le _) tauEq rfl (by simp)
  by_cases shiftedZero : shifted = 0
  · have coefficientZero : coefficient = 0 := by simp [coefficient, shiftedZero]
    have quotientZero : regularClearedCoefficient parent factor x₀ s d j = 0 := by
      simp [regularClearedCoefficient, coefficient, shifted, coefficientZero]
    rw [quotientZero, regularWeightNat_zero, zero_add]
    have ellJLeDR : ell * j ≤ DR :=
      (Nat.mul_le_mul_left ell jLeD).trans ellDLeDR
    calc
      j * tau ≤ (DR - ell * j + (d - j) * b) + j * tau :=
        Nat.le_add_left _ _
      _ = DR + d * b :=
        source_structural_ledger DR ell d b tau j tauEq ellJLeDR jLeD
      _ = tau + sourceMu DR ell d b := parameterEq.symm
  · have shiftedBound : shifted.natDegree + ell * j ≤ DR :=
      shiftedParentCoefficient_bound parent x₀ ell DR s j globalBound shiftedZero
    have shiftedDegree : shifted.natDegree ≤ DR - ell * j :=
      Nat.le_sub_of_add_le shiftedBound
    have coefficientDegree : coefficient.natDegree ≤
        (DR - ell * j) + (d - j) * b := by
      exact Polynomial.natDegree_mul_le.trans <|
        (Nat.add_le_add_right shiftedDegree _).trans <|
          Nat.add_le_add_left
            (Polynomial.natDegree_pow_le.trans
              (Nat.mul_le_mul_left _ wLeB)) _
    change regularWeightNat factor factorNeZero tau
          (AdjoinRoot.of (monicization factor) coefficient) + j * tau ≤
      tau + sourceMu DR ell d b
    refine (Nat.add_le_add_right (quotientBound.trans coefficientDegree)
      (j * tau)).trans ?_
    rw [parameterEq]
    exact (source_structural_ledger DR ell d b tau j tauEq
      (shiftedBound.trans' (Nat.le_add_left _ _)) jLeD).le

/-! ## Recurrence and weight bound in the regular quotient -/

/-- One literal summand `rho_{s,j} eta^nu prod delta_{u_i}` of (67). -/
def divisionFreeTerm
    {K : Type*} [Field K] {factor : BivariatePolynomial K}
    {t : Nat} {tPositive : 0 < t}
    (index : DivisionFreeTermIndex t tPositive)
    (rho eta : RegularQuotient factor)
    (delta : Nat → RegularQuotient factor) : RegularQuotient factor :=
  rho * eta ^ index.nu * ∏ partIndex, delta (index.parts partIndex)

/-- A recurrence summand during well-founded construction.  Each recursive
call carries the proof supplied by `DivisionFreeTermIndex.part_lt`. -/
def divisionFreeRecursiveTerm
    {K : Type*} [Field K] {factor : BivariatePolynomial K}
    {t : Nat} {tPositive : 0 < t}
    (index : DivisionFreeTermIndex t tPositive)
    (rho eta : RegularQuotient factor)
    (earlier : ∀ order : Nat, order < t → RegularQuotient factor) :
    RegularQuotient factor :=
  rho * eta ^ index.nu *
    ∏ partIndex, earlier (index.parts partIndex) (index.part_lt partIndex)

/-- The coefficients `delta_t`, defined by the actual recurrence (67) in
the regular quotient. -/
def divisionFreeCoefficients
    {K : Type*} [Field K] {factor : BivariatePolynomial K}
    (eta : RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor)
    (t : Nat) : RegularQuotient factor :=
  Nat.strongRec (motive := fun _ ↦ RegularQuotient factor)
    (fun order earlier ↦
      if orderPositive : 0 < order then
        -∑ index ∈ terms order orderPositive,
          divisionFreeRecursiveTerm index
            (rho order orderPositive index) eta earlier
      else AdjoinRoot.root (monicization factor)) t

@[simp] theorem divisionFreeCoefficients_zero
    {K : Type*} [Field K] {factor : BivariatePolynomial K}
    (eta : RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor) :
    divisionFreeCoefficients eta terms rho 0 =
      AdjoinRoot.root (monicization factor) := by
  rw [divisionFreeCoefficients, Nat.strongRec_eq]
  simp

/-- Unfolding the well-founded definition gives exactly equation (67). -/
theorem divisionFreeCoefficients_of_pos
    {K : Type*} [Field K] {factor : BivariatePolynomial K}
    (eta : RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor)
    (t : Nat) (tPositive : 0 < t) :
    divisionFreeCoefficients eta terms rho t =
      -∑ index ∈ terms t tPositive,
        divisionFreeTerm index (rho t tPositive index) eta
          (divisionFreeCoefficients eta terms rho) := by
  rw [divisionFreeCoefficients, Nat.strongRec_eq]
  simp only [dif_pos tPositive]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro index indexMem
  unfold divisionFreeRecursiveTerm divisionFreeTerm
  congr 1

/-- The denominator-free ceiling `tau+e_t mu`. -/
def divisionFreeCeiling (tau mu t : Nat) : Nat :=
  tau + henselExponent t * mu

@[simp] theorem divisionFreeCeiling_zero (tau mu : Nat) :
    divisionFreeCeiling tau mu 0 = tau := by
  simp [divisionFreeCeiling]

/-- A single denominator-free recurrence summand satisfies the target
ceiling. -/
theorem divisionFreeTerm_weight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell DH tau mu t : Nat)
    (tPositive : 0 < t)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (index : DivisionFreeTermIndex t tPositive)
    (rho eta : RegularQuotient factor)
    (rhoBound : regularWeightNat factor factorNeZero tau rho +
      index.j * tau ≤ tau + mu)
    (etaBound : regularWeightNat factor factorNeZero tau eta ≤ mu)
    (delta : Nat → RegularQuotient factor)
    (deltaBound : ∀ partIndex,
      regularWeightNat factor factorNeZero tau
          (delta (index.parts partIndex)) ≤
        divisionFreeCeiling tau mu (index.parts partIndex)) :
    regularWeightNat factor factorNeZero tau
        (divisionFreeTerm index rho eta delta) ≤
      divisionFreeCeiling tau mu t := by
  have etaPowerBound := regularWeightNat_pow_le factor factorNeZero ell DH
    factorCoefficientBound eta index.nu
  rw [generatorWeightEq] at etaPowerBound
  have etaPowerCeiling : regularWeightNat factor factorNeZero tau
      (eta ^ index.nu) ≤ index.nu * mu :=
    etaPowerBound.trans (Nat.mul_le_mul_left _ etaBound)
  have productBound := regularWeightNat_finset_prod_le factor factorNeZero
    ell DH factorCoefficientBound Finset.univ
    (fun partIndex : Fin index.j ↦ delta (index.parts partIndex))
  rw [generatorWeightEq] at productBound
  have productCeiling : regularWeightNat factor factorNeZero tau
      (∏ partIndex, delta (index.parts partIndex)) ≤
        index.j * tau + tupleHenselExponent index.parts * mu := by
    refine productBound.trans ?_
    calc
      ∑ partIndex : Fin index.j,
          regularWeightNat factor factorNeZero tau
            (delta (index.parts partIndex)) ≤
          ∑ partIndex : Fin index.j,
            divisionFreeCeiling tau mu (index.parts partIndex) := by
        exact Finset.sum_le_sum fun partIndex _ ↦ deltaBound partIndex
      _ = index.j * tau + tupleHenselExponent index.parts * mu := by
        unfold divisionFreeCeiling tupleHenselExponent
        simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        simp
  have firstMul := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound rho (eta ^ index.nu)
  have secondMul := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound (rho * eta ^ index.nu)
      (∏ partIndex, delta (index.parts partIndex))
  rw [generatorWeightEq] at firstMul secondMul
  have rawBound : regularWeightNat factor factorNeZero tau
      (divisionFreeTerm index rho eta delta) ≤
        regularWeightNat factor factorNeZero tau rho + index.nu * mu +
          (index.j * tau + tupleHenselExponent index.parts * mu) := by
    unfold divisionFreeTerm
    exact secondMul.trans <| Nat.add_le_add
      (firstMul.trans (Nat.add_le_add_left etaPowerCeiling _)) productCeiling
  refine rawBound.trans ?_
  have exponentEq := index.nu_add_tupleHenselExponent
  unfold divisionFreeCeiling
  have exponentPositive : 0 < henselExponent t := by
    unfold henselExponent
    omega
  have exponentSplit : henselExponent t =
      1 + (henselExponent t - 1) := by omega
  calc
    regularWeightNat factor factorNeZero tau rho + index.nu * mu +
          (index.j * tau + tupleHenselExponent index.parts * mu) =
        (regularWeightNat factor factorNeZero tau rho + index.j * tau) +
          (index.nu + tupleHenselExponent index.parts) * mu := by ring
    _ ≤ (tau + mu) + (henselExponent t - 1) * mu := by
      rw [exponentEq]
      exact Nat.add_le_add_right rhoBound _
    _ = tau + henselExponent t * mu := by
      have muJoin : mu + (henselExponent t - 1) * mu =
          henselExponent t * mu := by
        calc
          mu + (henselExponent t - 1) * mu =
              (1 + (henselExponent t - 1)) * mu := by ring
          _ = henselExponent t * mu := by rw [← exponentSplit]
      rw [add_assoc, muJoin]

/-- Strong induction for any family defined by the literal recurrence (67).
The only coefficient hypothesis is the checked estimate (59). -/
theorem division_free_hensel_estimate_nat
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell DH tau mu : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (eta : RegularQuotient factor)
    (etaBound : regularWeightNat factor factorNeZero tau eta ≤ mu)
    (delta : Nat → RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor)
    (base : delta 0 = AdjoinRoot.root (monicization factor))
    (recurrence : ∀ (t : Nat) (tPositive : 0 < t),
      delta t = -∑ index ∈ terms t tPositive,
        divisionFreeTerm index (rho t tPositive index) eta delta)
    (rhoBound : ∀ (t : Nat) (tPositive : 0 < t)
      (index : DivisionFreeTermIndex t tPositive), index ∈ terms t tPositive →
        regularWeightNat factor factorNeZero tau (rho t tPositive index) +
          index.j * tau ≤ tau + mu) :
    ∀ t, regularWeightNat factor factorNeZero tau (delta t) ≤
      divisionFreeCeiling tau mu t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t induction =>
      by_cases tZero : t = 0
      · subst t
        rw [base, divisionFreeCeiling_zero]
        have rootBound := regularWeightNat_root_le factor factorNeZero ell DH
          factorCoefficientBound
        simpa [generatorWeightEq] using rootBound
      · have tPositive : 0 < t := Nat.pos_of_ne_zero tZero
        rw [recurrence t tPositive, regularWeightNat_neg]
        apply regularWeightNat_finset_sum_le factor factorNeZero tau
          (divisionFreeCeiling tau mu t) (terms t tPositive)
        intro index indexMem
        apply divisionFreeTerm_weight_le factor factorNeZero ell DH tau mu t
          tPositive factorCoefficientBound generatorWeightEq index
          (rho t tPositive index) eta (rhoBound t tPositive index indexMem)
          etaBound delta
        intro partIndex
        exact induction (index.parts partIndex) (index.part_lt partIndex)

/-- Paper-facing form of the division-free estimate. -/
theorem division_free_hensel_estimate
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell DH tau mu : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (eta : RegularQuotient factor)
    (etaBound : regularWeightNat factor factorNeZero tau eta ≤ mu)
    (delta : Nat → RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor)
    (base : delta 0 = AdjoinRoot.root (monicization factor))
    (recurrence : ∀ (t : Nat) (tPositive : 0 < t),
      delta t = -∑ index ∈ terms t tPositive,
        divisionFreeTerm index (rho t tPositive index) eta delta)
    (rhoBound : ∀ (t : Nat) (tPositive : 0 < t)
      (index : DivisionFreeTermIndex t tPositive), index ∈ terms t tPositive →
        regularWeightNat factor factorNeZero tau (rho t tPositive index) +
          index.j * tau ≤ tau + mu)
    (t : Nat) :
    regularWeight factor factorNeZero tau (delta t) ≤
      (divisionFreeCeiling tau mu t : Nat) := by
  have rawBound := division_free_hensel_estimate_nat factor factorNeZero ell DH
    tau mu factorCoefficientBound generatorWeightEq eta etaBound delta terms rho
    base recurrence rhoBound t
  by_cases deltaZero : delta t = 0
  · simp [deltaZero]
  · rw [regularWeight_eq_coe factor factorNeZero tau deltaZero]
    exact WithBot.coe_le_coe.mpr rawBound

/-- The actual recursively defined family satisfies the denominator-free
estimate; no recurrence hypothesis appears in this statement. -/
theorem division_free_defined_estimate
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell DH tau mu : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (eta : RegularQuotient factor)
    (etaBound : regularWeightNat factor factorNeZero tau eta ≤ mu)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor)
    (rhoBound : ∀ (t : Nat) (tPositive : 0 < t)
      (index : DivisionFreeTermIndex t tPositive), index ∈ terms t tPositive →
        regularWeightNat factor factorNeZero tau (rho t tPositive index) +
          index.j * tau ≤ tau + mu)
    (t : Nat) :
    regularWeight factor factorNeZero tau
        (divisionFreeCoefficients eta terms rho t) ≤
      (divisionFreeCeiling tau mu t : Nat) := by
  apply division_free_hensel_estimate factor factorNeZero ell DH tau mu
    factorCoefficientBound generatorWeightEq eta etaBound
    (divisionFreeCoefficients eta terms rho) terms rho
  · exact divisionFreeCoefficients_zero eta terms rho
  · exact divisionFreeCoefficients_of_pos eta terms rho
  · exact rhoBound

/-! ## Relation with the direct source normalization -/

/-- The regular leading coefficient `W` inside `O`. -/
def regularLeadingCoefficient
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    RegularQuotient factor :=
  AdjoinRoot.of (monicization factor) factor.leadingCoeff

/-- Image of one recurrence summand after inserting the inductive image
formula for all earlier coefficients. -/
theorem divisionFreeTerm_image
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (d t : Nat) (tPositive : 0 < t)
    (index : DivisionFreeTermIndex t tPositive) (jLeD : index.j ≤ d)
    (rho eta : RegularQuotient factor)
    (delta : Nat → RegularQuotient factor)
    (alpha : Nat → BranchFunctionField factor)
    (coefficient : BranchFunctionField factor)
    (rhoImage : regularToFunctionField factor factorPositive rho =
      coefficient *
        regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) ^ (d - index.j))
    (earlierImage : ∀ partIndex,
      regularToFunctionField factor factorPositive
          (delta (index.parts partIndex)) =
        regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) *
          regularToFunctionField factor factorPositive eta ^
              henselExponent (index.parts partIndex) *
            alpha (index.parts partIndex)) :
    regularToFunctionField factor factorPositive
        (divisionFreeTerm index rho eta delta) =
      regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) ^ d *
        regularToFunctionField factor factorPositive eta ^
            (henselExponent t - 1) *
          (coefficient * ∏ partIndex, alpha (index.parts partIndex)) := by
  let mapToField := regularToFunctionField factor factorPositive
  let leadingImage := mapToField (regularLeadingCoefficient factor)
  let etaImage := mapToField eta
  have productImage :
      ∏ partIndex : Fin index.j,
          mapToField (delta (index.parts partIndex)) =
        leadingImage ^ index.j *
          etaImage ^ tupleHenselExponent index.parts *
            ∏ partIndex, alpha (index.parts partIndex) := by
    calc
      ∏ partIndex : Fin index.j,
          mapToField (delta (index.parts partIndex)) =
          ∏ partIndex : Fin index.j,
            (leadingImage *
              etaImage ^ henselExponent (index.parts partIndex) *
                alpha (index.parts partIndex)) := by
        apply Finset.prod_congr rfl
        intro partIndex _
        exact earlierImage partIndex
      _ = (∏ _partIndex : Fin index.j, leadingImage) *
            (∏ partIndex : Fin index.j,
              etaImage ^ henselExponent (index.parts partIndex)) *
            ∏ partIndex : Fin index.j, alpha (index.parts partIndex) := by
        simp_rw [Finset.prod_mul_distrib]
      _ = leadingImage ^ index.j *
            etaImage ^ tupleHenselExponent index.parts *
              ∏ partIndex, alpha (index.parts partIndex) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum]
        rfl
  unfold divisionFreeTerm
  rw [map_mul, map_mul, map_pow, map_prod, rhoImage, productImage]
  have leadingSplit : d - index.j + index.j = d := Nat.sub_add_cancel jLeD
  have etaSplit := index.nu_add_tupleHenselExponent
  change coefficient * leadingImage ^ (d - index.j) * etaImage ^ index.nu *
        (leadingImage ^ index.j *
          etaImage ^ tupleHenselExponent index.parts *
            ∏ partIndex, alpha (index.parts partIndex)) =
      leadingImage ^ d * etaImage ^ (henselExponent t - 1) *
        (coefficient * ∏ partIndex, alpha (index.parts partIndex))
  calc
    coefficient * leadingImage ^ (d - index.j) * etaImage ^ index.nu *
          (leadingImage ^ index.j *
            etaImage ^ tupleHenselExponent index.parts *
              ∏ partIndex, alpha (index.parts partIndex)) =
        coefficient *
          (leadingImage ^ (d - index.j) * leadingImage ^ index.j) *
          (etaImage ^ index.nu *
            etaImage ^ tupleHenselExponent index.parts) *
          ∏ partIndex, alpha (index.parts partIndex) := by ring
    _ = coefficient * leadingImage ^ d *
          etaImage ^ (henselExponent t - 1) *
          ∏ partIndex, alpha (index.parts partIndex) := by
      rw [← pow_add, leadingSplit, ← pow_add, etaSplit]
    _ = leadingImage ^ d * etaImage ^ (henselExponent t - 1) *
          (coefficient * ∏ partIndex, alpha (index.parts partIndex)) := by ring

/-- Equation (64) follows by strong induction from the actual recurrence
(67), the cleared-coefficient identities, and the coefficient recurrence
(61) in the function field. -/
theorem divisionFreeCoefficients_image
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) (d : Nat) (dPositive : 1 ≤ d)
    (eta : RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor)
    (coefficient : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → BranchFunctionField factor)
    (zeta : BranchFunctionField factor)
    (alpha : Nat → BranchFunctionField factor)
    (baseImage : regularToFunctionField factor factorPositive
        (AdjoinRoot.root (monicization factor)) =
      regularToFunctionField factor factorPositive
          (regularLeadingCoefficient factor) * alpha 0)
    (etaImage : regularToFunctionField factor factorPositive eta =
      regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) ^ (d - 1) * zeta)
    (jLeD : ∀ (t : Nat) (tPositive : 0 < t)
      (index : DivisionFreeTermIndex t tPositive), index ∈ terms t tPositive →
        index.j ≤ d)
    (rhoImage : ∀ (t : Nat) (tPositive : 0 < t)
      (index : DivisionFreeTermIndex t tPositive), index ∈ terms t tPositive →
        regularToFunctionField factor factorPositive (rho t tPositive index) =
          coefficient t tPositive index *
            regularToFunctionField factor factorPositive
                (regularLeadingCoefficient factor) ^ (d - index.j))
    (coefficientRecurrence : ∀ (t : Nat) (tPositive : 0 < t),
      zeta * alpha t =
        -∑ index ∈ terms t tPositive,
          coefficient t tPositive index *
            ∏ partIndex, alpha (index.parts partIndex)) :
    ∀ t,
      regularToFunctionField factor factorPositive
          (divisionFreeCoefficients eta terms rho t) =
        regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) *
          regularToFunctionField factor factorPositive eta ^ henselExponent t *
            alpha t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t induction =>
      by_cases tZero : t = 0
      · subst t
        rw [divisionFreeCoefficients_zero, henselExponent_zero, pow_zero,
          mul_one]
        exact baseImage
      · have tPositive : 0 < t := Nat.pos_of_ne_zero tZero
        rw [divisionFreeCoefficients_of_pos eta terms rho t tPositive,
          map_neg, map_sum]
        have sumImage :
            ∑ index ∈ terms t tPositive,
                regularToFunctionField factor factorPositive
                  (divisionFreeTerm index (rho t tPositive index) eta
                    (divisionFreeCoefficients eta terms rho)) =
              regularToFunctionField factor factorPositive
                    (regularLeadingCoefficient factor) ^ d *
                regularToFunctionField factor factorPositive eta ^
                    (henselExponent t - 1) *
                  ∑ index ∈ terms t tPositive,
                    coefficient t tPositive index *
                      ∏ partIndex, alpha (index.parts partIndex) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro index indexMem
          exact divisionFreeTerm_image factor factorPositive d t tPositive index
            (jLeD t tPositive index indexMem) (rho t tPositive index) eta
            (divisionFreeCoefficients eta terms rho) alpha
            (coefficient t tPositive index)
            (rhoImage t tPositive index indexMem)
            (fun partIndex ↦ induction (index.parts partIndex)
              (index.part_lt partIndex))
        rw [sumImage]
        let leadingImage := regularToFunctionField factor factorPositive
          (regularLeadingCoefficient factor)
        let mappedEta := regularToFunctionField factor factorPositive eta
        have exponentPositive : 0 < henselExponent t := by
          unfold henselExponent
          omega
        have etaPowerSplit : mappedEta ^ henselExponent t =
            mappedEta ^ (henselExponent t - 1) * mappedEta := by
          conv_lhs => rw [show henselExponent t =
            (henselExponent t - 1) + 1 by omega]
          rw [pow_succ]
        have leadingPowerSplit : leadingImage ^ d =
            leadingImage * leadingImage ^ (d - 1) := by
          conv_lhs => rw [show d = 1 + (d - 1) by omega]
          rw [pow_add, pow_one]
        have etaImage' : mappedEta = leadingImage ^ (d - 1) * zeta :=
          etaImage
        calc
          -(leadingImage ^ d * mappedEta ^ (henselExponent t - 1) *
              ∑ index ∈ terms t tPositive,
                coefficient t tPositive index *
                  ∏ partIndex, alpha (index.parts partIndex)) =
              leadingImage ^ d * mappedEta ^ (henselExponent t - 1) *
                (-∑ index ∈ terms t tPositive,
                  coefficient t tPositive index *
                    ∏ partIndex, alpha (index.parts partIndex)) := by ring
          _ = leadingImage ^ d * mappedEta ^ (henselExponent t - 1) *
                (zeta * alpha t) := by
            rw [coefficientRecurrence t tPositive]
          _ = leadingImage * mappedEta ^ henselExponent t * alpha t := by
            rw [etaPowerSplit, etaImage', leadingPowerSplit]
            ring

/-- For positive order the two numerator normalizations differ by exactly
`W^(t-1)`.  The hypotheses are the two proved function-field image
identities (13) and (64), together with the intrinsic identity `eta=W xi`.
No cancellation is used: injectivity of `iota` suffices. -/
theorem divisionFree_eq_sourceNumerator
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (eta xi : RegularQuotient factor)
    (delta beta : Nat → RegularQuotient factor)
    (alpha : Nat → BranchFunctionField factor)
    (etaEq : eta = regularLeadingCoefficient factor * xi)
    (deltaImage : ∀ t,
      regularToFunctionField factor factorPositive (delta t) =
        regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) *
          regularToFunctionField factor factorPositive eta ^ henselExponent t *
            alpha t)
    (betaImage : ∀ t,
      regularToFunctionField factor factorPositive (beta t) =
        regularToFunctionField factor factorPositive
              (regularLeadingCoefficient factor) ^ (t + 1) *
          regularToFunctionField factor factorPositive xi ^ henselExponent t *
            alpha t)
    (t : Nat) (tPositive : 0 < t) :
    delta t = regularLeadingCoefficient factor ^ (t - 1) * beta t := by
  apply regularToFunctionField_injective factor factorNeZero factorPositive
  let mapToField := regularToFunctionField factor factorPositive
  let leadingImage := mapToField (regularLeadingCoefficient factor)
  let xiImage := mapToField xi
  have etaImage : mapToField eta = leadingImage * xiImage := by
    rw [etaEq, map_mul]
  have exponentEq : henselExponent t + 1 = 2 * t := by
    unfold henselExponent
    omega
  have sourceLeadingExponent : (t - 1) + (t + 1) = 2 * t := by omega
  calc
    mapToField (delta t) =
        leadingImage * mapToField eta ^ henselExponent t * alpha t :=
      deltaImage t
    _ = leadingImage * (leadingImage * xiImage) ^ henselExponent t *
          alpha t := by rw [etaImage]
    _ = leadingImage ^ (henselExponent t + 1) *
          xiImage ^ henselExponent t * alpha t := by
      rw [mul_pow, pow_succ']
      ring
    _ = leadingImage ^ (2 * t) * xiImage ^ henselExponent t * alpha t := by
      rw [exponentEq]
    _ = leadingImage ^ ((t - 1) + (t + 1)) *
          xiImage ^ henselExponent t * alpha t := by rw [sourceLeadingExponent]
    _ = leadingImage ^ (t - 1) *
          (leadingImage ^ (t + 1) * xiImage ^ henselExponent t * alpha t) := by
      rw [pow_add]
      ring
    _ = mapToField (regularLeadingCoefficient factor ^ (t - 1) * beta t) := by
      rw [map_mul, map_pow, betaImage]

/-- At order zero both normalizations are the regular generator `T`. -/
theorem divisionFree_eq_sourceNumerator_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (delta beta : Nat → RegularQuotient factor)
    (deltaZero : delta 0 = AdjoinRoot.root (monicization factor))
    (betaZero : beta 0 = AdjoinRoot.root (monicization factor)) :
    delta 0 = beta 0 := by rw [deltaZero, betaZero]

/-- Exact weight relation (69) for a nonzero source numerator. -/
theorem divisionFree_sourceNumerator_weight_eq
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight w t : Nat)
    (wEq : w = factor.leadingCoeff.natDegree)
    (delta beta : Nat → RegularQuotient factor)
    (relation : delta t = regularLeadingCoefficient factor ^ (t - 1) * beta t)
    (betaNeZero : beta t ≠ 0) :
    regularWeight factor factorNeZero generatorWeight (delta t) =
      ((t - 1) * w : Nat) +
        regularWeight factor factorNeZero generatorWeight (beta t) := by
  have leadingNeZero : factor.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr factorNeZero
  have powerNeZero : factor.leadingCoeff ^ (t - 1) ≠ 0 :=
    pow_ne_zero _ leadingNeZero
  rw [relation]
  have powerMap : regularLeadingCoefficient factor ^ (t - 1) =
      AdjoinRoot.of (monicization factor) (factor.leadingCoeff ^ (t - 1)) := by
    exact (map_pow (AdjoinRoot.of (monicization factor)) factor.leadingCoeff
      (t - 1)).symm
  rw [powerMap, regularWeight_coefficient_mul factor factorNeZero
    generatorWeight (factor.leadingCoeff ^ (t - 1)) powerNeZero (beta t)
    betaNeZero]
  rw [Polynomial.natDegree_pow, ← wEq]

/-- The direct ceiling plus the visible factor `W^(t-1)` is exactly the
denominator-free ceiling. -/
theorem direct_and_divisionFree_ceilings_equivalent
    (tau mu sigma w t : Nat) (tPositive : 0 < t)
    (wLeMu : w ≤ mu) (sigmaEq : sigma = mu - w) :
    sourceNumeratorCeiling tau w sigma t + (t - 1) * w =
      divisionFreeCeiling tau mu t := by
  have muSplit : mu = w + sigma := by
    rw [sigmaEq, Nat.add_sub_of_le wLeMu]
  have exponentSplit : henselExponent t = t + (t - 1) := by
    unfold henselExponent
    omega
  rw [sourceNumeratorCeiling, divisionFreeCeiling, muSplit, exponentSplit]
  ring

#print axioms tupleHenselExponent_add_positivePartCount
#print axioms DivisionFreeTermIndex.two_le_positivePartCount_of_s_eq_zero
#print axioms DivisionFreeTermIndex.tupleHenselExponent_le_target_sub_one
#print axioms DivisionFreeTermIndex.part_lt
#print axioms regularDerivativeElement_weight_le
#print axioms exists_sourceDerivative_for_regularDerivative
#print axioms regularClearedCoefficient_weight_add_le
#print axioms divisionFreeCoefficients_of_pos
#print axioms divisionFreeTerm_weight_le
#print axioms division_free_hensel_estimate_nat
#print axioms division_free_hensel_estimate
#print axioms division_free_defined_estimate
#print axioms divisionFreeTerm_image
#print axioms divisionFreeCoefficients_image
#print axioms divisionFree_eq_sourceNumerator
#print axioms divisionFree_eq_sourceNumerator_zero
#print axioms divisionFree_sourceNumerator_weight_eq
#print axioms direct_and_divisionFree_ceilings_equivalent

end

end WeightedHensel

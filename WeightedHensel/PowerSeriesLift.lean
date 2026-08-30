/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.Specialization
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Characteristic-free power-series Hensel lifting

The Newton argument below supplies the non-monic simple-root form needed by
the paper.  Mathlib's packaged `HenselianRing` theorem asks for monicity;
the proof here uses only a simple approximate root and adic completeness.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped Ring

noncomputable section

/-- A simple approximate root in an adically complete ring lifts to an
actual root.  No monicity hypothesis is used. -/
theorem exists_adic_root_of_simple_approximation
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (polynomial : R[X]) (approximation : R)
    (rootModuloIdeal : polynomial.eval approximation ∈ I)
    (derivativeUnitModuloIdeal : IsUnit
      (Ideal.Quotient.mk I (polynomial.derivative.eval approximation))) :
    ∃ root : R, polynomial.IsRoot root ∧ root - approximation ∈ I := by
  classical
  let derivativePolynomial := derivative polynomial
  let approximations : Nat → R := fun n ↦ Nat.recOn n approximation fun _ value ↦
    value - polynomial.eval value *
      (derivativePolynomial.eval value)⁻¹ʳ
  have approximationStep : ∀ n, approximations (n + 1) =
      approximations n - polynomial.eval (approximations n) *
        (derivativePolynomial.eval (approximations n))⁻¹ʳ := by
    intro n
    simp only [approximations]
  have congruentToInitial : ∀ n,
      approximations n ≡ approximation [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n induction =>
      rw [approximationStep, sub_eq_add_neg, ← add_zero approximation]
      refine induction.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at rootModuloIdeal ⊢
      exact (induction.eval polynomial).trans rootModuloIdeal
  have derivativeUnits : ∀ n,
      IsUnit (derivativePolynomial.eval (approximations n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I
      (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert derivativeUnitModuloIdeal using 1
    exact SModEq.def.mp ((congruentToInitial n).eval _)
  have evaluationPower : ∀ n,
      polynomial.eval (approximations n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      change polynomial.eval approximation ∈ I ^ (0 + 1)
      simpa only [zero_add, pow_one] using rootModuloIdeal
    | succ n induction =>
      rw [← taylor_eval_sub (approximations n), approximationStep,
        sub_eq_add_neg, sub_eq_add_neg, add_neg_cancel_comm]
      rw [eval_eq_sum,
        sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
        ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, taylor_coeff_zero,
          taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (derivativeUnits n),
          mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨twoLe, _⟩
        have powerLe : n + 2 ≤ i * (n + 1) := by
          nlinarith only [twoLe]
        refine Ideal.mul_mem_left _ _
          (Ideal.pow_le_pow_right powerLe ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow
          ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ induction) _
  have cauchy : ∀ m n, m ≤ n →
      approximations m ≡ approximations n
        [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n less
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le less
    clear less
    induction k with
    | zero => rw [add_zero]
    | succ k induction =>
      rw [← add_assoc, approximationStep,
        ← add_zero (approximations m), sub_eq_add_neg]
      refine induction.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _
        (Ideal.pow_le_pow_right ?_ (evaluationPower _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨root, limit⟩ := IsPrecomplete.prec' approximations (cauchy _ _)
  refine ⟨root, ?_, ?_⟩
  · show polynomial.IsRoot root
    suffices ∀ n, polynomial.eval root ≡ 0
        [SMOD (I ^ n • ⊤ : Ideal R)] by
      exact IsHausdorff.haus' _ this
    intro n
    specialize limit n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at limit ⊢
    refine (limit.symm.eval polynomial).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (evaluationPower _)
  · specialize limit (0 + 1)
    rw [approximationStep, pow_one, ← Ideal.one_eq_top,
      Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at limit
    rw [← SModEq.sub_mem, ← add_zero approximation]
    refine limit.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ rootModuloIdeal

/-- Exact non-monic simple-root Hensel lifting over a power-series ring. -/
theorem exists_powerSeries_root_of_simple_constant_root
    {L : Type*} [Field L]
    (polynomial : Polynomial (PowerSeries L)) (constantRoot : L)
    (rootModuloVariable : PowerSeries.constantCoeff
      (polynomial.eval (PowerSeries.C constantRoot)) = 0)
    (derivativeModuloVariableNeZero : PowerSeries.constantCoeff
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) ≠ 0) :
    ∃ root : PowerSeries L,
      polynomial.IsRoot root ∧
        PowerSeries.constantCoeff root = constantRoot := by
  let variableIdeal : Ideal (PowerSeries L) :=
    Ideal.span {PowerSeries.X}
  have rootMem : polynomial.eval (PowerSeries.C constantRoot) ∈
      variableIdeal := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    exact rootModuloVariable
  have derivativeUnit : IsUnit
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr
      (Ne.isUnit derivativeModuloVariableNeZero)
  have quotientDerivativeUnit : IsUnit
      (Ideal.Quotient.mk variableIdeal
        (polynomial.derivative.eval (PowerSeries.C constantRoot))) :=
    derivativeUnit.map (Ideal.Quotient.mk variableIdeal)
  obtain ⟨root, rootEquation, rootCongruent⟩ :=
    exists_adic_root_of_simple_approximation variableIdeal polynomial
      (PowerSeries.C constantRoot) rootMem quotientDerivativeUnit
  refine ⟨root, rootEquation, ?_⟩
  have constantDifference : PowerSeries.constantCoeff
      (root - PowerSeries.C constantRoot) = 0 := by
    rw [← PowerSeries.X_dvd_iff, ← Ideal.mem_span_singleton]
    exact rootCongruent
  rw [map_sub, PowerSeries.constantCoeff_C] at constantDifference
  exact sub_eq_zero.mp constantDifference

/-- A simple power-series lift with a fixed constant coefficient is unique. -/
theorem powerSeries_root_unique_of_simple_constant_root
    {L : Type*} [Field L]
    (polynomial : Polynomial (PowerSeries L)) (constantRoot : L)
    (derivativeModuloVariableNeZero : PowerSeries.constantCoeff
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) ≠ 0)
    (left right : PowerSeries L)
    (leftRoot : polynomial.IsRoot left)
    (rightRoot : polynomial.IsRoot right)
    (leftConstant : PowerSeries.constantCoeff left = constantRoot)
    (rightConstant : PowerSeries.constantCoeff right = constantRoot) :
    left = right := by
  have derivativeConstant : PowerSeries.constantCoeff
      (polynomial.derivative.eval left) =
        PowerSeries.constantCoeff
          (polynomial.derivative.eval (PowerSeries.C constantRoot)) := by
    rw [← Polynomial.eval₂_id, ← Polynomial.eval₂_id,
      Polynomial.hom_eval₂, Polynomial.hom_eval₂,
      leftConstant, PowerSeries.constantCoeff_C]
  have derivativeUnit : IsUnit (polynomial.derivative.eval left) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr <| by
      rw [derivativeConstant]
      exact Ne.isUnit derivativeModuloVariableNeZero
  have differenceNotUnit : ¬ IsUnit (left - right) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [map_sub, leftConstant, rightConstant, sub_self]
    exact not_isUnit_zero
  exact IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    leftRoot.eq_zero rightRoot.eq_zero differenceNotUnit derivativeUnit

/-! ## The shifted parent over the selected function field -/

/-- Embed the ground field into the selected branch function field. -/
def branchBaseMap
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    K →+* BranchFunctionField factor :=
  (regularCoefficientMap factor).comp Polynomial.C

/-- The transcendental challenge value inside the selected branch field. -/
def branchChallenge
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    BranchFunctionField factor :=
  regularCoefficientMap factor Polynomial.X

/-- The coefficient embedding `K[Z] → L` is literal evaluation at the
embedded ground field and transcendental challenge. -/
theorem regularCoefficientMap_eq_eval₂
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (polynomial : Polynomial K) :
    regularCoefficientMap factor polynomial =
      polynomial.eval₂ (branchBaseMap factor) (branchChallenge factor) := by
  let evaluation := Polynomial.eval₂RingHom (branchBaseMap factor)
    (branchChallenge factor)
  have homEq : regularCoefficientMap factor = evaluation := by
    apply Polynomial.ringHom_ext
    · intro coefficient
      simp [evaluation, branchBaseMap]
    · simp [evaluation, branchChallenge]
  exact DFunLike.congr_fun homEq polynomial

/-- Hasse coefficients commute with a ground-field homomorphism and
evaluation. -/
theorem map_eval_hasseDeriv
    {K L : Type*} [Field K] [Field L] (mapBase : K →+* L)
    (polynomial : Polynomial K) (x₀ : K) (order : Nat) :
    mapBase ((Polynomial.hasseDeriv order polynomial).eval x₀) =
      (Polynomial.hasseDeriv order (polynomial.map mapBase)).eval
        (mapBase x₀) := by
  have mappedTaylor := congrArg (fun result : Polynomial L ↦ result.coeff order)
    (Polynomial.map_taylor polynomial x₀ mapBase)
  simpa only [Polynomial.coeff_map, Polynomial.taylor_coeff] using mappedTaylor

/-- Translation in `X`, ground-field extension, and evaluation in the
challenge variable commute on every shifted coefficient. -/
theorem shiftedChallengeCoefficient_map_eval₂
    {K L : Type*} [Field K] [Field L] (mapBase : K →+* L)
    (polynomial : BivariatePolynomial K) (x₀ : K) (z : L)
    (order : Nat) :
    (shiftedChallengeCoefficient (mapBase x₀) order
        (polynomial.map (Polynomial.mapRingHom mapBase))).eval z =
      (shiftedChallengeCoefficient x₀ order polynomial).eval₂ mapBase z := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [Polynomial.map_add, shiftedChallengeCoefficient_add,
        Polynomial.eval_add, shiftedChallengeCoefficient_add,
        Polynomial.eval₂_add, leftInduction, rightInduction]
  | monomial exponent coefficient =>
      rw [Polynomial.map_monomial, shiftedChallengeCoefficient_monomial,
        shiftedChallengeCoefficient_monomial, Polynomial.eval_monomial,
        Polynomial.eval₂_monomial, map_eval_hasseDeriv]
      rfl

/-- Extend ground-field coefficients through all three polynomial layers. -/
def mapTrivariateCoefficients
    {K L : Type*} [Field K] [Field L] (mapBase : K →+* L)
    (parent : TrivariatePolynomial K) : TrivariatePolynomial L :=
  parent.map (Polynomial.mapRingHom (Polynomial.mapRingHom mapBase))

/-- The original parent with all scalar coefficients embedded into the
selected branch function field. -/
def functionFieldParent
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))] :
    TrivariatePolynomial (BranchFunctionField factor) :=
  mapTrivariateCoefficients (branchBaseMap factor) parent

/-- The shifted parent `R(x₀+U,Y,Z)` over the selected function field. -/
def functionFieldShiftedParent
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))] (x₀ : K) :
    Polynomial (PowerSeries (BranchFunctionField factor)) :=
  specializedShiftedParent (functionFieldParent parent factor)
    (branchBaseMap factor x₀) (branchChallenge factor)

/-- The same shifted parent before completing `L[U]` to `L[[U]]`. -/
def functionFieldPolynomialParent
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))] (x₀ : K) :
    Polynomial (Polynomial (BranchFunctionField factor)) :=
  (specializeChallenge (branchChallenge factor)
      (functionFieldParent parent factor)).map
    (Polynomial.taylorAlgHom (branchBaseMap factor x₀)).toRingHom

/-- Completing the finite shifted parent coefficientwise gives exactly the
power-series shifted parent. -/
theorem map_functionFieldPolynomialParent
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))] (x₀ : K) :
    (functionFieldPolynomialParent parent factor x₀).map
        (Polynomial.coeToPowerSeries.ringHom
          (R := BranchFunctionField factor)) =
      functionFieldShiftedParent parent factor x₀ := by
  let basePoint := branchBaseMap factor x₀
  have homEq :
      (Polynomial.coeToPowerSeries.ringHom
          (R := BranchFunctionField factor)).comp
          (Polynomial.taylorAlgHom basePoint).toRingHom =
        shiftedEvaluationHom basePoint := by
    apply DFunLike.ext _ _
    intro polynomial
    exact (shiftedEvaluationHom_eq_coe_taylor basePoint polynomial).symm
  unfold functionFieldPolynomialParent functionFieldShiftedParent
  rw [specializedShiftedParent_eq_map_specializeChallenge,
    Polynomial.map_map, homEq]

/-- Constant coefficient after the literal shift is evaluation at the shift
base point. -/
theorem constantCoeff_comp_shiftedEvaluationHom
    {L : Type*} [Field L] (x₀ : L) :
    (PowerSeries.constantCoeff (R := L)).comp (shiftedEvaluationHom x₀) =
      Polynomial.evalRingHom x₀ := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    simp [shiftedEvaluationHom]
  · simp [shiftedEvaluationHom]

/-- Constant coefficient after specializing `Z` and shifting `X` is the
literal two-variable evaluation map. -/
theorem constantCoeff_comp_specializedShiftedCoefficientHom
    {L : Type*} [Field L] (x₀ z : L) :
    (PowerSeries.constantCoeff (R := L)).comp
        (specializedShiftedCoefficientHom x₀ z) =
      (Polynomial.evalRingHom z).comp
        (Polynomial.mapRingHom (Polynomial.evalRingHom x₀)) := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    rw [specializedShiftedCoefficientHom_eq_comp]
    simp only [RingHom.comp_apply, coe_evalRingHom, Polynomial.eval_C]
    calc
      PowerSeries.constantCoeff (shiftedEvaluationHom x₀ coefficient) =
          coefficient.eval x₀ :=
        DFunLike.congr_fun (constantCoeff_comp_shiftedEvaluationHom x₀)
          coefficient
      _ = ((Polynomial.mapRingHom (Polynomial.evalRingHom x₀))
          (Polynomial.C coefficient)).eval z := by simp
  · simp [specializedShiftedCoefficientHom, shiftedEvaluationHom]

/-- Evaluating the shifted parent at a constant series and then taking
constant coefficient is exactly evaluation of `R(x₀,Y,Z)`. -/
theorem constantCoeff_specializedShiftedParent_eval_C
    {L : Type*} [Field L] (parent : TrivariatePolynomial L)
    (x₀ z value : L) :
    PowerSeries.constantCoeff
        ((specializedShiftedParent parent x₀ z).eval
          (PowerSeries.C value)) =
      (specializeX x₀ parent).eval₂ (Polynomial.evalRingHom z) value := by
  unfold specializedShiftedParent
  rw [Polynomial.eval_map, Polynomial.hom_eval₂]
  rw [constantCoeff_comp_specializedShiftedCoefficientHom]
  simp only [PowerSeries.constantCoeff_C]
  unfold specializeX
  exact (Polynomial.eval₂_map (p := parent)
    (Polynomial.mapRingHom (Polynomial.evalRingHom x₀))
    (Polynomial.evalRingHom z) value).symm

/-- The bounded derivative scalar is exactly the constant coefficient of
the derivative of the shifted parent at a constant value. -/
theorem specializedDerivativeValue_eq_constantCoeff_derivative
    {L : Type*} [Field L] (parent : TrivariatePolynomial L)
    (x₀ z value : L) (d : Nat) (parentDegreeLe : parent.natDegree ≤ d) :
    specializedDerivativeValue parent x₀ z (PowerSeries.C value) d =
      PowerSeries.constantCoeff
        ((specializedShiftedParent parent x₀ z).derivative.eval
          (PowerSeries.C value)) := by
  rw [specializedShiftedParent_eq_sum_range parent x₀ z d parentDegreeLe]
  unfold specializedDerivativeValue
  simp only [PowerSeries.constantCoeff_C]
  rw [map_sum, Polynomial.eval_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro j jMem
  rw [Polynomial.derivative_monomial, Polynomial.eval_monomial]
  simp only [map_mul, map_natCast, PowerSeries.constantCoeff_C, map_pow]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [coeff_specializedShiftedCoefficientHom]
  unfold shiftedParentCoefficient
  ring

/-- Every shifted coefficient after passing to the function field is the
image of the original `c_{s,j}(Z)`. -/
theorem functionField_shiftedParentCoefficient
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (s j : Nat) :
    (shiftedParentCoefficient (branchBaseMap factor x₀) s j
        (functionFieldParent parent factor)).eval (branchChallenge factor) =
      regularCoefficientMap factor
        (shiftedParentCoefficient x₀ s j parent) := by
  unfold shiftedParentCoefficient functionFieldParent mapTrivariateCoefficients
  rw [Polynomial.coeff_map]
  change
    (shiftedChallengeCoefficient (branchBaseMap factor x₀) s
        ((parent.coeff j).map
          (Polynomial.mapRingHom (branchBaseMap factor)))).eval
        (branchChallenge factor) = _
  rw [shiftedChallengeCoefficient_map_eval₂]
  exact (regularCoefficientMap_eq_eval₂ factor
    (shiftedChallengeCoefficient x₀ s (parent.coeff j))).symm

/-- The scalar attached to a retained tuple after passing to the function
field is the image of the original shifted coefficient `c_{s,j}(Z)`. -/
theorem functionField_parentDivisionFreeScalar
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) {t : Nat} {tPositive : 0 < t}
    (index : DivisionFreeTermIndex t tPositive) :
    parentDivisionFreeScalar (functionFieldParent parent factor)
        (branchBaseMap factor x₀) (branchChallenge factor) index =
      regularCoefficientMap factor
        (shiftedParentCoefficient x₀ index.s index.j parent) := by
  exact functionField_shiftedParentCoefficient parent factor x₀ index.s index.j

/-- Specializing the scalar-extended parent in the function field agrees
with applying the original coefficient map after specialization. -/
theorem functionField_specializeX_map
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))] (x₀ : K) :
    (specializeX (branchBaseMap factor x₀)
        (functionFieldParent parent factor)).map
          (Polynomial.evalRingHom (branchChallenge factor)) =
      (specializeX x₀ parent).map (regularCoefficientMap factor) := by
  ext j
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  rw [← shiftedParentCoefficient_zero
      (branchBaseMap factor x₀) j (functionFieldParent parent factor),
    ← shiftedParentCoefficient_zero x₀ j parent]
  exact functionField_shiftedParentCoefficient parent factor x₀ 0 j

/-- The selected branch divisor makes its adjoined root a constant root of
the function-field shifted parent. -/
theorem functionFieldShiftedParent_rootModuloVariable
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (factorDvd : factor ∣ specializeX x₀ parent) :
    PowerSeries.constantCoeff
        ((functionFieldShiftedParent parent factor x₀).eval
          (PowerSeries.C (AdjoinRoot.root (branchPolynomial factor)))) = 0 := by
  rw [functionFieldShiftedParent,
    constantCoeff_specializedShiftedParent_eval_C]
  rw [← Polynomial.eval_map, functionField_specializeX_map,
    Polynomial.eval_map]
  obtain ⟨quotient, factorization⟩ := factorDvd
  rw [factorization, Polynomial.eval₂_mul,
    branchPolynomial_eval₂_root, zero_mul]

/-- The cleared derivative identity after an arbitrary field extension and
challenge evaluation.  This is the function-field analogue of the finite
specialization calculation. -/
theorem eval₂_sourceClearedRepresentative_derivative_map
    {K L : Type*} [Field K] [Field L]
    (parent : TrivariatePolynomial K) (mapBase : K →+* L)
    (x₀ : K) (z y : L) (W : Polynomial K) (d : Nat) :
    (sourceClearedRepresentative parent x₀ 0 d 1
        (fun j ↦ (j : K)) W).eval₂
          (Polynomial.eval₂RingHom mapBase z)
          (W.eval₂ mapBase z * y) =
      (W.eval₂ mapBase z) ^ (d - 1) *
        ∑ j ∈ Finset.range (d + 1),
          (shiftedParentCoefficient x₀ 0 j parent).eval₂ mapBase z *
            (j : L) * y ^ (j - 1) := by
  classical
  have rangeDecomposition : Finset.range (d + 1) =
      insert 0 (Finset.Icc 1 d) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold sourceClearedRepresentative
  rw [Polynomial.eval₂_finsetSum]
  rw [rangeDecomposition, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j jMem
  have oneLeJ : 1 ≤ j := (Finset.mem_Icc.mp jMem).1
  have jLeD : j ≤ d := (Finset.mem_Icc.mp jMem).2
  rw [Polynomial.eval₂_monomial]
  simp only [map_mul, map_pow, coe_eval₂RingHom, map_natCast]
  rw [mul_pow]
  have exponentEq : d - j + (j - 1) = d - 1 := by omega
  let w := W.eval₂ mapBase z
  let coefficient :=
    (shiftedParentCoefficient x₀ 0 j parent).eval₂ mapBase z
  change (j : L) * coefficient * w ^ (d - j) *
      (w ^ (j - 1) * y ^ (j - 1)) =
    w ^ (d - 1) * (coefficient * (j : L) * y ^ (j - 1))
  have powerEq : w ^ (d - j) * w ^ (j - 1) = w ^ (d - 1) := by
    rw [← pow_add, exponentEq]
  calc
    (j : L) * coefficient * w ^ (d - j) *
        (w ^ (j - 1) * y ^ (j - 1)) =
      (w ^ (d - j) * w ^ (j - 1)) *
        (coefficient * (j : L) * y ^ (j - 1)) := by ring
    _ = w ^ (d - 1) *
        (coefficient * (j : L) * y ^ (j - 1)) := by rw [powerEq]

/-- Extending scalar coefficients cannot increase the outer `Y` degree. -/
theorem functionFieldParent_natDegree_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))] :
    (functionFieldParent parent factor).natDegree ≤ parent.natDegree := by
  exact Polynomial.natDegree_map_le

/-- The intrinsic derivative element maps to `W^(d-1)` times the literal
derivative scalar of the function-field shifted parent. -/
theorem regularToFunctionField_regularDerivativeElement
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d : Nat) (series : PowerSeries (BranchFunctionField factor))
    (constantRoot : PowerSeries.constantCoeff series =
      AdjoinRoot.root (branchPolynomial factor)) :
    regularToFunctionField factor factorPositive
        (regularDerivativeElement parent factor x₀ d) =
      regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) ^ (d - 1) *
        specializedDerivativeValue (functionFieldParent parent factor)
          (branchBaseMap factor x₀) (branchChallenge factor) series d := by
  have coefficientMapEq : regularCoefficientMap factor =
      Polynomial.eval₂RingHom (branchBaseMap factor)
        (branchChallenge factor) := by
    apply DFunLike.ext _ _
    intro polynomial
    exact regularCoefficientMap_eq_eval₂ factor polynomial
  let representative := sourceClearedRepresentative parent x₀ 0 d 1
    (fun j ↦ (j : K)) factor.leadingCoeff
  have mappedRepresentative :
      regularToFunctionField factor factorPositive
          (regularDerivativeElement parent factor x₀ d) =
        representative.eval₂ (regularCoefficientMap factor)
          (regularGenerator factor) := by
    unfold regularDerivativeElement regularToFunctionField representative
    rw [AdjoinRoot.lift_mk]
  rw [mappedRepresentative]
  calc
    representative.eval₂ (regularCoefficientMap factor)
          (regularGenerator factor) =
        representative.eval₂
          (Polynomial.eval₂RingHom (branchBaseMap factor)
            (branchChallenge factor))
          (factor.leadingCoeff.eval₂ (branchBaseMap factor)
              (branchChallenge factor) *
            AdjoinRoot.root (branchPolynomial factor)) := by
      unfold regularGenerator
      rw [coefficientMapEq]
      rfl
    _ = factor.leadingCoeff.eval₂ (branchBaseMap factor)
            (branchChallenge factor) ^ (d - 1) *
          ∑ j ∈ Finset.range (d + 1),
            (shiftedParentCoefficient x₀ 0 j parent).eval₂
                (branchBaseMap factor) (branchChallenge factor) *
              (j : BranchFunctionField factor) *
                (AdjoinRoot.root (branchPolynomial factor)) ^ (j - 1) := by
      exact eval₂_sourceClearedRepresentative_derivative_map parent
        (branchBaseMap factor) x₀ (branchChallenge factor)
        (AdjoinRoot.root (branchPolynomial factor)) factor.leadingCoeff d
    _ = regularToFunctionField factor factorPositive
              (regularLeadingCoefficient factor) ^ (d - 1) *
          specializedDerivativeValue (functionFieldParent parent factor)
            (branchBaseMap factor x₀) (branchChallenge factor) series d := by
      simp only [regularLeadingCoefficient, regularToFunctionField_of]
      rw [regularCoefficientMap_eq_eval₂]
      unfold specializedDerivativeValue
      apply congrArg
        (fun value : BranchFunctionField factor ↦
          factor.leadingCoeff.eval₂ (branchBaseMap factor)
              (branchChallenge factor) ^ (d - 1) * value)
      apply Finset.sum_congr rfl
      intro j jMem
      rw [functionField_shiftedParentCoefficient parent factor x₀ 0 j,
        regularCoefficientMap_eq_eval₂, constantRoot]

/-- A nonzero intrinsic regular derivative gives the simple constant-root
condition required by Hensel lifting in the function field. -/
theorem functionFieldShiftedParent_derivative_ne_zero
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d : Nat) (parentDegreeLe : parent.natDegree ≤ d)
    (etaNeZero : regularDerivativeElement parent factor x₀ d ≠ 0) :
    PowerSeries.constantCoeff
        ((functionFieldShiftedParent parent factor x₀).derivative.eval
          (PowerSeries.C (AdjoinRoot.root (branchPolynomial factor)))) ≠ 0 := by
  let rootValue := AdjoinRoot.root (branchPolynomial factor)
  let constantSeries : PowerSeries (BranchFunctionField factor) :=
    PowerSeries.C rootValue
  have constantSeriesRoot : PowerSeries.constantCoeff constantSeries =
      AdjoinRoot.root (branchPolynomial factor) := by
    simp [constantSeries, rootValue]
  have etaImage := regularToFunctionField_regularDerivativeElement parent factor
    factorPositive x₀ d constantSeries constantSeriesRoot
  have parentDegreeInField :
      (functionFieldParent parent factor).natDegree ≤ d :=
    (functionFieldParent_natDegree_le parent factor).trans parentDegreeLe
  have derivativeIdentity :=
    specializedDerivativeValue_eq_constantCoeff_derivative
      (functionFieldParent parent factor) (branchBaseMap factor x₀)
      (branchChallenge factor) rootValue d parentDegreeInField
  intro derivativeZero
  have zetaZero : specializedDerivativeValue
        (functionFieldParent parent factor) (branchBaseMap factor x₀)
        (branchChallenge factor) constantSeries d = 0 := by
    change specializedDerivativeValue (functionFieldParent parent factor)
      (branchBaseMap factor x₀) (branchChallenge factor)
        (PowerSeries.C rootValue) d = 0
    rw [derivativeIdentity]
    exact derivativeZero
  have mappedEtaZero : regularToFunctionField factor factorPositive
      (regularDerivativeElement parent factor x₀ d) = 0 := by
    rw [etaImage, zetaZero, mul_zero]
  exact (regularToFunctionField_ne_zero factor factorNeZero factorPositive
    etaNeZero) mappedEtaZero

/-- Separability of the specialized parent over `K(Z)` supplies the
nonvanishing intrinsic regular derivative required on every irreducible
branch divisor. This is the explicit Step 2 hypothesis in BCHKS26.

The proof first transports separability to the selected branch field. The
branch root is then a simple root of the specialized parent, while the
cleared-derivative identity differs from its literal derivative value only
by a nonzero power of the branch leading coefficient. -/
theorem regularDerivativeElement_ne_zero_of_specialized_separable
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorIrreducible : Irreducible factor)
    (factorPositive : 0 < factor.natDegree)
    (x₀ : K) (d : Nat) (parentDegreeLe : parent.natDegree ≤ d)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (specializedSeparable :
      (branchPolynomial (specializeX x₀ parent)).Separable) :
    regularDerivativeElement parent factor x₀ d ≠ 0 := by
  letI : Fact (Irreducible (branchPolynomial factor)) :=
    ⟨branchPolynomial_irreducible factor factorIrreducible factorPositive⟩
  let rootMap : RationalFunctionField K →+* BranchFunctionField factor :=
    AdjoinRoot.of (branchPolynomial factor)
  let root : BranchFunctionField factor :=
    AdjoinRoot.root (branchPolynomial factor)
  let specializedParent : Polynomial (BranchFunctionField factor) :=
    (specializeX x₀ parent).map (regularCoefficientMap factor)
  have mapEq :
      (branchPolynomial (specializeX x₀ parent)).map rootMap =
        specializedParent := by
    dsimp [rootMap, specializedParent]
    unfold branchPolynomial regularCoefficientMap
    rw [Polynomial.map_map]
    rfl
  have specializedParentSeparable : specializedParent.Separable := by
    rw [← mapEq]
    exact specializedSeparable.map
  have specializedParentRoot : specializedParent.eval root = 0 := by
    unfold specializedParent
    rw [Polynomial.eval_map]
    obtain ⟨quotient, factorization⟩ := factorDvd
    rw [factorization, Polynomial.eval₂_mul,
      branchPolynomial_eval₂_root, zero_mul]
  have derivativeAtRootNeZero :
      specializedParent.derivative.eval root ≠ 0 := by
    have value := specializedParentSeparable.eval₂_derivative_ne_zero
      (RingHom.id (BranchFunctionField factor)) specializedParentRoot
    simpa using value
  have derivativeIdentity :
      specializedDerivativeValue (functionFieldParent parent factor)
          (branchBaseMap factor x₀) (branchChallenge factor)
          (PowerSeries.C root) d =
        specializedParent.derivative.eval root := by
    rw [specializedDerivativeValue_eq_constantCoeff_derivative
      (functionFieldParent parent factor) (branchBaseMap factor x₀)
      (branchChallenge factor) root d
      ((functionFieldParent_natDegree_le parent factor).trans parentDegreeLe)]
    calc
      PowerSeries.constantCoeff
          ((specializedShiftedParent (functionFieldParent parent factor)
              (branchBaseMap factor x₀) (branchChallenge factor)).derivative.eval
            (PowerSeries.C root)) =
          PowerSeries.constantCoeff
            ((specializedShiftedParent
                (Polynomial.derivative (functionFieldParent parent factor))
                (branchBaseMap factor x₀) (branchChallenge factor)).eval
              (PowerSeries.C root)) := by
            congr 2
            simp [specializedShiftedParent]
      _ = (specializeX (branchBaseMap factor x₀)
              (Polynomial.derivative (functionFieldParent parent factor))).eval₂
            (Polynomial.evalRingHom (branchChallenge factor)) root :=
          constantCoeff_specializedShiftedParent_eval_C
            (Polynomial.derivative (functionFieldParent parent factor))
            (branchBaseMap factor x₀) (branchChallenge factor) root
      _ = (Polynomial.derivative
              (specializeX (branchBaseMap factor x₀)
                (functionFieldParent parent factor))).eval₂
            (Polynomial.evalRingHom (branchChallenge factor)) root := by
          simp [specializeX]
      _ = (Polynomial.derivative
              ((specializeX (branchBaseMap factor x₀)
                (functionFieldParent parent factor)).map
                  (Polynomial.evalRingHom (branchChallenge factor)))).eval root := by
          rw [Polynomial.derivative_map, Polynomial.eval_map]
      _ = specializedParent.derivative.eval root := by
          rw [functionField_specializeX_map]
  intro etaZero
  have imageZero : regularToFunctionField factor factorPositive
      (regularDerivativeElement parent factor x₀ d) = 0 := by
    rw [etaZero, map_zero]
  have imageIdentity := regularToFunctionField_regularDerivativeElement
    parent factor factorPositive x₀ d (PowerSeries.C root) (by simp [root])
  rw [imageZero, derivativeIdentity] at imageIdentity
  have leadingNeZero : regularToFunctionField factor factorPositive
      (regularLeadingCoefficient factor) ≠ 0 := by
    simp only [regularLeadingCoefficient, regularToFunctionField_of]
    have leadingNe : factor.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr factorIrreducible.ne_zero
    have mappedNe := (regularCoefficientMap_injective factor factorPositive).ne
      leadingNe
    simpa using mappedNe
  exact derivativeAtRootNeZero
    ((mul_eq_zero.mp imageIdentity.symm).resolve_left
      (pow_ne_zero _ leadingNeZero))

/-- The selected simple branch has an exact characteristic-free
power-series Hensel lift with the prescribed constant coefficient. -/
theorem exists_functionField_powerSeriesRoot
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d : Nat) (parentDegreeLe : parent.natDegree ≤ d)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (etaNeZero : regularDerivativeElement parent factor x₀ d ≠ 0) :
    ∃ root : PowerSeries (BranchFunctionField factor),
      (functionFieldShiftedParent parent factor x₀).IsRoot root ∧
        PowerSeries.constantCoeff root =
          AdjoinRoot.root (branchPolynomial factor) := by
  exact exists_powerSeries_root_of_simple_constant_root
    (functionFieldShiftedParent parent factor x₀)
    (AdjoinRoot.root (branchPolynomial factor))
    (functionFieldShiftedParent_rootModuloVariable parent factor x₀ factorDvd)
    (functionFieldShiftedParent_derivative_ne_zero parent factor factorNeZero
      factorPositive x₀ d parentDegreeLe etaNeZero)

/-- Each canonical quotient coefficient `rho_{s,j}` maps to the literal
shifted scalar times the required power of `W`. -/
theorem regularToFunctionField_parentDivisionFreeCoefficient
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d : Nat) {t : Nat} {tPositive : 0 < t}
    (index : DivisionFreeTermIndex t tPositive) :
    regularToFunctionField factor factorPositive
        (parentDivisionFreeCoefficient parent factor x₀ d index) =
      parentDivisionFreeScalar (functionFieldParent parent factor)
          (branchBaseMap factor x₀) (branchChallenge factor) index *
        regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) ^ (d - index.j) := by
  rw [functionField_parentDivisionFreeScalar parent factor x₀ index]
  simp [parentDivisionFreeCoefficient, regularClearedCoefficient,
    regularLeadingCoefficient]

/-- Equation (64) for the canonical coefficients attached to the actual
parent and an actual function-field power-series root. -/
theorem parentDivisionFreeCoefficients_image_of_root
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (d : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (root : PowerSeries (BranchFunctionField factor))
    (rootEquation : (functionFieldShiftedParent parent factor x₀).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (branchPolynomial factor)) (t : Nat) :
    regularToFunctionField factor factorPositive
        (parentDivisionFreeCoefficients parent factor x₀ d t) =
      regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) *
        regularToFunctionField factor factorPositive
            (regularDerivativeElement parent factor x₀ d) ^
          henselExponent t * PowerSeries.coeff t root := by
  let parentInField := functionFieldParent parent factor
  let basePoint := branchBaseMap factor x₀
  let challenge := branchChallenge factor
  let eta := regularDerivativeElement parent factor x₀ d
  let terms := parentDivisionFreeTerms d
  let rho := fun (order : Nat) (orderPositive : 0 < order)
      (index : DivisionFreeTermIndex order orderPositive) ↦
    parentDivisionFreeCoefficient parent factor x₀ d index
  let coefficient := fun (order : Nat) (orderPositive : 0 < order)
      (index : DivisionFreeTermIndex order orderPositive) ↦
    parentDivisionFreeScalar parentInField basePoint challenge index
  let zeta := specializedDerivativeValue parentInField basePoint challenge root d
  let alpha := fun order ↦ PowerSeries.coeff order root
  have parentDegreeLeInField : parentInField.natDegree ≤ d :=
    (functionFieldParent_natDegree_le parent factor).trans parentDegreeLe
  have baseImage : regularToFunctionField factor factorPositive
        (AdjoinRoot.root (monicization factor)) =
      regularToFunctionField factor factorPositive
          (regularLeadingCoefficient factor) * alpha 0 := by
    rw [regularToFunctionField_root]
    unfold regularGenerator regularLeadingCoefficient alpha
    rw [regularToFunctionField_of,
      PowerSeries.coeff_zero_eq_constantCoeff, rootConstant]
  have etaImage : regularToFunctionField factor factorPositive eta =
      regularToFunctionField factor factorPositive
            (regularLeadingCoefficient factor) ^ (d - 1) * zeta := by
    exact regularToFunctionField_regularDerivativeElement parent factor
      factorPositive x₀ d root rootConstant
  have jLeD : ∀ (order : Nat) (orderPositive : 0 < order)
      (index : DivisionFreeTermIndex order orderPositive),
      index ∈ terms order orderPositive → index.j ≤ d := by
    intro order orderPositive index indexMem
    exact parentDivisionFreeTerms_j_le d order orderPositive index indexMem
  have rhoImage : ∀ (order : Nat) (orderPositive : 0 < order)
      (index : DivisionFreeTermIndex order orderPositive),
      index ∈ terms order orderPositive →
        regularToFunctionField factor factorPositive
            (rho order orderPositive index) =
          coefficient order orderPositive index *
            regularToFunctionField factor factorPositive
              (regularLeadingCoefficient factor) ^ (d - index.j) := by
    intro order orderPositive index indexMem
    exact regularToFunctionField_parentDivisionFreeCoefficient parent factor
      factorPositive x₀ d index
  have coefficientRecurrence : ∀ (order : Nat) (orderPositive : 0 < order),
      zeta * alpha order =
        -∑ index ∈ terms order orderPositive,
          coefficient order orderPositive index *
            ∏ partIndex, alpha (index.parts partIndex) := by
    intro order orderPositive
    have recurrence := specializedParent_coefficient_recurrence parentInField
      basePoint challenge root d order parentDegreeLeInField orderPositive
        rootEquation
    rw [retainedParentTermSum_eq_parentDivisionFreeTerms_sum parentInField
      basePoint challenge root d order orderPositive] at recurrence
    exact recurrence
  have image := divisionFreeCoefficients_image factor factorPositive d
    dPositive eta terms rho coefficient zeta alpha baseImage etaImage jLeD
      rhoImage coefficientRecurrence t
  simpa only [parentDivisionFreeCoefficients, eta, terms, rho, coefficient,
    zeta, alpha, parentInField, basePoint, challenge] using image

#print axioms exists_adic_root_of_simple_approximation
#print axioms exists_powerSeries_root_of_simple_constant_root
#print axioms powerSeries_root_unique_of_simple_constant_root
#print axioms regularCoefficientMap_eq_eval₂
#print axioms shiftedChallengeCoefficient_map_eval₂
#print axioms map_functionFieldPolynomialParent
#print axioms specializedDerivativeValue_eq_constantCoeff_derivative
#print axioms functionField_shiftedParentCoefficient
#print axioms functionField_parentDivisionFreeScalar
#print axioms functionFieldShiftedParent_rootModuloVariable
#print axioms eval₂_sourceClearedRepresentative_derivative_map
#print axioms regularToFunctionField_regularDerivativeElement
#print axioms functionFieldShiftedParent_derivative_ne_zero
#print axioms regularDerivativeElement_ne_zero_of_specialized_separable
#print axioms exists_functionField_powerSeriesRoot
#print axioms regularToFunctionField_parentDivisionFreeCoefficient
#print axioms parentDivisionFreeCoefficients_image_of_root

end

end WeightedHensel

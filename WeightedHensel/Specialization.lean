/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.ResultantBound
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Finite specialization of the regular branch

This file constructs specialization only on the integral quotient `O`.
It also records the literal commuting square between translation in the
weight-zero variable `X` and specialization of the challenge variable `Z`.
No evaluation homomorphism from the fraction field is introduced.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-! ## Translation and challenge specialization -/

/-- Substitute `X = x₀ + U` into a univariate polynomial, with the result
viewed as a formal power series in `U`. -/
def shiftedEvaluationHom
    {K : Type*} [Field K] (x₀ : K) : Polynomial K →+* PowerSeries K :=
  Polynomial.eval₂RingHom PowerSeries.C
    (PowerSeries.C x₀ + PowerSeries.X)

/-- First specialize `Z=z`, then substitute `X=x₀+U`. -/
def specializedShiftedCoefficientHom
    {K : Type*} [Field K] (x₀ z : K) :
    BivariatePolynomial K →+* PowerSeries K :=
  Polynomial.eval₂RingHom (shiftedEvaluationHom x₀) (PowerSeries.C z)

/-- The parent after concrete challenge specialization and literal
translation of `X`. It remains a polynomial in `Y`, now over `K[[U]]`. -/
def specializedShiftedParent
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) : Polynomial (PowerSeries K) :=
  parent.map (specializedShiftedCoefficientHom x₀ z)

/-- Specialize the challenge variable `Z=z`, leaving a polynomial in `Y`
over `K[X]`. -/
def specializeChallenge
    {K : Type*} [Field K] (z : K) (parent : TrivariatePolynomial K) :
    Polynomial (Polynomial K) :=
  parent.map (Polynomial.evalRingHom (Polynomial.C z))

/-- Substitute a challenge-dependent polynomial candidate for `Y` after
specializing `Z=z`. -/
def challengeCandidatePolynomial
    {K : Type*} [Field K] (z : K) (candidate : Polynomial K)
    (parent : TrivariatePolynomial K) : Polynomial K :=
  (specializeChallenge z parent).eval candidate

/-- The shifted power-series expansion of a candidate polynomial. -/
def shiftedCandidateSeries
    {K : Type*} [Field K] (x₀ : K)
    (candidate : Polynomial K) : PowerSeries K :=
  shiftedEvaluationHom x₀ candidate

theorem specializedShiftedCoefficientHom_eq_comp
    {K : Type*} [Field K] (x₀ z : K) :
    specializedShiftedCoefficientHom x₀ z =
      (shiftedEvaluationHom x₀).comp
        (Polynomial.evalRingHom (Polynomial.C z)) := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    simp [specializedShiftedCoefficientHom, shiftedEvaluationHom]
  · simp [specializedShiftedCoefficientHom, shiftedEvaluationHom]

theorem shiftedEvaluationHom_eq_coe_taylor
    {K : Type*} [Field K] (x₀ : K) (polynomial : Polynomial K) :
    shiftedEvaluationHom x₀ polynomial =
      (Polynomial.taylor x₀ polynomial : PowerSeries K) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [map_add, leftInduction, rightInduction, map_add]
      exact (Polynomial.coe_add (Polynomial.taylor x₀ left)
        (Polynomial.taylor x₀ right)).symm
  | monomial exponent coefficient =>
      change Polynomial.eval₂ PowerSeries.C
          (PowerSeries.C x₀ + PowerSeries.X)
          (Polynomial.monomial exponent coefficient) = _
      rw [Polynomial.eval₂_monomial, Polynomial.taylor_monomial,
        Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_add, Polynomial.coe_X]
      rw [add_comm]
      rw [Polynomial.coe_C]

theorem coeff_shiftedEvaluationHom
    {K : Type*} [Field K] (x₀ : K) (polynomial : Polynomial K)
    (order : Nat) :
    PowerSeries.coeff order (shiftedEvaluationHom x₀ polynomial) =
      (Polynomial.hasseDeriv order polynomial).eval x₀ := by
  rw [shiftedEvaluationHom_eq_coe_taylor, Polynomial.coeff_coe,
    Polynomial.taylor_coeff]

/-- Exact coefficient commuting square for the shifted coefficient
`c_{s,j}(Z)`. -/
theorem coeff_specializedShiftedCoefficientHom
    {K : Type*} [Field K] (x₀ z : K)
    (polynomial : BivariatePolynomial K) (order : Nat) :
    PowerSeries.coeff order
        (specializedShiftedCoefficientHom x₀ z polynomial) =
      (shiftedChallengeCoefficient x₀ order polynomial).eval z := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [map_add, map_add, shiftedChallengeCoefficient_add,
        Polynomial.eval_add, leftInduction, rightInduction]
  | monomial challengeExponent coefficient =>
      rw [specializedShiftedCoefficientHom_eq_comp, RingHom.comp_apply,
        coe_evalRingHom, Polynomial.eval_monomial, map_mul, map_pow]
      rw [show shiftedEvaluationHom x₀ (Polynomial.C z) ^ challengeExponent =
          PowerSeries.C (z ^ challengeExponent) by
        simp [shiftedEvaluationHom]]
      rw [PowerSeries.coeff_mul_C]
      rw [shiftedChallengeCoefficient_monomial, Polynomial.eval_monomial]
      rw [coeff_shiftedEvaluationHom]

theorem specializedShiftedParent_eq_map_specializeChallenge
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) :
    specializedShiftedParent parent x₀ z =
      (specializeChallenge z parent).map (shiftedEvaluationHom x₀) := by
  unfold specializedShiftedParent specializeChallenge
  rw [specializedShiftedCoefficientHom_eq_comp, ← Polynomial.map_map]

/-- A polynomial candidate root remains a root after the literal
translation into formal power series. -/
theorem shiftedCandidateSeries_isRoot
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (candidate : Polynomial K)
    (candidateRoot : challengeCandidatePolynomial z candidate parent = 0) :
    (specializedShiftedParent parent x₀ z).IsRoot
      (shiftedCandidateSeries x₀ candidate) := by
  rw [Polynomial.IsRoot, specializedShiftedParent_eq_map_specializeChallenge]
  change ((specializeChallenge z parent).map
      (shiftedEvaluationHom x₀)).eval
        (shiftedEvaluationHom x₀ candidate) = 0
  rw [Polynomial.eval_map]
  calc
    Polynomial.eval₂ (shiftedEvaluationHom x₀)
        (shiftedEvaluationHom x₀ candidate)
        (specializeChallenge z parent) =
      shiftedEvaluationHom x₀
        ((specializeChallenge z parent).eval candidate) := by
      symm
      exact Polynomial.hom_eval₂
        (specializeChallenge z parent) (RingHom.id (Polynomial K))
          (shiftedEvaluationHom x₀) candidate
    _ = 0 := by
      change shiftedEvaluationHom x₀
          (challengeCandidatePolynomial z candidate parent) = 0
      rw [candidateRoot, map_zero]

@[simp] theorem constantCoeff_shiftedCandidateSeries
    {K : Type*} [Field K] (x₀ : K) (candidate : Polynomial K) :
    PowerSeries.constantCoeff (shiftedCandidateSeries x₀ candidate) =
      candidate.eval x₀ := by
  unfold shiftedCandidateSeries
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    coeff_shiftedEvaluationHom]
  simp

theorem coeff_shiftedCandidateSeries_eq_zero_of_natDegree_lt
    {K : Type*} [Field K] (x₀ : K) (candidate : Polynomial K)
    (order : Nat) (degreeLt : candidate.natDegree < order) :
    PowerSeries.coeff order (shiftedCandidateSeries x₀ candidate) = 0 := by
  rw [shiftedCandidateSeries, coeff_shiftedEvaluationHom,
    Polynomial.hasseDeriv_eq_zero_of_lt_natDegree candidate order degreeLt,
    Polynomial.eval_zero]

/-! ## The literal finite partition family -/

/-- A bounded raw tuple `(s,j,u)` for coefficient order `t` and parent
`Y`-degree bound `d`. Bounds are part of the data, so this type is finite. -/
abbrev BoundedRawTermIndex (d t : Nat) :=
  Σ s : Fin (t + 1), Σ j : Fin (d + 1),
    ↥((Finset.range j.val).finsuppAntidiag (t - s.val))

/-- Number of nonzero entries of a finite-support convolution tuple on a
fixed index set. -/
def finsuppPositivePartCount (indices : Finset Nat)
    (parts : Nat →₀ Nat) : Nat :=
  (indices.filter fun index ↦ parts index ≠ 0).card

theorem positivePartCount_fin_eq_finsuppPositivePartCount
    (j : Nat) (parts : Nat →₀ Nat) :
    positivePartCount (fun index : Fin j ↦ parts index.val) =
      finsuppPositivePartCount (Finset.range j) parts := by
  classical
  unfold positivePartCount finsuppPositivePartCount
  have imageEq :
      ((Finset.univ.filter
          (fun index : Fin j ↦ parts index.val ≠ 0)).image Fin.val) =
        (Finset.range j).filter (fun index ↦ parts index ≠ 0) := by
    ext index
    simp [Fin.exists_iff, and_comm]
  calc
    (Finset.univ.filter
        (fun index : Fin j ↦ parts index.val ≠ 0)).card =
        ((Finset.univ.filter
          (fun index : Fin j ↦ parts index.val ≠ 0)).image Fin.val).card := by
      rw [Finset.card_image_of_injective _ Fin.val_injective]
    _ = ((Finset.range j).filter fun index ↦ parts index ≠ 0).card := by
      rw [imageEq]

/-- In a positive-total convolution tuple with exactly one positive part,
that unique part carries the whole order. -/
theorem exists_unique_full_part_of_finsuppPositivePartCount_eq_one
    (indices : Finset Nat) (parts : Nat →₀ Nat) (total : Nat)
    (partsSum : ∑ index ∈ indices, parts index = total)
    (onePositive : finsuppPositivePartCount indices parts = 1) :
    ∃! index, index ∈ indices ∧ parts index = total := by
  classical
  have singleton : ∃ index,
      indices.filter (fun other ↦ parts other ≠ 0) = {index} :=
    Finset.card_eq_one.mp onePositive
  obtain ⟨index, filteredEq⟩ := singleton
  have indexFiltered : index ∈
      indices.filter (fun other ↦ parts other ≠ 0) := by
    rw [filteredEq]
    exact Finset.mem_singleton_self index
  have indexMem := (Finset.mem_filter.mp indexFiltered).1
  have otherZero : ∀ other ∈ indices, other ≠ index → parts other = 0 := by
    intro other otherMem otherNe
    by_contra otherNonzero
    have otherFiltered : other ∈
        indices.filter (fun candidate ↦ parts candidate ≠ 0) :=
      Finset.mem_filter.mpr ⟨otherMem, otherNonzero⟩
    rw [filteredEq, Finset.mem_singleton] at otherFiltered
    exact otherNe otherFiltered
  have indexFull : parts index = total := by
    calc
      parts index = ∑ other ∈ indices, parts other := by
        rw [Finset.sum_eq_single index]
        · intro other otherMem otherNe
          exact otherZero other otherMem otherNe
        · intro indexNotMem
          exact (indexNotMem indexMem).elim
      _ = total := partsSum
  refine ⟨index, ⟨indexMem, indexFull⟩, ?_⟩
  intro other otherProperty
  by_contra otherNe
  have totalPositive : 0 < total := by
    have indexNonzero := (Finset.mem_filter.mp indexFiltered).2
    rw [indexFull] at indexNonzero
    exact Nat.pos_of_ne_zero indexNonzero
  have otherNonzero : parts other ≠ 0 := by
    rw [otherProperty.2]
    exact Nat.ne_of_gt totalPositive
  exact otherNonzero (otherZero other otherProperty.1 otherNe)

/-- The singleton convolution tuples at positive total order. -/
def linearFinsuppParts (j total : Nat) : Finset (Nat →₀ Nat) :=
  ((Finset.range j).finsuppAntidiag total).filter
    (fun parts ↦ finsuppPositivePartCount (Finset.range j) parts = 1)

theorem Finsupp.single_mem_linearFinsuppParts
    (j total index : Nat) (totalPositive : 0 < total)
    (indexMem : index ∈ Finset.range j) :
    Finsupp.single index total ∈ linearFinsuppParts j total := by
  classical
  rw [linearFinsuppParts, Finset.mem_filter]
  constructor
  · rw [Finset.mem_finsuppAntidiag]
    constructor
    · rw [Finset.sum_eq_single index]
      · simp
      · intro other otherMem otherNe
        simp [otherNe]
      · intro indexNotMem
        exact (indexNotMem indexMem).elim
    · intro supportIndex supportMem
      have supportNe : Finsupp.single index total supportIndex ≠ 0 :=
        Finsupp.mem_support_iff.mp supportMem
      have supportEq : supportIndex = index := by
        by_contra supportNeIndex
        apply supportNe
        simp [supportNeIndex]
      simpa [supportEq] using indexMem
  · unfold finsuppPositivePartCount
    have filterEq :
        (Finset.range j).filter
            (fun candidate ↦ Finsupp.single index total candidate ≠ 0) =
          {index} := by
      ext candidate
      simp only [Finset.mem_filter, Finset.mem_range,
        Finset.mem_singleton]
      constructor
      · rintro ⟨candidateMem, candidateNeZero⟩
        by_contra candidateNeIndex
        apply candidateNeZero
        simp [candidateNeIndex]
      · intro candidateEq
        subst candidate
        exact ⟨Finset.mem_range.mp indexMem, by
          simp [totalPositive.ne']⟩
    rw [filterEq]
    simp

theorem eq_single_of_mem_finsuppAntidiag_of_count_eq_one
    (indices : Finset Nat) (parts : Nat →₀ Nat) (total : Nat)
    (partsMem : parts ∈ indices.finsuppAntidiag total)
    (onePositive : finsuppPositivePartCount indices parts = 1) :
    ∃ index ∈ indices, parts = Finsupp.single index total := by
  classical
  have partsData := Finset.mem_finsuppAntidiag.mp partsMem
  obtain ⟨index, indexProperty, unique⟩ :=
    exists_unique_full_part_of_finsuppPositivePartCount_eq_one
      indices parts total partsData.1 onePositive
  refine ⟨index, indexProperty.1, ?_⟩
  apply Finsupp.ext
  intro candidate
  by_cases candidateMem : candidate ∈ indices
  · by_cases candidateEq : candidate = index
    · subst candidate
      simp [indexProperty.2]
    · by_cases candidateZero : parts candidate = 0
      · simp [candidateZero, candidateEq]
      · have filteredCard := onePositive
        unfold finsuppPositivePartCount at filteredCard
        have indexFiltered : index ∈
            indices.filter (fun other ↦ parts other ≠ 0) := by
          exact Finset.mem_filter.mpr
            ⟨indexProperty.1, by
              rw [indexProperty.2]
              exact Nat.ne_of_gt (by
                have := partsData.1
                by_contra totalNotPositive
                have totalZero : total = 0 := by omega
                rw [totalZero] at indexProperty
                exact candidateZero (by
                  have sumZero : ∑ other ∈ indices, parts other = 0 := by
                    rw [partsData.1, totalZero]
                  exact (Finset.sum_eq_zero_iff_of_nonneg
                    (fun _ _ ↦ Nat.zero_le _)).mp sumZero candidate
                      candidateMem))⟩
        have candidateFiltered : candidate ∈
            indices.filter (fun other ↦ parts other ≠ 0) :=
          Finset.mem_filter.mpr ⟨candidateMem, candidateZero⟩
        obtain ⟨only, filterEq⟩ := Finset.card_eq_one.mp filteredCard
        have onlyEq : only = index := by
          rw [filterEq, Finset.mem_singleton] at indexFiltered
          exact indexFiltered.symm
        have filteredEq :
            indices.filter (fun other ↦ parts other ≠ 0) = {index} := by
          simpa [onlyEq] using filterEq
        rw [filteredEq, Finset.mem_singleton] at candidateFiltered
        exact (candidateEq candidateFiltered).elim
  · have candidateNotSupport : candidate ∉ parts.support :=
      fun supportMem ↦ candidateMem (partsData.2 supportMem)
    have candidateZero : parts candidate = 0 := by
      simpa [Finsupp.mem_support_iff] using candidateNotSupport
    have candidateNeIndex : candidate ≠ index := by
      intro candidateEq
      apply candidateMem
      simpa [candidateEq] using indexProperty.1
    simp [candidateZero, candidateNeIndex]

theorem linearFinsuppParts_eq_image
    (j total : Nat) (totalPositive : 0 < total) :
    linearFinsuppParts j total =
      (Finset.range j).image (fun index ↦ Finsupp.single index total) := by
  classical
  ext parts
  constructor
  · intro partsMem
    have data := Finset.mem_filter.mp partsMem
    obtain ⟨index, indexMem, rfl⟩ :=
      eq_single_of_mem_finsuppAntidiag_of_count_eq_one
        (Finset.range j) parts total data.1 data.2
    exact Finset.mem_image.mpr ⟨index, indexMem, rfl⟩
  · intro partsMem
    obtain ⟨index, indexMem, rfl⟩ := Finset.mem_image.mp partsMem
    exact Finsupp.single_mem_linearFinsuppParts j total index totalPositive
      indexMem

theorem prod_coeff_single_finsupp
    {K : Type*} [Field K] (series : PowerSeries K)
    (j total index : Nat) (indexMem : index ∈ Finset.range j) :
    ∏ partIndex ∈ Finset.range j,
        PowerSeries.coeff (Finsupp.single index total partIndex) series =
      PowerSeries.constantCoeff series ^ (j - 1) *
        PowerSeries.coeff total series := by
  classical
  let coefficient := fun partIndex : Nat ↦
    PowerSeries.coeff (Finsupp.single index total partIndex) series
  have erasedConstant :
      ∏ partIndex ∈ (Finset.range j).erase index,
          coefficient partIndex =
        PowerSeries.constantCoeff series ^ (j - 1) := by
    calc
      ∏ partIndex ∈ (Finset.range j).erase index,
          coefficient partIndex =
          ∏ _partIndex ∈ (Finset.range j).erase index,
            PowerSeries.constantCoeff series := by
        apply Finset.prod_congr rfl
        intro partIndex partMem
        have partNe : partIndex ≠ index := Finset.ne_of_mem_erase partMem
        simp [coefficient, partNe, PowerSeries.coeff_zero_eq_constantCoeff]
      _ = PowerSeries.constantCoeff series ^
            ((Finset.range j).erase index).card := by
        rw [Finset.prod_const]
      _ = PowerSeries.constantCoeff series ^ (j - 1) := by
        rw [Finset.card_erase_of_mem indexMem, Finset.card_range]
  calc
    ∏ partIndex ∈ Finset.range j,
        PowerSeries.coeff (Finsupp.single index total partIndex) series =
        (∏ partIndex ∈ (Finset.range j).erase index,
          coefficient partIndex) * coefficient index := by
      symm
      exact Finset.prod_erase_mul (Finset.range j) coefficient indexMem
    _ = PowerSeries.constantCoeff series ^ (j - 1) *
          PowerSeries.coeff total series := by
      rw [erasedConstant]
      simp [coefficient]

theorem sum_linearFinsuppParts_product
    {K : Type*} [Field K] (series : PowerSeries K)
    (j total : Nat) (totalPositive : 0 < total) :
    ∑ parts ∈ linearFinsuppParts j total,
        ∏ partIndex ∈ Finset.range j,
          PowerSeries.coeff (parts partIndex) series =
      (j : K) * PowerSeries.constantCoeff series ^ (j - 1) *
        PowerSeries.coeff total series := by
  classical
  rw [linearFinsuppParts_eq_image j total totalPositive,
    Finset.sum_image
      (Finsupp.single_left_injective totalPositive.ne').injOn]
  calc
    ∑ index ∈ Finset.range j,
        ∏ partIndex ∈ Finset.range j,
          PowerSeries.coeff (Finsupp.single index total partIndex) series =
        ∑ _index ∈ Finset.range j,
          PowerSeries.constantCoeff series ^ (j - 1) *
            PowerSeries.coeff total series := by
      apply Finset.sum_congr rfl
      intro index indexMem
      exact prod_coeff_single_finsupp series j total index indexMem
    _ = (j : K) * PowerSeries.constantCoeff series ^ (j - 1) *
          PowerSeries.coeff total series := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- The retained tuples have total order `t-s` and exclude precisely the
linear occurrence at `s=0`. -/
def BoundedRawTermIndex.Retained {d t : Nat}
    (index : BoundedRawTermIndex d t) : Prop :=
  ¬ (index.1.val = 0 ∧
    finsuppPositivePartCount (Finset.range index.2.1.val) index.2.2.1 = 1)

instance BoundedRawTermIndex.instDecidableRetained
    {d t : Nat} (index : BoundedRawTermIndex d t) :
    Decidable index.Retained := by
  unfold BoundedRawTermIndex.Retained finsuppPositivePartCount
  infer_instance

/-- The actual finite partition index used by the parent recurrence. -/
abbrev BoundedTermIndex (d t : Nat) :=
  {index : BoundedRawTermIndex d t // index.Retained}

/-- The omitted singleton linear tuples. -/
abbrev ExcludedTermIndex (d t : Nat) :=
  {index : BoundedRawTermIndex d t // ¬ index.Retained}

/-- Forget the explicit finite bounds, obtaining the abstract recurrence
index used by `divisionFreeCoefficients`. -/
def BoundedTermIndex.toDivisionFree
    {d t : Nat} (tPositive : 0 < t) (index : BoundedTermIndex d t) :
    DivisionFreeTermIndex t tPositive where
  s := index.1.1.val
  s_le := by omega
  j := index.1.2.1.val
  parts := fun partIndex ↦ index.1.2.2.1 partIndex.val
  order_eq := by
    have partsSum := (Finset.mem_finsuppAntidiag.mp index.1.2.2.2).1
    unfold tupleOrder
    calc
      ∑ partIndex : Fin index.1.2.1.val,
          index.1.2.2.1 partIndex.val =
          ∑ partIndex ∈ Finset.range index.1.2.1.val,
            index.1.2.2.1 partIndex :=
        Fin.sum_univ_eq_sum_range index.1.2.2.1 index.1.2.1.val
      _ = t - index.1.1.val := partsSum
  notLinear := by
    intro linear
    apply index.2
    exact ⟨linear.1, by
      rw [← positivePartCount_fin_eq_finsuppPositivePartCount]
      exact linear.2⟩

theorem BoundedTermIndex.toDivisionFree_injective
    {d t : Nat} (tPositive : 0 < t) :
    Function.Injective
      (BoundedTermIndex.toDivisionFree (d := d) tPositive) := by
  classical
  intro left right indexEq
  apply Subtype.ext
  rcases left with ⟨⟨leftS, leftJ, leftParts⟩, leftRetained⟩
  rcases right with ⟨⟨rightS, rightJ, rightParts⟩, rightRetained⟩
  have sEq : leftS = rightS := by
    apply Fin.ext
    exact congrArg DivisionFreeTermIndex.s indexEq
  subst rightS
  have jEq : leftJ = rightJ := by
    apply Fin.ext
    exact congrArg DivisionFreeTermIndex.j indexEq
  subst rightJ
  have fullPartsEq : leftParts = rightParts := by
    apply Subtype.ext
    apply Finsupp.ext
    intro partIndex
    by_cases partMem : partIndex ∈ Finset.range leftJ.val
    · let boundedPart : Fin leftJ.val :=
        ⟨partIndex, Finset.mem_range.mp partMem⟩
      have packagedEq := congrArg
        (fun (index : DivisionFreeTermIndex t tPositive) ↦
          (⟨index.j, index.parts⟩ : Σ degree : Nat, Fin degree → Nat))
        indexEq
      have partsEq :
          (BoundedTermIndex.toDivisionFree tPositive
            ⟨⟨leftS, ⟨leftJ, leftParts⟩⟩, leftRetained⟩).parts =
          (BoundedTermIndex.toDivisionFree tPositive
            ⟨⟨leftS, ⟨leftJ, rightParts⟩⟩, rightRetained⟩).parts := by
        exact eq_of_heq (Sigma.mk.inj packagedEq).2
      exact congrFun partsEq boundedPart
    · have leftSupport :=
        (Finset.mem_finsuppAntidiag.mp leftParts.2).2
      have rightSupport :=
        (Finset.mem_finsuppAntidiag.mp rightParts.2).2
      have leftNotSupport : partIndex ∉ leftParts.1.support :=
        fun member ↦ partMem (leftSupport member)
      have rightNotSupport : partIndex ∉ rightParts.1.support :=
        fun member ↦ partMem (rightSupport member)
      have leftZero : leftParts.1 partIndex = 0 := by
        simpa [Finsupp.mem_support_iff] using leftNotSupport
      have rightZero : rightParts.1 partIndex = 0 := by
        simpa [Finsupp.mem_support_iff] using rightNotSupport
      rw [leftZero, rightZero]
  cases fullPartsEq
  rfl

/-- The literal finite family `P̊_{s,j,t}`, bundled in the recurrence's
abstract index type. -/
def parentDivisionFreeTerms (d t : Nat) (tPositive : 0 < t) :
    Finset (DivisionFreeTermIndex t tPositive) :=
  by
    classical
    exact (Finset.univ : Finset (BoundedTermIndex d t)).map
      ⟨BoundedTermIndex.toDivisionFree tPositive,
        BoundedTermIndex.toDivisionFree_injective tPositive⟩

theorem parentDivisionFreeTerms_j_le
    (d t : Nat) (tPositive : 0 < t)
    (index : DivisionFreeTermIndex t tPositive)
    (indexMem : index ∈ parentDivisionFreeTerms d t tPositive) :
    index.j ≤ d := by
  classical
  rw [parentDivisionFreeTerms, Finset.mem_map] at indexMem
  obtain ⟨bounded, _, rfl⟩ := indexMem
  change bounded.1.2.1.val ≤ d
  omega

/-- The coefficient attached to an actual retained parent tuple. -/
def parentDivisionFreeScalar
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) {t : Nat} {tPositive : 0 < t}
    (index : DivisionFreeTermIndex t tPositive) : K :=
  (shiftedParentCoefficient x₀ index.s index.j parent).eval z

/-- The quotient coefficient attached to an actual retained parent tuple. -/
def parentDivisionFreeCoefficient
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K) (d : Nat)
    {t : Nat} {tPositive : 0 < t}
    (index : DivisionFreeTermIndex t tPositive) : RegularQuotient factor :=
  regularClearedCoefficient parent factor x₀ index.s d index.j

/-- The paper's coefficients `δ_t`, now defined from the actual shifted
parent coefficients and retained partition tuples. -/
def parentDivisionFreeCoefficients
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K) (d t : Nat) :
    RegularQuotient factor :=
  divisionFreeCoefficients
    (regularDerivativeElement parent factor x₀ d)
    (parentDivisionFreeTerms d)
    (fun _t _tPositive index ↦
      parentDivisionFreeCoefficient parent factor x₀ d index) t

/-- The denominator-free estimate for the canonical coefficients obtained
from the actual parent polynomial. -/
theorem parentDivisionFreeCoefficients_weight_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K)
    (ell DH DR d b tau : Nat)
    (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d) (ellDLeDR : ell * d ≤ DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b) (t : Nat) :
    regularWeight factor factorNeZero tau
        (parentDivisionFreeCoefficients parent factor x₀ d t) ≤
      (divisionFreeCeiling tau (sourceMu DR ell d b) t : Nat) := by
  apply division_free_defined_estimate factor factorNeZero ell DH tau
    (sourceMu DR ell d b) factorCoefficientBound generatorWeightEq
    (regularDerivativeElement parent factor x₀ d)
    (regularDerivativeElement_weight_le parent factor x₀ ell DH DR d b tau
      factorNeZero factorCoefficientBound generatorWeightEq globalBound tauEq
      wLeB dPositive)
    (parentDivisionFreeTerms d)
    (fun _order _orderPositive index ↦
      parentDivisionFreeCoefficient parent factor x₀ d index)
  intro order orderPositive index indexMem
  exact regularClearedCoefficient_weight_add_le parent factor x₀ ell DH DR d
    b tau index.s index.j factorNeZero factorCoefficientBound
    generatorWeightEq globalBound tauEq ellLeDR dPositive ellDLeDR
    (parentDivisionFreeTerms_j_le d order orderPositive index indexMem) wLeB

/-- Scalar value of one bounded raw parent tuple at a candidate series. -/
def boundedRawTermValue
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) {d t : Nat}
    (index : BoundedRawTermIndex d t) : K :=
  (shiftedParentCoefficient x₀ index.1.val index.2.1.val parent).eval z *
    ∏ partIndex : Fin index.2.1.val,
      PowerSeries.coeff (index.2.2.1 partIndex.val) series

/-- The complete coefficient-`t` tuple sum, before removing the singleton
linear occurrence. -/
def fullParentTermSum
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat) : K :=
  ∑ s ∈ Finset.range (t + 1),
    ∑ j ∈ Finset.range (d + 1),
      ∑ parts ∈ (Finset.range j).finsuppAntidiag (t - s),
        (shiftedParentCoefficient x₀ s j parent).eval z *
          ∏ partIndex ∈ Finset.range j,
            PowerSeries.coeff (parts partIndex) series

theorem specializedShiftedParent_eq_sum_range
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (d : Nat) (parentDegreeLe : parent.natDegree ≤ d) :
    specializedShiftedParent parent x₀ z =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.monomial j
          (specializedShiftedCoefficientHom x₀ z (parent.coeff j)) := by
  unfold specializedShiftedParent
  conv_lhs => rw [parent.as_sum_range' (d + 1) (by omega)]
  simp only [Polynomial.map_sum, Polynomial.map_monomial]

/-- The complete bounded tuple sum is exactly the coefficient of order
`t` in the specialized parent evaluated at the candidate series. -/
theorem fullParentTermSum_eq_coeff_eval
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat)
    (parentDegreeLe : parent.natDegree ≤ d) :
    fullParentTermSum parent x₀ z series d t =
      PowerSeries.coeff t
        ((specializedShiftedParent parent x₀ z).eval series) := by
  classical
  have coefficientProduct (j : Nat) :
      PowerSeries.coeff t
          (specializedShiftedCoefficientHom x₀ z (parent.coeff j) *
            series ^ j) =
        ∑ s ∈ Finset.range (t + 1),
          ∑ parts ∈ (Finset.range j).finsuppAntidiag (t - s),
            (shiftedParentCoefficient x₀ s j parent).eval z *
              ∏ partIndex ∈ Finset.range j,
                PowerSeries.coeff (parts partIndex) series := by
    rw [PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun s u ↦
        PowerSeries.coeff s
            (specializedShiftedCoefficientHom x₀ z (parent.coeff j)) *
          PowerSeries.coeff u (series ^ j)) t]
    apply Finset.sum_congr rfl
    intro s sMem
    rw [coeff_specializedShiftedCoefficientHom,
      PowerSeries.coeff_pow, Finset.mul_sum]
    rfl
  rw [fullParentTermSum, Finset.sum_comm]
  simp_rw [← coefficientProduct]
  rw [specializedShiftedParent_eq_sum_range parent x₀ z d parentDegreeLe,
    Polynomial.eval_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_monomial]

/-- The retained nonlinear tuple sum. -/
def retainedParentTermSum
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat) : K :=
  by
    classical
    exact ∑ index : BoundedTermIndex d t,
      boundedRawTermValue parent x₀ z series index.1

def excludedParentTermSum
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat) : K :=
  by
    classical
    exact ∑ index : ExcludedTermIndex d t,
      boundedRawTermValue parent x₀ z series index.1

def indexedFullParentTermSum
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat) : K :=
  ∑ index : BoundedRawTermIndex d t,
    boundedRawTermValue parent x₀ z series index

theorem indexedFullParentTermSum_eq_retained_add_excluded
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat) :
    indexedFullParentTermSum parent x₀ z series d t =
      retainedParentTermSum parent x₀ z series d t +
        excludedParentTermSum parent x₀ z series d t := by
  classical
  let raw : Finset (BoundedRawTermIndex d t) := Finset.univ
  let value : BoundedRawTermIndex d t → K := fun index ↦
    boundedRawTermValue parent x₀ z series index
  have retainedAsFilter :
      retainedParentTermSum parent x₀ z series d t =
        ∑ index ∈ raw.filter BoundedRawTermIndex.Retained, value index := by
    unfold retainedParentTermSum
    symm
    exact Finset.sum_subtype _ (fun index ↦ by simp [raw]) value
  have excludedAsFilter :
      excludedParentTermSum parent x₀ z series d t =
        ∑ index ∈ raw.filter
            (fun candidate ↦ ¬ candidate.Retained), value index := by
    unfold excludedParentTermSum
    symm
    exact Finset.sum_subtype _ (fun index ↦ by simp [raw]) value
  rw [retainedAsFilter, excludedAsFilter]
  unfold indexedFullParentTermSum
  change (∑ index ∈ raw, value index) = _
  exact (Finset.sum_filter_add_sum_filter_not raw
    BoundedRawTermIndex.Retained value).symm

theorem excludedParentTermSum_eq_ite_sum
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat) :
    excludedParentTermSum parent x₀ z series d t =
      ∑ index : BoundedRawTermIndex d t,
        if ¬ index.Retained then
          boundedRawTermValue parent x₀ z series index else 0 := by
  classical
  let raw : Finset (BoundedRawTermIndex d t) := Finset.univ
  let value : BoundedRawTermIndex d t → K := fun index ↦
    boundedRawTermValue parent x₀ z series index
  calc
    excludedParentTermSum parent x₀ z series d t =
        ∑ index ∈ raw.filter (fun candidate ↦ ¬ candidate.Retained),
          value index := by
      unfold excludedParentTermSum
      symm
      exact Finset.sum_subtype _ (fun index ↦ by simp [raw]) value
    _ = ∑ index ∈ raw,
          if ¬ index.Retained then value index else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ index : BoundedRawTermIndex d t,
          if ¬ index.Retained then value index else 0 := by
      simp [raw]

theorem excludedParentTermSum_eq_linear_sum
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat)
    (_tPositive : 0 < t) :
    excludedParentTermSum parent x₀ z series d t =
      ∑ j ∈ Finset.range (d + 1),
        (shiftedParentCoefficient x₀ 0 j parent).eval z *
          ∑ parts ∈ linearFinsuppParts j t,
            ∏ partIndex ∈ Finset.range j,
              PowerSeries.coeff (parts partIndex) series := by
  classical
  rw [excludedParentTermSum_eq_ite_sum]
  unfold boundedRawTermValue
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero]
  have tailZero :
      (∑ i : Fin t,
        ∑ j : Fin (d + 1),
          ∑ parts : ↥((Finset.range j.val).finsuppAntidiag
              (t - i.succ.val)),
            if ¬ BoundedRawTermIndex.Retained
                (⟨i.succ, ⟨j, parts⟩⟩ : BoundedRawTermIndex d t) then
              (shiftedParentCoefficient x₀ i.succ.val j.val parent).eval z *
                ∏ partIndex : Fin j.val,
                  PowerSeries.coeff (parts.1 partIndex.val) series
            else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i iMem
    apply Finset.sum_eq_zero
    intro j jMem
    apply Finset.sum_eq_zero
    intro parts partsMem
    simp [BoundedRawTermIndex.Retained]
  rw [tailZero, add_zero]
  simp only [BoundedRawTermIndex.Retained, Fin.val_zero, true_and,
    not_not]
  let outer : Nat → K := fun j ↦
    ∑ parts : ↥((Finset.range j).finsuppAntidiag t),
      if finsuppPositivePartCount (Finset.range j) parts.1 = 1 then
        (shiftedParentCoefficient x₀ 0 j parent).eval z *
          ∏ partIndex : Fin j,
            PowerSeries.coeff (parts.1 partIndex.val) series
      else 0
  change (∑ j : Fin (d + 1), outer j.val) = _
  rw [Fin.sum_univ_eq_sum_range outer (d + 1)]
  apply Finset.sum_congr rfl
  intro j jMem
  dsimp only [outer]
  let coefficient := (shiftedParentCoefficient x₀ 0 j parent).eval z
  let antidiagonal := (Finset.range j).finsuppAntidiag t
  let predicate := fun parts : Nat →₀ Nat ↦
    finsuppPositivePartCount (Finset.range j) parts = 1
  change (∑ parts : ↥antidiagonal,
      if predicate parts.1 then
        coefficient * ∏ partIndex : Fin j,
          PowerSeries.coeff (parts.1 partIndex.val) series
      else 0) =
    coefficient * ∑ parts ∈ antidiagonal.filter predicate,
      ∏ partIndex ∈ Finset.range j,
        PowerSeries.coeff (parts partIndex) series
  symm
  rw [Finset.mul_sum]
  calc
    ∑ parts ∈ antidiagonal.filter predicate,
          coefficient *
            ∏ partIndex ∈ Finset.range j,
              PowerSeries.coeff (parts partIndex) series =
        ∑ parts ∈ antidiagonal,
          if predicate parts then
            coefficient *
              ∏ partIndex ∈ Finset.range j,
                PowerSeries.coeff (parts partIndex) series
          else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ parts : ↥antidiagonal,
          if predicate parts.1 then
            coefficient *
              ∏ partIndex ∈ Finset.range j,
                PowerSeries.coeff (parts.1 partIndex) series
          else 0 := by
      exact Finset.sum_subtype _ (fun parts ↦ by simp) _
    _ = ∑ parts : ↥antidiagonal,
          if predicate parts.1 then
            coefficient *
              ∏ partIndex : Fin j,
                PowerSeries.coeff (parts.1 partIndex.val) series
          else 0 := by
      apply Finset.sum_congr rfl
      intro parts partsMem
      split
      · apply congrArg (fun value : K ↦ coefficient * value)
        exact (Fin.prod_univ_eq_prod_range
          (fun partIndex ↦ PowerSeries.coeff (parts.1 partIndex) series) j).symm
      · rfl

/-- The specialized derivative scalar, written in the same bounded
coefficient coordinates as the recurrence. -/
def specializedDerivativeValue
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d : Nat) : K :=
  ∑ j ∈ Finset.range (d + 1),
    (shiftedParentCoefficient x₀ 0 j parent).eval z * (j : K) *
      PowerSeries.constantCoeff series ^ (j - 1)

/-- Evaluation of the literal cleared derivative representative. -/
theorem eval₂_sourceClearedRepresentative_derivative
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z y : K) (W : Polynomial K) (d : Nat) :
    (sourceClearedRepresentative parent x₀ 0 d 1
        (fun j ↦ (j : K)) W).eval₂ (Polynomial.evalRingHom z)
          (W.eval z * y) =
      W.eval z ^ (d - 1) *
        ∑ j ∈ Finset.range (d + 1),
          (shiftedParentCoefficient x₀ 0 j parent).eval z * (j : K) *
            y ^ (j - 1) := by
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
  simp only [map_mul, map_pow, coe_evalRingHom, Polynomial.eval_C]
  rw [mul_pow]
  have exponentEq : d - j + (j - 1) = d - 1 := by omega
  let w := W.eval z
  let coefficient := (shiftedParentCoefficient x₀ 0 j parent).eval z
  change (j : K) * coefficient * w ^ (d - j) *
      (w ^ (j - 1) * y ^ (j - 1)) =
    w ^ (d - 1) * (coefficient * (j : K) * y ^ (j - 1))
  have powerEq : w ^ (d - j) * w ^ (j - 1) = w ^ (d - 1) := by
    rw [← pow_add, exponentEq]
  calc
    (j : K) * coefficient * w ^ (d - j) *
        (w ^ (j - 1) * y ^ (j - 1)) =
      (w ^ (d - j) * w ^ (j - 1)) *
        (coefficient * (j : K) * y ^ (j - 1)) := by ring
    _ = w ^ (d - 1) *
        (coefficient * (j : K) * y ^ (j - 1)) := by rw [powerEq]

theorem excludedParentTermSum_eq_derivative_mul_coeff
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat)
    (tPositive : 0 < t) :
    excludedParentTermSum parent x₀ z series d t =
      specializedDerivativeValue parent x₀ z series d *
        PowerSeries.coeff t series := by
  rw [excludedParentTermSum_eq_linear_sum parent x₀ z series d t tPositive]
  unfold specializedDerivativeValue
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j jMem
  rw [sum_linearFinsuppParts_product series j t tPositive]
  ring

theorem indexedFullParentTermSum_eq_fullParentTermSum
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat) :
    indexedFullParentTermSum parent x₀ z series d t =
      fullParentTermSum parent x₀ z series d t := by
  classical
  unfold indexedFullParentTermSum fullParentTermSum boundedRawTermValue
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  let outer : Nat → K := fun s ↦
    ∑ j : Fin (d + 1),
      ∑ parts : ↥((Finset.range j.val).finsuppAntidiag (t - s)),
        (shiftedParentCoefficient x₀ s j.val parent).eval z *
          ∏ partIndex : Fin j.val,
            PowerSeries.coeff (parts.1 partIndex.val) series
  change (∑ s : Fin (t + 1), outer s.val) = _
  rw [Fin.sum_univ_eq_sum_range outer (t + 1)]
  apply Finset.sum_congr rfl
  intro s sMem
  dsimp only [outer]
  let inner : Nat → K := fun j ↦
    ∑ parts : ↥((Finset.range j).finsuppAntidiag (t - s)),
      (shiftedParentCoefficient x₀ s j parent).eval z *
        ∏ partIndex : Fin j,
          PowerSeries.coeff (parts.1 partIndex.val) series
  change (∑ j : Fin (d + 1), inner j.val) = _
  rw [Fin.sum_univ_eq_sum_range inner (d + 1)]
  apply Finset.sum_congr rfl
  intro j jMem
  dsimp only [inner]
  symm
  calc
    ∑ parts ∈ (Finset.range j).finsuppAntidiag (t - s),
          (shiftedParentCoefficient x₀ s j parent).eval z *
            ∏ partIndex ∈ Finset.range j,
              PowerSeries.coeff (parts partIndex) series =
        ∑ parts : ↥((Finset.range j).finsuppAntidiag (t - s)),
          (shiftedParentCoefficient x₀ s j parent).eval z *
            ∏ partIndex ∈ Finset.range j,
              PowerSeries.coeff (parts.1 partIndex) series := by
      exact Finset.sum_subtype _ (fun parts ↦ by simp) _
    _ = ∑ parts : ↥((Finset.range j).finsuppAntidiag (t - s)),
          (shiftedParentCoefficient x₀ s j parent).eval z *
            ∏ partIndex : Fin j,
              PowerSeries.coeff (parts.1 partIndex.val) series := by
      apply Finset.sum_congr rfl
      intro parts _
      apply congrArg
        (fun value : K ↦
          (shiftedParentCoefficient x₀ s j parent).eval z * value)
      exact (Fin.prod_univ_eq_prod_range
        (fun partIndex ↦ PowerSeries.coeff (parts.1 partIndex) series) j).symm

/-- The exact retained-tuple coefficient equation obtained from the actual
root identity `R(X,p(X),z)=0`. -/
theorem specializedParent_coefficient_recurrence
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat)
    (parentDegreeLe : parent.natDegree ≤ d)
    (tPositive : 0 < t)
    (root : (specializedShiftedParent parent x₀ z).IsRoot series) :
    specializedDerivativeValue parent x₀ z series d *
        PowerSeries.coeff t series =
      -retainedParentTermSum parent x₀ z series d t := by
  have coefficientZero : PowerSeries.coeff t
      ((specializedShiftedParent parent x₀ z).eval series) = 0 := by
    rw [root.eq_zero, map_zero]
  have fullZero : fullParentTermSum parent x₀ z series d t = 0 := by
    rw [fullParentTermSum_eq_coeff_eval parent x₀ z series d t
      parentDegreeLe, coefficientZero]
  have indexedZero : indexedFullParentTermSum parent x₀ z series d t = 0 := by
    rw [indexedFullParentTermSum_eq_fullParentTermSum, fullZero]
  rw [indexedFullParentTermSum_eq_retained_add_excluded,
    excludedParentTermSum_eq_derivative_mul_coeff parent x₀ z series d t
      tPositive] at indexedZero
  exact eq_neg_of_add_eq_zero_right indexedZero

theorem retainedParentTermSum_eq_parentDivisionFreeTerms_sum
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ z : K) (series : PowerSeries K) (d t : Nat)
    (tPositive : 0 < t) :
    retainedParentTermSum parent x₀ z series d t =
      ∑ index ∈ parentDivisionFreeTerms d t tPositive,
        parentDivisionFreeScalar parent x₀ z index *
          ∏ partIndex,
            PowerSeries.coeff (index.parts partIndex) series := by
  classical
  rw [retainedParentTermSum, parentDivisionFreeTerms, Finset.sum_map]
  rfl

/-! ## Direct specialization on the integral quotient -/

/-- The scaled branch value `t_z=W(z)p_z(x₀)`. -/
def branchRootValue
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (x₀ z : K) (candidate : Polynomial K) : K :=
  factor.leadingCoeff.eval z * candidate.eval x₀

theorem branchRootPair
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0) :
    (monicization factor).eval₂ (Polynomial.evalRingHom z)
        (branchRootValue factor x₀ z candidate) = 0 := by
  exact monicization_root_of_localFactor_root factor factorPositive z
    (candidate.eval x₀) localRoot

/-- The paper's map `π_z : O → K`, constructed directly on `O`. -/
def branchSpecialization
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0) : RegularQuotient factor →+* K :=
  regularSpecialization factor z (branchRootValue factor x₀ z candidate)
    (branchRootPair factor factorPositive x₀ z candidate localRoot)

@[simp] theorem branchSpecialization_root
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (AdjoinRoot.root (monicization factor)) =
      branchRootValue factor x₀ z candidate := by
  exact regularSpecialization_root factor z
    (branchRootValue factor x₀ z candidate)
      (branchRootPair factor factorPositive x₀ z candidate localRoot)

@[simp] theorem branchSpecialization_of
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0) (coefficient : Polynomial K) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (AdjoinRoot.of (monicization factor) coefficient) =
      coefficient.eval z := by
  exact regularSpecialization_of factor z
    (branchRootValue factor x₀ z candidate)
      (branchRootPair factor factorPositive x₀ z candidate localRoot)
        coefficient

@[simp] theorem branchSpecialization_regularLeadingCoefficient
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (regularLeadingCoefficient factor) =
      factor.leadingCoeff.eval z := by
  simp [regularLeadingCoefficient]

/-- The cleared shifted coefficient specializes to the literal scalar
`c_{s,j}(z) W(z)^(d-j)`. -/
theorem branchSpecialization_regularClearedCoefficient
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0) (s d j : Nat) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (regularClearedCoefficient parent factor x₀ s d j) =
      (shiftedParentCoefficient x₀ s j parent).eval z *
        factor.leadingCoeff.eval z ^ (d - j) := by
  simp [regularClearedCoefficient]

/-- The intrinsic regular derivative specializes to
`W(z)^(d-1) ζ_z`. -/
theorem branchSpecialization_regularDerivativeElement
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0) (d : Nat) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (regularDerivativeElement parent factor x₀ d) =
      factor.leadingCoeff.eval z ^ (d - 1) *
        specializedDerivativeValue parent x₀ z
          (shiftedCandidateSeries x₀ candidate) d := by
  unfold branchSpecialization regularSpecialization regularDerivativeElement
  rw [AdjoinRoot.lift_mk]
  unfold branchRootValue
  rw [eval₂_sourceClearedRepresentative_derivative parent x₀ z
    (candidate.eval x₀) factor.leadingCoeff d]
  unfold specializedDerivativeValue
  rw [constantCoeff_shiftedCandidateSeries]

/-- At order zero the cleared coefficient specializes to
`W(z) a_{z,0}`. -/
theorem branchSpecialization_divisionFreeCoefficient_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (eta : RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (divisionFreeCoefficients eta terms rho 0) =
      factor.leadingCoeff.eval z *
        PowerSeries.coeff 0 (shiftedCandidateSeries x₀ candidate) := by
  rw [divisionFreeCoefficients_zero, branchSpecialization_root,
    branchRootValue, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_shiftedCandidateSeries]

/-! ## The recurrence commuting square -/

/-- Image of one denominator-free recurrence summand under an arbitrary
finite branch specialization. -/
theorem divisionFreeTerm_specialization
    {K : Type*} [Field K] {factor : BivariatePolynomial K}
    {t : Nat} {tPositive : 0 < t}
    (specialization : RegularQuotient factor →+* K)
    (d : Nat) (index : DivisionFreeTermIndex t tPositive)
    (jLeD : index.j ≤ d)
    (rho eta : RegularQuotient factor)
    (delta : Nat → RegularQuotient factor) (alpha : Nat → K)
    (coefficient : K)
    (rhoImage : specialization rho =
      coefficient * specialization (regularLeadingCoefficient factor) ^
        (d - index.j))
    (earlierImage : ∀ partIndex,
      specialization (delta (index.parts partIndex)) =
        specialization (regularLeadingCoefficient factor) *
          specialization eta ^ henselExponent (index.parts partIndex) *
            alpha (index.parts partIndex)) :
    specialization (divisionFreeTerm index rho eta delta) =
      specialization (regularLeadingCoefficient factor) ^ d *
        specialization eta ^ (henselExponent t - 1) *
          (coefficient * ∏ partIndex, alpha (index.parts partIndex)) := by
  let leadingImage := specialization (regularLeadingCoefficient factor)
  let etaImage := specialization eta
  have productImage :
      ∏ partIndex : Fin index.j,
          specialization (delta (index.parts partIndex)) =
        leadingImage ^ index.j *
          etaImage ^ tupleHenselExponent index.parts *
            ∏ partIndex, alpha (index.parts partIndex) := by
    calc
      ∏ partIndex : Fin index.j,
          specialization (delta (index.parts partIndex)) =
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
            ∏ partIndex : Fin index.j,
              alpha (index.parts partIndex) := by
        simp_rw [Finset.prod_mul_distrib]
      _ = leadingImage ^ index.j *
            etaImage ^ tupleHenselExponent index.parts *
              ∏ partIndex, alpha (index.parts partIndex) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum]
        rfl
  unfold divisionFreeTerm
  rw [map_mul, map_mul, map_pow, map_prod, rhoImage, productImage]
  have leadingSplit : d - index.j + index.j = d :=
    Nat.sub_add_cancel jLeD
  have etaSplit := index.nu_add_tupleHenselExponent
  change coefficient * leadingImage ^ (d - index.j) *
        etaImage ^ index.nu *
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
          (coefficient * ∏ partIndex, alpha (index.parts partIndex)) := by
      ring

/-- The literal recurrence commutes with every specialization satisfying
the specialized coefficient recurrence. This theorem contains the order-zero
case separately and uses strong induction at positive order. -/
theorem divisionFreeCoefficients_specialization
    {K : Type*} [Field K] {factor : BivariatePolynomial K}
    (specialization : RegularQuotient factor →+* K)
    (d : Nat) (dPositive : 1 ≤ d)
    (eta : RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (DivisionFreeTermIndex t tPositive))
    (rho : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → RegularQuotient factor)
    (coefficient : ∀ (t : Nat) (tPositive : 0 < t),
      DivisionFreeTermIndex t tPositive → K)
    (zeta : K) (alpha : Nat → K)
    (baseImage : specialization
        (AdjoinRoot.root (monicization factor)) =
      specialization (regularLeadingCoefficient factor) * alpha 0)
    (etaImage : specialization eta =
      specialization (regularLeadingCoefficient factor) ^ (d - 1) * zeta)
    (jLeD : ∀ (t : Nat) (tPositive : 0 < t)
      (index : DivisionFreeTermIndex t tPositive),
      index ∈ terms t tPositive → index.j ≤ d)
    (rhoImage : ∀ (t : Nat) (tPositive : 0 < t)
      (index : DivisionFreeTermIndex t tPositive),
      index ∈ terms t tPositive →
        specialization (rho t tPositive index) =
          coefficient t tPositive index *
            specialization (regularLeadingCoefficient factor) ^
              (d - index.j))
    (coefficientRecurrence : ∀ (t : Nat) (tPositive : 0 < t),
      zeta * alpha t =
        -∑ index ∈ terms t tPositive,
          coefficient t tPositive index *
            ∏ partIndex, alpha (index.parts partIndex)) :
    ∀ t,
      specialization (divisionFreeCoefficients eta terms rho t) =
        specialization (regularLeadingCoefficient factor) *
          specialization eta ^ henselExponent t * alpha t := by
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
                specialization
                  (divisionFreeTerm index (rho t tPositive index) eta
                    (divisionFreeCoefficients eta terms rho)) =
              specialization (regularLeadingCoefficient factor) ^ d *
                specialization eta ^ (henselExponent t - 1) *
                  ∑ index ∈ terms t tPositive,
                    coefficient t tPositive index *
                      ∏ partIndex, alpha (index.parts partIndex) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro index indexMem
          exact divisionFreeTerm_specialization specialization d index
            (jLeD t tPositive index indexMem) (rho t tPositive index) eta
            (divisionFreeCoefficients eta terms rho) alpha
            (coefficient t tPositive index)
            (rhoImage t tPositive index indexMem)
            (fun partIndex ↦ induction (index.parts partIndex)
              (index.part_lt partIndex))
        rw [sumImage]
        let leadingImage := specialization (regularLeadingCoefficient factor)
        let mappedEta := specialization eta
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
        have etaImage' : mappedEta =
            leadingImage ^ (d - 1) * zeta := etaImage
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

/-- Equation (73) for the coefficients intrinsically defined from the
actual parent polynomial.  The map is the regular-quotient specialization;
no evaluation map from the function field is used. -/
theorem branchSpecialization_parentDivisionFreeCoefficients
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    (x₀ z : K) (candidate : Polynomial K)
    (localRoot : factor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (d : Nat) (dPositive : 1 ≤ d)
    (parentDegreeLe : parent.natDegree ≤ d)
    (candidateRoot : challengeCandidatePolynomial z candidate parent = 0)
    (t : Nat) :
    branchSpecialization factor factorPositive x₀ z candidate localRoot
        (parentDivisionFreeCoefficients parent factor x₀ d t) =
      factor.leadingCoeff.eval z *
        branchSpecialization factor factorPositive x₀ z candidate localRoot
            (regularDerivativeElement parent factor x₀ d) ^
          henselExponent t *
        PowerSeries.coeff t (shiftedCandidateSeries x₀ candidate) := by
  let specialization :=
    branchSpecialization factor factorPositive x₀ z candidate localRoot
  let eta := regularDerivativeElement parent factor x₀ d
  let terms := parentDivisionFreeTerms d
  let rho := fun (order : Nat) (orderPositive : 0 < order)
      (index : DivisionFreeTermIndex order orderPositive) ↦
    parentDivisionFreeCoefficient parent factor x₀ d index
  let coefficient := fun (order : Nat) (orderPositive : 0 < order)
      (index : DivisionFreeTermIndex order orderPositive) ↦
    parentDivisionFreeScalar parent x₀ z index
  let series := shiftedCandidateSeries x₀ candidate
  let zeta := specializedDerivativeValue parent x₀ z series d
  have baseImage : specialization
        (AdjoinRoot.root (monicization factor)) =
      specialization (regularLeadingCoefficient factor) *
        PowerSeries.coeff 0 series := by
    dsimp only [specialization, series]
    rw [branchSpecialization_root,
      branchSpecialization_regularLeadingCoefficient, branchRootValue,
      PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_shiftedCandidateSeries]
  have etaImage : specialization eta =
      specialization (regularLeadingCoefficient factor) ^ (d - 1) * zeta := by
    dsimp only [specialization, eta, zeta, series]
    simpa only [branchSpecialization_regularLeadingCoefficient] using
      branchSpecialization_regularDerivativeElement parent factor
        factorPositive x₀ z candidate localRoot d
  have jLeD : ∀ (order : Nat) (orderPositive : 0 < order)
      (index : DivisionFreeTermIndex order orderPositive),
      index ∈ terms order orderPositive → index.j ≤ d := by
    intro order orderPositive index indexMem
    exact parentDivisionFreeTerms_j_le d order orderPositive index indexMem
  have rhoImage : ∀ (order : Nat) (orderPositive : 0 < order)
      (index : DivisionFreeTermIndex order orderPositive),
      index ∈ terms order orderPositive →
        specialization (rho order orderPositive index) =
          coefficient order orderPositive index *
            specialization (regularLeadingCoefficient factor) ^
              (d - index.j) := by
    intro order orderPositive index indexMem
    dsimp only [specialization, rho, coefficient,
      parentDivisionFreeCoefficient, parentDivisionFreeScalar]
    simpa only [branchSpecialization_regularLeadingCoefficient] using
      branchSpecialization_regularClearedCoefficient parent factor
        factorPositive x₀ z candidate localRoot index.s d index.j
  have coefficientRecurrence : ∀ (order : Nat) (orderPositive : 0 < order),
      zeta * PowerSeries.coeff order series =
        -∑ index ∈ terms order orderPositive,
          coefficient order orderPositive index *
            ∏ partIndex,
              PowerSeries.coeff (index.parts partIndex) series := by
    intro order orderPositive
    have recurrence := specializedParent_coefficient_recurrence parent x₀ z
      series d order parentDegreeLe orderPositive
        (shiftedCandidateSeries_isRoot parent x₀ z candidate candidateRoot)
    rw [retainedParentTermSum_eq_parentDivisionFreeTerms_sum parent x₀ z
      series d order orderPositive] at recurrence
    exact recurrence
  have specialized := divisionFreeCoefficients_specialization specialization
    d dPositive eta terms rho coefficient zeta
      (fun order ↦ PowerSeries.coeff order series) baseImage etaImage jLeD
      rhoImage coefficientRecurrence t
  simpa only [parentDivisionFreeCoefficients, specialization, eta, terms, rho,
    coefficient, zeta, series,
    branchSpecialization_regularLeadingCoefficient] using specialized

#print axioms specializedShiftedCoefficientHom_eq_comp
#print axioms coeff_specializedShiftedCoefficientHom
#print axioms shiftedCandidateSeries_isRoot
#print axioms branchRootPair
#print axioms branchSpecialization_regularClearedCoefficient
#print axioms branchSpecialization_divisionFreeCoefficient_zero
#print axioms divisionFreeTerm_specialization
#print axioms divisionFreeCoefficients_specialization
#print axioms fullParentTermSum_eq_coeff_eval
#print axioms specializedParent_coefficient_recurrence
#print axioms parentDivisionFreeCoefficients_weight_le
#print axioms branchSpecialization_regularDerivativeElement
#print axioms branchSpecialization_parentDivisionFreeCoefficients

end

end WeightedHensel

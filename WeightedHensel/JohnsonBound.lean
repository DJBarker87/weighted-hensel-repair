/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import Mathlib

/-!
# A direct finite Johnson list bound

This is the application-independent second-moment argument used to check the
two concrete multiplicity-three Guruswami--Sudan list caps.  For agreement
sets `A_c`, coordinate multiplicities count incidences.  Cauchy--Schwarz and
the pairwise overlap bound give the usual Johnson inequality.
-/

set_option autoImplicit false

namespace WeightedHensel

open scoped BigOperators

noncomputable section

variable {Coordinate Candidate : Type*}
  [Fintype Coordinate] [DecidableEq Coordinate]
  [Fintype Candidate] [DecidableEq Candidate]

/-- Real-valued incidence bit for one candidate and coordinate. -/
def johnsonIncidence (agreement : Candidate → Finset Coordinate)
    (candidate : Candidate) (coordinate : Coordinate) : Real :=
  if coordinate ∈ agreement candidate then 1 else 0

/-- Number of candidates agreeing at one coordinate, represented in `Real`. -/
def johnsonMultiplicity (agreement : Candidate → Finset Coordinate)
    (coordinate : Coordinate) : Real :=
  ∑ candidate : Candidate, johnsonIncidence agreement candidate coordinate

@[simp] theorem sum_johnsonIncidence
    (agreement : Candidate → Finset Coordinate) (candidate : Candidate) :
    (∑ coordinate : Coordinate,
      johnsonIncidence agreement candidate coordinate) =
      (agreement candidate).card := by
  classical
  simp [johnsonIncidence]

theorem sum_johnsonMultiplicity_eq_sum_card
    (agreement : Candidate → Finset Coordinate) :
    (∑ coordinate : Coordinate, johnsonMultiplicity agreement coordinate) =
      ∑ candidate : Candidate, ((agreement candidate).card : Real) := by
  classical
  simp only [johnsonMultiplicity]
  rw [Finset.sum_comm]
  simp

@[simp] theorem sum_johnsonIncidence_mul
    (agreement : Candidate → Finset Coordinate)
    (left right : Candidate) :
    (∑ coordinate : Coordinate,
      johnsonIncidence agreement left coordinate *
        johnsonIncidence agreement right coordinate) =
      (((agreement left) ∩ (agreement right)).card : Real) := by
  classical
  simp [johnsonIncidence, Finset.inter_comm]

/-- Expanding the square counts ordered pairs on agreement intersections. -/
theorem sum_johnsonMultiplicity_sq_eq_pair_intersections
    (agreement : Candidate → Finset Coordinate) :
    (∑ coordinate : Coordinate,
      johnsonMultiplicity agreement coordinate ^ 2) =
      ∑ left : Candidate, ∑ right : Candidate,
        (((agreement left) ∩ (agreement right)).card : Real) := by
  classical
  calc
    (∑ coordinate : Coordinate,
        johnsonMultiplicity agreement coordinate ^ 2) =
        ∑ coordinate : Coordinate,
          ∑ left : Candidate, ∑ right : Candidate,
            johnsonIncidence agreement left coordinate *
              johnsonIncidence agreement right coordinate := by
      congr with coordinate
      simp [johnsonMultiplicity, pow_two, Finset.sum_mul, Finset.mul_sum,
        mul_comm]
    _ = ∑ left : Candidate, ∑ coordinate : Coordinate,
          ∑ right : Candidate,
            johnsonIncidence agreement left coordinate *
              johnsonIncidence agreement right coordinate := by
      rw [Finset.sum_comm]
    _ = ∑ left : Candidate, ∑ right : Candidate,
          ∑ coordinate : Coordinate,
            johnsonIncidence agreement left coordinate *
              johnsonIncidence agreement right coordinate := by
      congr with left
      rw [Finset.sum_comm]
    _ = ∑ left : Candidate, ∑ right : Candidate,
        (((agreement left) ∩ (agreement right)).card : Real) := by
      congr with left
      congr with right
      exact sum_johnsonIncidence_mul agreement left right

/-- The second moment is bounded by the diagonal and ordered off-diagonal
pairs. -/
theorem sum_johnsonMultiplicity_sq_le
    (agreement : Candidate → Finset Coordinate) (overlapCap : Nat)
    (overlap : ∀ left right : Candidate, left ≠ right →
      ((agreement left) ∩ (agreement right)).card ≤ overlapCap) :
    (∑ coordinate : Coordinate,
      johnsonMultiplicity agreement coordinate ^ 2) ≤
      (∑ coordinate : Coordinate,
        johnsonMultiplicity agreement coordinate) +
        overlapCap * Fintype.card Candidate *
          (Fintype.card Candidate - 1) := by
  classical
  rw [sum_johnsonMultiplicity_sq_eq_pair_intersections,
    sum_johnsonMultiplicity_eq_sum_card]
  have innerBound : ∀ candidate : Candidate,
      (∑ other : Candidate,
        (((agreement candidate) ∩ (agreement other)).card : Real)) ≤
        (agreement candidate).card +
          overlapCap * (Fintype.card Candidate - 1) := by
    intro candidate
    calc
      (∑ other : Candidate,
          (((agreement candidate) ∩ (agreement other)).card : Real)) =
          ((agreement candidate).card : Real) +
            ∑ other ∈ Finset.univ.erase candidate,
              (((agreement candidate) ∩ (agreement other)).card : Real) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ candidate)]
        simp
      _ ≤ ((agreement candidate).card : Real) +
          ∑ _other ∈ Finset.univ.erase candidate,
            (overlapCap : Real) := by
        gcongr with other otherMem
        exact_mod_cast overlap candidate other
          (Finset.ne_of_mem_erase otherMem).symm
      _ = ((agreement candidate).card : Real) +
          overlapCap * (Fintype.card Candidate - 1) := by
        letI : Nonempty Candidate := ⟨candidate⟩
        have cardPositive : 0 < Fintype.card Candidate := Fintype.card_pos
        simp [Finset.card_erase_of_mem, Nat.cast_sub cardPositive]
        ring
  calc
    (∑ candidate : Candidate, ∑ other : Candidate,
        (((agreement candidate) ∩ (agreement other)).card : Real)) ≤
        ∑ candidate : Candidate,
          ((agreement candidate).card +
            overlapCap * (Fintype.card Candidate - 1) : Real) := by
      gcongr with candidate
      exact innerBound candidate
    _ = (∑ candidate : Candidate,
          ((agreement candidate).card : Real)) +
          overlapCap * Fintype.card Candidate *
            (Fintype.card Candidate - 1) := by
      simp [Finset.sum_add_distrib]
      ring

/-- Generic second-moment Johnson inequalities. -/
theorem johnson_second_moment
    (agreement : Candidate → Finset Coordinate)
    (agreementFloor overlapCap : Nat)
    (large : ∀ candidate : Candidate,
      agreementFloor ≤ (agreement candidate).card)
    (overlap : ∀ left right : Candidate, left ≠ right →
      ((agreement left) ∩ (agreement right)).card ≤ overlapCap) :
    let listSize : Real := Fintype.card Candidate
    let wordSize : Real := Fintype.card Coordinate
    let incidenceCount : Real :=
      ∑ coordinate : Coordinate, johnsonMultiplicity agreement coordinate
    listSize * agreementFloor ≤ incidenceCount ∧
      incidenceCount ^ 2 ≤
        wordSize *
          (incidenceCount +
            overlapCap * listSize * (listSize - 1)) := by
  classical
  dsimp
  constructor
  · rw [sum_johnsonMultiplicity_eq_sum_card]
    calc
      (Fintype.card Candidate : Real) * agreementFloor =
          ∑ _candidate : Candidate, (agreementFloor : Real) := by simp
      _ ≤ ∑ candidate : Candidate,
          ((agreement candidate).card : Real) := by
        gcongr with candidate
        exact_mod_cast large candidate
  · calc
      (∑ coordinate : Coordinate,
          johnsonMultiplicity agreement coordinate) ^ 2 ≤
          (Fintype.card Coordinate : Real) *
            ∑ coordinate : Coordinate,
              johnsonMultiplicity agreement coordinate ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq
          (s := Finset.univ) (f := johnsonMultiplicity agreement)
      _ ≤ (Fintype.card Coordinate : Real) *
          ((∑ coordinate : Coordinate,
              johnsonMultiplicity agreement coordinate) +
            overlapCap * Fintype.card Candidate *
              (Fintype.card Candidate - 1)) := by
        gcongr
        exact sum_johnsonMultiplicity_sq_le agreement overlapCap overlap

/-- Arithmetic form of the Johnson argument. `boundPlusOne` is the first
forbidden list size. -/
theorem list_card_lt_of_johnson_parameters
    (agreement : Candidate → Finset Coordinate)
    (wordSize agreementFloor overlapCap boundPlusOne : Nat)
    (coordinateCard : Fintype.card Coordinate = wordSize)
    (large : ∀ candidate : Candidate,
      agreementFloor ≤ (agreement candidate).card)
    (overlap : ∀ left right : Candidate, left ≠ right →
      ((agreement left) ∩ (agreement right)).card ≤ overlapCap)
    (overlapLeFloor : overlapCap ≤ agreementFloor)
    (halfLe : (wordSize : Real) / 2 ≤
      (boundPlusOne : Real) * agreementFloor)
    (positive : 0 <
      (((agreementFloor : Real) ^ 2 - wordSize * overlapCap) *
          boundPlusOne -
        wordSize * ((agreementFloor : Real) - overlapCap))) :
    Fintype.card Candidate < boundPlusOne := by
  classical
  obtain ⟨lower, secondMoment⟩ := johnson_second_moment agreement
    agreementFloor overlapCap large overlap
  rw [coordinateCard] at secondMoment
  by_contra listNotSmall
  have listSizeNat : boundPlusOne ≤ Fintype.card Candidate :=
    Nat.le_of_not_gt listNotSmall
  have listSize : (boundPlusOne : Real) ≤ Fintype.card Candidate := by
    exact_mod_cast listSizeNat
  have floorNonnegative : (0 : Real) ≤ agreementFloor := by positivity
  have wordNonnegative : (0 : Real) ≤ wordSize := by positivity
  have overlapFloor : (overlapCap : Real) ≤ agreementFloor := by
    exact_mod_cast overlapLeFloor
  have halfList : (wordSize : Real) / 2 ≤
      (Fintype.card Candidate : Real) * agreementFloor :=
    halfLe.trans (mul_le_mul_of_nonneg_right listSize floorNonnegative)
  have productNonnegative : 0 ≤
      ((∑ coordinate : Coordinate,
          johnsonMultiplicity agreement coordinate) -
          (Fintype.card Candidate : Real) * agreementFloor) *
        ((∑ coordinate : Coordinate,
          johnsonMultiplicity agreement coordinate) +
          (Fintype.card Candidate : Real) * agreementFloor - wordSize) :=
    mul_nonneg (sub_nonneg.mpr lower) (by linarith)
  have monotone :
      ((Fintype.card Candidate : Real) * agreementFloor) ^ 2 -
          wordSize *
            ((Fintype.card Candidate : Real) * agreementFloor) ≤
        (∑ coordinate : Coordinate,
          johnsonMultiplicity agreement coordinate) ^ 2 -
          wordSize *
            (∑ coordinate : Coordinate,
              johnsonMultiplicity agreement coordinate) := by
    nlinarith [productNonnegative]
  have bound :
      ((Fintype.card Candidate : Real) * agreementFloor) ^ 2 -
          wordSize *
            ((Fintype.card Candidate : Real) * agreementFloor) ≤
        wordSize * overlapCap * (Fintype.card Candidate : Real) *
          ((Fintype.card Candidate : Real) - 1) := by
    calc
      _ ≤ (∑ coordinate : Coordinate,
          johnsonMultiplicity agreement coordinate) ^ 2 -
          wordSize *
            (∑ coordinate : Coordinate,
              johnsonMultiplicity agreement coordinate) := monotone
      _ ≤ wordSize * overlapCap * (Fintype.card Candidate : Real) *
          ((Fintype.card Candidate : Real) - 1) := by
        norm_num at secondMoment ⊢
        nlinarith [secondMoment]
  have coefficientPositive : 0 <
      (agreementFloor : Real) ^ 2 - wordSize * overlapCap := by
    by_contra coefficientNotPositive
    have coefficientNonpositive :
        (agreementFloor : Real) ^ 2 - wordSize * overlapCap ≤ 0 :=
      le_of_not_gt coefficientNotPositive
    nlinarith [positive,
      mul_nonneg wordNonnegative (sub_nonneg.mpr overlapFloor)]
  have factorPositive : 0 <
      ((agreementFloor : Real) ^ 2 - wordSize * overlapCap) *
          Fintype.card Candidate -
        wordSize * ((agreementFloor : Real) - overlapCap) := by
    nlinarith
  have listPositive : (0 : Real) < Fintype.card Candidate := by
    have boundPositive : 0 < boundPlusOne := by
      by_contra boundNotPositive
      have boundZero : boundPlusOne = 0 :=
        Nat.eq_zero_of_not_pos boundNotPositive
      subst boundPlusOne
      norm_num at positive
      nlinarith [mul_nonneg wordNonnegative
        (sub_nonneg.mpr overlapFloor)]
    exact lt_of_lt_of_le (by exact_mod_cast boundPositive) listSize
  have strict : 0 <
      (Fintype.card Candidate : Real) *
        ((((agreementFloor : Real) ^ 2 - wordSize * overlapCap) *
            Fintype.card Candidate) -
          wordSize * ((agreementFloor : Real) - overlapCap)) :=
    mul_pos listPositive factorPositive
  nlinarith [bound, strict]

#print axioms list_card_lt_of_johnson_parameters

end

end WeightedHensel

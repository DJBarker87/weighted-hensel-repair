/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FixedBranch

/-!
# Reed--Solomon and generalized Reed--Solomon curve values

This file records the application-independent code interface used by the two
concrete instances.  A generalized Reed--Solomon multiplier is normalized
before the fixed-branch theorem and restored after coefficientwise
interpolation.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-- Evaluation word of an ordinary Reed--Solomon message polynomial. -/
def reedSolomonWord
    {K Domain : Type*} [Field K]
    (points : Domain → K) (message : Polynomial K) : Domain → K :=
  fun coordinate ↦ message.eval (points coordinate)

/-- Evaluation word of a generalized Reed--Solomon message polynomial. -/
def generalizedReedSolomonWord
    {K Domain : Type*} [Field K]
    (points multiplier : Domain → K) (message : Polynomial K) : Domain → K :=
  fun coordinate ↦ multiplier coordinate * message.eval (points coordinate)

/-- Normalize a received challenge polynomial by the nonzero GRS multiplier
at its coordinate. -/
def normalizeGRSChallenge
    {K Domain : Type*} [Field K]
    (multiplier : Domain → K) (received : Domain → Polynomial K)
    (coordinate : Domain) : Polynomial K :=
  Polynomial.C (multiplier coordinate)⁻¹ * received coordinate

theorem normalizeGRSChallenge_eval
    {K Domain : Type*} [Field K]
    (multiplier : Domain → K) (received : Domain → Polynomial K)
    (coordinate : Domain) (z : K) :
    (normalizeGRSChallenge multiplier received coordinate).eval z =
      (multiplier coordinate)⁻¹ * (received coordinate).eval z := by
  simp [normalizeGRSChallenge]

/-- Normalization cannot increase challenge degree. -/
theorem normalizeGRSChallenge_natDegree_le
    {K Domain : Type*} [Field K]
    (multiplier : Domain → K) (received : Domain → Polynomial K)
    (coordinate : Domain) :
    (normalizeGRSChallenge multiplier received coordinate).natDegree ≤
      (received coordinate).natDegree := by
  calc
    (normalizeGRSChallenge multiplier received coordinate).natDegree ≤
        (Polynomial.C (multiplier coordinate)⁻¹ : Polynomial K).natDegree +
          (received coordinate).natDegree :=
      Polynomial.natDegree_mul_le
    _ = (received coordinate).natDegree := by simp

/-- Restoring a nonzero multiplier exactly recovers the original received
challenge polynomial. -/
theorem restore_normalizedGRSChallenge
    {K Domain : Type*} [Field K]
    (multiplier : Domain → K) (received : Domain → Polynomial K)
    (coordinate : Domain) (multiplierNeZero : multiplier coordinate ≠ 0) :
    Polynomial.C (multiplier coordinate) *
        normalizeGRSChallenge multiplier received coordinate =
      received coordinate := by
  unfold normalizeGRSChallenge
  rw [← mul_assoc, ← Polynomial.C_mul]
  simp [multiplierNeZero]

/-- A GRS agreement becomes the ordinary polynomial-evaluation agreement
required by the fixed-branch theorem after normalization. -/
theorem normalize_grs_agreement
    {K Domain : Type*} [Field K]
    (points multiplier : Domain → K)
    (received : Domain → Polynomial K) (candidate : Polynomial K)
    (coordinate : Domain) (z : K)
    (multiplierNeZero : multiplier coordinate ≠ 0)
    (agreement : multiplier coordinate * candidate.eval (points coordinate) =
      (received coordinate).eval z) :
    candidate.eval (points coordinate) =
      (normalizeGRSChallenge multiplier received coordinate).eval z := by
  rw [normalizeGRSChallenge_eval, ← agreement]
  field_simp

/-- Evaluating a coefficientwise challenge curve and then restoring the GRS
multiplier gives the scalar-power combination of the GRS coefficient words. -/
theorem restore_candidateCurve_grs
    {K Domain : Type*} [Field K]
    (points multiplier : Domain → K)
    (coefficientCurve : Nat → Polynomial K)
    (M : Nat) (z : K) (coordinate : Domain) :
    multiplier coordinate *
        (candidateCurve coefficientCurve M z).eval (points coordinate) =
      ∑ j ∈ Finset.range (M + 1),
        z ^ j *
          (multiplier coordinate *
            (coefficientCurve j).eval (points coordinate)) := by
  classical
  unfold candidateCurve
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j jMem
  ring

/-- The intrinsic mathematical conclusion of curve decodability: coefficient
messages of degree at most `m`, with every surviving candidate on their
degree-`M` scalar-power curve. -/
def IsCandidateCurve
    {K : Type*} [Field K] (candidate : K → Polynomial K)
    (challenges : Finset K) (m M : Nat) : Prop :=
  ∃ coefficientCurve : Nat → Polynomial K,
    (∀ j, j ≤ M → (coefficientCurve j).natDegree ≤ m) ∧
      ∀ z ∈ challenges,
        candidate z = candidateCurve coefficientCurve M z

#print axioms normalizeGRSChallenge_natDegree_le
#print axioms restore_normalizedGRSChallenge
#print axioms normalize_grs_agreement
#print axioms restore_candidateCurve_grs

end

end WeightedHensel

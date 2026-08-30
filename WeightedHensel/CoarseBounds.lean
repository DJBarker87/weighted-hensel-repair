/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.DivisionFreeRecurrence

/-!
# Downstream coarse allowances

This module checks equations (43)--(47) and (94)--(101): the repaired
ceilings may exceed the source's unsupported intermediate bound, but remain
strictly below the coarser threshold actually consumed downstream.
-/

set_option autoImplicit false

namespace WeightedHensel

/-- Equation (94): the generator weight is bounded by the common parent
degree allowance. -/
theorem sourceTau_le_commonDegree
    (DH DStar ell h tau : Nat)
    (DHLe : DH ≤ DStar) (hPositive : 1 ≤ h)
    (tauEq : tau = DH + ell - ell * h) :
    tau ≤ DStar := by
  have ellLe : ell ≤ ell * h := Nat.le_mul_of_pos_right ell hPositive
  rw [tauEq]
  omega

/-- Equation (95): the cleared derivative parameter is bounded by
`d DStar`. -/
theorem sourceMu_le_commonDegree
    (DH DR DStar ell h d mu : Nat)
    (DHLe : DH ≤ DStar) (DRLe : DR ≤ DStar)
    (dPositive : 1 ≤ d)
    (muEq : mu = (DR - ell) + (d - 1) * (DH - ell * h)) :
    mu ≤ d * DStar := by
  rw [muEq]
  calc
    (DR - ell) + (d - 1) * (DH - ell * h) ≤
        DStar + (d - 1) * DStar := by
      exact Nat.add_le_add
        ((Nat.sub_le DR ell).trans DRLe)
        (Nat.mul_le_mul_left (d - 1)
          ((Nat.sub_le DH (ell * h)).trans DHLe))
    _ = d * DStar := by
      calc
        DStar + (d - 1) * DStar = (1 + (d - 1)) * DStar := by ring
        _ = d * DStar := by
          congr 1
          omega

/-- The slightly sharper form of equation (43), used for the pole budget. -/
theorem sourceMu_lt_commonDegree
    (DH DR DStar ell h d mu : Nat)
    (DHLe : DH ≤ DStar) (DRLe : DR ≤ DStar)
    (ellPositive : 1 ≤ ell) (ellLeDR : ell ≤ DR)
    (dPositive : 1 ≤ d)
    (muEq : mu = (DR - ell) + (d - 1) * (DH - ell * h)) :
    mu < d * DStar := by
  have drSubLt : DR - ell < DStar := by omega
  rw [muEq]
  calc
    (DR - ell) + (d - 1) * (DH - ell * h) <
        DStar + (d - 1) * DStar := by
      exact Nat.add_lt_add_of_lt_of_le drSubLt
        (Nat.mul_le_mul_left (d - 1)
          ((Nat.sub_le DH (ell * h)).trans DHLe))
    _ = d * DStar := by
      calc
        DStar + (d - 1) * DStar = (1 + (d - 1)) * DStar := by ring
        _ = d * DStar := by
          congr 1
          omega

/-- Equation (101) before multiplication by the branch degree. -/
theorem divisionFreeCeiling_lt_coarse
    (tau mu d DStar t : Nat) (tPositive : 0 < t)
    (dPositive : 1 ≤ d) (DStarPositive : 1 ≤ DStar)
    (tauLe : tau ≤ DStar) (muLe : mu ≤ d * DStar) :
    divisionFreeCeiling tau mu t < (2 * t + 1) * d * DStar := by
  have commonLe : DStar ≤ d * DStar := by
    simpa using Nat.mul_le_mul_right DStar dPositive
  have exponentEq : henselExponent t = 2 * t - 1 :=
    henselExponent_of_pos tPositive
  have firstBound : divisionFreeCeiling tau mu t ≤
      DStar + (2 * t - 1) * (d * DStar) := by
    unfold divisionFreeCeiling
    rw [exponentEq]
    exact Nat.add_le_add tauLe
      (Nat.mul_le_mul_left (2 * t - 1) muLe)
  have secondBound : DStar + (2 * t - 1) * (d * DStar) ≤
      (2 * t) * (d * DStar) := by
    calc
      DStar + (2 * t - 1) * (d * DStar) ≤
          d * DStar + (2 * t - 1) * (d * DStar) :=
        Nat.add_le_add_right commonLe _
      _ = (2 * t) * (d * DStar) := by
        calc
          d * DStar + (2 * t - 1) * (d * DStar) =
              (1 + (2 * t - 1)) * (d * DStar) := by ring
          _ = (2 * t) * (d * DStar) := by
            congr 1
            omega
  have dDPositive : 0 < d * DStar :=
    Nat.mul_pos dPositive DStarPositive
  have strict : (2 * t) * (d * DStar) <
      (2 * t + 1) * (d * DStar) :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self (2 * t)) dDPositive
  exact firstBound.trans_lt (secondBound.trans_lt (by
    simpa [Nat.mul_assoc] using strict))

/-- Equation (101), including the outer branch-degree factor. -/
theorem weightedDivisionFreeBudget_lt_coarse
    (h tau mu d DStar t : Nat) (hPositive : 1 ≤ h)
    (tPositive : 0 < t) (dPositive : 1 ≤ d)
    (DStarPositive : 1 ≤ DStar)
    (tauLe : tau ≤ DStar) (muLe : mu ≤ d * DStar) :
    h * divisionFreeCeiling tau mu t <
      h * ((2 * t + 1) * d * DStar) := by
  exact Nat.mul_lt_mul_of_pos_left
    (divisionFreeCeiling_lt_coarse tau mu d DStar t tPositive dPositive
      DStarPositive tauLe muLe) hPositive

/-- Equation (44): roots of `W` and of the derivative numerator fit below
the same coarse pole allowance. -/
theorem sourcePoleBudget_lt_coarse
    (h w xiWeight sigma mu d DStar : Nat)
    (hPositive : 1 ≤ h) (wLeMu : w ≤ mu)
    (sigmaEq : sigma = mu - w) (xiWeightLe : xiWeight ≤ sigma)
    (muLt : mu < d * DStar) :
    w + h * xiWeight < h * d * DStar := by
  have sigmaSplit : sigma + w = mu := by
    rw [sigmaEq, Nat.sub_add_cancel wLeMu]
  have wLeHw : w ≤ h * w := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right w hPositive
  calc
    w + h * xiWeight ≤ w + h * sigma :=
      Nat.add_le_add_left (Nat.mul_le_mul_left h xiWeightLe) w
    _ ≤ h * w + h * sigma := Nat.add_le_add_right wLeHw _
    _ = h * mu := by rw [← Nat.mul_add, Nat.add_comm w sigma, sigmaSplit]
    _ < h * (d * DStar) := Nat.mul_lt_mul_of_pos_left muLt hPositive
    _ = h * d * DStar := by ring

/-- The direct repaired ceiling is bounded by its denominator-free form. -/
theorem sourceNumeratorCeiling_le_divisionFree
    (tau w sigma mu t : Nat) (tPositive : 0 < t)
    (wLeMu : w ≤ mu) (sigmaEq : sigma = mu - w) :
    sourceNumeratorCeiling tau w sigma t ≤
      divisionFreeCeiling tau mu t := by
  have equality := direct_and_divisionFree_ceilings_equivalent tau mu sigma w
    t tPositive wLeMu sigmaEq
  rw [← equality]
  exact Nat.le_add_right _ _

/-- Equation (45): every individual direct-repair coefficient resultant
fits below the downstream allowance. -/
theorem sourceCoefficientResultantBudget_lt_coarse
    (h tau w sigma mu d DStar t : Nat) (hPositive : 1 ≤ h)
    (tPositive : 0 < t) (dPositive : 1 ≤ d)
    (DStarPositive : 1 ≤ DStar)
    (wLeMu : w ≤ mu) (sigmaEq : sigma = mu - w)
    (tauLe : tau ≤ DStar) (muLe : mu ≤ d * DStar) :
    h * sourceNumeratorCeiling tau w sigma t <
      h * ((2 * t + 1) * d * DStar) := by
  exact (Nat.mul_le_mul_left h
      (sourceNumeratorCeiling_le_divisionFree tau w sigma mu t tPositive
        wLeMu sigmaEq)).trans_lt
    (weightedDivisionFreeBudget_lt_coarse h tau mu d DStar t hPositive
      tPositive dPositive DStarPositive tauLe muLe)

/-- Equation (46): every summand of the direct common numerator has the
same ceiling `P_m`. -/
theorem sourceCommonNumeratorSummand_ceiling_eq
    (tau w sigma t m : Nat) (tLeM : t ≤ m) :
    sourceNumeratorCeiling tau w sigma t + (m - t) * w +
        (henselExponent m - henselExponent t) * sigma =
      sourceNumeratorCeiling tau w sigma m := by
  have exponentLe : henselExponent t ≤ henselExponent m :=
    henselExponent_monotone tLeM
  unfold sourceNumeratorCeiling
  have tSplit : t + (m - t) = m := Nat.add_sub_of_le tLeM
  have exponentSplit : henselExponent t +
      (henselExponent m - henselExponent t) = henselExponent m :=
    Nat.add_sub_of_le exponentLe
  calc
    tau + t * w + henselExponent t * sigma + (m - t) * w +
        (henselExponent m - henselExponent t) * sigma =
      tau + (t + (m - t)) * w +
        (henselExponent t +
          (henselExponent m - henselExponent t)) * sigma := by ring
    _ = tau + m * w + henselExponent m * sigma := by
      rw [tSplit, exponentSplit]

/-- Equation (47): the target challenge term also fits under `P_m`. -/
theorem sourceCommonTarget_ceiling_le
    (tau w sigma m challengeDegree : Nat)
    (challengePlusLeadingLe : challengeDegree + w ≤ tau) :
    challengeDegree + (m + 1) * w + henselExponent m * sigma ≤
      sourceNumeratorCeiling tau w sigma m := by
  unfold sourceNumeratorCeiling
  calc
    challengeDegree + (m + 1) * w + henselExponent m * sigma =
        (challengeDegree + w) + m * w + henselExponent m * sigma := by ring
    _ ≤ tau + m * w + henselExponent m * sigma :=
      by omega

/-- The direct common numerator and its second resultant use exactly the
same downstream coarse allowance as an individual coefficient at `m`. -/
theorem sourceSecondResultantBudget_lt_coarse
    (h tau w sigma mu d DStar m : Nat) (hPositive : 1 ≤ h)
    (mPositive : 0 < m) (dPositive : 1 ≤ d)
    (DStarPositive : 1 ≤ DStar)
    (wLeMu : w ≤ mu) (sigmaEq : sigma = mu - w)
    (tauLe : tau ≤ DStar) (muLe : mu ≤ d * DStar) :
    h * sourceNumeratorCeiling tau w sigma m <
      h * ((2 * m + 1) * d * DStar) :=
  sourceCoefficientResultantBudget_lt_coarse h tau w sigma mu d DStar m
    hPositive mPositive dPositive DStarPositive wLeMu sigmaEq tauLe muLe

#print axioms sourceTau_le_commonDegree
#print axioms sourceMu_le_commonDegree
#print axioms sourceMu_lt_commonDegree
#print axioms divisionFreeCeiling_lt_coarse
#print axioms weightedDivisionFreeBudget_lt_coarse
#print axioms sourcePoleBudget_lt_coarse
#print axioms sourceNumeratorCeiling_le_divisionFree
#print axioms sourceCoefficientResultantBudget_lt_coarse
#print axioms sourceCommonNumeratorSummand_ceiling_eq
#print axioms sourceCommonTarget_ceiling_le
#print axioms sourceSecondResultantBudget_lt_coarse

end WeightedHensel

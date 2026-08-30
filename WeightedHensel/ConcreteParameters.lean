/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.CurveDecodability
import WeightedHensel.JohnsonBound
import WeightedHensel.FactorDegreeTransfer

/-!
# Concrete parameters from the paper

This file checks the two Reed--Solomon parameter columns without importing
the Aspis application.  The concrete list caps `100` and `99` are kept
separate from the rate-only analytic parameters `112` and `113`.
-/

set_option autoImplicit false

namespace WeightedHensel

open scoped BigOperators

noncomputable section

/-! ## Literal table entries -/

def degree28DomainSize : Nat := 2 ^ 20
def degree3DomainSize : Nat := 2 ^ 18

def degree28MaximumPolynomialDegree : Nat := 1024
def degree3MaximumPolynomialDegree : Nat := 255

def degree28ChallengeCurveDegree : Nat := 28
def degree3ChallengeCurveDegree : Nat := 3

def degree28BranchWeight : Nat := 28
def degree3BranchWeight : Nat := 3

def degree28SupportThreshold : Nat := 38229
def degree3SupportThreshold : Nat := 9557

def degree28ConcreteListCap : Nat := 100
def degree3ConcreteListCap : Nat := 99

def degree28AnalyticListParameter : Nat := 112
def degree3AnalyticListParameter : Nat := 113

def degree28OuterExceptionalCount : Nat := 87316067086790
def degree3OuterExceptionalCount : Nat := 2388155905379

def degree28CurveDecodabilityCount : Nat := 336869026605739
def degree3CurveDecodabilityCount : Nat := 9396508281246

theorem concrete_evaluation_domain_sizes :
    degree28DomainSize = 1048576 ∧ degree3DomainSize = 262144 := by
  norm_num [degree28DomainSize, degree3DomainSize]

theorem concrete_polynomial_and_curve_degrees :
    degree28MaximumPolynomialDegree = 1024 ∧
    degree3MaximumPolynomialDegree = 255 ∧
    degree28ChallengeCurveDegree = 28 ∧
    degree3ChallengeCurveDegree = 3 ∧
    degree28BranchWeight = 28 ∧ degree3BranchWeight = 3 := by
  norm_num [degree28MaximumPolynomialDegree,
    degree3MaximumPolynomialDegree, degree28ChallengeCurveDegree,
    degree3ChallengeCurveDegree, degree28BranchWeight, degree3BranchWeight]

/-! ## Agreement and multiplicity-three list caps -/

noncomputable def degree28Rate : Real := 1 / 1024
noncomputable def degree3Rate : Real := 255 / degree3DomainSize
noncomputable def concreteAgreement : Real :=
  (1 + 1 / (2 * 3 : Real)) * Real.sqrt degree28Rate

noncomputable def concreteMultiplicityRatio (rate : Real) : Real :=
  Real.sqrt rate /
    (2 * (concreteAgreement - Real.sqrt rate))

noncomputable def concreteMultiplicity (rate : Real) : Nat :=
  max ⌈concreteMultiplicityRatio rate⌉₊ 3

private theorem degree3Rate_pos : 0 < degree3Rate := by
  norm_num [degree3Rate, degree3DomainSize]

private theorem sqrt_degree28Rate_eq :
    Real.sqrt degree28Rate = 1 / 32 := by
  rw [show degree28Rate = (1 / 32 : Real) ^ 2 by
    norm_num [degree28Rate]]
  rw [Real.sqrt_sq_eq_abs]
  norm_num

theorem exact_concrete_agreement : concreteAgreement = 7 / 192 := by
  rw [concreteAgreement, sqrt_degree28Rate_eq]
  norm_num

theorem exact_degree28_multiplicity_ratio :
    concreteMultiplicityRatio degree28Rate = 3 := by
  rw [concreteMultiplicityRatio, exact_concrete_agreement,
    sqrt_degree28Rate_eq]
  norm_num

theorem exact_degree28_multiplicity :
    concreteMultiplicity degree28Rate = 3 := by
  simp [concreteMultiplicity, exact_degree28_multiplicity_ratio]

private theorem sqrt_degree3Rate_sq :
    Real.sqrt degree3Rate ^ 2 = degree3Rate :=
  Real.sq_sqrt degree3Rate_pos.le

private theorem sqrt_degree3Rate_nonneg : 0 ≤ Real.sqrt degree3Rate :=
  Real.sqrt_nonneg _

private theorem sqrt_degree3Rate_lt_one_div_32 :
    Real.sqrt degree3Rate < 1 / 32 := by
  have square := sqrt_degree3Rate_sq
  have nonnegative := sqrt_degree3Rate_nonneg
  norm_num [degree3Rate, degree3DomainSize] at square ⊢
  nlinarith

theorem degree3_multiplicity_ratio_le_three :
    concreteMultiplicityRatio degree3Rate ≤ 3 := by
  have sqrtLtAgreement :
      Real.sqrt degree3Rate < concreteAgreement := by
    rw [exact_concrete_agreement]
    have strict := sqrt_degree3Rate_lt_one_div_32
    norm_num at strict ⊢
    linarith
  have denominatorPositive :
      0 < 2 * (concreteAgreement - Real.sqrt degree3Rate) := by
    linarith
  rw [show concreteMultiplicityRatio degree3Rate =
      Real.sqrt degree3Rate /
        (2 * (concreteAgreement - Real.sqrt degree3Rate)) by rfl]
  rw [div_le_iff₀ denominatorPositive, exact_concrete_agreement]
  have strict := sqrt_degree3Rate_lt_one_div_32
  norm_num at strict ⊢
  linarith

theorem exact_degree3_multiplicity :
    concreteMultiplicity degree3Rate = 3 := by
  have ceiling : ⌈concreteMultiplicityRatio degree3Rate⌉₊ ≤ 3 :=
    (Nat.ceil_le).2 degree3_multiplicity_ratio_le_three
  unfold concreteMultiplicity
  omega

theorem exact_degree28_agreement_floor :
    (degree28SupportThreshold : Real) <
        concreteAgreement * degree28DomainSize ∧
      concreteAgreement * degree28DomainSize <
        degree28SupportThreshold + 1 := by
  rw [exact_concrete_agreement]
  norm_num [degree28SupportThreshold, degree28DomainSize]

theorem exact_degree3_agreement_floor :
    (degree3SupportThreshold : Real) <
        concreteAgreement * degree3DomainSize ∧
      concreteAgreement * degree3DomainSize <
        degree3SupportThreshold + 1 := by
  rw [exact_concrete_agreement]
  norm_num [degree3SupportThreshold, degree3DomainSize]

/-- The concrete multiplicity-three initial list contains at most `100`
candidates under the exact RS overlap premise. -/
theorem degree28_guruswamiSudan_list_card_le_100
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (agreement : Candidate → Finset (Fin 1048576))
    (large : ∀ candidate, 38230 ≤ (agreement candidate).card)
    (overlap : ∀ left right, left ≠ right →
      ((agreement left) ∩ (agreement right)).card ≤ 1024) :
    Fintype.card Candidate ≤ degree28ConcreteListCap := by
  have strict : Fintype.card Candidate < 101 := by
    apply list_card_lt_of_johnson_parameters agreement
      1048576 38230 1024 101
    · simp
    · exact large
    · exact overlap
    · norm_num
    · norm_num
    · norm_num
  unfold degree28ConcreteListCap
  omega

/-- The concrete multiplicity-three folded list contains at most `99`
candidates under the exact RS overlap premise. -/
theorem degree3_guruswamiSudan_list_card_le_99
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (agreement : Candidate → Finset (Fin 262144))
    (large : ∀ candidate, 9558 ≤ (agreement candidate).card)
    (overlap : ∀ left right, left ≠ right →
      ((agreement left) ∩ (agreement right)).card ≤ 255) :
    Fintype.card Candidate ≤ degree3ConcreteListCap := by
  have strict : Fintype.card Candidate < 100 := by
    apply list_card_lt_of_johnson_parameters agreement
      262144 9558 255 100
    · simp
    · exact large
    · exact overlap
    · norm_num
    · norm_num
    · norm_num
  unfold degree3ConcreteListCap
  omega

/-! ## The separate analytic parameters `112` and `113` -/

noncomputable def rateOnlyListExpression (rate : Real) : Real :=
  ((7 : Real) / 2) / Real.sqrt rate

theorem degree28_rateOnlyListExpression_eq_112 :
    rateOnlyListExpression degree28Rate =
      degree28AnalyticListParameter := by
  rw [rateOnlyListExpression, sqrt_degree28Rate_eq]
  norm_num [degree28AnalyticListParameter]

theorem degree3_rateOnlyListExpression_lt_113 :
    rateOnlyListExpression degree3Rate <
      degree3AnalyticListParameter := by
  rw [rateOnlyListExpression, div_lt_iff₀ (Real.sqrt_pos.2 degree3Rate_pos)]
  have square := sqrt_degree3Rate_sq
  have positive := Real.sqrt_pos.2 degree3Rate_pos
  norm_num [degree3Rate, degree3DomainSize,
    degree3AnalyticListParameter] at square ⊢
  have sqrt255Square : Real.sqrt (255 : Real) ^ 2 = 255 :=
    Real.sq_sqrt (by norm_num)
  have sqrt255Positive : 0 < Real.sqrt (255 : Real) :=
    Real.sqrt_pos.2 (by norm_num)
  nlinarith [sqrt255Square]

theorem concrete_list_caps_are_not_analytic_parameters :
    degree28ConcreteListCap < degree28AnalyticListParameter ∧
      degree3ConcreteListCap < degree3AnalyticListParameter := by
  norm_num [degree28ConcreteListCap, degree28AnalyticListParameter,
    degree3ConcreteListCap, degree3AnalyticListParameter]

/-! ## Appendix A exceptional counts -/

/-- Integer ceiling of equation (122), after cancelling the domain-size
denominator.  Adding `2` before division by `3` is ceiling division. -/
def curveDecodabilityAllowance
    (lambda maximumDegree curveDegree domainSize : Nat) : Nat :=
  (lambda *
      (2 * lambda ^ 4 * maximumDegree + 3 * domainSize) *
      curveDegree + 2) / 3

/-- Equation (123). -/
def outerExceptionalAllowance
    (maximumDegree curveDegree domainSize Y Z : Nat) : Nat :=
  Z + 224 * Y * Z +
    58 * (maximumDegree + 1) * Y ^ 2 * Z +
    (curveDegree * domainSize + 1) * Y

theorem exact_degree28_curveDecodabilityAllowance :
    curveDecodabilityAllowance 112 1024 28 (2 ^ 20) =
      degree28CurveDecodabilityCount := by
  norm_num [curveDecodabilityAllowance,
    degree28CurveDecodabilityCount]

theorem exact_degree3_curveDecodabilityAllowance :
    curveDecodabilityAllowance 113 255 3 (2 ^ 18) =
      degree3CurveDecodabilityCount := by
  norm_num [curveDecodabilityAllowance,
    degree3CurveDecodabilityCount]

theorem exact_degree28_outerExceptionalAllowance :
    outerExceptionalAllowance 1024 28 (2 ^ 20) 112 117078 =
      degree28OuterExceptionalCount := by
  norm_num [outerExceptionalAllowance, degree28OuterExceptionalCount]

theorem exact_degree3_outerExceptionalAllowance :
    outerExceptionalAllowance 255 3 (2 ^ 18) 113 12594 =
      degree3OuterExceptionalCount := by
  norm_num [outerExceptionalAllowance, degree3OuterExceptionalCount]

theorem concrete_outer_allowances_lt_curve_allowances :
    degree28OuterExceptionalCount < degree28CurveDecodabilityCount ∧
      degree3OuterExceptionalCount < degree3CurveDecodabilityCount := by
  norm_num [degree28OuterExceptionalCount, degree28CurveDecodabilityCount,
    degree3OuterExceptionalCount, degree3CurveDecodabilityCount]

/-! ## Challenge domains and the degree-28 subcode warning -/

theorem nonzero_challenge_card
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    (Finset.univ.erase (0 : K)).card = Fintype.card K - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : K))]
  simp

theorem all_challenge_card
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    (Finset.univ : Finset K).card = Fintype.card K := by
  simp

def degree28ReleasedMessageImageDimension : Nat := 1024
def degree28AmbientPolynomialDimension : Nat := 1025

/-- The released image is a proper subspace-sized object; it is not
identified with the full degree-at-most-1024 polynomial space. -/
theorem degree28_released_subcode_dimension_strict :
    degree28ReleasedMessageImageDimension <
      degree28AmbientPolynomialDimension := by
  norm_num [degree28ReleasedMessageImageDimension,
    degree28AmbientPolynomialDimension]

/-! ## Concrete consumption of the coarse repaired Hensel bound -/

theorem degree28_fixedBranchBudget_lt
    (h d tau mu : Nat) (hPositive : 1 ≤ h) (hLeD : h ≤ d)
    (dPositive : 1 ≤ d) (dLe : d ≤ 112)
    (tauLe : tau ≤ 117078) (muLe : mu ≤ d * 117078) :
    h * divisionFreeCeiling tau mu 1024 <
      112 * ((2 * 1024 + 1) * 112 * 117078) := by
  have hLe : h ≤ 112 := hLeD.trans dLe
  exact (weightedDivisionFreeBudget_lt_coarse h tau mu d 117078 1024
    hPositive (by norm_num) dPositive (by norm_num) tauLe muLe).trans_le <| by
      gcongr

theorem degree3_fixedBranchBudget_lt
    (h d tau mu : Nat) (hPositive : 1 ≤ h) (hLeD : h ≤ d)
    (dPositive : 1 ≤ d) (dLe : d ≤ 113)
    (tauLe : tau ≤ 12594) (muLe : mu ≤ d * 12594) :
    h * divisionFreeCeiling tau mu 255 <
      113 * ((2 * 255 + 1) * 113 * 12594) := by
  have hLe : h ≤ 113 := hLeD.trans dLe
  exact (weightedDivisionFreeBudget_lt_coarse h tau mu d 12594 255
    hPositive (by norm_num) dPositive (by norm_num) tauLe muLe).trans_le <| by
      gcongr

/-- The exact degree-28 curve allowance is more than sufficient for the
incidence inequality consumed by the fixed-branch theorem. -/
theorem degree28_concrete_incidence
    (challengeCount branchBudget : Nat)
    (many : degree28CurveDecodabilityCount < challengeCount)
    (budget : branchBudget <
      112 * ((2 * 1024 + 1) * 112 * 117078)) :
    1024 * challengeCount + 1048576 * branchBudget <
      challengeCount * (38229 + 1) := by
  norm_num [degree28CurveDecodabilityCount] at many budget ⊢
  omega

/-- The exact degree-3 curve allowance is more than sufficient for the
incidence inequality consumed by the fixed-branch theorem. -/
theorem degree3_concrete_incidence
    (challengeCount branchBudget : Nat)
    (many : degree3CurveDecodabilityCount < challengeCount)
    (budget : branchBudget <
      113 * ((2 * 255 + 1) * 113 * 12594)) :
    255 * challengeCount + 262144 * branchBudget <
      challengeCount * (9557 + 1) := by
  norm_num [degree3CurveDecodabilityCount] at many budget ⊢
  omega

#print axioms exact_degree28_multiplicity
#print axioms exact_degree3_multiplicity
#print axioms degree28_guruswamiSudan_list_card_le_100
#print axioms degree3_guruswamiSudan_list_card_le_99
#print axioms degree28_rateOnlyListExpression_eq_112
#print axioms degree3_rateOnlyListExpression_lt_113
#print axioms exact_degree28_curveDecodabilityAllowance
#print axioms exact_degree3_curveDecodabilityAllowance
#print axioms exact_degree28_outerExceptionalAllowance
#print axioms exact_degree3_outerExceptionalAllowance
#print axioms concrete_outer_allowances_lt_curve_allowances
#print axioms degree28_released_subcode_dimension_strict
#print axioms degree28_fixedBranchBudget_lt
#print axioms degree3_fixedBranchBudget_lt
#print axioms degree28_concrete_incidence
#print axioms degree3_concrete_incidence

end

end WeightedHensel

/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.SourceRecurrence

/-!
# Direct repair of the source numerator recurrence

This module first constructs the literal coefficients of
`R(x₀+U,Y,Z)`, then proves the corrected auxiliary-numerator estimate and
the strong induction for the original numerators `β_t`.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-! ## Coefficients after translating the weight-zero variable -/

/-- The coefficient of `U^s` after replacing the inner variable `X` by
`x₀+U` in a polynomial in `K[X,Z]`. Hasse derivatives make the definition
valid in every characteristic. -/
noncomputable def shiftedChallengeCoefficient
    {K : Type*} [Field K] (x₀ : K) (order : Nat)
    (polynomial : BivariatePolynomial K) : Polynomial K :=
  polynomial.sum fun challengeExponent coefficient ↦
    Polynomial.monomial challengeExponent
      ((Polynomial.hasseDeriv order coefficient).eval x₀)

@[simp] theorem shiftedChallengeCoefficient_add
    {K : Type*} [Field K] (x₀ : K) (order : Nat)
    (left right : BivariatePolynomial K) :
    shiftedChallengeCoefficient x₀ order (left + right) =
      shiftedChallengeCoefficient x₀ order left +
        shiftedChallengeCoefficient x₀ order right := by
  unfold shiftedChallengeCoefficient
  rw [Polynomial.sum_add_index]
  · intro exponent
    simp
  · intro exponent leftCoefficient rightCoefficient
    simp only [map_add, Polynomial.eval_add]

@[simp] theorem shiftedChallengeCoefficient_monomial
    {K : Type*} [Field K] (x₀ : K) (order challengeExponent : Nat)
    (coefficient : Polynomial K) :
    shiftedChallengeCoefficient x₀ order
        (Polynomial.monomial challengeExponent coefficient) =
      Polynomial.monomial challengeExponent
        ((Polynomial.hasseDeriv order coefficient).eval x₀) := by
  unfold shiftedChallengeCoefficient
  rw [Polynomial.sum_monomial_index]
  simp

theorem coeff_shiftedChallengeCoefficient
    {K : Type*} [Field K] (x₀ : K) (order : Nat)
    (polynomial : BivariatePolynomial K) (challengeExponent : Nat) :
    (shiftedChallengeCoefficient x₀ order polynomial).coeff
        challengeExponent =
      (Polynomial.hasseDeriv order
        (polynomial.coeff challengeExponent)).eval x₀ := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [shiftedChallengeCoefficient_add, Polynomial.coeff_add,
        leftInduction, rightInduction, Polynomial.coeff_add, map_add,
        Polynomial.eval_add]
  | monomial exponent coefficient =>
      rw [shiftedChallengeCoefficient_monomial]
      by_cases same : exponent = challengeExponent
      · subst exponent
        simp
      · simp [Polynomial.coeff_monomial, same]

/-- Translation in `X` cannot increase `Z`-degree. -/
theorem shiftedChallengeCoefficient_natDegree_le
    {K : Type*} [Field K] (x₀ : K) (order : Nat)
    (polynomial : BivariatePolynomial K) :
    (shiftedChallengeCoefficient x₀ order polynomial).natDegree ≤
      polynomial.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro challengeExponent exponentLarge
  rw [coeff_shiftedChallengeCoefficient]
  have coefficientZero : polynomial.coeff challengeExponent = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt exponentLarge
  rw [coefficientZero, map_zero, Polynomial.eval_zero]

/-- Specialization of the inner variable `X` at `x₀`, leaving `Y,Z`
polynomial. -/
def specializeX
    {K : Type*} [Field K] (x₀ : K) (parent : TrivariatePolynomial K) :
    BivariatePolynomial K :=
  parent.map (Polynomial.mapRingHom (Polynomial.evalRingHom x₀))

/-- The full shifted coefficient `c_{s,j}(Z)`. -/
def shiftedParentCoefficient
    {K : Type*} [Field K] (x₀ : K) (order yExponent : Nat)
    (parent : TrivariatePolynomial K) : Polynomial K :=
  shiftedChallengeCoefficient x₀ order (parent.coeff yExponent)

/-- At shifted order zero, `c_{0,j}` is the coefficient of `Y^j` in
`R(x₀,Y,Z)`. -/
theorem shiftedParentCoefficient_zero
    {K : Type*} [Field K] (x₀ : K) (yExponent : Nat)
    (parent : TrivariatePolynomial K) :
    shiftedParentCoefficient x₀ 0 yExponent parent =
      (specializeX x₀ parent).coeff yExponent := by
  ext challengeExponent
  rw [shiftedParentCoefficient, coeff_shiftedChallengeCoefficient]
  simp [specializeX]

/-- The paper's full coefficient hypothesis in the original variables:
`X` has weight zero, `Y` weight `ell`, and `Z` weight one. -/
def ParentCoefficientBound
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (ell bound : Nat) : Prop :=
  ∀ yExponent ∈ parent.support,
    (parent.coeff yExponent).natDegree + ell * yExponent ≤ bound

/-- Translation in the weight-zero variable preserves the full coefficient
bound. This is Lemma 4.1 and also the local form of the 2026 transfer lemma. -/
theorem shiftedParentCoefficient_bound
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ : K) (ell bound order yExponent : Nat)
    (globalBound : ParentCoefficientBound parent ell bound)
    (coefficientNeZero : shiftedParentCoefficient x₀ order yExponent parent ≠ 0) :
    (shiftedParentCoefficient x₀ order yExponent parent).natDegree +
        ell * yExponent ≤ bound := by
  have parentCoefficientNeZero : parent.coeff yExponent ≠ 0 := by
    intro parentCoefficientZero
    apply coefficientNeZero
    simp [shiftedParentCoefficient, parentCoefficientZero,
      shiftedChallengeCoefficient]
  have yMem : yExponent ∈ parent.support :=
    Polynomial.mem_support_iff.mpr parentCoefficientNeZero
  exact (Nat.add_le_add_right
      (shiftedChallengeCoefficient_natDegree_le x₀ order
        (parent.coeff yExponent)) (ell * yExponent)).trans
    (globalBound yExponent yMem)

/-! ## The cleared auxiliary numerator -/

/-- The literal polynomial representative
`∑_{j=q}^d κj c_{s,j}(Z) T^(j-q) W^(d-j)` from equation (27). -/
def sourceClearedRepresentative
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ : K) (s d q : Nat) (kappa : Nat → K) (W : Polynomial K) :
    BivariatePolynomial K :=
  ∑ j ∈ Finset.Icc q d,
    Polynomial.monomial (j - q)
      (Polynomial.C (kappa j) * shiftedParentCoefficient x₀ s j parent *
        W ^ (d - j))

/-- A polynomial coefficient monomial has its expected upper weight. -/
theorem weight_outer_monomial_le
    {K : Type*} [Field K] (tau exponent : Nat) (coefficient : Polynomial K) :
    weight tau (Polynomial.monomial exponent coefficient) ≤
      (coefficient.natDegree + exponent * tau : Nat) := by
  by_cases coefficientZero : coefficient = 0
  · simp [coefficientZero]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, weight_mul_eq,
    weight_C_of_ne_zero tau coefficientZero, weight_pow, weight_generator,
    Polynomial.degree_eq_natDegree coefficientZero]
  simp [nsmul_eq_mul]

/-- The elementary arithmetic in the auxiliary-numerator summand. -/
theorem auxiliary_term_ledger
    (DR ell d b tau q j : Nat) (tauEq : tau = b + ell)
    (qLeJ : q ≤ j) (jLeD : j ≤ d) (ellJLe : ell * j ≤ DR) :
    (DR - ell * j) + (d - j) * b + (j - q) * tau =
      DR - ell * q + (d - q) * b := by
  have jSplit : j = q + (j - q) := (Nat.add_sub_of_le qLeJ).symm
  have dSplit : d - j + (j - q) = d - q := by omega
  have ellSplit : ell * j = ell * q + ell * (j - q) := by
    have scaledSplit := congrArg (fun value : Nat ↦ ell * value) jSplit
    calc
      ell * j = ell * (q + (j - q)) := scaledSplit
      _ = ell * q + ell * (j - q) := by rw [Nat.mul_add]
  have ellQLe : ell * q ≤ DR := by
    rw [ellSplit] at ellJLe
    omega
  have subtractShift :
      DR - ell * j + ell * (j - q) = DR - ell * q := by
    rw [ellSplit] at ellJLe ⊢
    omega
  rw [tauEq, Nat.mul_add]
  calc
    DR - ell * j + (d - j) * b +
        ((j - q) * b + (j - q) * ell) =
      (DR - ell * j + ell * (j - q)) +
        ((d - j) + (j - q)) * b := by ring
    _ = DR - ell * q + (d - q) * b := by
      rw [subtractShift, dSplit]

/-- The full cleared representative has weight at most
`D_R-ℓq+(d-q)b`. -/
theorem sourceClearedRepresentative_weight_le
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (x₀ : K) (ell DR d b tau s q : Nat) (kappa : Nat → K)
    (W : Polynomial K)
    (globalBound : ParentCoefficientBound parent ell DR)
    (tauEq : tau = b + ell) (wLeB : W.natDegree ≤ b)
    (_qLeD : q ≤ d) :
    weight tau (sourceClearedRepresentative parent x₀ s d q kappa W) ≤
      (DR - ell * q + (d - q) * b : Nat) := by
  unfold sourceClearedRepresentative
  apply weight_finset_sum_le
  intro j jMem
  have qLeJ : q ≤ j := (Finset.mem_Icc.mp jMem).1
  have jLeD : j ≤ d := (Finset.mem_Icc.mp jMem).2
  let shifted := shiftedParentCoefficient x₀ s j parent
  let coefficient := Polynomial.C (kappa j) * shifted * W ^ (d - j)
  by_cases shiftedZero : shifted = 0
  · have shiftedZero' : shiftedParentCoefficient x₀ s j parent = 0 := by
      simpa [shifted] using shiftedZero
    simp [shiftedZero']
  have shiftedBound : shifted.natDegree + ell * j ≤ DR := by
    exact shiftedParentCoefficient_bound parent x₀ ell DR s j globalBound
      shiftedZero
  have ellJLe : ell * j ≤ DR := shiftedBound.trans' (Nat.le_add_left _ _)
  have scalarDegreeLe :
      (Polynomial.C (kappa j) * shifted).natDegree ≤ shifted.natDegree := by
    exact Polynomial.natDegree_mul_le.trans (by simp)
  have coefficientDegreeLe :
      coefficient.natDegree ≤ shifted.natDegree + (d - j) * W.natDegree := by
    exact Polynomial.natDegree_mul_le.trans <|
      (Nat.add_le_add_right scalarDegreeLe _).trans <|
        Nat.add_le_add_left Polynomial.natDegree_pow_le _
  have shiftedDegreeLe : shifted.natDegree ≤ DR - ell * j :=
    Nat.le_sub_of_add_le shiftedBound
  have termDegreeLe :
      coefficient.natDegree + (j - q) * tau ≤
        (DR - ell * j) + (d - j) * b + (j - q) * tau := by
    apply Nat.add_le_add_right
    exact coefficientDegreeLe.trans <|
      Nat.add_le_add shiftedDegreeLe (Nat.mul_le_mul_left _ wLeB)
  exact (weight_outer_monomial_le tau (j - q) coefficient).trans <|
    WithBot.coe_le_coe.mpr <| termDegreeLe.trans_eq
      (auxiliary_term_ledger DR ell d b tau q j tauEq qLeJ jLeD ellJLe)

/-- If `H ∣ P` and `P` has outer degree at most `d`, then the leading
coefficient of `H` divides the `Y^d` coefficient of `P`. -/
theorem leadingCoeff_dvd_coefficient_of_dvd
    {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (factor polynomial : Polynomial R) (d : Nat)
    (factorDvd : factor ∣ polynomial) (degreeLe : polynomial.natDegree ≤ d) :
    factor.leadingCoeff ∣ polynomial.coeff d := by
  by_cases coefficientZero : polynomial.coeff d = 0
  · simp [coefficientZero]
  have polynomialNeZero : polynomial ≠ 0 := by
    intro polynomialZero
    rw [polynomialZero] at coefficientZero
    exact coefficientZero (Polynomial.coeff_zero d)
  have dLeDegree : d ≤ polynomial.natDegree :=
    Polynomial.le_natDegree_of_ne_zero coefficientZero
  have degreeEq : polynomial.natDegree = d := Nat.le_antisymm degreeLe dLeDegree
  rw [← degreeEq]
  exact Polynomial.leadingCoeff_dvd_leadingCoeff factorDvd

/-- The divisibility hypothesis in `K[Z,Y]` supplies the extra factor of
`W` in every `s=0` cleared numerator. -/
theorem leadingCoeff_dvd_sourceClearedRepresentative_zero
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K) (d q : Nat)
    (kappa : Nat → K) (_qLeD : q ≤ d)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (specializedDegreeLe : (specializeX x₀ parent).natDegree ≤ d) :
    Polynomial.C factor.leadingCoeff ∣
      sourceClearedRepresentative parent x₀ 0 d q kappa factor.leadingCoeff := by
  unfold sourceClearedRepresentative
  apply Finset.dvd_sum
  intro j jMem
  have jLeD := (Finset.mem_Icc.mp jMem).2
  have coefficientDvd : factor.leadingCoeff ∣
      Polynomial.C (kappa j) * shiftedParentCoefficient x₀ 0 j parent *
        factor.leadingCoeff ^ (d - j) := by
    by_cases jEq : j = d
    · subst j
      simp only [Nat.sub_self, pow_zero, mul_one]
      apply dvd_mul_of_dvd_right _ (Polynomial.C (kappa d))
      rw [shiftedParentCoefficient_zero]
      exact leadingCoeff_dvd_coefficient_of_dvd factor
        (specializeX x₀ parent) d factorDvd specializedDegreeLe
    · have exponentPositive : 0 < d - j := Nat.sub_pos_of_lt (lt_of_le_of_ne jLeD jEq)
      exact dvd_mul_of_dvd_right
        (dvd_pow_self factor.leadingCoeff (Nat.ne_of_gt exponentPositive))
        (Polynomial.C (kappa j) * shiftedParentCoefficient x₀ 0 j parent)
  obtain ⟨quotient, quotientEq⟩ := coefficientDvd
  refine ⟨Polynomial.monomial (j - q) quotient, ?_⟩
  rw [quotientEq]
  simp

/-- Corrected auxiliary-numerator theorem. It constructs `B_{s,λ}` in
the regular quotient and proves
`Λ(B) ≤ D_R-ℓq+(d-q)b-ε_s w`. -/
theorem exists_sourceAuxiliaryNumerator
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K)
    (ell DH DR d b tau s q : Nat) (kappa : Nat → K)
    (factorNeZero : factor ≠ 0)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (ellDegreeLe : ell * factor.natDegree ≤ DH)
    (bEq : b = DH - ell * factor.natDegree)
    (tauEq : tau = b + ell)
    (globalBound : ParentCoefficientBound parent ell DR)
    (wLeB : factor.leadingCoeff.natDegree ≤ b)
    (qLeD : q ≤ d)
    (factorDvd : factor ∣ specializeX x₀ parent)
    (specializedDegreeLe : (specializeX x₀ parent).natDegree ≤ d) :
    ∃ auxiliary : RegularQuotient factor,
      AdjoinRoot.mk (monicization factor)
          (sourceClearedRepresentative parent x₀ s d q kappa
            factor.leadingCoeff) =
        AdjoinRoot.of (monicization factor) factor.leadingCoeff ^ sourceEpsilon s *
          auxiliary ∧
      regularWeight factor factorNeZero tau auxiliary ≤
        (DR - ell * q + (d - q) * b -
          sourceEpsilon s * factor.leadingCoeff.natDegree : Nat) ∧
      (auxiliary = 0 ∨
        sourceEpsilon s * factor.leadingCoeff.natDegree +
            regularWeightNat factor factorNeZero tau auxiliary ≤
          DR - ell * q + (d - q) * b) := by
  let cleared := sourceClearedRepresentative parent x₀ s d q kappa
    factor.leadingCoeff
  let ceiling := DR - ell * q + (d - q) * b
  have clearedWeight : weight tau cleared ≤ (ceiling : WithBot Nat) := by
    exact sourceClearedRepresentative_weight_le parent x₀ ell DR d b tau s q
      kappa factor.leadingCoeff globalBound tauEq wLeB qLeD
  have generatorWeightEq : DH + ell - ell * factor.natDegree = tau := by
    rw [tauEq, bEq]
    omega
  by_cases sZero : s = 0
  · subst s
    have clearedDvd : Polynomial.C factor.leadingCoeff ∣ cleared := by
      exact leadingCoeff_dvd_sourceClearedRepresentative_zero parent factor x₀
        d q kappa qLeD factorDvd specializedDegreeLe
    obtain ⟨representative, representativeEq⟩ := clearedDvd
    refine ⟨AdjoinRoot.mk (monicization factor) representative, ?_, ?_, ?_⟩
    · simp only [sourceEpsilon_zero, pow_one]
      change AdjoinRoot.mk (monicization factor) cleared =
        AdjoinRoot.of (monicization factor) factor.leadingCoeff *
          AdjoinRoot.mk (monicization factor) representative
      rw [representativeEq, map_mul]
      rfl
    · have representativeWeight :
          weight tau representative ≤
            (ceiling - factor.leadingCoeff.natDegree : Nat) := by
        by_cases representativeZero : representative = 0
        · simp [representativeZero]
        have leadingNeZero : factor.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr factorNeZero
        have productBound := clearedWeight
        rw [representativeEq, weight_C_mul_natDegree tau leadingNeZero,
          weight_eq_coe tau representativeZero] at productBound
        have naturalBound : factor.leadingCoeff.natDegree +
            localBivariateWeight tau representative ≤ ceiling := by
          exact WithBot.coe_le_coe.mp productBound
        have reorderedBound : localBivariateWeight tau representative +
            factor.leadingCoeff.natDegree ≤ ceiling := by omega
        rw [weight_eq_coe tau representativeZero]
        exact WithBot.coe_le_coe.mpr (Nat.le_sub_of_add_le reorderedBound)
      simp only [sourceEpsilon_zero, one_mul]
      rw [← generatorWeightEq] at representativeWeight ⊢
      exact (regularWeight_mk_le factor factorNeZero ell DH
        factorCoefficientBound representative).trans representativeWeight
    · let auxiliary : RegularQuotient factor :=
        AdjoinRoot.mk (monicization factor) representative
      by_cases auxiliaryZero : auxiliary = 0
      · exact Or.inl auxiliaryZero
      · apply Or.inr
        have representativeNeZero : representative ≠ 0 := by
          intro representativeZero
          apply auxiliaryZero
          simp [auxiliary, representativeZero]
        have leadingNeZero : factor.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr factorNeZero
        have productBound := clearedWeight
        rw [representativeEq, weight_C_mul_natDegree tau leadingNeZero,
          weight_eq_coe tau representativeNeZero] at productBound
        have polynomialBound : factor.leadingCoeff.natDegree +
            localBivariateWeight tau representative ≤ ceiling :=
          WithBot.coe_le_coe.mp productBound
        rw [localBivariateWeight_eq_iteratedBivariateWeight] at polynomialBound
        have quotientBound := regularWeightNat_mk_le factor factorNeZero ell DH
          factorCoefficientBound representative
        rw [generatorWeightEq] at quotientBound
        have finalBound : factor.leadingCoeff.natDegree +
            regularWeightNat factor factorNeZero tau
              (AdjoinRoot.mk (monicization factor) representative) ≤ ceiling :=
          (Nat.add_le_add_left quotientBound _).trans polynomialBound
        simpa [sourceEpsilon_zero, ceiling] using finalBound
  · refine ⟨AdjoinRoot.mk (monicization factor) cleared, ?_, ?_, ?_⟩
    · have epsilonZero : sourceEpsilon s = 0 :=
        sourceEpsilon_of_pos (Nat.pos_of_ne_zero sZero)
      change AdjoinRoot.mk (monicization factor) cleared =
        AdjoinRoot.of (monicization factor) factor.leadingCoeff ^ sourceEpsilon s *
          AdjoinRoot.mk (monicization factor) cleared
      rw [epsilonZero, pow_zero, one_mul]
    · have quotientBound := regularWeight_mk_le factor factorNeZero ell DH
          factorCoefficientBound cleared
      rw [generatorWeightEq] at quotientBound
      have epsilonZero : sourceEpsilon s = 0 := sourceEpsilon_of_pos (Nat.pos_of_ne_zero sZero)
      rw [epsilonZero, zero_mul, Nat.sub_zero]
      exact quotientBound.trans clearedWeight
    · let auxiliary : RegularQuotient factor :=
        AdjoinRoot.mk (monicization factor) cleared
      by_cases auxiliaryZero : auxiliary = 0
      · exact Or.inl auxiliaryZero
      · apply Or.inr
        have clearedNeZero : cleared ≠ 0 := by
          intro clearedZero
          apply auxiliaryZero
          simp [auxiliary, clearedZero]
        have quotientBound := regularWeightNat_mk_le factor factorNeZero ell DH
          factorCoefficientBound cleared
        rw [generatorWeightEq] at quotientBound
        have polynomialBound : localBivariateWeight tau cleared ≤ ceiling := by
          rw [weight_eq_coe tau clearedNeZero] at clearedWeight
          exact WithBot.coe_le_coe.mp clearedWeight
        rw [localBivariateWeight_eq_iteratedBivariateWeight] at polynomialBound
        have epsilonZero : sourceEpsilon s = 0 :=
          sourceEpsilon_of_pos (Nat.pos_of_ne_zero sZero)
        rw [epsilonZero, zero_mul, zero_add]
        change regularWeightNat factor factorNeZero tau auxiliary ≤ ceiling
        exact quotientBound.trans polynomialBound

/-! ## Source parameters and the derivative numerator -/

/-- `μ = (D_R-ℓ)+(d-1)b`. -/
def sourceMu (DR ell d b : Nat) : Nat :=
  (DR - ell) + (d - 1) * b

/-- `σ = μ-w`. -/
def sourceSigma (DR ell d b w : Nat) : Nat :=
  sourceMu DR ell d b - w

/-- Specializing the auxiliary theorem to `s=0,q=1` constructs the source
derivative numerator and proves `Λ(ξ) ≤ σ`. -/
theorem exists_sourceDerivativeNumerator
    {K : Type*} [Field K] (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K) (x₀ : K)
    (ell DH DR d b tau : Nat) (kappa : Nat → K)
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
      AdjoinRoot.mk (monicization factor)
          (sourceClearedRepresentative parent x₀ 0 d 1 kappa
            factor.leadingCoeff) =
        AdjoinRoot.of (monicization factor) factor.leadingCoeff * xi ∧
      regularWeight factor factorNeZero tau xi ≤
        (sourceSigma DR ell d b factor.leadingCoeff.natDegree : Nat) := by
  obtain ⟨xi, clearing, xiBound, _⟩ := exists_sourceAuxiliaryNumerator
    parent factor x₀ ell DH DR d b tau 0 1 kappa factorNeZero
    factorCoefficientBound ellDegreeLe bEq tauEq globalBound wLeB dPositive
    factorDvd specializedDegreeLe
  refine ⟨xi, ?_, ?_⟩
  · simpa using clearing
  · simpa [sourceSigma, sourceMu] using xiBound

/-- The corrected source ceiling `P_t = τ + tw + e_tσ`. -/
def sourceNumeratorCeiling (tau w sigma t : Nat) : Nat :=
  tau + t * w + henselExponent t * sigma

@[simp] theorem sourceNumeratorCeiling_zero (tau w sigma : Nat) :
    sourceNumeratorCeiling tau w sigma 0 = tau := by
  simp [sourceNumeratorCeiling]

/-- For positive order, the direct and denominator-free numerical forms of
the corrected ceiling agree. -/
theorem sourceNumeratorCeiling_eq
    (tau w mu sigma t : Nat) (tPositive : 0 < t)
    (wLeMu : w ≤ mu) (sigmaEq : sigma = mu - w) :
    sourceNumeratorCeiling tau w sigma t =
      tau + henselExponent t * mu - (t - 1) * w := by
  have muSplit : mu = w + sigma := by
    rw [sigmaEq, Nat.add_sub_of_le wLeMu]
  have exponentSplit : henselExponent t = t + (t - 1) := by
    simp only [henselExponent]
    omega
  have master : sourceNumeratorCeiling tau w sigma t + (t - 1) * w =
      tau + henselExponent t * mu := by
    rw [sourceNumeratorCeiling, muSplit, exponentSplit]
    ring
  have subtractLe : (t - 1) * w ≤ tau + henselExponent t * mu := by
    rw [← master]
    exact Nat.le_add_left _ _
  omega

/-! ## The three numerical ledgers in one recurrence summand -/

/-- Once the auxiliary numerator and the recursive coefficient product have
their respective bounds, the three source ledgers put every recurrence
summand below `P_t`.  The hypothesis on `auxiliaryWeight` is deliberately
written before truncated subtraction: it says
`epsilon * w + Lambda(B) ≤ D_R-ℓq+(d-q)b`. -/
theorem source_recurrence_term_ceiling
    (DR ell d b tau mu sigma w t : Nat) (tPositive : 0 < t)
    (index : SourceTermIndex t tPositive) (auxiliaryWeight : Nat)
    (ellLe : ell ≤ DR) (dPositive : 1 ≤ d) (wLeMu : w ≤ mu)
    (tauEq : tau = b + ell)
    (muEq : mu = (DR - ell) + (d - 1) * b)
    (sigmaEq : sigma = mu - w)
    (ellQLe : ell * index.q ≤ DR) (qLeD : index.q ≤ d)
    (auxiliaryBound :
      index.epsilon * w + auxiliaryWeight ≤
        DR - ell * index.q + (d - index.q) * b) :
    (index.s + index.epsilon - 1) * w +
          (2 * index.s + index.q - 2) * sigma + auxiliaryWeight +
        (index.q * tau + index.n * w +
          (2 * index.n - index.q) * sigma) ≤
      sourceNumeratorCeiling tau w sigma t := by
  let structural := DR - ell * index.q + (d - index.q) * b
  have structuralEq : structural + index.q * tau = DR + d * b := by
    exact source_structural_ledger DR ell d b tau index.q tauEq ellQLe qLeD
  have parameterEq : tau + w + sigma = DR + d * b :=
    source_parameter_ledger DR ell d b tau mu sigma w ellLe dPositive
      wLeMu tauEq muEq sigmaEq
  have structuralParameter :
      structural + index.q * tau = tau + w + sigma :=
    structuralEq.trans parameterEq.symm
  have derivativeEq := index.derivative_ledger
  have orderEq := index.s_add_n
  have exponentPositive : 0 < henselExponent t := by
    unfold henselExponent
    omega
  have exponentSplit :
      henselExponent t = 1 + (henselExponent t - 1) := by omega
  by_cases sZero : index.s = 0
  · have epsilonOne : index.epsilon = 1 := by simp [SourceTermIndex.epsilon, sZero]
    have nEq : index.n = t := by omega
    have derivativeZero :
        (index.q - 2) + (2 * t - index.q) = henselExponent t - 1 := by
      simpa [sZero, nEq] using derivativeEq
    have auxiliaryPlusW : auxiliaryWeight + w ≤ structural := by
      simpa [epsilonOne, structural, Nat.add_comm] using auxiliaryBound
    have auxiliaryStructural :
        auxiliaryWeight + index.q * tau ≤ tau + sigma := by
      have enlarged :
          auxiliaryWeight + w + index.q * tau ≤
            structural + index.q * tau :=
        Nat.add_le_add_right auxiliaryPlusW (index.q * tau)
      rw [structuralParameter] at enlarged
      omega
    calc
      (index.s + index.epsilon - 1) * w +
            (2 * index.s + index.q - 2) * sigma + auxiliaryWeight +
          (index.q * tau + index.n * w +
            (2 * index.n - index.q) * sigma) =
          (auxiliaryWeight + index.q * tau) + t * w +
            (henselExponent t - 1) * sigma := by
              rw [sZero, epsilonOne, nEq]
              simp only [zero_add, Nat.sub_self, zero_mul]
              rw [← derivativeZero]
              ring_nf
      _ ≤ (tau + sigma) + t * w +
            (henselExponent t - 1) * sigma :=
        Nat.add_le_add_right
          (Nat.add_le_add_right auxiliaryStructural (t * w)) _
      _ = sourceNumeratorCeiling tau w sigma t := by
        have sigmaJoin :
            sigma + (henselExponent t - 1) * sigma =
              henselExponent t * sigma := by
          calc
            sigma + (henselExponent t - 1) * sigma =
                (1 + (henselExponent t - 1)) * sigma := by ring
            _ = henselExponent t * sigma := by rw [← exponentSplit]
        unfold sourceNumeratorCeiling
        calc
          tau + sigma + t * w + (henselExponent t - 1) * sigma =
              tau + t * w +
                (sigma + (henselExponent t - 1) * sigma) := by ring
          _ = tau + t * w + henselExponent t * sigma := by rw [sigmaJoin]
  · have sPositive : 0 < index.s := Nat.pos_of_ne_zero sZero
    have epsilonZero : index.epsilon = 0 := by
      simp [SourceTermIndex.epsilon, sourceEpsilon_of_pos sPositive]
    have auxiliaryLe : auxiliaryWeight ≤ structural := by
      simpa [epsilonZero, structural] using auxiliaryBound
    have auxiliaryStructural :
        auxiliaryWeight + index.q * tau ≤ tau + w + sigma := by
      exact (Nat.add_le_add_right auxiliaryLe (index.q * tau)).trans_eq
        structuralParameter
    have orderSplit : t = 1 + ((index.s - 1) + index.n) := by omega
    have wJoin :
        w + ((index.s - 1) + index.n) * w = t * w := by
      conv_rhs => rw [orderSplit]
      ring
    have sigmaJoin :
        sigma + (henselExponent t - 1) * sigma =
          henselExponent t * sigma := by
      calc
        sigma + (henselExponent t - 1) * sigma =
            (1 + (henselExponent t - 1)) * sigma := by ring
        _ = henselExponent t * sigma := by rw [← exponentSplit]
    calc
      (index.s + index.epsilon - 1) * w +
            (2 * index.s + index.q - 2) * sigma + auxiliaryWeight +
          (index.q * tau + index.n * w +
            (2 * index.n - index.q) * sigma) =
          (auxiliaryWeight + index.q * tau) +
            ((index.s - 1) + index.n) * w +
            (henselExponent t - 1) * sigma := by
              rw [epsilonZero, Nat.add_zero, ← derivativeEq]
              ring
      _ ≤ (tau + w + sigma) +
            ((index.s - 1) + index.n) * w +
            (henselExponent t - 1) * sigma :=
        Nat.add_le_add_right
          (Nat.add_le_add_right auxiliaryStructural
            (((index.s - 1) + index.n) * w)) _
      _ = sourceNumeratorCeiling tau w sigma t := by
        unfold sourceNumeratorCeiling
        calc
          tau + w + sigma + ((index.s - 1) + index.n) * w +
                (henselExponent t - 1) * sigma =
              tau + (w + ((index.s - 1) + index.n) * w) +
                (sigma + (henselExponent t - 1) * sigma) := by ring
          _ = tau + t * w + henselExponent t * sigma := by
            rw [wJoin, sigmaJoin]

/-! ## The original numerator recurrence -/

/-- The product of previously constructed numerators prescribed by a
partition `lambda`. -/
def sourceRecursiveProduct
    {K : Type*} [Field K] {factor : BivariatePolynomial K}
    (beta : Nat → RegularQuotient factor) (partition : SourcePartition) :
    RegularQuotient factor :=
  ∏ index ∈ partition.support, beta index.1 ^ partition index

/-- The literal summand in equation (34). -/
def sourceRecurrenceTerm
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    {t : Nat} {tPositive : 0 < t} (index : SourceTermIndex t tPositive)
    (xi : RegularQuotient factor) (beta : Nat → RegularQuotient factor)
    (auxiliary : RegularQuotient factor) : RegularQuotient factor :=
  AdjoinRoot.of (monicization factor) factor.leadingCoeff ^
        (index.s + index.epsilon - 1) *
      xi ^ (2 * index.s + index.q - 2) * auxiliary *
    sourceRecursiveProduct beta index.partition

/-- The product of earlier numerators contributes exactly the partition
totals `q`, `n`, and `2n-q` to the three ledgers. -/
theorem sourceRecursiveProduct_weight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell DH tau w sigma : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (beta : Nat → RegularQuotient factor) (partition : SourcePartition)
    (betaBound : ∀ index ∈ partition.support,
      regularWeightNat factor factorNeZero tau (beta index.1) ≤
        sourceNumeratorCeiling tau w sigma index.1) :
    regularWeightNat factor factorNeZero tau
        (sourceRecursiveProduct beta partition) ≤
      partitionSize partition * tau + partitionOrder partition * w +
        partitionHenselExponent partition * sigma := by
  have productBound := regularWeightNat_finset_prod_le factor factorNeZero
    ell DH factorCoefficientBound partition.support
    (fun index ↦ beta index.1 ^ partition index)
  rw [generatorWeightEq] at productBound
  refine productBound.trans ?_
  calc
    ∑ index ∈ partition.support,
          regularWeightNat factor factorNeZero tau
            (beta index.1 ^ partition index) ≤
        ∑ index ∈ partition.support,
          partition index * sourceNumeratorCeiling tau w sigma index.1 := by
      apply Finset.sum_le_sum
      intro index indexMem
      have powerBound := regularWeightNat_pow_le factor factorNeZero ell DH
        factorCoefficientBound (beta index.1) (partition index)
      rw [generatorWeightEq] at powerBound
      exact powerBound.trans (Nat.mul_le_mul_left _ (betaBound index indexMem))
    _ = partitionSize partition * tau + partitionOrder partition * w +
          partitionHenselExponent partition * sigma := by
      unfold sourceNumeratorCeiling partitionSize partitionOrder
        partitionHenselExponent
      change
        (∑ index ∈ partition.support,
          partition index *
            (tau + index.1 * w + henselExponent index.1 * sigma)) =
          (∑ index ∈ partition.support, partition index) * tau +
            (∑ index ∈ partition.support,
              index.1 * partition index) * w +
            (∑ index ∈ partition.support,
              partition index * henselExponent index.1) * sigma
      simp_rw [Nat.mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_mul]
      apply congrArg₂ (fun left right : Nat ↦ left + right)
      · apply congrArg₂ (fun left right : Nat ↦ left + right)
        · rfl
        · apply Finset.sum_congr rfl
          intro index _
          ring
      · apply Finset.sum_congr rfl
        intro index _
        ring

/-- Each literal summand in the original recurrence is below `P_t`. -/
theorem sourceRecurrenceTerm_weight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0)
    (ell DH DR d b tau mu sigma w t : Nat) (tPositive : 0 < t)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (wEq : w = factor.leadingCoeff.natDegree)
    (ellLe : ell ≤ DR) (dPositive : 1 ≤ d) (wLeMu : w ≤ mu)
    (tauEq : tau = b + ell)
    (muEq : mu = (DR - ell) + (d - 1) * b)
    (sigmaEq : sigma = mu - w)
    (index : SourceTermIndex t tPositive)
    (qLeD : index.q ≤ d) (ellQLe : ell * index.q ≤ DR)
    (xi : RegularQuotient factor)
    (xiBound : regularWeightNat factor factorNeZero tau xi ≤ sigma)
    (beta : Nat → RegularQuotient factor)
    (betaBound : ∀ recursiveIndex ∈ index.partition.support,
      regularWeightNat factor factorNeZero tau (beta recursiveIndex.1) ≤
        sourceNumeratorCeiling tau w sigma recursiveIndex.1)
    (auxiliary : RegularQuotient factor)
    (auxiliaryBound : auxiliary = 0 ∨
      index.epsilon * w +
          regularWeightNat factor factorNeZero tau auxiliary ≤
        DR - ell * index.q + (d - index.q) * b) :
    regularWeightNat factor factorNeZero tau
        (sourceRecurrenceTerm factor index xi beta auxiliary) ≤
      sourceNumeratorCeiling tau w sigma t := by
  rcases auxiliaryBound with auxiliaryZero | auxiliaryBound
  · subst auxiliary
    simp [sourceRecurrenceTerm]
  have leadingBound := regularWeightNat_of_le_natDegree factor factorNeZero
    ell DH factorCoefficientBound factor.leadingCoeff
  rw [generatorWeightEq, ← wEq] at leadingBound
  have leadingPowerBound := regularWeightNat_pow_le factor factorNeZero ell DH
    factorCoefficientBound
    (AdjoinRoot.of (monicization factor) factor.leadingCoeff)
    (index.s + index.epsilon - 1)
  rw [generatorWeightEq] at leadingPowerBound
  have leadingPowerCeiling :
      regularWeightNat factor factorNeZero tau
          (AdjoinRoot.of (monicization factor) factor.leadingCoeff ^
            (index.s + index.epsilon - 1)) ≤
        (index.s + index.epsilon - 1) * w :=
    leadingPowerBound.trans (Nat.mul_le_mul_left _ leadingBound)
  have xiPowerBound := regularWeightNat_pow_le factor factorNeZero ell DH
    factorCoefficientBound xi (2 * index.s + index.q - 2)
  rw [generatorWeightEq] at xiPowerBound
  have xiPowerCeiling :
      regularWeightNat factor factorNeZero tau
          (xi ^ (2 * index.s + index.q - 2)) ≤
        (2 * index.s + index.q - 2) * sigma :=
    xiPowerBound.trans (Nat.mul_le_mul_left _ xiBound)
  have recursiveProductBound := sourceRecursiveProduct_weight_le factor
    factorNeZero ell DH tau w sigma factorCoefficientBound generatorWeightEq
    beta index.partition betaBound
  rw [index.partitionHenselExponent_eq_two_n_sub_q] at recursiveProductBound
  change regularWeightNat factor factorNeZero tau
      (sourceRecursiveProduct beta index.partition) ≤
    index.q * tau + index.n * w + (2 * index.n - index.q) * sigma
      at recursiveProductBound
  have firstMul := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound
    (AdjoinRoot.of (monicization factor) factor.leadingCoeff ^
      (index.s + index.epsilon - 1))
    (xi ^ (2 * index.s + index.q - 2))
  have secondMul := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound
    (AdjoinRoot.of (monicization factor) factor.leadingCoeff ^
        (index.s + index.epsilon - 1) *
      xi ^ (2 * index.s + index.q - 2)) auxiliary
  have thirdMul := regularWeightNat_mul_le factor factorNeZero ell DH
    factorCoefficientBound
    (AdjoinRoot.of (monicization factor) factor.leadingCoeff ^
          (index.s + index.epsilon - 1) *
        xi ^ (2 * index.s + index.q - 2) * auxiliary)
    (sourceRecursiveProduct beta index.partition)
  rw [generatorWeightEq] at firstMul secondMul thirdMul
  have prefixBound :
      regularWeightNat factor factorNeZero tau
          (AdjoinRoot.of (monicization factor) factor.leadingCoeff ^
                (index.s + index.epsilon - 1) *
              xi ^ (2 * index.s + index.q - 2) * auxiliary) ≤
        (index.s + index.epsilon - 1) * w +
            (2 * index.s + index.q - 2) * sigma +
          regularWeightNat factor factorNeZero tau auxiliary := by
    exact secondMul.trans (Nat.add_le_add_right
      (firstMul.trans (Nat.add_le_add leadingPowerCeiling xiPowerCeiling)) _)
  have completeBound :
      regularWeightNat factor factorNeZero tau
          (sourceRecurrenceTerm factor index xi beta auxiliary) ≤
        ((index.s + index.epsilon - 1) * w +
              (2 * index.s + index.q - 2) * sigma +
            regularWeightNat factor factorNeZero tau auxiliary) +
          (index.q * tau + index.n * w +
            (2 * index.n - index.q) * sigma) := by
    unfold sourceRecurrenceTerm
    exact thirdMul.trans (Nat.add_le_add prefixBound recursiveProductBound)
  exact completeBound.trans <|
    source_recurrence_term_ceiling DR ell d b tau mu sigma w t tPositive
      index (regularWeightNat factor factorNeZero tau auxiliary) ellLe
      dPositive wLeMu tauEq muEq sigmaEq ellQLe qLeD auxiliaryBound

/-- Strong-induction form of the corrected estimate for the original
numerators `beta_t`.  The recurrence is stated literally in the regular
quotient; all recursive indices are certified earlier by `SourceTermIndex`. -/
theorem corrected_source_hensel_estimate_nat
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0)
    (ell DH DR d b tau mu sigma w : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (wEq : w = factor.leadingCoeff.natDegree)
    (ellLe : ell ≤ DR) (dPositive : 1 ≤ d) (wLeMu : w ≤ mu)
    (tauEq : tau = b + ell)
    (muEq : mu = (DR - ell) + (d - 1) * b)
    (sigmaEq : sigma = mu - w)
    (xi : RegularQuotient factor)
    (xiBound : regularWeightNat factor factorNeZero tau xi ≤ sigma)
    (beta : Nat → RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (SourceTermIndex t tPositive))
    (auxiliary : ∀ (t : Nat) (tPositive : 0 < t),
      SourceTermIndex t tPositive → RegularQuotient factor)
    (base : beta 0 = AdjoinRoot.root (monicization factor))
    (recurrence : ∀ (t : Nat) (tPositive : 0 < t),
      beta t = ∑ index ∈ terms t tPositive,
        sourceRecurrenceTerm factor index xi beta
          (auxiliary t tPositive index))
    (admissible : ∀ (t : Nat) (tPositive : 0 < t)
      (index : SourceTermIndex t tPositive), index ∈ terms t tPositive →
        index.q ≤ d ∧ ell * index.q ≤ DR ∧
          (auxiliary t tPositive index = 0 ∨
            index.epsilon * w + regularWeightNat factor factorNeZero tau
                (auxiliary t tPositive index) ≤
              DR - ell * index.q + (d - index.q) * b)) :
    ∀ t : Nat, regularWeightNat factor factorNeZero tau (beta t) ≤
      sourceNumeratorCeiling tau w sigma t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t induction =>
      by_cases tZero : t = 0
      · subst t
        rw [base, sourceNumeratorCeiling_zero]
        have rootBound := regularWeightNat_root_le factor factorNeZero ell DH
          factorCoefficientBound
        simpa [generatorWeightEq] using rootBound
      · have tPositive : 0 < t := Nat.pos_of_ne_zero tZero
        rw [recurrence t tPositive]
        apply regularWeightNat_finset_sum_le factor factorNeZero tau
          (sourceNumeratorCeiling tau w sigma t) (terms t tPositive)
        intro index indexMem
        obtain ⟨qLeD, ellQLe, auxiliaryBound⟩ :=
          admissible t tPositive index indexMem
        apply sourceRecurrenceTerm_weight_le factor factorNeZero ell DH DR d b
          tau mu sigma w t tPositive factorCoefficientBound generatorWeightEq
          wEq ellLe dPositive wLeMu tauEq muEq sigmaEq index qLeD ellQLe xi
          xiBound beta
        · intro recursiveIndex recursiveMem
          exact induction recursiveIndex.1
            (index.recursive_index_lt recursiveIndex recursiveMem)
        · exact auxiliaryBound

/-- Paper-facing `WithBot` statement: `Lambda(beta_t) ≤ P_t`, with
`Lambda(0)=-infinity`. -/
theorem corrected_source_hensel_estimate
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0)
    (ell DH DR d b tau mu sigma w : Nat)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ DH)
    (generatorWeightEq : DH + ell - ell * factor.natDegree = tau)
    (wEq : w = factor.leadingCoeff.natDegree)
    (ellLe : ell ≤ DR) (dPositive : 1 ≤ d) (wLeMu : w ≤ mu)
    (tauEq : tau = b + ell)
    (muEq : mu = (DR - ell) + (d - 1) * b)
    (sigmaEq : sigma = mu - w)
    (xi : RegularQuotient factor)
    (xiBound : regularWeightNat factor factorNeZero tau xi ≤ sigma)
    (beta : Nat → RegularQuotient factor)
    (terms : ∀ (t : Nat) (tPositive : 0 < t),
      Finset (SourceTermIndex t tPositive))
    (auxiliary : ∀ (t : Nat) (tPositive : 0 < t),
      SourceTermIndex t tPositive → RegularQuotient factor)
    (base : beta 0 = AdjoinRoot.root (monicization factor))
    (recurrence : ∀ (t : Nat) (tPositive : 0 < t),
      beta t = ∑ index ∈ terms t tPositive,
        sourceRecurrenceTerm factor index xi beta
          (auxiliary t tPositive index))
    (admissible : ∀ (t : Nat) (tPositive : 0 < t)
      (index : SourceTermIndex t tPositive), index ∈ terms t tPositive →
        index.q ≤ d ∧ ell * index.q ≤ DR ∧
          (auxiliary t tPositive index = 0 ∨
            index.epsilon * w + regularWeightNat factor factorNeZero tau
                (auxiliary t tPositive index) ≤
              DR - ell * index.q + (d - index.q) * b))
    (t : Nat) :
    regularWeight factor factorNeZero tau (beta t) ≤
      (sourceNumeratorCeiling tau w sigma t : Nat) := by
  have rawBound := corrected_source_hensel_estimate_nat factor factorNeZero ell
    DH DR d b tau mu sigma w factorCoefficientBound generatorWeightEq wEq ellLe
    dPositive wLeMu tauEq muEq sigmaEq xi xiBound beta terms auxiliary base
    recurrence admissible t
  by_cases betaZero : beta t = 0
  · simp [betaZero]
  · rw [regularWeight_eq_coe factor factorNeZero tau betaZero]
    exact WithBot.coe_le_coe.mpr rawBound

#print axioms shiftedParentCoefficient_zero
#print axioms shiftedParentCoefficient_bound
#print axioms sourceClearedRepresentative_weight_le
#print axioms leadingCoeff_dvd_sourceClearedRepresentative_zero
#print axioms exists_sourceAuxiliaryNumerator
#print axioms exists_sourceDerivativeNumerator
#print axioms sourceNumeratorCeiling_eq
#print axioms source_recurrence_term_ceiling
#print axioms sourceRecursiveProduct_weight_le
#print axioms sourceRecurrenceTerm_weight_le
#print axioms corrected_source_hensel_estimate_nat
#print axioms corrected_source_hensel_estimate

end

end WeightedHensel

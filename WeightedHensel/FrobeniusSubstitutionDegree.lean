/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.FrobeniusFactorTransfer
import WeightedHensel.PowerSeriesLift

/-!
# The `(1,k,0)` substitution-degree argument

The paper's global `(1,k,0)`-weighted degree hypothesis is exactly the
finite-degree hypothesis needed to turn Hensel truncation into an exact
polynomial root.  This file proves that implication rather than exposing
it as an additional terminal assumption.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial

noncomputable section

/-- Swapping `X` and `Z` commutes with scalar extension. -/
theorem swap_map_mapRingHom
    {K L : Type*} [Field K] [Field L]
    (base : K →+* L) (polynomial : BivariatePolynomial K) :
    Polynomial.Bivariate.swap
        (polynomial.map (Polynomial.mapRingHom base)) =
      (Polynomial.Bivariate.swap polynomial).map
        (Polynomial.mapRingHom base) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      simp only [Polynomial.map_add]
      rw [map_add, map_add, leftIH, rightIH]
      exact (Polynomial.map_add
        (f := Polynomial.mapRingHom base)).symm
  | monomial exponent coefficient =>
      rw [Polynomial.map_monomial, Polynomial.Bivariate.swap_monomial,
        Polynomial.Bivariate.swap_monomial]
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map]
      congr 1
      · ext value
        simp
      · rw [Polynomial.coe_mapRingHom]
        congr 1
        symm
        rw [Polynomial.map_pow, Polynomial.map_X]

/-- Evaluating the second variable at a constant is the same as swapping
the variables and mapping the now-coefficient variable by evaluation. -/
theorem eval_constant_eq_map_swap
    {L : Type*} [Field L]
    (value : L) (polynomial : BivariatePolynomial L) :
    polynomial.eval (Polynomial.C value) =
      (Polynomial.Bivariate.swap polynomial).map
        (Polynomial.evalRingHom value) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      simp only [Polynomial.eval_add, map_add, leftIH, rightIH]
      exact (Polynomial.map_add
        (f := Polynomial.evalRingHom value)).symm
  | monomial exponent coefficient =>
      rw [Polynomial.eval_monomial, Polynomial.Bivariate.swap_monomial,
        Polynomial.map_mul, Polynomial.map_C]
      have composition :
          (Polynomial.evalRingHom value).comp Polynomial.C =
            RingHom.id L := by
        ext scalar
        simp
      rw [Polynomial.map_map, composition, Polynomial.map_id]
      congr 1
      have evalPower :
          (Polynomial.evalRingHom value) (Polynomial.X ^ exponent) =
            value ^ exponent := by
        rw [map_pow, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      rw [evalPower]
      exact (map_pow
        (Polynomial.C : L →+* Polynomial L) value exponent).symm

/-- Specializing `Z` and translating `X` cannot increase the `X` degree
of one `Y` coefficient beyond the literal swapped coefficient degree. -/
theorem functionFieldPolynomialParent_coeff_natDegree_le_swap
    {K : Type*} [Field K]
    (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (yExponent : Nat) :
    ((functionFieldPolynomialParent parent factor x₀).coeff
        yExponent).natDegree ≤
      (Polynomial.Bivariate.swap
        (parent.coeff yExponent)).natDegree := by
  simp only [functionFieldPolynomialParent, specializeChallenge,
    Polynomial.coeff_map, functionFieldParent, mapTrivariateCoefficients]
  change (Polynomial.taylor (branchBaseMap factor x₀)
      (((parent.coeff yExponent).map
        (Polynomial.mapRingHom (branchBaseMap factor))).eval
          (Polynomial.C (branchChallenge factor)))).natDegree ≤ _
  rw [Polynomial.natDegree_taylor, eval_constant_eq_map_swap]
  calc
    _ ≤ (Polynomial.Bivariate.swap
        ((parent.coeff yExponent).map
          (Polynomial.mapRingHom (branchBaseMap factor)))).natDegree :=
      Polynomial.natDegree_map_le
    _ = _ := by
      rw [swap_map_mapRingHom]
      exact Polynomial.natDegree_map_eq_of_injective
        (Polynomial.map_injective (branchBaseMap factor)
          (branchBaseMap factor).injective)
        (Polynomial.Bivariate.swap (parent.coeff yExponent))

/-- Substituting a polynomial of degree at most `weight` into the outer
variable has degree bounded by the local bivariate weight. -/
theorem natDegree_eval_le_localBivariateWeight
    {L : Type*} [Field L]
    (weight : Nat) (polynomial : BivariatePolynomial L)
    (value : Polynomial L) (valueDegree : value.natDegree ≤ weight) :
    (polynomial.eval value).natDegree ≤
      localBivariateWeight weight polynomial := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent exponentMem
  calc
    (polynomial.coeff exponent * value ^ exponent).natDegree ≤
        (polynomial.coeff exponent).natDegree +
          (value ^ exponent).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (polynomial.coeff exponent).natDegree +
          exponent * value.natDegree :=
      Nat.add_le_add_left Polynomial.natDegree_pow_le _
    _ ≤ (polynomial.coeff exponent).natDegree +
          exponent * weight :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left exponent valueDegree) _
    _ ≤ localBivariateWeight weight polynomial :=
      coeff_weight_le_localBivariateWeight weight polynomial exponent
        exponentMem

/-- The function-field parent substitution is bounded by the paper's
literal `(1,weight,0)` weighted degree. -/
theorem functionFieldPolynomialParent_eval_natDegree_le_fullXYWeightedDegree
    {K : Type*} [Field K]
    (parent : TrivariatePolynomial K)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) (weight : Nat)
    (value : Polynomial (BranchFunctionField factor))
    (valueDegree : value.natDegree ≤ weight) :
    ((functionFieldPolynomialParent parent factor x₀).eval
        value).natDegree ≤ fullXYWeightedDegree weight parent := by
  have evaluationBound := natDegree_eval_le_localBivariateWeight weight
    (functionFieldPolynomialParent parent factor x₀) value valueDegree
  apply evaluationBound.trans
  apply localBivariateWeight_le_of_coeff
  intro yExponent yMem
  have currentCoefficientNeZero :
      (functionFieldPolynomialParent parent factor x₀).coeff
          yExponent ≠ 0 :=
    Polynomial.mem_support_iff.mp yMem
  have parentCoefficientNeZero : parent.coeff yExponent ≠ 0 := by
    intro parentCoefficientZero
    apply currentCoefficientNeZero
    simp [functionFieldPolynomialParent, specializeChallenge,
      functionFieldParent, mapTrivariateCoefficients,
      parentCoefficientZero]
  have swappedCoefficientNeZero :
      Polynomial.Bivariate.swap (parent.coeff yExponent) ≠ 0 :=
    by
      simpa using
        (Polynomial.Bivariate.swap (R := K)).injective.ne
          parentCoefficientNeZero
  have swappedCoefficient :
      (swapXZEquiv parent).coeff yExponent =
        Polynomial.Bivariate.swap (parent.coeff yExponent) := by
    simp [swapXZEquiv, Polynomial.coe_mapAlgEquiv]
  have swappedSupport :
      yExponent ∈ (swapXZEquiv parent).support := by
    apply Polynomial.mem_support_iff.mpr
    rw [swappedCoefficient]
    exact swappedCoefficientNeZero
  calc
    ((functionFieldPolynomialParent parent factor x₀).coeff
          yExponent).natDegree + yExponent * weight ≤
        (Polynomial.Bivariate.swap
            (parent.coeff yExponent)).natDegree +
          yExponent * weight :=
      Nat.add_le_add_right
        (functionFieldPolynomialParent_coeff_natDegree_le_swap
          parent factor x₀ yExponent) _
    _ ≤ localBivariateWeight weight (swapXZEquiv parent) :=
      by
        rw [← swappedCoefficient]
        exact coeff_weight_le_localBivariateWeight weight
          (swapXZEquiv parent) yExponent swappedSupport
    _ = fullXYWeightedDegree weight parent := rfl

/-- Swapping `X,Z` commutes with expansion of the response exponent. -/
theorem swapXZEquiv_expandResponse
    {K : Type*} [Field K]
    (q : Nat) (parent : TrivariatePolynomial K) :
    swapXZEquiv (expandResponse q parent) =
      Polynomial.expand (BivariatePolynomial K) q (swapXZEquiv parent) := by
  unfold swapXZEquiv expandResponse
  rw [Polynomial.coe_mapAlgEquiv]
  exact Polynomial.map_expand

/-- Weighting the expanded response variable by `k` dominates weighting
the separable response variable by `q*k`. -/
theorem fullXYWeightedDegree_le_expandResponse
    {K : Type*} [Field K]
    (q k : Nat) (qPositive : 0 < q)
    (parent : TrivariatePolynomial K) :
    fullXYWeightedDegree (q * k) parent ≤
      fullXYWeightedDegree k (expandResponse q parent) := by
  unfold fullXYWeightedDegree
  rw [swapXZEquiv_expandResponse]
  apply localBivariateWeight_le_of_coeff
  intro yExponent yMem
  have expandedCoefficient :=
    Polynomial.coeff_expand_mul qPositive (swapXZEquiv parent) yExponent
  have expandedSupport : yExponent * q ∈
      (Polynomial.expand (BivariatePolynomial K) q
        (swapXZEquiv parent)).support := by
    apply Polynomial.mem_support_iff.mpr
    rw [expandedCoefficient]
    exact Polynomial.mem_support_iff.mp yMem
  have expandedBound := coeff_weight_le_localBivariateWeight k
    (Polynomial.expand (BivariatePolynomial K) q (swapXZEquiv parent))
    (yExponent * q) expandedSupport
  rw [expandedCoefficient] at expandedBound
  calc
    ((swapXZEquiv parent).coeff yExponent).natDegree +
          yExponent * (q * k) =
        ((swapXZEquiv parent).coeff yExponent).natDegree +
          (yExponent * q) * k := by ring
    _ ≤ _ := expandedBound

/-- Each positive-multiplicity expanded factor has `(1,k,0)` weight below
the global interpolant cutoff. -/
theorem expandedFactor_fullXYWeightedDegree_lt_global
    {K I : Type*} [Field K] [DecidableEq I]
    (indices : Finset I) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (parent : I → TrivariatePolynomial K)
    (q multiplicity : I → Nat)
    (contentNeZero : content ≠ 0)
    (parentNeZero : ∀ index, index ∈ indices → parent index ≠ 0)
    (qPositive : ∀ index, index ∈ indices → 0 < q index)
    (multiplicityPositive :
      ∀ index, index ∈ indices → 1 ≤ multiplicity index)
    (globalFactorization : Q = Polynomial.C content *
      ∏ index ∈ indices,
        expandResponse (q index) (parent index) ^ multiplicity index)
    (k DX : Nat) (globalDegreeLt : fullXYWeightedDegree k Q < DX)
    (index : I) (indexMem : index ∈ indices) :
    fullXYWeightedDegree k
        (expandResponse (q index) (parent index)) < DX := by
  have exactSum := fullFactor_XY_weight_summation indices Q content
    (fun candidateIndex =>
      expandResponse (q candidateIndex) (parent candidateIndex))
    multiplicity contentNeZero
    (fun candidateIndex candidateMem =>
      expandResponse_ne_zero (q candidateIndex)
        (qPositive candidateIndex candidateMem)
        (parent candidateIndex) (parentNeZero candidateIndex candidateMem))
    globalFactorization k
  have oneFactorLe :
      fullXYWeightedDegree k
          (expandResponse (q index) (parent index)) ≤
        fullXYWeightedDegree k Q := by
    rw [exactSum]
    calc
      fullXYWeightedDegree k
          (expandResponse (q index) (parent index)) ≤
        multiplicity index *
          fullXYWeightedDegree k
            (expandResponse (q index) (parent index)) := by
          calc
            _ = 1 * fullXYWeightedDegree k
                (expandResponse (q index) (parent index)) := by ring
            _ ≤ _ := Nat.mul_le_mul_right _
              (multiplicityPositive index indexMem)
      _ ≤ ∑ candidateIndex ∈ indices,
          multiplicity candidateIndex *
            fullXYWeightedDegree k
              (expandResponse (q candidateIndex)
                (parent candidateIndex)) :=
        Finset.single_le_sum
          (f := fun candidateIndex =>
            multiplicity candidateIndex *
              fullXYWeightedDegree k
                (expandResponse (q candidateIndex)
                  (parent candidateIndex)))
          (fun _ _ => Nat.zero_le _) indexMem
      _ ≤ fullXYWeightedDegree k (Polynomial.C content) +
          ∑ candidateIndex ∈ indices,
            multiplicity candidateIndex *
              fullXYWeightedDegree k
                (expandResponse (q candidateIndex)
                  (parent candidateIndex)) :=
        Nat.le_add_left _ _
  exact oneFactorLe.trans_lt globalDegreeLt

/-- Paper-facing substitution bound obtained solely from the global
factorization and `(1,k,0)` weighted-degree hypothesis. -/
theorem frobenius_substitutionDegreeBound
    {K I : Type*} [Field K] [DecidableEq I]
    (indices : Finset I) (Q : TrivariatePolynomial K)
    (content : BivariatePolynomial K)
    (parent : I → TrivariatePolynomial K)
    (q multiplicity : I → Nat)
    (contentNeZero : content ≠ 0)
    (parentNeZero : ∀ index, index ∈ indices → parent index ≠ 0)
    (qPositive : ∀ index, index ∈ indices → 0 < q index)
    (multiplicityPositive :
      ∀ index, index ∈ indices → 1 ≤ multiplicity index)
    (globalFactorization : Q = Polynomial.C content *
      ∏ index ∈ indices,
        expandResponse (q index) (parent index) ^ multiplicity index)
    (k DX : Nat) (globalDegreeLt : fullXYWeightedDegree k Q < DX)
    (index : I) (indexMem : index ∈ indices)
    (factor : BivariatePolynomial K)
    [Fact (Irreducible (branchPolynomial factor))]
    (x₀ : K) :
    ∀ gamma : Polynomial (BranchFunctionField factor),
      gamma.natDegree ≤ q index * k →
        ((functionFieldPolynomialParent (parent index) factor x₀).eval
          gamma).natDegree < DX := by
  intro gamma gammaDegree
  have localBound :=
    functionFieldPolynomialParent_eval_natDegree_le_fullXYWeightedDegree
      (parent index) factor x₀ (q index * k) gamma gammaDegree
  have expandBound := fullXYWeightedDegree_le_expandResponse
    (q index) k (qPositive index indexMem) (parent index)
  have factorLt := expandedFactor_fullXYWeightedDegree_lt_global
    indices Q content parent q multiplicity contentNeZero parentNeZero
    qPositive multiplicityPositive globalFactorization k DX globalDegreeLt
    index indexMem
  exact localBound.trans_lt (expandBound.trans_lt factorLt)

#print axioms functionFieldPolynomialParent_eval_natDegree_le_fullXYWeightedDegree
#print axioms fullXYWeightedDegree_le_expandResponse
#print axioms expandedFactor_fullXYWeightedDegree_lt_global
#print axioms frobenius_substitutionDegreeBound

end

end WeightedHensel

/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.CommonNumerator
import WeightedHensel.Incidence
import Mathlib.LinearAlgebra.Lagrange

/-!
# Coefficientwise interpolation from heavy coordinates

The received challenge polynomials at `m+1` heavy coordinates are
interpolated coefficientwise in the codeword variable.  This module proves
both the function-field identity for the truncated branch and the resulting
base-field identity for every surviving challenge.
-/

set_option autoImplicit false

namespace WeightedHensel

open Polynomial
open scoped BigOperators

noncomputable section

/-- The degree-`j` challenge coefficient, interpolated as a polynomial in
the codeword coordinate. -/
def lagrangeCoefficientCurve
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (received : Domain → Polynomial K) (j : Nat) : Polynomial K :=
  Lagrange.interpolate nodes points fun node ↦ (received node).coeff j

/-- Each coefficient curve has degree at most `m` when there are exactly
`m+1` interpolation nodes. -/
theorem lagrangeCoefficientCurve_natDegree_le
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (received : Domain → Polynomial K) (m j : Nat)
    (nodesCard : nodes.card = m + 1) :
    (lagrangeCoefficientCurve nodes points received j).natDegree ≤ m := by
  apply Polynomial.natDegree_le_iff_degree_le.mpr
  calc
    (lagrangeCoefficientCurve nodes points received j).degree ≤
        (nodes.card - 1 : Nat) := by
      exact Lagrange.degree_interpolate_le
        (fun node ↦ (received node).coeff j) pointsInjectiveOn
    _ = (m : WithBot Nat) := by rw [nodesCard]; simp

/-- At an interpolation node, the coefficient curve returns the literal
challenge coefficient of the received polynomial. -/
theorem lagrangeCoefficientCurve_eval_at_node
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (received : Domain → Polynomial K) (j : Nat)
    (node : Domain) (nodeMem : node ∈ nodes) :
    (lagrangeCoefficientCurve nodes points received j).eval (points node) =
      (received node).coeff j := by
  exact Lagrange.eval_interpolate_at_node
    (fun coordinate ↦ (received coordinate).coeff j)
    pointsInjectiveOn nodeMem

/-- The base-field curve obtained from the coefficient polynomials. -/
def candidateCurve
    {K : Type*} [Field K] (coefficientCurve : Nat → Polynomial K)
    (M : Nat) (z : K) : Polynomial K :=
  ∑ j ∈ Finset.range (M + 1),
    Polynomial.C (z ^ j) * coefficientCurve j

/-- The corresponding polynomial over the fixed branch function field,
where `Z` is the transcendental challenge element. -/
def functionFieldCoefficientCurve
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (factor : BivariatePolynomial K)
    (nodes : Finset Domain) (points : Domain → K)
    (received : Domain → Polynomial K) (M : Nat) :
    Polynomial (BranchFunctionField factor) :=
  ∑ j ∈ Finset.range (M + 1),
    Polynomial.C (branchChallenge factor ^ j) *
      (lagrangeCoefficientCurve nodes points received j).map
        (branchBaseMap factor)

/-- Evaluation at a selected node recovers the embedded received challenge
polynomial. -/
theorem functionFieldCoefficientCurve_eval_at_node
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (factor : BivariatePolynomial K)
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (received : Domain → Polynomial K) (M : Nat)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ M)
    (node : Domain) (nodeMem : node ∈ nodes) :
    (functionFieldCoefficientCurve factor nodes points received M).eval
        (branchBaseMap factor (points node)) =
      regularCoefficientMap factor (received node) := by
  classical
  unfold functionFieldCoefficientCurve
  rw [Polynomial.eval_finsetSum]
  rw [regularCoefficientMap_eq_eval₂]
  have degreeLt : (received node).natDegree < M + 1 := by
    exact Nat.lt_succ_of_le (receivedDegree node)
  rw [Polynomial.eval₂_eq_sum_range' (branchBaseMap factor) degreeLt
    (branchChallenge factor)]
  apply Finset.sum_congr rfl
  intro j jMem
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_map_apply]
  rw [lagrangeCoefficientCurve_eval_at_node nodes points pointsInjectiveOn
    received j node nodeMem]
  ring

/-- The function-field coefficient curve has degree at most `m` in the
codeword variable. -/
theorem functionFieldCoefficientCurve_natDegree_le
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (factor : BivariatePolynomial K)
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (received : Domain → Polynomial K) (M m : Nat)
    (nodesCard : nodes.card = m + 1) :
    (functionFieldCoefficientCurve factor nodes points received M).natDegree ≤
      m := by
  classical
  unfold functionFieldCoefficientCurve
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j jMem
  exact (Polynomial.natDegree_C_mul_le _ _).trans <|
    Polynomial.natDegree_map_le.trans <|
      lagrangeCoefficientCurve_natDegree_le nodes points pointsInjectiveOn
        received m j nodesCard

/-- A centered truncation through order `m` has degree at most `m`. -/
theorem centeredCoefficientTruncation_natDegree_le
    {K L : Type*} [Field K] [Field L] (baseMap : K →+* L) (x₀ : K)
    (alpha : Nat → L) (m : Nat) :
    (centeredCoefficientTruncation baseMap x₀ alpha m).natDegree ≤ m := by
  classical
  unfold centeredCoefficientTruncation
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro t tMem
  refine Polynomial.natDegree_mul_le.trans ?_
  have tLeM : t ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp tMem)
  calc
    (Polynomial.C (alpha t)).natDegree +
        ((Polynomial.X - Polynomial.C (baseMap x₀)) ^ t).natDegree ≤
        0 + t := by
      exact Nat.add_le_add (by rw [Polynomial.natDegree_C])
        (Polynomial.natDegree_pow_le.trans (by
          have bound := Nat.mul_le_mul_left t
            (Polynomial.natDegree_X_sub_C_le (baseMap x₀))
          rw [Nat.mul_one] at bound
          exact bound))
    _ ≤ m := by simpa using tLeM

/-- The coefficient embedding of the ground field is injective. -/
theorem branchBaseMap_injective
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) :
    Function.Injective (branchBaseMap factor) := by
  intro left right equality
  apply Polynomial.C_injective
  apply regularCoefficientMap_injective factor factorPositive
  simpa [branchBaseMap] using equality

/-- Equality at `m+1` heavy coordinates identifies the whole truncated
branch with the coefficientwise-interpolated curve. -/
theorem centeredCoefficientTruncation_eq_functionFieldCoefficientCurve
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree)
    [Fact (Irreducible (branchPolynomial factor))]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (received : Domain → Polynomial K) (M m : Nat)
    (nodesCard : nodes.card = m + 1)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ M)
    (x₀ : K) (alpha : Nat → BranchFunctionField factor)
    (matchesNodes : ∀ node ∈ nodes,
      (centeredCoefficientTruncation (branchBaseMap factor) x₀ alpha m).eval
          (branchBaseMap factor (points node)) =
        regularCoefficientMap factor (received node)) :
    centeredCoefficientTruncation (branchBaseMap factor) x₀ alpha m =
      functionFieldCoefficientCurve factor nodes points received M := by
  let mappedPoints := fun node ↦ branchBaseMap factor (points node)
  have mappedPointsInjectiveOn : Set.InjOn mappedPoints nodes :=
    (branchBaseMap_injective factor factorPositive).comp_injOn pointsInjectiveOn
  have truncDegreeLt :
      (centeredCoefficientTruncation (branchBaseMap factor) x₀ alpha m).degree <
        (nodes.card : WithBot Nat) := by
    calc
      _ ≤ (m : WithBot Nat) :=
        Polynomial.degree_le_of_natDegree_le
          (centeredCoefficientTruncation_natDegree_le
            (branchBaseMap factor) x₀ alpha m)
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self m
  have curveDegreeLt :
      (functionFieldCoefficientCurve factor nodes points received M).degree <
        (nodes.card : WithBot Nat) := by
    calc
      _ ≤ (m : WithBot Nat) :=
        Polynomial.degree_le_of_natDegree_le
          (functionFieldCoefficientCurve_natDegree_le factor nodes points
            pointsInjectiveOn received M m nodesCard)
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self m
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq nodes
    mappedPointsInjectiveOn truncDegreeLt curveDegreeLt
  intro node nodeMem
  rw [functionFieldCoefficientCurve_eval_at_node factor nodes points
    pointsInjectiveOn received M receivedDegree node nodeMem]
  exact matchesNodes node nodeMem

/-- At every node, the ordinary candidate curve evaluates to the received
challenge polynomial. -/
theorem candidateCurve_eval_at_node
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (received : Domain → Polynomial K) (M : Nat)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ M)
    (z : K) (node : Domain) (nodeMem : node ∈ nodes) :
    (candidateCurve
        (lagrangeCoefficientCurve nodes points received) M z).eval
        (points node) = (received node).eval z := by
  classical
  unfold candidateCurve
  rw [Polynomial.eval_finsetSum]
  have degreeLt : (received node).natDegree < M + 1 :=
    Nat.lt_succ_of_le (receivedDegree node)
  rw [Polynomial.eval_eq_sum_range' degreeLt z]
  apply Finset.sum_congr rfl
  intro j jMem
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [lagrangeCoefficientCurve_eval_at_node nodes points pointsInjectiveOn
    received j node nodeMem]
  ring

/-- A degree-`m` candidate agreeing with the received challenge polynomial
on `m+1` nodes is exactly the specialization of the coefficient curve. -/
theorem candidate_eq_candidateCurve
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjectiveOn : Set.InjOn points nodes)
    (received : Domain → Polynomial K) (M m : Nat)
    (nodesCard : nodes.card = m + 1)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ M)
    (z : K) (candidate : Polynomial K)
    (candidateDegree : candidate.natDegree ≤ m)
    (matchesNodes : ∀ node ∈ nodes,
      candidate.eval (points node) = (received node).eval z) :
    candidate = candidateCurve
      (lagrangeCoefficientCurve nodes points received) M z := by
  have rightDegree :
      (candidateCurve
          (lagrangeCoefficientCurve nodes points received) M z).natDegree ≤ m := by
    classical
    unfold candidateCurve
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j jMem
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (lagrangeCoefficientCurve_natDegree_le nodes points pointsInjectiveOn
        received m j nodesCard)
  have leftDegreeLt : candidate.degree < (nodes.card : WithBot Nat) := by
    calc
      _ ≤ (m : WithBot Nat) :=
        Polynomial.degree_le_of_natDegree_le candidateDegree
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self m
  have rightDegreeLt :
      (candidateCurve
          (lagrangeCoefficientCurve nodes points received) M z).degree <
        (nodes.card : WithBot Nat) := by
    calc
      _ ≤ (m : WithBot Nat) :=
        Polynomial.degree_le_of_natDegree_le rightDegree
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self m
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq nodes
    pointsInjectiveOn leftDegreeLt rightDegreeLt
  intro node nodeMem
  rw [candidateCurve_eval_at_node nodes points pointsInjectiveOn received M
    receivedDegree z node nodeMem]
  exact matchesNodes node nodeMem

#print axioms lagrangeCoefficientCurve_natDegree_le
#print axioms lagrangeCoefficientCurve_eval_at_node
#print axioms functionFieldCoefficientCurve_eval_at_node
#print axioms functionFieldCoefficientCurve_natDegree_le
#print axioms centeredCoefficientTruncation_natDegree_le
#print axioms centeredCoefficientTruncation_eq_functionFieldCoefficientCurve
#print axioms candidateCurve_eval_at_node
#print axioms candidate_eq_candidateCurve

end

end WeightedHensel

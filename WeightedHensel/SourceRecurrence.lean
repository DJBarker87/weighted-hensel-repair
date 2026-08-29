/-
Copyright (c) 2026 Dominic Barker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Barker
-/

import WeightedHensel.RegularQuotient
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Order

/-!
# The source-style Hensel recurrence indices

This file formalizes the partition data in recurrence (A.1)/(34). A
partition records only positive coefficient indices. Consequently its order
is `∑ r λr` and its size is `q = ∑ λr` without a separate side condition
excluding index zero.
-/

set_option autoImplicit false

namespace WeightedHensel

open scoped BigOperators

noncomputable section

/-- Positive Hensel coefficient indices. -/
abbrev PositiveIndex := {r : Nat // 0 < r}

/-- A finite multiplicity function `λ = (λr)_{r≥1}`. -/
abbrev SourcePartition := PositiveIndex →₀ Nat

/-- The total `U`-order `n = ∑ r λr`. -/
def partitionOrder (partition : SourcePartition) : Nat :=
  partition.sum fun index multiplicity ↦ index.1 * multiplicity

/-- The number of coefficient factors `q = |λ| = ∑ λr`. -/
def partitionSize (partition : SourcePartition) : Nat :=
  partition.sum fun _ multiplicity ↦ multiplicity

/-- The total derivative-denominator exponent contributed by the recursive
coefficient product. -/
def partitionHenselExponent (partition : SourcePartition) : Nat :=
  partition.sum fun index multiplicity ↦
    multiplicity * henselExponent index.1

/-- The partition with one occurrence of coefficient `t`. -/
def singletonPartition (t : Nat) (tPositive : 0 < t) : SourcePartition :=
  Finsupp.single ⟨t, tPositive⟩ 1

@[simp] theorem partitionSize_zero : partitionSize 0 = 0 := by
  simp [partitionSize]

@[simp] theorem partitionOrder_zero : partitionOrder 0 = 0 := by
  simp [partitionOrder]

@[simp] theorem partitionSize_singleton
    (t : Nat) (tPositive : 0 < t) :
    partitionSize (singletonPartition t tPositive) = 1 := by
  simp [partitionSize, singletonPartition]

@[simp] theorem partitionOrder_singleton
    (t : Nat) (tPositive : 0 < t) :
    partitionOrder (singletonPartition t tPositive) = t := by
  simp [partitionOrder, singletonPartition]

/-- A partition has no more parts than total positive order. -/
theorem partitionSize_le_order (partition : SourcePartition) :
    partitionSize partition ≤ partitionOrder partition := by
  unfold partitionSize partitionOrder
  apply Finsupp.sum_le_sum
  intro index _
  exact Nat.le_mul_of_pos_left _ index.2

/-- Size zero forces the empty partition. -/
theorem partition_eq_zero_of_size_eq_zero
    {partition : SourcePartition} (sizeZero : partitionSize partition = 0) :
    partition = 0 := by
  apply Finsupp.ext
  intro index
  simp only [Finsupp.zero_apply]
  by_contra valueNeZero
  have singleLe := Finsupp.single_le_sum partition
    (g := fun _ multiplicity ↦ multiplicity)
    (fun _ _ ↦ Nat.zero_le _) index
  have valueLe : partition index ≤ partitionSize partition := by
    simpa [partitionSize] using singleLe
  omega

/-- Order zero forces the empty partition. -/
theorem partition_eq_zero_of_order_eq_zero
    {partition : SourcePartition} (orderZero : partitionOrder partition = 0) :
    partition = 0 := by
  apply partition_eq_zero_of_size_eq_zero
  have := partitionSize_le_order partition
  omega

/-- The exact denominator-exponent identity for a source partition. -/
theorem partitionHenselExponent_add_size
    (partition : SourcePartition) :
    partitionHenselExponent partition + partitionSize partition =
      2 * partitionOrder partition := by
  classical
  unfold partitionHenselExponent partitionSize partitionOrder
  change
    (∑ index ∈ partition.support,
      partition index * henselExponent index.1) +
      ∑ index ∈ partition.support, partition index =
        2 * ∑ index ∈ partition.support, index.1 * partition index
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index indexMem
  have indexPositive := index.2
  simp only [henselExponent]
  have exponentSucc : 2 * index.1 - 1 + 1 = 2 * index.1 := by omega
  calc
    partition index * (2 * index.1 - 1) + partition index =
        partition index * ((2 * index.1 - 1) + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ = partition index * (2 * index.1) := by rw [exponentSucc]
    _ = 2 * (index.1 * partition index) := by ring

/-- Therefore the product contributes exactly `2n-q`. -/
theorem partitionHenselExponent_eq
    (partition : SourcePartition) :
    partitionHenselExponent partition =
      2 * partitionOrder partition - partitionSize partition := by
  have identity := partitionHenselExponent_add_size partition
  omega

/-- A size-one partition is a unique singleton. -/
theorem partitionSize_eq_one_iff (partition : SourcePartition) :
    partitionSize partition = 1 ↔
      ∃ index : PositiveIndex, partition = Finsupp.single index 1 := by
  exact Finsupp.sum_eq_one_iff partition

/-- If a positive part consumes the entire order, no other part occurs. -/
theorem partition_eq_single_of_full_part
    (partition : SourcePartition) (index : PositiveIndex)
    (indexMem : index ∈ partition.support)
    (indexFull : index.1 = partitionOrder partition) :
    partition = Finsupp.single index 1 := by
  have valueNeZero : partition index ≠ 0 := Finsupp.mem_support_iff.mp indexMem
  have orderTermLe := Finsupp.single_le_sum partition
    (g := fun candidate multiplicity ↦ candidate.1 * multiplicity)
    (fun _ _ ↦ Nat.zero_le _) index
  have termLe : index.1 * partition index ≤ partitionOrder partition := by
    simpa [partitionOrder] using orderTermLe
  have valueOne : partition index = 1 := by
    have indexPositive := index.2
    have valuePositive : 0 < partition index := Nat.pos_of_ne_zero valueNeZero
    have valueLeOne : partition index ≤ 1 := by
      rw [← Nat.mul_le_mul_left_iff indexPositive]
      simpa [indexFull] using termLe
    omega
  have sizePositive : 0 < partitionSize partition := by
    have sizeSingleLe := Finsupp.single_le_sum partition
      (g := fun _ multiplicity ↦ multiplicity)
      (fun _ _ ↦ Nat.zero_le _) index
    have : partition index ≤ partitionSize partition := by
      simpa [partitionSize] using sizeSingleLe
    omega
  have sizeLeOne : partitionSize partition ≤ 1 := by
    let excess := partition.sum fun candidate multiplicity ↦
      (candidate.1 - 1) * multiplicity
    have orderSplit : partitionOrder partition = partitionSize partition + excess := by
      classical
      unfold partitionOrder partitionSize excess
      change (∑ candidate ∈ partition.support,
          candidate.1 * partition candidate) =
        (∑ candidate ∈ partition.support, partition candidate) +
          ∑ candidate ∈ partition.support,
            (candidate.1 - 1) * partition candidate
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro candidate _
      have candidatePositive := candidate.2
      have candidateSplit : candidate.1 = 1 + (candidate.1 - 1) := by omega
      calc
        candidate.1 * partition candidate =
            (1 + (candidate.1 - 1)) * partition candidate := by
          rw [← candidateSplit]
        _ = partition candidate +
            (candidate.1 - 1) * partition candidate := by ring
    have excessSingleLe := Finsupp.single_le_sum partition
      (g := fun candidate multiplicity ↦ (candidate.1 - 1) * multiplicity)
      (fun _ _ ↦ Nat.zero_le _) index
    have excessLower : index.1 - 1 ≤ excess := by
      have : (index.1 - 1) * partition index ≤ excess := by
        simpa [excess] using excessSingleLe
      rw [valueOne, mul_one] at this
      exact this
    omega
  have sizeOne : partitionSize partition = 1 := by omega
  obtain ⟨other, partitionEq⟩ := (partitionSize_eq_one_iff partition).mp sizeOne
  have indexEq : index = other := by
    have atIndex := congrArg (fun p : SourcePartition ↦ p index) partitionEq
    by_contra indexNe
    have singleAtIndex : (Finsupp.single other 1 : SourcePartition) index = 0 := by
      simp [Ne.symm indexNe]
    rw [singleAtIndex] at atIndex
    exact valueNeZero atIndex
  subst other
  exact partitionEq

/-- An admissible summand in the source recurrence for positive target
order `t`. The excluded singleton is represented literally. -/
structure SourceTermIndex (t : Nat) (tPositive : 0 < t) where
  s : Nat
  s_le : s ≤ t
  partition : SourcePartition
  order_eq : partitionOrder partition = t - s
  notExcluded : ¬ (s = 0 ∧ partition = singletonPartition t tPositive)

namespace SourceTermIndex

variable {t : Nat} {tPositive : 0 < t}

/-- The partition order `n=t-s`. -/
def n (index : SourceTermIndex t tPositive) : Nat :=
  partitionOrder index.partition

/-- The partition size `q=|λ|`. -/
def q (index : SourceTermIndex t tPositive) : Nat :=
  partitionSize index.partition

/-- The source indicator `ε_s`. -/
def epsilon (index : SourceTermIndex t tPositive) : Nat :=
  sourceEpsilon index.s

theorem s_add_n (index : SourceTermIndex t tPositive) :
    index.s + index.n = t := by
  rw [n, index.order_eq, Nat.add_comm]
  exact Nat.sub_add_cancel index.s_le

/-- At `s=t`, the partition is empty and `q=0`. This corrects the source's
harmless prose slip. -/
theorem partition_eq_zero_of_s_eq_t
    (index : SourceTermIndex t tPositive) (sEq : index.s = t) :
    index.partition = 0 := by
  apply partition_eq_zero_of_order_eq_zero
  rw [index.order_eq, sEq, Nat.sub_self]

theorem q_eq_zero_of_s_eq_t
    (index : SourceTermIndex t tPositive) (sEq : index.s = t) :
    index.q = 0 := by
  rw [q, partition_eq_zero_of_s_eq_t index sEq, partitionSize_zero]

/-- At `s=0`, the unique occurrence of `α_t` is precisely the excluded
singleton partition. -/
theorem singleton_excluded_of_s_eq_zero
    (index : SourceTermIndex t tPositive) (sZero : index.s = 0) :
    index.partition ≠ singletonPartition t tPositive := by
  intro singletonEq
  exact index.notExcluded ⟨sZero, singletonEq⟩

/-- Every recursive coefficient index appearing in an admissible term is
strictly earlier than the target order. -/
theorem recursive_index_lt
    (index : SourceTermIndex t tPositive) (r : PositiveIndex)
    (rMem : r ∈ index.partition.support) :
    r.1 < t := by
  have valueNeZero : index.partition r ≠ 0 := Finsupp.mem_support_iff.mp rMem
  have orderTermLe := Finsupp.single_le_sum index.partition
    (g := fun candidate multiplicity ↦ candidate.1 * multiplicity)
    (fun _ _ ↦ Nat.zero_le _) r
  have termLe : r.1 * index.partition r ≤ partitionOrder index.partition := by
    simpa [partitionOrder] using orderTermLe
  have rLeOrder : r.1 ≤ partitionOrder index.partition := by
    exact (Nat.le_mul_of_pos_right r.1 (Nat.pos_of_ne_zero valueNeZero)).trans termLe
  have rLeTarget : r.1 ≤ t := by
    rw [index.order_eq] at rLeOrder
    omega
  by_contra notLt
  have rEq : r.1 = t := by omega
  have orderEqTarget : partitionOrder index.partition = t := by
    apply le_antisymm
    · rw [index.order_eq]
      exact Nat.sub_le t index.s
    · simpa [rEq] using rLeOrder
  have sZero : index.s = 0 := by
    rw [index.order_eq] at orderEqTarget
    omega
  have singletonAtR : index.partition = Finsupp.single r 1 :=
    partition_eq_single_of_full_part index.partition r rMem
      (rEq.trans orderEqTarget.symm)
  have rSubtypeEq : r = ⟨t, tPositive⟩ := Subtype.ext rEq
  apply index.notExcluded
  constructor
  · exact sZero
  · simpa [singletonPartition, rSubtypeEq] using singletonAtR

/-- At shifted order zero the excluded singleton leaves at least two
positive parts. -/
theorem two_le_q_of_s_eq_zero
    (index : SourceTermIndex t tPositive) (sZero : index.s = 0) :
    2 ≤ index.q := by
  have orderEq : partitionOrder index.partition = t := by
    rw [index.order_eq, sZero, Nat.sub_zero]
  have qPositive : 0 < index.q := by
    by_contra qNotPositive
    have qZero : partitionSize index.partition = 0 := by
      simp only [q] at qNotPositive ⊢
      omega
    have partitionZero := partition_eq_zero_of_size_eq_zero qZero
    rw [partitionZero, partitionOrder_zero] at orderEq
    omega
  by_contra qNotTwo
  have qOne : partitionSize index.partition = 1 := by
    simp only [q] at qPositive qNotTwo ⊢
    omega
  obtain ⟨r, partitionEq⟩ := (partitionSize_eq_one_iff index.partition).mp qOne
  have orderAtR : r.1 = t := by
    rw [partitionEq] at orderEq
    simpa [partitionOrder] using orderEq
  have rEq : r = ⟨t, tPositive⟩ := Subtype.ext orderAtR
  apply index.notExcluded
  exact ⟨sZero, by simpa [singletonPartition, rEq] using partitionEq⟩

/-- The exponent `s+ε_s-1` of `W` is an honest nonnegative exponent. -/
theorem one_le_s_add_epsilon (index : SourceTermIndex t tPositive) :
    1 ≤ index.s + index.epsilon := by
  by_cases sZero : index.s = 0
  · simp [epsilon, sZero]
  · have sPositive := Nat.pos_of_ne_zero sZero
    rw [epsilon, sourceEpsilon_of_pos sPositive, Nat.add_zero]
    exact sPositive

/-- The exponent `2s+q-2` of `ξ` is an honest nonnegative exponent. -/
theorem two_le_two_mul_s_add_q (index : SourceTermIndex t tPositive) :
    2 ≤ 2 * index.s + index.q := by
  by_cases sZero : index.s = 0
  · simpa [sZero] using two_le_q_of_s_eq_zero index sZero
  · have sPositive := Nat.pos_of_ne_zero sZero
    omega

/-- Exact exponent contributed by the product of earlier numerators. -/
theorem partitionHenselExponent_eq_two_n_sub_q
    (index : SourceTermIndex t tPositive) :
    partitionHenselExponent index.partition = 2 * index.n - index.q := by
  exact partitionHenselExponent_eq index.partition

/-- The signed `W` ledger from the corrected source proof. Signed integers
are essential here: the paper's displayed subtraction by `ε_s` is not a
truncated natural subtraction. -/
theorem w_ledger (index : SourceTermIndex t tPositive) :
    ((index.s + index.epsilon - 1 : Nat) : Int) - index.epsilon + index.n =
      (t : Int) - 1 := by
  have sumEq := index.s_add_n
  by_cases sZero : index.s = 0
  · simp [epsilon, sZero] at sumEq ⊢
    omega
  · have sPositive := Nat.pos_of_ne_zero sZero
    simp [epsilon, sourceEpsilon_of_pos sPositive]
    omega

/-- The derivative-exponent ledger from the corrected source proof. -/
theorem derivative_ledger (index : SourceTermIndex t tPositive) :
    (2 * index.s + index.q - 2) + (2 * index.n - index.q) =
      henselExponent t - 1 := by
  have sumEq := index.s_add_n
  have exponentNonnegative := index.two_le_two_mul_s_add_q
  have sizeLeOrder := partitionSize_le_order index.partition
  change partitionSize index.partition ≤ partitionOrder index.partition at sizeLeOrder
  simp only [q, n] at sumEq exponentNonnegative sizeLeOrder ⊢
  simp only [henselExponent]
  omega

end SourceTermIndex

/-! ## Parameter ledgers -/

/-- The structural terms in one recurrence summand cancel exactly. -/
theorem source_structural_ledger
    (DR ell d b tau q : Nat) (tauEq : tau = b + ell)
    (ellQLe : ell * q ≤ DR) (qLe : q ≤ d) :
    DR - ell * q + (d - q) * b + q * tau = DR + d * b := by
  have drCancel : DR - ell * q + ell * q = DR := Nat.sub_add_cancel ellQLe
  have dCancel : d - q + q = d := Nat.sub_add_cancel qLe
  rw [tauEq, Nat.mul_add]
  calc
    DR - ell * q + (d - q) * b + (q * b + q * ell) =
        (DR - ell * q + ell * q) + ((d - q) * b + q * b) := by ring
    _ = DR + d * b := by
      rw [drCancel, ← Nat.add_mul, dCancel]

/-- The final parameter identity `τ+w+σ = D_R+db`. -/
theorem source_parameter_ledger
    (DR ell d b tau mu sigma w : Nat)
    (ellLe : ell ≤ DR) (dPositive : 1 ≤ d) (wLeMu : w ≤ mu)
    (tauEq : tau = b + ell)
    (muEq : mu = (DR - ell) + (d - 1) * b)
    (sigmaEq : sigma = mu - w) :
    tau + w + sigma = DR + d * b := by
  have drCancel : DR - ell + ell = DR := Nat.sub_add_cancel ellLe
  have dCancel : d - 1 + 1 = d := Nat.sub_add_cancel dPositive
  have wCancel : w + (mu - w) = mu := Nat.add_sub_of_le wLeMu
  have wCancel' :
      w + ((DR - ell) + (d - 1) * b - w) =
        (DR - ell) + (d - 1) * b := by
    rw [← muEq]
    exact wCancel
  rw [tauEq, sigmaEq, muEq]
  calc
    b + ell + w + ((DR - ell) + (d - 1) * b - w) =
        (b + ell) + (w + ((DR - ell) + (d - 1) * b - w)) := by
      ac_rfl
    _ = b + ell + ((DR - ell) + (d - 1) * b) := by rw [wCancel']
    _ = (DR - ell + ell) + (1 + (d - 1)) * b := by ring
    _ = DR + d * b := by rw [drCancel, Nat.add_sub_of_le dPositive]

#print axioms partitionHenselExponent_add_size
#print axioms partition_eq_single_of_full_part
#print axioms SourceTermIndex.partition_eq_zero_of_s_eq_t
#print axioms SourceTermIndex.singleton_excluded_of_s_eq_zero
#print axioms SourceTermIndex.recursive_index_lt
#print axioms SourceTermIndex.two_le_q_of_s_eq_zero
#print axioms SourceTermIndex.w_ledger
#print axioms SourceTermIndex.derivative_ledger
#print axioms source_structural_ledger
#print axioms source_parameter_ledger

end

end WeightedHensel

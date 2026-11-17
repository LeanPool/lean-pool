/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

public import LeanPool.ECRuntime.BitString
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring.RingNF

/-!
# Mutation

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Flip a Boolean bit. -/
def flipBit (b : Bool) : Bool :=
  !b

@[simp] theorem flipBit_false : flipBit false = true := by
  rfl

@[simp] theorem flipBit_true : flipBit true = false := by
  rfl

@[simp] theorem flipBit_flipBit (b : Bool) : flipBit (flipBit b) = b := by
  cases b <;> rfl

/-- A mutation mask is the finite set of coordinates that are flipped. -/
abbrev MutationMask (n : ℕ) := Finset (Fin n)

/-- Apply a deterministic mutation mask. -/
def mutateWithMask {n : ℕ} (x : BitString n) (mask : MutationMask n) : BitString n :=
  fun i => if i ∈ mask then flipBit (x i) else x i

@[simp] theorem mutateWithMask_empty {n : ℕ} (x : BitString n) :
    mutateWithMask x ∅ = x := by
  funext i
  simp [mutateWithMask]

@[simp] theorem mutateWithMask_single_same
    {n : ℕ} (x : BitString n) (i : Fin n) :
    mutateWithMask x {i} i = flipBit (x i) := by
  simp [mutateWithMask]

@[simp] theorem mutateWithMask_single_other
    {n : ℕ} (x : BitString n) (i j : Fin n) (hji : j ≠ i) :
    mutateWithMask x {i} j = x j := by
  simp [mutateWithMask, hji]

/-- Applying the same mutation mask twice returns the original search point. -/
@[simp] theorem mutateWithMask_involutive
    {n : ℕ} (x : BitString n) (mask : MutationMask n) :
    mutateWithMask (mutateWithMask x mask) mask = x := by
  funext i
  by_cases hi : i ∈ mask
  · simp [mutateWithMask, hi]
  · simp [mutateWithMask, hi]

/-- Flipping a zero bit and no other bit increases Hamming weight by one. -/
theorem oneCount_mutate_single_of_false
    {n : ℕ} (x : BitString n) (i : Fin n) (hi : x i = false) :
    oneCount (mutateWithMask x {i}) = oneCount x + 1 := by
  unfold oneCount
  have hiu : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hrest :
      (Finset.univ.erase i).sum (fun j => bitValue (mutateWithMask x {i} j)) =
        (Finset.univ.erase i).sum (fun j => bitValue (x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [mutateWithMask, hji]
  rw [← Finset.sum_erase_add Finset.univ
      (fun j => bitValue (mutateWithMask x {i} j)) hiu]
  rw [← Finset.sum_erase_add Finset.univ (fun j => bitValue (x j)) hiu]
  rw [hrest]
  simp [mutateWithMask, hi]

/-- Flipping a one bit and no other bit decreases Hamming weight by one. -/
theorem oneCount_mutate_single_of_true
    {n : ℕ} (x : BitString n) (i : Fin n) (hi : x i = true) :
    oneCount (mutateWithMask x {i}) + 1 = oneCount x := by
  unfold oneCount
  have hiu : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hrest :
      (Finset.univ.erase i).sum (fun j => bitValue (mutateWithMask x {i} j)) =
        (Finset.univ.erase i).sum (fun j => bitValue (x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [mutateWithMask, hji]
  rw [← Finset.sum_erase_add Finset.univ
      (fun j => bitValue (mutateWithMask x {i} j)) hiu]
  rw [← Finset.sum_erase_add Finset.univ (fun j => bitValue (x j)) hiu]
  rw [hrest]
  simp [mutateWithMask, hi]

/-- The same zero-to-one flip decreases the number of zero bits by one. -/
theorem zeroCount_mutate_single_of_false
    {n : ℕ} (x : BitString n) (i : Fin n) (hi : x i = false) :
    zeroCount (mutateWithMask x {i}) + 1 = zeroCount x := by
  have hBefore := oneCount_add_zeroCount x
  have hAfter := oneCount_add_zeroCount (mutateWithMask x {i})
  have hOne := oneCount_mutate_single_of_false x i hi
  omega

/-- A one-to-zero flip increases the number of zero bits by one. -/
theorem zeroCount_mutate_single_of_true
    {n : ℕ} (x : BitString n) (i : Fin n) (hi : x i = true) :
    zeroCount (mutateWithMask x {i}) = zeroCount x + 1 := by
  have hBefore := oneCount_add_zeroCount x
  have hAfter := oneCount_add_zeroCount (mutateWithMask x {i})
  have hOne := oneCount_mutate_single_of_true x i hi
  omega

/-- Probability weight of a mutation mask when all bits are flipped independently with rate `p`. -/
def mutationMaskWeight {n : ℕ} (p : ℝ) (mask : MutationMask n) : ℝ :=
  p ^ mask.card * (1 - p) ^ (n - mask.card)

/-- Mutation-mask weights are nonnegative for a genuine probability parameter. -/
theorem mutationMaskWeight_nonneg
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (mask : MutationMask n) :
    0 ≤ mutationMaskWeight p mask := by
  unfold mutationMaskWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- The independent-bit mutation weights over all masks sum to one. -/
theorem mutationMaskWeight_sum (n : ℕ) (p : ℝ) :
    (∑ mask : MutationMask n, mutationMaskWeight p mask) = 1 := by
  simpa [MutationMask, mutationMaskWeight] using
    (Fintype.sum_pow_mul_eq_add_pow (Fin n) p (1 - p))

/-- The weight of flipping one specified coordinate and no others. -/
theorem mutationMaskWeight_singleton
    {n : ℕ} (p : ℝ) (i : Fin n) :
    mutationMaskWeight p ({i} : MutationMask n) = p * (1 - p) ^ (n - 1) := by
  simp [mutationMaskWeight]

/-- The weight of flipping two distinct specified coordinates and no others. -/
theorem mutationMaskWeight_pair
    {n : ℕ} (p : ℝ) (i j : Fin n) (hij : i ≠ j) :
    mutationMaskWeight p ({i, j} : MutationMask n) =
      p ^ 2 * (1 - p) ^ (n - 2) := by
  simp [mutationMaskWeight, hij]

/--
Total probability weight of all masks that flip exactly one currently-zero bit
and no other coordinate.
-/
def singleZeroFlipWeight {n : ℕ} (p : ℝ) (x : BitString n) : ℝ :=
  ∑ i ∈ zeroPositions x, mutationMaskWeight p ({i} : MutationMask n)

/-- The exact mass of the simple OneMax-improving single-zero-flip events. -/
theorem singleZeroFlipWeight_eq {n : ℕ} (p : ℝ) (x : BitString n) :
    singleZeroFlipWeight p x =
      (zeroCount x : ℝ) * (p * (1 - p) ^ (n - 1)) := by
  unfold singleZeroFlipWeight
  simp_rw [mutationMaskWeight_singleton]
  rw [Finset.sum_const, nsmul_eq_mul, zeroPositions_card]

/-- Standard `(1+1)`-EA mutation rate `1/n`; the zero-dimensional case is separated. -/
noncomputable def standardMutationRate (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ)⁻¹

/-- The elementary OneMax improvement event: flip one specified bad bit and no other bit. -/
noncomputable def specifiedSingleFlipProb (n : ℕ) : ℝ :=
  standardMutationRate n * (1 - standardMutationRate n) ^ (n - 1)

/-- Aggregate probability of `k` disjoint specified single-bit improvement events. -/
noncomputable def kSingleFlipProb (n k : ℕ) : ℝ :=
  (k : ℝ) * specifiedSingleFlipProb n

/-- Mutation masks that flip exactly one currently-zero coordinate. -/
def zeroSingletonMasks {n : ℕ} (x : BitString n) : Finset (MutationMask n) :=
  (zeroPositions x).image (fun i => ({i} : MutationMask n))

/-- The total mutation weight of zero-singleton masks is the single-zero-flip weight. -/
theorem zeroSingletonMasks_weight_eq {n : ℕ} (p : ℝ) (x : BitString n) :
    (∑ mask ∈ zeroSingletonMasks x, mutationMaskWeight p mask) =
      singleZeroFlipWeight p x := by
  unfold zeroSingletonMasks singleZeroFlipWeight
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact Finset.singleton_injective hab

/--
Erasing one flipped coordinate gives the exact Bernoulli-mask balance
`(1-p) * wt(mask) = p * wt(mask.erase j)`.  This identity is the finite-sum
replacement for conditional-probability calculations used in the classical linear-function
drift proof.
-/
theorem mutationMaskWeight_erase_balance {n : ℕ} (p : ℝ)
    (mask : MutationMask n) (j : Fin n) (hj : j ∈ mask) :
    (1 - p) * mutationMaskWeight p mask =
      p * mutationMaskWeight p (mask.erase j) := by
  have hcardle : mask.card ≤ n := by
    simpa using (Finset.card_le_univ mask)
  have hcardpos : 1 ≤ mask.card := Finset.one_le_card.mpr ⟨j, hj⟩
  have herase : (mask.erase j).card = mask.card - 1 := Finset.card_erase_of_mem hj
  have hcard : mask.card = (mask.erase j).card + 1 := by
    omega
  have hpow : n - (mask.erase j).card = (n - mask.card) + 1 := by
    omega
  have hpPow :
      p ^ mask.card = p ^ ((mask.erase j).card + 1) :=
    congrArg (fun k : ℕ => p ^ k) hcard
  have hqPow :
      (1 - p) ^ (n - (mask.erase j).card) =
        (1 - p) ^ ((n - mask.card) + 1) :=
    congrArg (fun k : ℕ => (1 - p) ^ k) hpow
  unfold mutationMaskWeight
  rw [hpPow, hqPow, pow_succ, pow_succ]
  ring

end ECRuntime

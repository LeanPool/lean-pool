/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.StaticUnaryUnbiasedMutation

/-!
# Coordinate marginals of static unary-unbiased mutation

This module formalizes the first distribution-level ingredient used in the
Doerr--Janett--Lengler analysis of static unary-unbiased mutation: every specified
coordinate flips with probability `χ / n`, where `χ` is the expected mutation radius.

The proof is deliberately stated directly for the finite mask law.  It uses only
Hamming-radius invariance, finite double counting, and the already-promoted radius
mass interface.  No independent-coordinate assumption is introduced.

The module also names two radius moments that are relevant for the later pair-flip
analysis.  In particular, `shiftedRadiusMoment` is the expression obtained by averaging
`k-1` against the *unconditional* radius law; it is bounded by `χ`.  The genuinely
conditional pair-flip calculation requires a different, size-biased radius law and is
therefore intentionally postponed.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-- Total probability mass of mutation masks that flip a specified coordinate. -/
noncomputable def coordinateFlipMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i : Fin n) : ℝ :=
  ∑ mask : MutationMask n, if i ∈ mask then law.weight mask else 0

/-- Coordinate flip mass is nonnegative. -/
theorem coordinateFlipMass_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i : Fin n) :
    0 ≤ law.coordinateFlipMass i := by
  unfold coordinateFlipMass
  apply Finset.sum_nonneg
  intro mask hmask
  by_cases hi : i ∈ mask
  · simp [hi, law.weight_nonneg mask]
  · simp [hi]

/-- Swapping two coordinates induces an equivalence on mutation masks. -/
def swapMaskEquiv {n : ℕ} (i j : Fin n) : MutationMask n ≃ MutationMask n :=
  (Equiv.swap i j).finsetCongr

@[simp] theorem swapMaskEquiv_card {n : ℕ} (i j : Fin n)
    (mask : MutationMask n) :
    (swapMaskEquiv i j mask).card = mask.card := by
  simp [swapMaskEquiv]

@[simp] theorem mem_swapMaskEquiv_right_iff {n : ℕ} (i j : Fin n)
    (mask : MutationMask n) :
    j ∈ swapMaskEquiv i j mask ↔ i ∈ mask := by
  simp [swapMaskEquiv]

/-- Radius invariance makes the probability of flipping a coordinate independent of
which coordinate was chosen. -/
theorem coordinateFlipMass_eq {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i j : Fin n) :
    law.coordinateFlipMass i = law.coordinateFlipMass j := by
  classical
  unfold coordinateFlipMass
  let e : MutationMask n ≃ MutationMask n := swapMaskEquiv i j
  refine Fintype.sum_equiv e
    (fun mask : MutationMask n => if i ∈ mask then law.weight mask else 0)
    (fun mask : MutationMask n => if j ∈ mask then law.weight mask else 0) ?_
  intro mask
  have hcard : mask.card = (e mask).card := by
    simp [e]
  have hw : law.weight mask = law.weight (e mask) :=
    law.card_invariant hcard
  have hmem : j ∈ e mask ↔ i ∈ mask := by
    simp [e]
  by_cases hi : i ∈ mask
  · have hj : j ∈ e mask := hmem.mpr hi
    simp [hi, hj, hw]
  · have hj : j ∉ e mask := by
      intro hj'
      exact hi (hmem.mp hj')
    simp [hi, hj]

/-- The expected mutation radius is the mask-weighted expectation of mask cardinality. -/
theorem meanRadius_eq_sum_mask_card_weight {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    law.meanRadius =
      ∑ mask : MutationMask n, (mask.card : ℝ) * law.weight mask := by
  unfold meanRadius radiusMass
  calc
    (∑ k ∈ Finset.range (n + 1),
        (k : ℝ) *
          ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            law.weight mask) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            (mask.card : ℝ) * law.weight mask := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mask hmask
      have hcard : mask.card = k := (Finset.mem_powersetCard.mp hmask).2
      rw [hcard]
    _ = ∑ mask : MutationMask n, (mask.card : ℝ) * law.weight mask := by
      have hdecomp :=
        Finset.sum_powerset (Finset.univ : Finset (Fin n))
          (fun mask : MutationMask n => (mask.card : ℝ) * law.weight mask)
      simpa using hdecomp.symm

/-- Summing the coordinate-flip probabilities over all coordinates gives the mean
mutation radius. -/
theorem sum_coordinateFlipMass_eq_meanRadius {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    (∑ i : Fin n, law.coordinateFlipMass i) = law.meanRadius := by
  rw [law.meanRadius_eq_sum_mask_card_weight]
  unfold coordinateFlipMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mask hmask
  calc
    (∑ i : Fin n, if i ∈ mask then law.weight mask else 0) =
        ∑ i ∈ mask, law.weight mask := by
      simp
    _ = (mask.card : ℝ) * law.weight mask := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Lemma 2 of Doerr--Janett--Lengler: in positive dimension, every specified
coordinate flips with probability exactly `χ / n`. -/
theorem coordinateFlipMass_eq_meanRadius_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n) (i : Fin n) :
    law.coordinateFlipMass i = law.meanRadius / (n : ℝ) := by
  have hsum := law.sum_coordinateFlipMass_eq_meanRadius
  have hconst :
      (∑ j : Fin n, law.coordinateFlipMass j) =
        (n : ℝ) * law.coordinateFlipMass i := by
    calc
      (∑ j : Fin n, law.coordinateFlipMass j) =
          ∑ _j : Fin n, law.coordinateFlipMass i := by
        apply Finset.sum_congr rfl
        intro j hj
        exact law.coordinateFlipMass_eq j i
      _ = (n : ℝ) * law.coordinateFlipMass i := by
        simp
  have hmul : (n : ℝ) * law.coordinateFlipMass i = law.meanRadius :=
    hconst.symm.trans hsum
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  apply (eq_div_iff hn0).2
  simpa [mul_comm] using hmul

/-- The unconditional shifted first radius moment, `E[K-1_{K>0}]` in finite-sum form.
This is *not* the radius distribution conditioned on a specified bit being flipped. -/
def shiftedRadiusMoment {n : ℕ} (law : StaticUnaryUnbiasedMutation n) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((k - 1 : ℕ) : ℝ) * law.radiusMass k

/-- The shifted radius moment is nonnegative. -/
theorem shiftedRadiusMoment_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    0 ≤ law.shiftedRadiusMoment := by
  unfold shiftedRadiusMoment
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (Nat.cast_nonneg _) (law.radiusMass_nonneg k)

/-- Averaging `k-1` against the original radius law is bounded by the mean radius `χ`. -/
theorem shiftedRadiusMoment_le_meanRadius {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    law.shiftedRadiusMoment ≤ law.meanRadius := by
  unfold shiftedRadiusMoment meanRadius
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Nat.sub_le k 1)
  · exact law.radiusMass_nonneg k

/-- Second factorial radius moment.  This is the moment naturally produced by the
probability that two distinct specified coordinates flip together. -/
def secondFactorialRadiusMoment {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (k : ℝ) * ((k - 1 : ℕ) : ℝ) * law.radiusMass k

/-- The second factorial radius moment is nonnegative. -/
theorem secondFactorialRadiusMoment_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    0 ≤ law.secondFactorialRadiusMoment := by
  unfold secondFactorialRadiusMoment
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (law.radiusMass_nonneg k)

end StaticUnaryUnbiasedMutation
end ECRuntime

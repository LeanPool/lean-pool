/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.HomogenizationError

/-!
# High-contrast homogenization: Provider.Regularity.GoodTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Summable weak-error tails on centered cubes

The normalized large-scale regularity argument uses the finite sum of the
Chapter 2 homogenization errors on centered Euclidean triadic cubes.  This
module records the finite-interval and infinite-tail predicates for the
identity comparison matrix.
-/

open scoped BigOperators

namespace HCPolySupport
namespace HighContrast

noncomputable section

private theorem rpow_half_nonneg (x : ℝ) :
    0 ≤ Real.rpow x (1 / (2 : ℝ)) := by
  simpa only [Real.sqrt_eq_rpow] using! Real.sqrt_nonneg x

/-- The multiscale weak error on the centered Euclidean triadic cube at scale
`k`, with identity comparison matrix and the `p = infinity`, `q = 2`
exponents. -/
@[expose]
def scalarIdentityWeakError {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (s : ℝ) (k : ℤ) : ℝ :=
  Book.Ch02.HomogenizationErrorOnCube (originCube d k) s
    .infinity (.finite 2) a (1 : Mat d)

/-- The identity weak error is nonnegative. -/
theorem scalarIdentityWeakError_nonneg {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (s : ℝ) (k : ℤ) :
    0 ≤ scalarIdentityWeakError a s k := by
  unfold scalarIdentityWeakError Book.Ch02.HomogenizationErrorOnCube
  simp only [Book.Ch02.HomogenizationError]
  unfold Book.Ch02.HomogenizationErrorFinite
  change 0 ≤ Real.rpow _ (1 / (2 : ℝ))
  exact rpow_half_nonneg _

/-- The finite `l¹` weak-error row between two integer scales. -/
@[expose]
def ScalarIdentityGoodTailOnInterval {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (s δ : ℝ) (n m : ℤ) : Prop :=
  (∑ k ∈ Finset.Icc n m, scalarIdentityWeakError a s k) ≤ δ

/-- The `l¹` weak-error row is bounded on every finite interval beginning at
`n`. -/
@[expose]
def ScalarIdentityGoodTail {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (s δ : ℝ) (n : ℤ) : Prop :=
  ∀ m, n ≤ m → ScalarIdentityGoodTailOnInterval a s δ n m

/-- Increasing the tolerance preserves a finite good-tail bound. -/
theorem ScalarIdentityGoodTailOnInterval.mono {d : ℕ} [NeZero d]
    {a : Book.Ch02.TriadicCoeffFamily d} {s δ δ' : ℝ} {n m : ℤ}
    (h : ScalarIdentityGoodTailOnInterval a s δ n m) (hδ : δ ≤ δ') :
    ScalarIdentityGoodTailOnInterval a s δ' n m :=
  h.trans hδ

/-- A good tail supplies its bound on every admissible finite interval. -/
theorem ScalarIdentityGoodTail.interval {d : ℕ} [NeZero d]
    {a : Book.Ch02.TriadicCoeffFamily d} {s δ : ℝ} {n m : ℤ}
    (h : ScalarIdentityGoodTail a s δ n) (hnm : n ≤ m) :
    ScalarIdentityGoodTailOnInterval a s δ n m :=
  h m hnm

/-- Increasing the tolerance preserves an infinite good-tail bound. -/
theorem ScalarIdentityGoodTail.mono {d : ℕ} [NeZero d]
    {a : Book.Ch02.TriadicCoeffFamily d} {s δ δ' : ℝ} {n : ℤ}
    (h : ScalarIdentityGoodTail a s δ n) (hδ : δ ≤ δ') :
    ScalarIdentityGoodTail a s δ' n := by
  intro m hnm
  exact (h.interval hnm).mono hδ

/-- Discarding initial scales preserves a finite good-tail bound. -/
theorem ScalarIdentityGoodTailOnInterval.mono_start {d : ℕ} [NeZero d]
    {a : Book.Ch02.TriadicCoeffFamily d} {s δ : ℝ} {n n' m : ℤ}
    (h : ScalarIdentityGoodTailOnInterval a s δ n m)
    (hnn' : n ≤ n') :
    ScalarIdentityGoodTailOnInterval a s δ n' m := by
  apply le_trans _ h
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc hnn' le_rfl) ?_
  intro k _ _
  exact scalarIdentityWeakError_nonneg a s k

/-- Discarding initial scales preserves an infinite good-tail bound. -/
theorem ScalarIdentityGoodTail.mono_start {d : ℕ} [NeZero d]
    {a : Book.Ch02.TriadicCoeffFamily d} {s δ : ℝ} {n n' : ℤ}
    (h : ScalarIdentityGoodTail a s δ n) (hnn' : n ≤ n') :
    ScalarIdentityGoodTail a s δ n' := by
  intro m hn'm
  exact (h.interval (hnn'.trans hn'm)).mono_start hnn'

/-- Every weak error in a good tail is bounded by its tolerance. -/
theorem ScalarIdentityGoodTail.weakError_le {d : ℕ} [NeZero d]
    {a : Book.Ch02.TriadicCoeffFamily d} {s δ : ℝ} {n k : ℤ}
    (h : ScalarIdentityGoodTail a s δ n) (hnk : n ≤ k) :
    scalarIdentityWeakError a s k ≤ δ := by
  have hk_mem : k ∈ Finset.Icc n k := Finset.mem_Icc.mpr ⟨hnk, le_rfl⟩
  have hk_le_sum :
      scalarIdentityWeakError a s k ≤
        ∑ j ∈ Finset.Icc n k, scalarIdentityWeakError a s j := by
    exact Finset.single_le_sum
      (fun j _ ↦ scalarIdentityWeakError_nonneg a s j) hk_mem
  exact hk_le_sum.trans (h.interval hnk)

end

end HighContrast
end HCPolySupport

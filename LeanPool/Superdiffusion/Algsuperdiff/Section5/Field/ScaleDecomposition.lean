/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamField

/-!
# ScaleDecomposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The low- and high-frequency parts of the stream field

The normalized stream matrix is split at shell index zero.  The
negative shells form the rough, locally bounded part `streamFieldSmall`; the
nonnegative shells form the differentiable part `streamFieldLarge`.  Both
series use the same normalization at the origin as `streamField`.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open HCPolySupport

noncomputable section

variable {d : ℕ} {gamma : ℝ}

/-- The normalized contribution of the shells with index strictly below zero. -/
def streamFieldSmall (omega : FullSample d gamma) (x : Vec d) : Mat d :=
  ∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x - omega.1.1 (-1 - (r : ℤ)) 0)

/-- The normalized contribution of the shells with nonnegative index. -/
def streamFieldLarge (omega : FullSample d gamma) (x : Vec d) : Mat d :=
  ∑' r : ℕ, (omega.1.1 (r : ℤ) x - omega.1.1 (r : ℤ) 0)

private theorem summable_streamIncrement_descending_matrix
    (omega : FullSample d gamma) (x : Vec d) :
    Summable fun r : ℕ =>
      omega.1.1 (-1 - (r : ℤ)) x - omega.1.1 (-1 - (r : ℤ)) 0 := by
  refine Pi.summable.mpr fun i => Pi.summable.mpr fun k => ?_
  simpa only [Matrix.sub_apply] using
    summable_streamIncrement_descending omega.1 (-1) x i k

private theorem summable_streamIncrement_ascending_matrix
    (omega : FullSample d gamma) (x : Vec d) :
    Summable fun r : ℕ =>
      omega.1.1 (r : ℤ) x - omega.1.1 (r : ℤ) 0 := by
  refine Pi.summable.mpr fun i => Pi.summable.mpr fun k => ?_
  simpa only [zero_add, Matrix.sub_apply] using
    summable_streamIncrement_ascending omega 0 x i k

@[simp]
theorem streamFieldSmall_apply_entry (omega : FullSample d gamma)
    (x : Vec d) (i k : Fin d) :
    streamFieldSmall omega x i k =
      ∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x i k -
        omega.1.1 (-1 - (r : ℤ)) 0 i k) := by
  rw [streamFieldSmall]
  have h1 : (∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x - omega.1.1 (-1 - (r : ℤ)) 0)) i
      = ∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x - omega.1.1 (-1 - (r : ℤ)) 0) i :=
    Pi.tsum_apply (summable_streamIncrement_descending_matrix omega x)
  have h2 : (∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x - omega.1.1 (-1 - (r : ℤ)) 0) i) k
      = ∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x - omega.1.1 (-1 - (r : ℤ)) 0) i k :=
    Pi.tsum_apply (Pi.summable.1 (summable_streamIncrement_descending_matrix omega x) i)
  rw [h1, h2]
  apply tsum_congr
  intro r
  rfl

@[simp]
theorem streamFieldLarge_apply_entry (omega : FullSample d gamma)
    (x : Vec d) (i k : Fin d) :
    streamFieldLarge omega x i k =
      ∑' r : ℕ, (omega.1.1 (r : ℤ) x i k - omega.1.1 (r : ℤ) 0 i k) := by
  rw [streamFieldLarge]
  have h1 : (∑' r : ℕ, (omega.1.1 (r : ℤ) x - omega.1.1 (r : ℤ) 0)) i
      = ∑' r : ℕ, (omega.1.1 (r : ℤ) x - omega.1.1 (r : ℤ) 0) i :=
    Pi.tsum_apply (summable_streamIncrement_ascending_matrix omega x)
  have h2 : (∑' r : ℕ, (omega.1.1 (r : ℤ) x - omega.1.1 (r : ℤ) 0) i) k
      = ∑' r : ℕ, (omega.1.1 (r : ℤ) x - omega.1.1 (r : ℤ) 0) i k :=
    Pi.tsum_apply (Pi.summable.1 (summable_streamIncrement_ascending_matrix omega x) i)
  rw [h1, h2]
  apply tsum_congr
  intro r
  rfl

/-- The normalized field is exactly the sum of its negative- and
nonnegative-shell parts. -/
theorem streamField_eq_small_add_large (omega : FullSample d gamma) (x : Vec d) :
    streamField omega x = streamFieldSmall omega x + streamFieldLarge omega x := by
  ext i k
  let f : ℤ → ℝ := fun n => omega.1.1 n x i k - omega.1.1 n 0 i k
  have hasc : Summable fun r : ℕ => f (r : ℤ) := by
    simpa only [f, zero_add] using
      summable_streamIncrement_ascending omega 0 x i k
  have hdesc : Summable fun r : ℕ => f (-((r : ℤ) + 1)) := by
    refine (summable_streamIncrement_descending omega.1 (-1) x i k).congr fun r => ?_
    simp only [f]
    have hidx : -((r : ℤ) + 1) = -1 - (r : ℤ) := by ring
    rw [hidx]
  have hsplit := tsum_of_nat_of_neg_add_one hasc hdesc
  rw [streamField_apply_entry]
  change (∑' n : ℤ, (omega.1.1 n x i k - omega.1.1 n 0 i k)) =
    streamFieldSmall omega x i k + streamFieldLarge omega x i k
  rw [streamFieldSmall_apply_entry, streamFieldLarge_apply_entry]
  change (∑' n : ℤ, f n) = _
  rw [hsplit, add_comm]
  congr 1
  · apply tsum_congr
    intro r
    simp only [f]
    have hidx : -((r : ℤ) + 1) = -1 - (r : ℤ) := by ring
    rw [hidx]

@[simp]
theorem streamFieldSmall_zero (omega : FullSample d gamma) :
    streamFieldSmall omega 0 = 0 := by
  ext i k
  simp only [streamFieldSmall_apply_entry, sub_self, tsum_zero, Matrix.zero_apply]

@[simp]
theorem streamFieldLarge_zero (omega : FullSample d gamma) :
    streamFieldLarge omega 0 = 0 := by
  ext i k
  simp only [streamFieldLarge_apply_entry, sub_self, tsum_zero, Matrix.zero_apply]

/-- Every value of the negative-shell part is skew-symmetric. -/
theorem streamFieldSmall_skew (omega : FullSample d gamma) (x : Vec d) :
    (streamFieldSmall omega x).transpose = -streamFieldSmall omega x := by
  ext i k
  rw [Matrix.transpose_apply, Matrix.neg_apply, streamFieldSmall_apply_entry,
    streamFieldSmall_apply_entry]
  calc
    (∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x k i -
        omega.1.1 (-1 - (r : ℤ)) 0 k i)) =
        ∑' r : ℕ, -(omega.1.1 (-1 - (r : ℤ)) x i k -
          omega.1.1 (-1 - (r : ℤ)) 0 i k) := by
      apply tsum_congr
      intro r
      rw [ShellField.skew_entry (omega.1.1 (-1 - (r : ℤ))) x k i,
        ShellField.skew_entry (omega.1.1 (-1 - (r : ℤ))) 0 k i]
      ring
    _ = -∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x i k -
        omega.1.1 (-1 - (r : ℤ)) 0 i k) := tsum_neg

/-- Every value of the nonnegative-shell part is skew-symmetric. -/
theorem streamFieldLarge_skew (omega : FullSample d gamma) (x : Vec d) :
    (streamFieldLarge omega x).transpose = -streamFieldLarge omega x := by
  ext i k
  rw [Matrix.transpose_apply, Matrix.neg_apply, streamFieldLarge_apply_entry,
    streamFieldLarge_apply_entry]
  calc
    (∑' r : ℕ, (omega.1.1 (r : ℤ) x k i - omega.1.1 (r : ℤ) 0 k i)) =
        ∑' r : ℕ, -(omega.1.1 (r : ℤ) x i k -
          omega.1.1 (r : ℤ) 0 i k) := by
      apply tsum_congr
      intro r
      rw [ShellField.skew_entry (omega.1.1 (r : ℤ)) x k i,
        ShellField.skew_entry (omega.1.1 (r : ℤ)) 0 k i]
      ring
    _ = -∑' r : ℕ, (omega.1.1 (r : ℤ) x i k -
        omega.1.1 (r : ℤ) 0 i k) := tsum_neg

end

end Algsuperdiff.Section5.Field

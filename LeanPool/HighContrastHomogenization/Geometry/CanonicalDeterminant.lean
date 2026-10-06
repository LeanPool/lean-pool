/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.Canonical
public import LeanPool.HighContrastHomogenization.Geometry.DetOrder

/-!
# High-contrast homogenization: Geometry.CanonicalDeterminant

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The determinant clause of the canonical balance

The determinant clause of the canonical balance reads determinants in the
balance chain `M(E) ≤ E ≤ 𝔡(E)^{1/2} M(E)`.  Since `det M(E) = 1` and the
matrices have size `2d`, this is `1 ≤ det(E) ≤ 𝔡(E)^d`, the determinant bound
used in `p.global.selection`, written before the `d`-th root is taken.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- The imbalance of a positive block is positive once the dimension is. -/
theorem canonImbalance_pos [Nonempty (Fin d)] {E : FullBlockMat d} (hE : E.PosDef) :
    0 < canonImbalance E := by
  have hpos : 0 < relSize E (canonBlock E) := relSize_pos hE (posDef_canonBlock hE)
  rw [canonImbalance]
  positivity

/-- **The lower determinant bound** used in `p.global.selection`: a
self-dominating positive block has determinant at least one. -/
theorem one_le_det_of_fullBlockSharp_le {E : FullBlockMat d} (hE : E.PosDef)
    (hle : fullBlockSharp E ≤ E) : 1 ≤ E.det := by
  obtain ⟨-, hME, -⟩ := canonBalance hE hle
  have h := det_le_det_of_le (posDef_canonBlock hE) hE hME
  rwa [det_canonBlock hE] at h

/-- **The upper determinant bound** used in `p.global.selection`: the
determinant of a self-dominating positive block is at most the `d`-th power of
its imbalance, the exponent being half the matrix size. -/
theorem det_le_canonImbalance_pow [Nonempty (Fin d)] {E : FullBlockMat d}
    (hE : E.PosDef) (hle : fullBlockSharp E ≤ E) :
    E.det ≤ canonImbalance E ^ d := by
  obtain ⟨-, -, hEd⟩ := canonBalance hE hle
  have hd : 0 < canonImbalance E := canonImbalance_pos hE
  have hs : 0 < Real.sqrt (canonImbalance E) := Real.sqrt_pos.mpr hd
  have hM : (canonBlock E).PosDef := posDef_canonBlock hE
  have hsM : (Real.sqrt (canonImbalance E) • canonBlock E).PosDef := posDef_smul hM hs
  have h := det_le_det_of_le hE hsM hEd
  have hdet : (Real.sqrt (canonImbalance E) • canonBlock E).det =
      canonImbalance E ^ d := by
    rw [Matrix.det_smul, det_canonBlock hE, mul_one]
    have hcard : Fintype.card (BlockCoord d) = 2 * d := by simp [two_mul]
    rw [hcard, pow_mul, Real.sq_sqrt hd.le]
  rwa [hdet] at h

end

end HighContrast
end HCPolySupport

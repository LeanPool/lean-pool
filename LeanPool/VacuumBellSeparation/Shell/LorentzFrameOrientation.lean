/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.SpacetimeFrameCoordinates

/-!
# Proper orientation of the explicit Lorentz frame

The normalized spatial cross product fixes the orientation. First-column
multilinearity reduces the four-dimensional determinant to the actual
spatial triple product, whose value is the positive gamma factor.
-/

@[expose] public section

namespace VacuumBellSeparation

open Matrix
open scoped Matrix

theorem spacetimeColumnMatrix_update_first (w w' e f n : Spacetime) :
    (spacetimeColumnMatrix w e f n).updateCol 0 (spacetimeFrameCoordinates w') =
      spacetimeColumnMatrix w' e f n := by
  ext i j
  fin_cases j <;> simp [spacetimeColumnMatrix]

theorem spacetimeColumnMatrix_det_add_first (w w' e f n : Spacetime) :
    (spacetimeColumnMatrix (w + w') e f n).det =
      (spacetimeColumnMatrix w e f n).det + (spacetimeColumnMatrix w' e f n).det := by
  rw [← spacetimeColumnMatrix_update_first w (w + w') e f n, map_add,
    Matrix.det_updateCol_add, spacetimeColumnMatrix_update_first,
      spacetimeColumnMatrix_update_first]

theorem spacetimeColumnMatrix_det_smul_first (a : ℝ) (w e f n : Spacetime) :
    (spacetimeColumnMatrix (a • w) e f n).det = a * (spacetimeColumnMatrix w e f n).det := by
  rw [← spacetimeColumnMatrix_update_first w (a • w) e f n, map_smul,
    Matrix.det_updateCol_smul, spacetimeColumnMatrix_update_first]

theorem spacetimeColumnMatrix_det_repeated_left (e f n : Spacetime) :
    (spacetimeColumnMatrix e e f n).det = 0 :=
  Matrix.det_zero_of_column_eq (by decide : (0 : Fin 4) ≠ 1) (fun _ => rfl)

theorem spacetimeColumnMatrix_det_repeated_right (e f n : Spacetime) :
    (spacetimeColumnMatrix f e f n).det = 0 :=
  Matrix.det_zero_of_column_eq (by decide : (0 : Fin 4) ≠ 2) (fun _ => rfl)

theorem spacetimeColumnMatrix_det_time (e f n : Spacetime) :
    (spacetimeColumnMatrix (1, 0) e f n).det =
      Matrix.det ![WithLp.ofLp e.2, WithLp.ofLp f.2, WithLp.ofLp n.2] := by
  let A := spacetimeColumnMatrix (1, 0) e f n
  have hc (i : Fin 4) : A i 0 = if i = 0 then 1 else 0 := by
    fin_cases i <;> rfl
  have hm : A.submatrix (Fin.succAbove (0 : Fin 4)) Fin.succ =
      (![WithLp.ofLp e.2, WithLp.ofLp f.2, WithLp.ofLp n.2] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  change A.det = _
  rw [Matrix.det_succ_column_zero]
  simp only [hc, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Fin.val_zero, pow_zero, one_mul, hm]
  exact Matrix.det_transpose _

theorem spacetimeColumnMatrix_det_normal (e f : Spacetime) :
    (spacetimeColumnMatrix (1, 0) e f (lorentzFrameNormal e f)).det =
      (lorentzFrameGamma e f)⁻¹ * ‖spatialEuclideanCross e.2 f.2‖ ^ 2 := by
  rw [spacetimeColumnMatrix_det_time, ← triple_product_eq_det,
    triple_product_permutation, triple_product_permutation]
  change ((lorentzFrameGamma e f)⁻¹ • crossProduct (WithLp.ofLp e.2) (WithLp.ofLp f.2)) ⬝ᵥ
      crossProduct (WithLp.ofLp e.2) (WithLp.ofLp f.2) = _
  rw [smul_dotProduct, smul_eq_mul]
  congr 1
  calc
    _ = inner ℝ (spatialEuclideanCross e.2 f.2) (spatialEuclideanCross e.2 f.2) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, spatialEuclideanCross, star_trivial]
    _ = _ := real_inner_self_eq_norm_sq _

theorem lorentzFrameLinear_det {e f : Spacetime}
    (he : minkowskiForm e e = -1) (hf : minkowskiForm f f = -1)
    (hef : minkowskiForm e f = 0) : LinearMap.det (lorentzFrameLinear e f) = 1 := by
  rw [← LinearMap.det_toMatrix spacetimeFrameBasis, lorentzFrameLinear_toMatrix]
  unfold lorentzFrameFuture
  rw [spacetimeColumnMatrix_det_smul_first, spacetimeColumnMatrix_det_add_first,
    spacetimeColumnMatrix_det_add_first, spacetimeColumnMatrix_det_smul_first,
    spacetimeColumnMatrix_det_smul_first, spacetimeColumnMatrix_det_repeated_left,
    spacetimeColumnMatrix_det_repeated_right, mul_zero, mul_zero, add_zero, add_zero,
    spacetimeColumnMatrix_det_normal, lorentzFrame_cross_norm_sq he hf hef]
  field_simp [ne_of_gt (lorentzFrameGamma_pos e f)]

theorem lorentzPairFrame_isProper {e f : Spacetime}
    (he : minkowskiForm e e = -1) (hf : minkowskiForm f f = -1)
    (hef : minkowskiForm e f = 0) : IsProperLorentzMap (lorentzPairFrame he hf hef) :=
  ⟨lorentzPairFrame_isLorentz he hf hef, lorentzFrameLinear_det he hf hef⟩

end VacuumBellSeparation

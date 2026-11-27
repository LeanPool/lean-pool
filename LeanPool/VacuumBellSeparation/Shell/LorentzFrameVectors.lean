/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LorentzMap
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Explicit orthonormal frame vectors in the original Minkowski spacetime

For an orthogonal negative unit pair e,f, the future normal is the
normalization of e0+e.time*e+f.time*f. The remaining negative unit vector
has zero time coordinate and is the normalized actual spatial cross
product. All normalizations are justified by the exact gamma square.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace Matrix

theorem minkowskiForm_comm (x y : Spacetime) :
    minkowskiForm x y = minkowskiForm y x := by
  simp only [minkowskiForm, real_inner_comm]
  ring

theorem minkowskiForm_add_left (x y z : Spacetime) :
    minkowskiForm (x + y) z = minkowskiForm x z + minkowskiForm y z := by
  simp only [minkowskiForm, Prod.fst_add, Prod.snd_add, inner_add_left]
  ring

@[simp] theorem minkowskiForm_add_right (x y z : Spacetime) :
    minkowskiForm x (y + z) = minkowskiForm x y + minkowskiForm x z := by
  simp only [minkowskiForm, Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

theorem minkowskiForm_smul_left (a : ℝ) (x y : Spacetime) :
    minkowskiForm (a • x) y = a * minkowskiForm x y := by
  change (a * x.1) * y.1 - inner ℝ (a • x.2) y.2 =
    a * (x.1 * y.1 - inner ℝ x.2 y.2)
  rw [real_inner_smul_left]
  ring

@[simp] theorem minkowskiForm_smul_right (a : ℝ) (x y : Spacetime) :
    minkowskiForm x (a • y) = a * minkowskiForm x y := by
  change x.1 * (a * y.1) - inner ℝ x.2 (a • y.2) =
    a * (x.1 * y.1 - inner ℝ x.2 y.2)
  rw [real_inner_smul_right]
  ring

theorem minkowskiForm_time_left (x : Spacetime) : minkowskiForm (1, 0) x = x.1 := by
  simp [minkowskiForm]

@[simp] theorem minkowskiForm_time_right (x : Spacetime) : minkowskiForm x (1, 0) = x.1 := by
  simp [minkowskiForm]

/-- Spatial Euclidean cross defined as `WithLp.toLp 2 (crossProduct (WithLp.ofLp x) (WithLp.ofLp
y))`. -/
noncomputable def spatialEuclideanCross
    (x y : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp x) (WithLp.ofLp y))

theorem spatialEuclideanCross_inner_left (x y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ x (spatialEuclideanCross x y) = 0 := by
  simp [spatialEuclideanCross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem spatialEuclideanCross_inner_right (x y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ y (spatialEuclideanCross x y) = 0 := by
  simp [spatialEuclideanCross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem spatialEuclideanCross_norm_sq (x y : EuclideanSpace ℝ (Fin 3)) :
    ‖spatialEuclideanCross x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq]
  simpa only [spatialEuclideanCross, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, star_trivial, dotProduct_comm, pow_two] using
    cross_dot_cross (WithLp.ofLp x) (WithLp.ofLp y) (WithLp.ofLp x) (WithLp.ofLp y)

/-- Lorentz frame gamma given by `Real.sqrt (1 + e.1 ^ 2 + f.1 ^ 2)`. -/
noncomputable def lorentzFrameGamma (e f : Spacetime) : ℝ :=
  Real.sqrt (1 + e.1 ^ 2 + f.1 ^ 2)

/-- Lorentz frame future given by `(lorentzFrameGamma e f)⁻¹ • ((1, 0) + e.1 • e + f.1 • f)`. -/
noncomputable def lorentzFrameFuture (e f : Spacetime) : Spacetime :=
  (lorentzFrameGamma e f)⁻¹ • ((1, 0) + e.1 • e + f.1 • f)

/-- Lorentz frame normal. -/
noncomputable def lorentzFrameNormal (e f : Spacetime) : Spacetime :=
  (0, (lorentzFrameGamma e f)⁻¹ • spatialEuclideanCross e.2 f.2)

theorem lorentzFrameGamma_pos (e f : Spacetime) : 0 < lorentzFrameGamma e f := by
  unfold lorentzFrameGamma
  positivity

theorem lorentzFrameGamma_sq (e f : Spacetime) :
    lorentzFrameGamma e f ^ 2 = 1 + e.1 ^ 2 + f.1 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem lorentzFrameFuture_time (e f : Spacetime) :
    (lorentzFrameFuture e f).1 = lorentzFrameGamma e f := by
  change (lorentzFrameGamma e f)⁻¹ * (1 + e.1 * e.1 + f.1 * f.1) = _
  rw [show 1 + e.1 * e.1 + f.1 * f.1 = lorentzFrameGamma e f ^ 2 by
    rw [lorentzFrameGamma_sq]; ring]
  field_simp [ne_of_gt (lorentzFrameGamma_pos e f)]

@[simp] theorem lorentzFrameNormal_time (e f : Spacetime) :
    (lorentzFrameNormal e f).1 = 0 := rfl

variable {e f : Spacetime}
  (he : minkowskiForm e e = -1) (hf : minkowskiForm f f = -1)
  (hef : minkowskiForm e f = 0)

include he hf hef in
theorem lorentzFrame_cross_norm_sq :
    ‖spatialEuclideanCross e.2 f.2‖ ^ 2 = lorentzFrameGamma e f ^ 2 := by
  have he' : ‖e.2‖ ^ 2 = 1 + e.1 ^ 2 := by
    have h := he
    simp only [minkowskiForm, real_inner_self_eq_norm_sq, ← pow_two] at h
    linarith
  have hf' : ‖f.2‖ ^ 2 = 1 + f.1 ^ 2 := by
    have h := hf
    simp only [minkowskiForm, real_inner_self_eq_norm_sq, ← pow_two] at h
    linarith
  have hef' : inner ℝ e.2 f.2 = e.1 * f.1 := by
    unfold minkowskiForm at hef
    linarith
  rw [spatialEuclideanCross_norm_sq, he', hf', hef', lorentzFrameGamma_sq]
  ring

include he hf hef in
theorem lorentzFrame_cross_norm :
    ‖spatialEuclideanCross e.2 f.2‖ = lorentzFrameGamma e f :=
  (sq_eq_sq₀ (norm_nonneg _) (lorentzFrameGamma_pos e f).le).mp
    (lorentzFrame_cross_norm_sq he hf hef)

include he hef in
theorem lorentzFrameFuture_orthogonal_left :
    minkowskiForm (lorentzFrameFuture e f) e = 0 := by
  have hfe : minkowskiForm f e = 0 := (minkowskiForm_comm f e).trans hef
  simp only [lorentzFrameFuture, minkowskiForm_smul_left, minkowskiForm_add_left,
    minkowskiForm_time_left, he, hfe]
  ring

include hf hef in
theorem lorentzFrameFuture_orthogonal_right :
    minkowskiForm (lorentzFrameFuture e f) f = 0 := by
  simp only [lorentzFrameFuture, minkowskiForm_smul_left, minkowskiForm_add_left,
    minkowskiForm_time_left, hef, hf]
  ring

include he hf hef in
theorem lorentzFrameFuture_square :
    minkowskiForm (lorentzFrameFuture e f) (lorentzFrameFuture e f) = 1 := by
  have hfe : minkowskiForm f e = 0 := (minkowskiForm_comm f e).trans hef
  have hN : minkowskiForm ((1, 0) + e.1 • e + f.1 • f)
      ((1, 0) + e.1 • e + f.1 • f) = lorentzFrameGamma e f ^ 2 := by
    simp only [minkowskiForm_add_left, minkowskiForm_add_right,
      minkowskiForm_smul_left, minkowskiForm_smul_right, minkowskiForm_time_left,
      minkowskiForm_time_right, he, hf, hef, hfe, lorentzFrameGamma_sq]
    change (1 + e.1 * e.1 + f.1 * f.1) +
      e.1 * (e.1 + e.1 * (-1) + f.1 * 0) +
      f.1 * (f.1 + e.1 * 0 + f.1 * (-1)) = 1 + e.1 ^ 2 + f.1 ^ 2
    ring
  simp only [lorentzFrameFuture, minkowskiForm_smul_left, minkowskiForm_smul_right, hN]
  field_simp [ne_of_gt (lorentzFrameGamma_pos e f)]

theorem lorentzFrameNormal_orthogonal_left :
    minkowskiForm e (lorentzFrameNormal e f) = 0 := by
  simp only [lorentzFrameNormal, minkowskiForm, mul_zero, real_inner_smul_right,
    spatialEuclideanCross_inner_left, mul_zero, sub_zero]

theorem lorentzFrameNormal_orthogonal_right :
    minkowskiForm f (lorentzFrameNormal e f) = 0 := by
  simp only [lorentzFrameNormal, minkowskiForm, mul_zero, real_inner_smul_right,
    spatialEuclideanCross_inner_right, mul_zero, sub_zero]

theorem lorentzFrameFuture_orthogonal_normal :
    minkowskiForm (lorentzFrameFuture e f) (lorentzFrameNormal e f) = 0 := by
  simp only [lorentzFrameFuture, minkowskiForm_smul_left, minkowskiForm_add_left,
    minkowskiForm_time_left, lorentzFrameNormal_time,
    lorentzFrameNormal_orthogonal_left, lorentzFrameNormal_orthogonal_right]
  ring

include he hf hef in
theorem lorentzFrameNormal_square :
    minkowskiForm (lorentzFrameNormal e f) (lorentzFrameNormal e f) = -1 := by
  change 0 * 0 - inner ℝ ((lorentzFrameGamma e f)⁻¹ • spatialEuclideanCross e.2 f.2)
    ((lorentzFrameGamma e f)⁻¹ • spatialEuclideanCross e.2 f.2) = -1
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    lorentzFrame_cross_norm_sq he hf hef]
  norm_num only [zero_mul]
  field_simp [ne_of_gt (lorentzFrameGamma_pos e f)]; norm_num

end VacuumBellSeparation

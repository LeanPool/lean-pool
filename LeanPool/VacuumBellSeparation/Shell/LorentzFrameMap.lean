/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.LorentzFrameVectors

/-!
# The actual future Lorentz automorphism with the constructed frame columns

Nondegeneracy of the original Minkowski form proves injectivity. Finite
dimension then supplies the genuine inverse and continuous equivalence.
Proper orientation is treated separately from this construction.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

/-- Spacetime axis. -/
noncomputable def spacetimeAxis (j : Fin 3) : Spacetime :=
  (0, WithLp.toLp 2 (Pi.single j 1))

/-- Linear map whose columns form the Lorentz frame determined by the two spacelike vectors. -/
noncomputable def lorentzFrameLinear (e f : Spacetime) : Spacetime →ₗ[ℝ] Spacetime where
  toFun x := x.1 • lorentzFrameFuture e f + x.2 0 • e + x.2 1 • f +
    x.2 2 • lorentzFrameNormal e f
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply, add_smul]
    abel
  map_smul' a x := by
    change (a * x.1) • lorentzFrameFuture e f + (a * x.2 0) • e +
      (a * x.2 1) • f + (a * x.2 2) • lorentzFrameNormal e f =
      a • (x.1 • lorentzFrameFuture e f + x.2 0 • e + x.2 1 • f +
        x.2 2 • lorentzFrameNormal e f)
    simp only [mul_smul, smul_add]

@[simp] theorem lorentzFrameLinear_apply (e f x : Spacetime) :
    lorentzFrameLinear e f x = x.1 • lorentzFrameFuture e f + x.2 0 • e + x.2 1 • f +
      x.2 2 • lorentzFrameNormal e f := rfl

theorem lorentzFrameLinear_time (e f : Spacetime) :
    lorentzFrameLinear e f (1, 0) = lorentzFrameFuture e f := by simp

theorem lorentzFrameLinear_first (e f : Spacetime) :
    lorentzFrameLinear e f (spacetimeAxis 0) = e := by simp [spacetimeAxis]

theorem lorentzFrameLinear_second (e f : Spacetime) :
    lorentzFrameLinear e f (spacetimeAxis 1) = f := by simp [spacetimeAxis]

theorem lorentzFrameLinear_third (e f : Spacetime) :
    lorentzFrameLinear e f (spacetimeAxis 2) = lorentzFrameNormal e f := by simp [spacetimeAxis]

theorem minkowskiForm_nondegenerate {x : Spacetime}
    (h : ∀ y, minkowskiForm x y = 0) : x = 0 := by
  have ht : x.1 = 0 := by simpa using h (1, 0)
  have hs : ‖x.2‖ ^ 2 = 0 := by
    have hy := h (0, x.2)
    simp only [minkowskiForm, mul_zero, real_inner_self_eq_norm_sq, zero_sub, neg_eq_zero] at hy
    exact hy
  exact Prod.ext ht (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

variable {e f : Spacetime}
  (he : minkowskiForm e e = -1) (hf : minkowskiForm f f = -1)
  (hef : minkowskiForm e f = 0)

include he hf hef in
theorem lorentzFrameLinear_preserves (x y : Spacetime) :
    minkowskiForm (lorentzFrameLinear e f x) (lorentzFrameLinear e f y) =
      minkowskiForm x y := by
  have hww := lorentzFrameFuture_square he hf hef
  have hwn := lorentzFrameFuture_orthogonal_normal (e := e) (f := f)
  have hwe := lorentzFrameFuture_orthogonal_left he hef
  have hwf := lorentzFrameFuture_orthogonal_right hf hef
  have hne := lorentzFrameNormal_orthogonal_left (e := e) (f := f)
  have hnf := lorentzFrameNormal_orthogonal_right (e := e) (f := f)
  have hnn := lorentzFrameNormal_square he hf hef
  have hfe : minkowskiForm f e = 0 := (minkowskiForm_comm f e).trans hef
  have hew : minkowskiForm e (lorentzFrameFuture e f) = 0 :=
    (minkowskiForm_comm _ _).trans hwe
  have hfw : minkowskiForm f (lorentzFrameFuture e f) = 0 :=
    (minkowskiForm_comm _ _).trans hwf
  have hnw : minkowskiForm (lorentzFrameNormal e f) (lorentzFrameFuture e f) = 0 :=
    (minkowskiForm_comm _ _).trans hwn
  have hnen : minkowskiForm (lorentzFrameNormal e f) e = 0 :=
    (minkowskiForm_comm _ _).trans hne
  have hnfn : minkowskiForm (lorentzFrameNormal e f) f = 0 :=
    (minkowskiForm_comm _ _).trans hnf
  simp only [lorentzFrameLinear_apply, minkowskiForm_add_left, minkowskiForm_add_right,
    minkowskiForm_smul_left, minkowskiForm_smul_right,
    he, hf, hef, hfe, hww, hwn, hwe, hwf, hne, hnf, hnn, hew, hfw, hnw, hnen, hnfn]
  simp only [minkowskiForm, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]
  ring

include he hf hef in
theorem lorentzFrameLinear_injective : Function.Injective (lorentzFrameLinear e f) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  apply minkowskiForm_nondegenerate
  intro y
  rw [← lorentzFrameLinear_preserves he hf hef, hx]
  simp [minkowskiForm]

/-- Continuous linear equivalence for the lorentz pair frame, of type `Spacetime ≃L[ℝ]
Spacetime`. -/
noncomputable def lorentzPairFrame : Spacetime ≃L[ℝ] Spacetime :=
  (LinearEquiv.ofInjectiveEndo (lorentzFrameLinear e f)
    (lorentzFrameLinear_injective he hf hef)).toContinuousLinearEquiv

@[simp] theorem lorentzPairFrame_apply (x : Spacetime) :
    lorentzPairFrame he hf hef x = lorentzFrameLinear e f x := rfl

theorem lorentzPairFrame_isLorentz : IsLorentzMap (lorentzPairFrame he hf hef) :=
  lorentzFrameLinear_preserves he hf hef

theorem lorentzPairFrame_isOrthochronous : IsOrthochronousMap (lorentzPairFrame he hf hef) := by
  change 0 < (lorentzFrameLinear e f (1, 0)).1
  rw [lorentzFrameLinear_time, lorentzFrameFuture_time]
  exact lorentzFrameGamma_pos e f

theorem lorentzPairFrame_gamma_sq :
    (lorentzPairFrame he hf hef (1, 0)).1 ^ 2 = 1 + e.1 ^ 2 + f.1 ^ 2 := by
  rw [lorentzPairFrame_apply, lorentzFrameLinear_time, lorentzFrameFuture_time,
    lorentzFrameGamma_sq]

end VacuumBellSeparation

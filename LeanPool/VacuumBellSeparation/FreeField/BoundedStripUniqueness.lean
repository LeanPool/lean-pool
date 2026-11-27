/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Complex.Hadamard

/-!
# Uniqueness from one boundary for bounded Hilbert-valued strip functions

The zero lower boundary is used in the genuine three-lines theorem. The upper
boundary is then recovered by continuity from the open strip. This allows
bounded frequency cutoffs without a separate contour integration theorem.
-/

@[expose] public section

namespace VacuumBellSeparation

open Set Complex Complex.HadamardThreeLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_zero_on_verticalClosedStrip_of_bounded_lower_zero (f : ℂ → E)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1)) {M : ℝ}
    (hb : ∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ M)
    (hzero : ∀ z : ℂ, z.re = 0 → f z = 0)
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : f z = 0 := by
  have hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hb w hw
  have hinterior : ∀ w ∈ verticalStrip 0 1, ‖f w‖ ≤ 0 := by
    intro w hw
    have h := norm_le_interp_of_mem_verticalClosedStrip₀₁' f
      (z := w) (a := 0) (b := M) ⟨hw.1.le, hw.2.le⟩ hd hB
      (fun v hv => by rw [hzero v hv, norm_zero])
      (fun v hv => hb v ⟨by rw [hv]; norm_num, by rw [hv]⟩)
    simpa only [Real.zero_rpow (show 1 - w.re ≠ 0 by linarith [hw.2]), zero_mul] using h
  apply norm_le_zero_iff.mp
  apply le_on_closure hinterior (continuous_norm.comp_continuousOn hd.2) continuousOn_const
  simpa only [verticalStrip, verticalClosedStrip, Complex.closure_preimage_re,
    closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hz

theorem eq_zero_on_horizontalClosedStrip_of_bounded_lower_zero {a : ℝ} (ha : 0 < a)
    (f : ℂ → E) (hd : DiffContOnCl ℂ f (Complex.im ⁻¹' Ioo 0 a)) {M : ℝ}
    (hb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ a → ‖f z‖ ≤ M)
    (hzero : ∀ t : ℝ, f t = 0) {z : ℂ} (hz₀ : 0 ≤ z.im) (hza : z.im ≤ a) :
    f z = 0 := by
  let R : ℂ → ℂ := fun w => (a : ℂ) * Complex.I * w
  have him (w : ℂ) : (R w).im = a * w.re := by simp [R, Complex.mul_im, Complex.mul_re]
  have hR : Differentiable ℂ R := by dsimp [R]; fun_prop
  have hm : MapsTo R (verticalStrip 0 1) (Complex.im ⁻¹' Ioo 0 a) := by
    intro w hw
    change 0 < (R w).im ∧ (R w).im < a
    rw [him]
    exact ⟨mul_pos ha hw.1, by nlinarith [hw.2]⟩
  have hdR : DiffContOnCl ℂ (f ∘ R) (verticalStrip 0 1) :=
    hd.comp hR.diffContOnCl hm
  let w : ℂ := -Complex.I * z / (a : ℂ)
  have hwre : w.re = z.im / a := by simp [w, Complex.div_ofReal_re, Complex.mul_re]
  have hw : w ∈ verticalClosedStrip 0 1 := by
    change 0 ≤ w.re ∧ w.re ≤ 1
    rw [hwre]
    exact ⟨div_nonneg hz₀ ha.le, (div_le_one ha).mpr hza⟩
  have hRw : R w = z := by
    dsimp [R, w]
    field_simp [ha.ne']
    simp []
  have he := eq_zero_on_verticalClosedStrip_of_bounded_lower_zero (f ∘ R) hdR
    (M := M) (fun v hv => hb (R v) (by rw [him]; exact mul_nonneg ha.le hv.1)
      (by rw [him]; nlinarith [hv.2]))
    (fun v hv => by
      have hi : (R v).im = 0 := by rw [him, hv, mul_zero]
      have hr : R v = ((R v).re : ℂ) := by
        apply Complex.ext
        · rfl
        · simpa only [Complex.ofReal_im] using hi
      change f (R v) = 0
      rw [hr]
      exact hzero (R v).re) hw
  simpa only [Function.comp_apply, hRw] using he

end VacuumBellSeparation

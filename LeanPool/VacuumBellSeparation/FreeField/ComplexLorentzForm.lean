/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSpacetime

/-!
# Preservation of the actual complex mass shell

The complexified real Lorentz map preserves the complex bilinear
Minkowski form, without conjugation. Its inverse is the complexification
of the original inverse map. These statements use all four coordinates.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- The real spacetime vector formed by taking the real part of each component. -/
noncomputable def complexSpacetimeRe (z : ComplexSpacetime) : Spacetime :=
  (z.1.re, WithLp.toLp 2 (fun i => (z.2 i).re))

/-- The real spacetime vector formed by taking the imaginary part of each component. -/
noncomputable def complexSpacetimeIm (z : ComplexSpacetime) : Spacetime :=
  (z.1.im, WithLp.toLp 2 (fun i => (z.2 i).im))

theorem complexSpacetime_re_add_im (z : ComplexSpacetime) :
    complexSpacetimeOfReal (complexSpacetimeRe z) +
      Complex.I • complexSpacetimeOfReal (complexSpacetimeIm z) = z := by
  apply Prod.ext
  · apply Complex.ext <;> simp [complexSpacetimeOfReal, complexSpacetimeRe,
      complexSpacetimeIm, Complex.mul_re, Complex.mul_im]
  · ext i
    apply Complex.ext <;> simp [complexSpacetimeOfReal, complexSpacetimeRe,
      complexSpacetimeIm, Complex.mul_re, Complex.mul_im]

/-- Complex Minkowski form given by `z.1 * w.1 - spatialDot z.2 w.2`. -/
noncomputable def complexMinkowskiForm (z w : ComplexSpacetime) : ℂ :=
  z.1 * w.1 - spatialDot z.2 w.2

theorem complexMinkowskiForm_add_left (x y z : ComplexSpacetime) :
    complexMinkowskiForm (x + y) z = complexMinkowskiForm x z + complexMinkowskiForm y z := by
  simp only [complexMinkowskiForm, Prod.fst_add, Prod.snd_add, spatialDot_eq, Pi.add_apply]
  ring

theorem complexMinkowskiForm_add_right (x y z : ComplexSpacetime) :
    complexMinkowskiForm x (y + z) = complexMinkowskiForm x y + complexMinkowskiForm x z := by
  simp only [complexMinkowskiForm, Prod.fst_add, Prod.snd_add, spatialDot_eq, Pi.add_apply]
  ring

theorem complexMinkowskiForm_smul_left (a : ℂ) (x y : ComplexSpacetime) :
    complexMinkowskiForm (a • x) y = a * complexMinkowskiForm x y := by
  change (a * x.1) * y.1 - spatialDot (fun i => a * x.2 i) y.2 =
    a * (x.1 * y.1 - spatialDot x.2 y.2)
  simp only [spatialDot_eq]
  ring

theorem complexMinkowskiForm_smul_right (a : ℂ) (x y : ComplexSpacetime) :
    complexMinkowskiForm x (a • y) = a * complexMinkowskiForm x y := by
  change x.1 * (a * y.1) - spatialDot x.2 (fun i => a * y.2 i) =
    a * (x.1 * y.1 - spatialDot x.2 y.2)
  simp only [spatialDot_eq]
  ring

theorem complexMinkowskiForm_ofReal (x y : Spacetime) :
    complexMinkowskiForm (complexSpacetimeOfReal x) (complexSpacetimeOfReal y) =
      (minkowskiForm x y : ℂ) := by
  change (x.1 : ℂ) * (y.1 : ℂ) -
    spatialDot (fun i => (x.2 i : ℂ)) (fun i => (y.2 i : ℂ)) = _
  rw [real_spatialDot]
  simp only [minkowskiForm, Complex.ofReal_sub, Complex.ofReal_mul]

theorem complexifiedSpacetimeMap_re_im (Λ : Spacetime ≃L[ℝ] Spacetime) (z : ComplexSpacetime) :
    complexifiedSpacetimeMap Λ z =
      complexSpacetimeOfReal (Λ (complexSpacetimeRe z)) +
        Complex.I • complexSpacetimeOfReal (Λ (complexSpacetimeIm z)) := by
  rw [← complexifiedSpacetimeMap_ofReal, ← complexifiedSpacetimeMap_ofReal,
    ← map_smul, ← map_add, complexSpacetime_re_add_im]

theorem complexMinkowskiForm_lorentz
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (z w : ComplexSpacetime) :
    complexMinkowskiForm (complexifiedSpacetimeMap Λ z) (complexifiedSpacetimeMap Λ w) =
      complexMinkowskiForm z w := by
  calc
    _ = complexMinkowskiForm
        (complexSpacetimeOfReal (complexSpacetimeRe z) +
          Complex.I • complexSpacetimeOfReal (complexSpacetimeIm z))
        (complexSpacetimeOfReal (complexSpacetimeRe w) +
          Complex.I • complexSpacetimeOfReal (complexSpacetimeIm w)) := by
      simp only [complexifiedSpacetimeMap_re_im, complexMinkowskiForm_add_left,
        complexMinkowskiForm_add_right, complexMinkowskiForm_smul_left,
        complexMinkowskiForm_smul_right, complexMinkowskiForm_ofReal]
      rw [hΛ (complexSpacetimeRe z) (complexSpacetimeRe w),
        hΛ (complexSpacetimeIm z) (complexSpacetimeRe w),
        hΛ (complexSpacetimeRe z) (complexSpacetimeIm w),
        hΛ (complexSpacetimeIm z) (complexSpacetimeIm w)]
    _ = _ := by rw [complexSpacetime_re_add_im, complexSpacetime_re_add_im]

theorem complexifiedSpacetimeMap_mem_shell
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) {m : ℝ} {z : ComplexSpacetime}
    (hz : z ∈ complexShell m) : complexifiedSpacetimeMap Λ z ∈ complexShell m := by
  change (complexifiedSpacetimeMap Λ z).1 ^ 2 -
    spatialDot (complexifiedSpacetimeMap Λ z).2 (complexifiedSpacetimeMap Λ z).2 = (m : ℂ) ^ 2
  rw [pow_two]
  change complexMinkowskiForm (complexifiedSpacetimeMap Λ z) (complexifiedSpacetimeMap Λ z) = _
  rw [complexMinkowskiForm_lorentz Λ hΛ]
  change z.1 ^ 2 - spatialDot z.2 z.2 = (m : ℂ) ^ 2 at hz
  simpa only [complexMinkowskiForm, ← pow_two] using hz

theorem complexifiedSpacetimeMap_inverse (Λ : Spacetime ≃L[ℝ] Spacetime) (z : ComplexSpacetime) :
    complexifiedSpacetimeMap Λ.symm (complexifiedSpacetimeMap Λ z) = z := by
  rw [complexifiedSpacetimeMap_re_im Λ z, map_add, map_smul,
    complexifiedSpacetimeMap_ofReal, complexifiedSpacetimeMap_ofReal,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
    complexSpacetime_re_add_im]

end VacuumBellSeparation

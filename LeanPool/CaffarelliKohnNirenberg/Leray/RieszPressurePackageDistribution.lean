/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageIdentity
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageSlices

/-!
# Distributional equation for space-time pressure slices

The spatial sign identity holds on almost every time slice of a space-time
tensor, for every smooth compactly supported spatial test function.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

theorem rieszPressureSpaceTime_slice_laplacian_identity
    (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, rieszPressureSpaceTime r hr F hF (x, t) *
            (-CKN.spatialLaplacian ψ x) =
          ∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
            F i j (x, t) * CKN.mixedSecond ψ i j x := by
  have hSlice := rieszPressureSpaceTime_slice_ae_eq r hr F hF
  filter_upwards [hSlice] with t hSliceT
  obtain ⟨hFt, hPressureSlice⟩ := hSliceT
  intro ψ hψ hψc
  have hSpatial := rieszPressureSlice_laplacian_identity_of_memLp
    r hr (fun i j x => F i j (x, t)) hFt ψ hψ hψc
  calc
    ∫ x, rieszPressureSpaceTime r hr F hF (x, t) *
        (-CKN.spatialLaplacian ψ x) =
      ∫ x, (rieszPressureSlice r hr
        (fun i j => (hFt i j).toLp (fun y : Vec3 => F i j (y, t))) : Vec3 → ℝ) x *
          (-CKN.spatialLaplacian ψ x) := by
        apply integral_congr_ae
        filter_upwards [hPressureSlice] with x hx
        rw [hx]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
          F i j (x, t) * CKN.mixedSecond ψ i j x := hSpatial

end CKN.Leray

end

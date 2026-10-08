/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.EndpointTrilinear
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeBoundEndpoint

/-!
# Fixed-time endpoint convection estimates

The endpoint slice estimate bounds the relative convection by the gradient
energy and the squared spatial `L∞` coefficient. The trilinear companion gives
the majorant used in the endpoint density passage (`lem:lps-comparison`).
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The fixed-time endpoint estimates for a convection difference. -/
theorem lps_endpoint_relative_convection_slice
    {u w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (huMeas : AEStronglyMeasurable u volume)
    (huInf : MemLp (fun x => vec3EuclideanNorm (u x)) ∞ volume)
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume) :
    |∫ x : Vec3, ∑ i : Fin 3, u x i * ∑ j : Fin 3, w x j * Dw x i j| ≤
        (1 / 2 : ℝ) * (∫ x : Vec3,
          ∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2) +
          (81 / 2 : ℝ) *
            (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) ∞ volume).toReal ^ 2 *
            (∫ x : Vec3, ∑ i : Fin 3, w x i ^ 2) ∧
      ∫ x : Vec3, vec3EuclideanNorm (w x) *
          Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2) *
          vec3EuclideanNorm (u x) ≤
        (1 / 2 : ℝ) * (∫ x : Vec3,
          (Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dw x i j ^ 2)) ^ 2) +
          (1 / 2 : ℝ) * (∫ x : Vec3, vec3EuclideanNorm (w x) ^ 2) *
            (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x)) ∞ volume).toReal ^ 2 := by
  have hrelative := lps_slice_relative_bound_infty huMeas huInf hw2 hDw2
  have htri := lps_slice_trilinear_bound_infinite hw2
    huMeas hDw2.aestronglyMeasurable
    (fun i j => (hDw2.eval i).eval j)
    (by simpa only [memLp_iff] using huInf.eLpNorm_lt_top)
  exact ⟨hrelative, htri⟩

end ESS

end

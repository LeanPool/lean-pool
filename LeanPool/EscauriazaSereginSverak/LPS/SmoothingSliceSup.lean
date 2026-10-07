/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeRegularitySpatial
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointRep

/-!
# Uniform bounds on time slices of `L²(I; H²)` fields

`prop:lps-smoothing`: an `L²(I; H²)` space-time field is bounded, on almost every time slice,
by the `H²` norm of the slice.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- On almost every time slice an `L²(I;H²)` field is bounded by a universal multiple of the
`H²` norm of the slice (`prop:lps-smoothing`). -/
theorem lps_ae_slice_sup_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a b : ℝ} {f : Vec3 × ℝ → ℝ} {D : List (Fin 3) → Vec3 × ℝ → ℝ},
      IsL2SobolevFamilyOn 2 (Set.univ : Set Vec3) (Ioo a b) f D →
      ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
        (f (x, t)) ^ 2 ≤ K * ∑ α ∈ sobolevWords 2, ∫ y : Vec3, (D α (y, t)) ^ 2 := by
  obtain ⟨C, hC, hrep⟩ := lps_sobolevFamily_contDiff_rep 0
  refine ⟨C ^ 2, by positivity, fun {a b f D} hD => ?_⟩
  filter_upwards [ESS.LPS.lps_sobolevFamily_spatialSlices_ae hD] with t ht
  obtain ⟨g, -, hgf, -, hgb⟩ := hrep (fun x => f (x, t)) (fun α x => D α (x, t)) ht
  filter_upwards [hgf] with x hx
  have h1 := hgb [] (by simp) x
  simp only [wordDeriv] at h1
  have h2 : (g x) ^ 2 ≤ C ^ 2 * sobolevNormSqOn (0 + 2) univ (fun α x => D α (x, t)) := by
    have h0 : 0 ≤ Real.sqrt (sobolevNormSqOn (0 + 2) univ (fun α x => D α (x, t))) :=
      Real.sqrt_nonneg _
    calc (g x) ^ 2 = |g x| ^ 2 := (sq_abs _).symm
      _ ≤ (C * Real.sqrt (sobolevNormSqOn (0 + 2) univ (fun α x => D α (x, t)))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = C ^ 2 * sobolevNormSqOn (0 + 2) univ (fun α x => D α (x, t)) := by
          rw [mul_pow, Real.sq_sqrt]
          exact Finset.sum_nonneg fun α _ => integral_nonneg fun y => sq_nonneg _
  rw [← hx]
  simpa [sobolevNormSqOn] using h2

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCGamma

/-!
# Source box of the Gaussian estimate

The output box remains inside the source cylinder, so its field energy is
integrable from the weak derivative data.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The Gaussian target box lies inside the original space-time cylinder. -/
theorem uc_source_target_box_subset
    (R T scale ρ t : ℝ) (hR : 0 < R) (hT : 0 < T)
    (hscale : 0 < scale) (hρ : 4 ≤ ρ)
    (hball : scale * ρ ≤ 3 * R / 4)
    (htime : 2 * scale ^ 2 ≤ 3 * T / 4)
    (hscaleSq : scale ^ 2 = 2 * t)
    (x₀ x : Vec3)
    (hx : vec3EuclideanNorm (x - x₀) ≤
      (3 / 8) * Real.sqrt (2 / 100) * R) :
    spaceTimeSet (vec3Ball x scale) (Ioo t (2 * t)) ⊆
      spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T) := by
  have hμ : 0 < Real.sqrt (2 / 100 : ℝ) := by positivity
  have hμhalf : Real.sqrt (2 / 100 : ℝ) ≤ 1 / 2 := by
    have hμsq : Real.sqrt (2 / 100 : ℝ) ^ 2 = 1 / 50 := by norm_num
    nlinarith only [hμ, hμsq]
  have hscaleR : scale ≤ 3 * R / 16 := by
    have hprod : 4 * scale ≤ scale * ρ :=
      by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hρ hscale.le
    linarith only [hprod, hball]
  have hdR : vec3EuclideanNorm (x - x₀) ≤ 3 * R / 16 := by
    have hμR : Real.sqrt (2 / 100 : ℝ) * R ≤ (1 / 2) * R :=
      mul_le_mul_of_nonneg_right hμhalf hR.le
    nlinarith only [hx, hμR]
  intro z hz
  constructor
  · have hdist : vec3EuclideanNorm (z.1 - x) < scale :=
      (mem_vec3Ball).1 hz.1
    have htri := vec3EuclideanNorm_add_le (z.1 - x) (x - x₀)
    have heq : z.1 - x + (x - x₀) = z.1 - x₀ := by abel
    rw [heq] at htri
    apply (mem_vec3Ball).2
    linarith only [htri, hdist, hdR, hscaleR, hR]
  · have h2t : 2 * t < T := by
      rw [← hscaleSq]
      linarith only [htime, hT]
    have ht : 0 < t := by nlinarith only [hscaleSq, hscale]
    exact ⟨by linarith only [hz.2.1, ht], hz.2.2.trans h2t⟩

end ESS

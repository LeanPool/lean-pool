/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRescaling

/-!
# Values on the shifted short-time cylinder

The shifted field is continuous through its lower time face, vanishes there,
and inherits the original quadratic spatial growth estimate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The shifted map carries the half-space cylinder with lower time face
included into the original positive-time cylinder with its zero face. -/
theorem bu_short_map_mem_halfClosure
    (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    {z : ParabolicPoint}
    (hz : z ∈ {x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) 1) :
    buAffinePoint (-scale ^ 2 / 2) scale z ∈
      {x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1 := by
  rcases hz with ⟨hy, hs⟩
  have hsq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hsqle : scale ^ 2 ≤ 1 := pow_le_one₀ hscale.le hscale1
  change 0 < scale * z.1 2 ∧
    -scale ^ 2 / 2 + scale ^ 2 * z.2 ∈ Ico 0 1
  refine ⟨mul_pos hscale hy, ?_⟩
  constructor
  · have hm := mul_nonneg hsq.le (sub_nonneg.mpr hs.1)
    nlinarith only [hm]
  · have hm := mul_lt_mul_of_pos_left hs.2 hsq
    nlinarith only [hm, hsqle]

/-- The shifted field is continuous on the cylinder with its lower time
face included. -/
theorem bu_short_field_continuousOn
    (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1)) :
    ContinuousOn (buAffineField (-scale ^ 2 / 2) scale w)
      ({x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) 1) := by
  change ContinuousOn (w ∘ buAffinePoint (-scale ^ 2 / 2) scale) _
  exact hcont.comp (buAffinePoint_continuous _ _).continuousOn
    (fun z hz => bu_short_map_mem_halfClosure scale hscale hscale1 hz)

/-- Quadratic spatial growth transfers to the shifted initial interval. -/
theorem bu_short_field_growth
    (M scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) 1)) :
    vec3EuclideanNorm (buAffineField (-scale ^ 2 / 2) scale w z) ≤
      Real.exp ((M * scale ^ 2) * vec3EuclideanNorm z.1 ^ 2) := by
  have hm := bu_short_map_mem_halfClosure scale hscale hscale1
    (show z ∈ {x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) 1 from
      ⟨hz.1, hz.2.1.le, hz.2.2⟩)
  have hsource : buAffinePoint (-scale ^ 2 / 2) scale z ∈
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1) := by
    refine ⟨hm.1, ?_, hm.2.2⟩
    have hsq : 0 < scale ^ 2 := sq_pos_of_pos hscale
    have ht := mul_pos hsq (sub_pos.mpr hz.2.1)
    change 0 < -scale ^ 2 / 2 + scale ^ 2 * z.2
    nlinarith only [ht]
  have hg := hgrowth (buAffinePoint (-scale ^ 2 / 2) scale z) hsource
  have hnorm : vec3EuclideanNorm (scale • z.1) ^ 2 =
      scale ^ 2 * vec3EuclideanNorm z.1 ^ 2 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos hscale]
    ring
  change vec3EuclideanNorm (w (buAffinePoint (-scale ^ 2 / 2) scale z)) ≤ _
  calc
    _ ≤ Real.exp (M * vec3EuclideanNorm (scale • z.1) ^ 2) := hg
    _ = _ := by rw [hnorm]; ring_nf

end ESS

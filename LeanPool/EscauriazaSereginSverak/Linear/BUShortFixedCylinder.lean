/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTimeErrorBound
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSupportGeometry

/-!
# A fixed cylinder for the lower-time limit

For fixed spatial radius all lower-time cutoff supports lie in one compact
cylinder. This keeps the spatial-phase derivative bounds independent of
the lower-time transition width.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Compact cylinder containing all supports at a fixed spatial radius. -/
@[expose] def buShortFixedCylinder (R : ℝ) : Set ParabolicPoint :=
  parabolicHomeomorph ⁻¹'
    ((euclideanClosedBall 0 (2 * R) ∩ {x : Vec3 | 1 ≤ x 2}) ×ˢ
      Icc (1 / 2 : ℝ) 1)

/-- The fixed cylinder is compact for positive radius. -/
theorem buShortFixedCylinder_isCompact
    {R : ℝ} (hR : 0 < R) : IsCompact (buShortFixedCylinder R) := by
  unfold buShortFixedCylinder
  apply parabolicHomeomorph.isCompact_preimage.mpr
  have hclosed : IsClosed {x : Vec3 | 1 ≤ x 2} :=
    isClosed_le continuous_const (continuous_apply 2)
  exact ((isCompact_euclideanClosedBall (0 : Vec3)
    (show 0 ≤ 2 * R by positivity)).inter_right hclosed).prod isCompact_Icc

/-- Every compact cutoff support at radius `R` lies in the same closed
spatial ball and time interval, independently of `ε`. -/
theorem buShortCutSupport_subset_fixedCylinder
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) :
    buCutSupportSet (buShortFullCutoff scale R hR ε) ⊆
      buShortFixedCylinder R := by
  let κ := buShortFullCutoff scale R hR ε
  have hκts := (buShortFullCutoff_compact_support
    hscale hscale1 hR hε).2
  have hspatial : tsupport κ ⊆
      {q : Vec3 × ℝ | q.1 ∈ euclideanClosedBall 0 (2 * R)} := by
    apply closure_minimal _
      ((isClosed_euclideanClosedBall (0 : Vec3) (2 * R)).preimage continuous_fst)
    intro q hq
    have hχne : ucSpatialCutoff (2 * R) (by positivity) q.1 ≠ 0 := by
      intro hzero
      exact hq (by simp [κ, buShortFullCutoff, hzero])
    have hχts : q.1 ∈ tsupport (ucSpatialCutoff (2 * R) (by positivity)) :=
      subset_tsupport _ (Function.mem_support.mpr hχne)
    have hball := ucSpatialCutoff_tsupport
      (show 0 < 2 * R by positivity) hχts
    have hnorm : vec3EuclideanNorm (q.1 - 0) < 2 * R :=
      (mem_vec3Ball).1 hball
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (show 0 ≤ 2 * R by positivity)).2
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using hnorm.le
  intro z hz
  have hqsp := hspatial hz
  have hqtime := hκts hz
  exact ⟨⟨hqsp, (show (1 : ℝ) ≤ (parabolicHomeomorph z).1 2 from
    hqtime.1.le)⟩, ⟨hqtime.2.1.le, hqtime.2.2.le⟩⟩

end ESS

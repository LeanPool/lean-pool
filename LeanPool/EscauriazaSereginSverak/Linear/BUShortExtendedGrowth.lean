/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortExtendedData
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGrowthAnyInterval

/-!
# Quadratic growth and local energy on the extended cylinder

The physical growth hypothesis supplies local velocity energy after the
short-time rescaling.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Quadratic spatial growth transfers through the extended short-time
parabolic rescaling. -/
theorem bu_short_extended_growth
    (M scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2))) :
    vec3EuclideanNorm (buAffineField (-scale ^ 2 / 2) scale w z) ≤
      Real.exp ((M * scale ^ 2) * vec3EuclideanNorm z.1 ^ 2) := by
  have hs : (0 : ℝ) < -scale ^ 2 / 2 + scale ^ 2 * z.2 ∧
      -scale ^ 2 / 2 + scale ^ 2 * z.2 < 1 := by
    have hsq : 0 < scale ^ 2 := sq_pos_of_pos hscale
    have hsqle : scale ^ 2 ≤ 1 := pow_le_one₀ hscale.le hscale1
    constructor
    · have h := mul_pos hsq (sub_pos.mpr hz.2.1)
      nlinarith only [h]
    · have h := mul_lt_mul_of_pos_left hz.2.2 hsq
      nlinarith only [h, hsqle]
  have hsource : buAffinePoint (-scale ^ 2 / 2) scale z ∈
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (0 : ℝ) 1) := by
    change 0 < scale * z.1 2 ∧
      -scale ^ 2 / 2 + scale ^ 2 * z.2 ∈ Ioo 0 1
    exact ⟨mul_pos hscale hz.1, hs⟩
  have hg := hgrowth _ hsource
  have hnorm : vec3EuclideanNorm (scale • z.1) ^ 2 =
      scale ^ 2 * vec3EuclideanNorm z.1 ^ 2 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos hscale]
    ring
  change vec3EuclideanNorm (w (buAffinePoint (-scale ^ 2 / 2) scale z)) ≤ _
  calc
    _ ≤ Real.exp (M * vec3EuclideanNorm (scale • z.1) ^ 2) := hg
    _ = _ := by rw [hnorm]; ring_nf

/-- The extended short-time cylinder has finite full quadratic data on
every bounded measurable subset. -/
theorem bu_short_extended_local_quadratic_l2
    (M scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) :
    ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)) →
      Bornology.IsBounded S →
      (∫⁻ z in S,
        ‖(buAffineField (-scale ^ 2 / 2) scale w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDw (-scale ^ 2 / 2) scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineD2w (-scale ^ 2 / 2) scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDtw (-scale ^ 2 / 2) scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  have hweak' := bu_short_extended_weak_derivatives scale hscale hscale1
    w Dw D2w Dtw hweak
  have hderiv' := bu_short_extended_derivative_l2 scale hscale hscale1
    w Dw D2w Dtw hweak hL2
  have hgrowth' : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)),
      vec3EuclideanNorm (v z) ≤
        Real.exp ((M * scale ^ 2) * vec3EuclideanNorm z.1 ^ 2) := by
    intro z hz
    exact bu_short_extended_growth M scale hscale hscale1 w hgrowth hz
  have hMbar : 0 < max (M * scale ^ 2) ((1 / (10 : ℝ) ^ 12) / 2) :=
    (by norm_num : (0 : ℝ) < (1 / (10 : ℝ) ^ 12) / 2).trans_le
      (le_max_right _ _)
  have hgrowthBar : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)),
      vec3EuclideanNorm (v z) ≤
        Real.exp (max (M * scale ^ 2) ((1 / (10 : ℝ) ^ 12) / 2) *
          vec3EuclideanNorm z.1 ^ 2) := by
    intro z hz
    exact (hgrowth' z hz).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (le_max_left _ _) (sq_nonneg _)))
  have hV := bu_growth_implies_local_l2_on_interval
    (Ioo (1 / 2 : ℝ) (3 / 2)) (max (M * scale ^ 2) ((1 / (10 : ℝ) ^ 12) / 2)) hMbar v hgrowthBar
  intro S hS hSb
  have hVfin : (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    hV S hS hSb
  have hDfin := hderiv' S hS hSb
  have hAEM : AEMeasurable (fun z => ‖v z‖ₑ ^ (2 : ℝ))
      (volume.restrict S) := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (hweak'.1.mono_set hS |>.aestronglyMeasurable.enorm)
  have hsplit := lintegral_add_left' hAEM
    (μ := volume.restrict S) (f := fun z => ‖v z‖ₑ ^ (2 : ℝ))
    (g := fun z => ‖Dv z‖ₑ ^ (2 : ℝ) +
      ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ))
  have hsum : (∫⁻ z in S,
      ‖v z‖ₑ ^ (2 : ℝ) +
      (‖Dv z‖ₑ ^ (2 : ℝ) + ‖D2v z‖ₑ ^ (2 : ℝ) +
        ‖Dtv z‖ₑ ^ (2 : ℝ))) < ⊤ := by
    rw [hsplit]
    exact ENNReal.add_lt_top.mpr ⟨hVfin, hDfin⟩
  apply lt_of_le_of_lt ?_ hsum
  apply lintegral_mono
  intro z
  change _ ≤ ‖v z‖ₑ ^ (2 : ℝ) +
      (‖Dv z‖ₑ ^ (2 : ℝ) + ‖D2v z‖ₑ ^ (2 : ℝ) +
        ‖Dtv z‖ₑ ^ (2 : ℝ))
  simp only [v, Dv, D2v, Dtv]
  exact le_of_eq (by ac_rfl)

end ESS

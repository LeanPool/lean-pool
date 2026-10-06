/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRescaling
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRescalingValues
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellCylinderSpace
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Extended rescaled data for short-time cells

The Gaussian averaging boxes near the top of the dyadic range extend
slightly past normalized time one. The original field provides data up
to normalized time three halves whenever the parabolic scale is small.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The extended normalized interval maps to the physical interval
from zero to `scale²`. -/
theorem bu_short_extended_source_interval (scale : ℝ) :
    Ioo (-scale ^ 2 / 2 + scale ^ 2 * (1 / 2 : ℝ))
      (-scale ^ 2 / 2 + scale ^ 2 * (3 / 2 : ℝ)) =
      Ioo (0 : ℝ) (scale ^ 2) := by
  congr 1 <;> ring

/-- The shifted field is continuous on the extended cylinder through its
lower time face. -/
theorem bu_short_extended_continuousOn
    (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1)) :
    ContinuousOn (buAffineField (-scale ^ 2 / 2) scale w)
      ({x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) (3 / 2)) := by
  change ContinuousOn (w ∘ buAffinePoint (-scale ^ 2 / 2) scale) _
  apply hcont.comp (buAffinePoint_continuous _ _).continuousOn
  intro z hz
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

/-- Weak derivatives persist on the extended normalized interval. -/
theorem bu_short_extended_weak_derivatives
    (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2))
      (buAffineField (-scale ^ 2 / 2) scale w)
      (buAffineDw (-scale ^ 2 / 2) scale Dw)
      (buAffineD2w (-scale ^ 2 / 2) scale D2w)
      (buAffineDtw (-scale ^ 2 / 2) scale Dtw) := by
  have hI : Ioo (0 : ℝ) (scale ^ 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨ht.1, ht.2.trans_le (pow_le_one₀ hscale.le hscale1)⟩
  have hrestricted := bu_weak_restrict_time hI w Dw D2w Dtw hweak
  exact bu_affine_weak_derivatives_interval
    (-scale ^ 2 / 2) scale (1 / 2) (3 / 2) hscale w Dw D2w Dtw
    (by simpa only [bu_short_extended_source_interval] using hrestricted)

/-- The derivative square integral is locally finite on the extended
normalized interval. -/
theorem bu_short_extended_derivative_l2
    (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
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
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∀ K : Set ParabolicPoint,
      K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)) →
      Bornology.IsBounded K →
      (∫⁻ z in K,
        ‖(buAffineDw (-scale ^ 2 / 2) scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineD2w (-scale ^ 2 / 2) scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDtw (-scale ^ 2 / 2) scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hI : Ioo (0 : ℝ) (scale ^ 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨ht.1, ht.2.trans_le (pow_le_one₀ hscale.le hscale1)⟩
  have hrestricted := bu_weak_restrict_time hI w Dw D2w Dtw hweak
  have hL2restricted (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 (scale ^ 2)))
      (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply hL2 S _ hSb
    intro z hz
    exact ⟨(hS hz).1, hI (hS hz).2⟩
  exact bu_affine_derivative_l2_interval
    (-scale ^ 2 / 2) scale (1 / 2) (3 / 2) hscale hscale1
    w Dw D2w Dtw
    (by simpa only [bu_short_extended_source_interval] using hrestricted)
    (by simpa only [bu_short_extended_source_interval] using hL2restricted)

/-- The weak heat inequality holds on the extended normalized interval
with the scaled coefficient. -/
theorem bu_short_extended_heat_ae_bound
    (scale c₁ : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hc₁ : 0 ≤ c₁)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z))) :
    ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)))),
      vec3EuclideanNorm
        (ucWeakHeatVector (buAffineD2w (-scale ^ 2 / 2) scale D2w)
          (buAffineDtw (-scale ^ 2 / 2) scale Dtw) z) ≤
        c₁ * scale * (Real.sqrt (spatialGradientSq
          (buAffineField (-scale ^ 2 / 2) scale w)
          (buAffineDw (-scale ^ 2 / 2) scale Dw) z) +
          vec3EuclideanNorm ((buAffineField (-scale ^ 2 / 2) scale w) z)) := by
  have hI : Ioo (0 : ℝ) (scale ^ 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨ht.1, ht.2.trans_le (pow_le_one₀ hscale.le hscale1)⟩
  exact bu_affine_weak_heat_ae_bound_interval
    (-scale ^ 2 / 2) scale (1 / 2) (3 / 2) c₁ hscale hscale1 hc₁
    (by simpa only [bu_short_extended_source_interval] using hI)
    w Dw D2w Dtw hineq

end ESS

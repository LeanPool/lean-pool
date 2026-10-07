/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalHeat
public import LeanPool.EscauriazaSereginSverak.Linear.BUWeakRestriction

/-!
# Short-time parabolic coordinates

The initial physical interval is placed at the lower face of the shifted
half-space Carleman cylinder in `lem:bu-small-time`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The shifted parabolic map sends the normalized interval `(1/2,1)`
onto the initial physical interval `(0,scale²/2)`. -/
theorem bu_short_source_interval (scale : ℝ) :
    Ioo (-scale ^ 2 / 2 + scale ^ 2 * (1 / 2 : ℝ))
      (-scale ^ 2 / 2 + scale ^ 2 * 1) =
      Ioo (0 : ℝ) (scale ^ 2 / 2) := by
  congr 1 <;> ring

/-- Weak derivatives transfer to the shifted half-space cylinder. -/
theorem bu_short_weak_derivatives
    (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo (1 / 2 : ℝ) 1)
      (buAffineField (-scale ^ 2 / 2) scale w)
      (buAffineDw (-scale ^ 2 / 2) scale Dw)
      (buAffineD2w (-scale ^ 2 / 2) scale D2w)
      (buAffineDtw (-scale ^ 2 / 2) scale Dtw) := by
  have hI : Ioo (0 : ℝ) (scale ^ 2 / 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    refine ⟨ht.1, ht.2.trans_le ?_⟩
    have hsq : scale ^ 2 ≤ 1 := pow_le_one₀ hscale.le hscale1
    linarith only [hsq]
  have hrestricted := bu_weak_restrict_time hI w Dw D2w Dtw hweak
  have hshifted := bu_affine_weak_derivatives_interval
    (-scale ^ 2 / 2) scale (1 / 2) 1 hscale w Dw D2w Dtw
    (by simpa only [bu_short_source_interval] using hrestricted)
  exact hshifted

/-- The local quadratic derivative bound persists on the shifted
half-space cylinder. -/
theorem bu_short_derivative_l2
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
      K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (1 / 2 : ℝ) 1) →
      Bornology.IsBounded K →
      (∫⁻ z in K,
        ‖(buAffineDw (-scale ^ 2 / 2) scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineD2w (-scale ^ 2 / 2) scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDtw (-scale ^ 2 / 2) scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hI : Ioo (0 : ℝ) (scale ^ 2 / 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    refine ⟨ht.1, ht.2.trans_le ?_⟩
    have hsq : scale ^ 2 ≤ 1 := pow_le_one₀ hscale.le hscale1
    linarith only [hsq]
  have hrestricted := bu_weak_restrict_time hI w Dw D2w Dtw hweak
  have hL2restricted (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 (scale ^ 2 / 2)))
      (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply hL2 S _ hSb
    intro z hz
    exact ⟨(hS hz).1, hI (hS hz).2⟩
  have hshifted := bu_affine_derivative_l2_interval
    (-scale ^ 2 / 2) scale (1 / 2) 1 hscale hscale1
    w Dw D2w Dtw
    (by simpa only [bu_short_source_interval] using hrestricted)
    (by simpa only [bu_short_source_interval] using hL2restricted)
  exact hshifted

/-- The differential inequality in the shifted cylinder has coefficient
`c₁ * scale`. -/
theorem bu_short_heat_ae_bound
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
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (1 / 2 : ℝ) 1))),
      vec3EuclideanNorm
        (ucWeakHeatVector (buAffineD2w (-scale ^ 2 / 2) scale D2w)
          (buAffineDtw (-scale ^ 2 / 2) scale Dtw) z) ≤
        c₁ * scale * (Real.sqrt (spatialGradientSq
          (buAffineField (-scale ^ 2 / 2) scale w)
          (buAffineDw (-scale ^ 2 / 2) scale Dw) z) +
          vec3EuclideanNorm ((buAffineField (-scale ^ 2 / 2) scale w) z)) := by
  have hI : Ioo (0 : ℝ) (scale ^ 2 / 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    refine ⟨ht.1, ht.2.trans_le ?_⟩
    have hsq : scale ^ 2 ≤ 1 := pow_le_one₀ hscale.le hscale1
    linarith only [hsq]
  exact bu_affine_weak_heat_ae_bound_interval
    (-scale ^ 2 / 2) scale (1 / 2) 1 c₁ hscale hscale1 hc₁
    (by simpa only [bu_short_source_interval] using hI)
    w Dw D2w Dtw hineq

end ESS

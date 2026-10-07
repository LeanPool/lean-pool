/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffBounds
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRescaling

/-!
# Weak heat inequality for the compact short-time field

The scaled differential inequality and scalar product rule give a
pointwise almost-everywhere bound for the compact cutoff field.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The spatial cutoff derivative size at a parabolic point. -/
@[expose] def buShortCutoffGradientSize (scale R : ℝ) (hR : 0 < R)
    (ε : ℝ) (z : ParabolicPoint) : ℝ :=
  ∑ j : Fin 3,
    |spatialPartial (buCutScalar (buShortFullCutoff scale R hR ε)) j z|

/-- The weak heat vector of the compact short-time field obeys the
scaled inequality plus explicit scalar cutoff errors. -/
theorem bu_short_cutoff_heat_ae_bound
    (scale R ε c₁ : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hc₁ : 0 ≤ c₁)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z))) :
    let κ := buShortFullCutoff scale R hR ε
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
    let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    let D2W := buCutD2 κ v Dv D2v
    let DtW := buCutDt κ v Dtv
    ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (1 / 2 : ℝ) 1))),
      vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ≤
        c₁ * scale * (vec3EuclideanNorm (W z) +
          3 * Real.sqrt (spatialGradientSq W DW z)) +
        (3 * (c₁ * scale) * buShortCutoffGradientSize scale R hR ε z +
          |timePartial (buCutScalar κ) z +
            ∑ j : Fin 3,
              spatialSecondPartial (buCutScalar κ) j j z|) *
          vec3EuclideanNorm (v z) +
        18 * buShortCutoffGradientSize scale R hR ε z *
          Real.sqrt (spatialGradientSq v Dv z) := by
  have hscaled := bu_short_heat_ae_bound scale c₁ hscale hscale1 hc₁
    w Dw D2w Dtw hineq
  filter_upwards [hscaled] with z hz
  let κ := buShortFullCutoff scale R hR ε
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  let M := buShortCutoffGradientSize scale R hR ε z
  have hM : 0 ≤ M := by
    dsimp [M, buShortCutoffGradientSize]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _
  have hderiv (j : Fin 3) :
      |spatialPartial (buCutScalar κ) j z| ≤ M :=
    buCut_spatialPartial_abs_le_sum κ z j
  exact buCut_heat_le κ v Dv D2v Dtv z (c₁ * scale)
    (mul_nonneg hc₁ hscale.le)
    (buShortFullCutoff_bounds scale R hR ε (parabolicHomeomorph z)).1
    M hM hderiv hz

end ESS

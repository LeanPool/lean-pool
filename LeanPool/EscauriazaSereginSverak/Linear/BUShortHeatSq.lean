/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatAE

/-!
# Quadratic heat inequality for the short-time cutoff

The weak heat inequality separates a quadratic term in the cutoff field
from an error containing derivatives of the scalar cutoff.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The scalar cutoff error appearing in the squared heat bound. -/
@[expose] def buShortCutoffHeatErrorSize (scale R : ℝ) (hR : 0 < R)
    (ε c₁ : ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) : ℝ :=
  (3 * (c₁ * scale) * buShortCutoffGradientSize scale R hR ε z +
    |timePartial (buCutScalar (buShortFullCutoff scale R hR ε)) z +
      ∑ j : Fin 3,
        spatialSecondPartial
          (buCutScalar (buShortFullCutoff scale R hR ε)) j j z|) *
      vec3EuclideanNorm (v z) +
    18 * buShortCutoffGradientSize scale R hR ε z *
      Real.sqrt (spatialGradientSq v Dv z)

/-- The square of the compact field's heat vector is bounded by a term
that can be absorbed in the Carleman left side and a cutoff error. -/
theorem bu_short_cutoff_heat_sq_ae_bound
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
      vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2 ≤
        36 * (c₁ * scale) ^ 2 *
          (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z) +
        2 * buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2 := by
  filter_upwards [bu_short_cutoff_heat_ae_bound scale R ε c₁
    hscale hscale1 hR hc₁ w Dw D2w Dtw hineq] with z hz
  let κ := buShortFullCutoff scale R hR ε
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  let D2W := buCutD2 κ v Dv D2v
  let DtW := buCutDt κ v Dtv
  let x := vec3EuclideanNorm (W z)
  let y := Real.sqrt (spatialGradientSq W DW z)
  let q := c₁ * scale
  let A := q * (x + 3 * y)
  let B := buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z
  have hL : vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ≤ A + B := by
    simpa only [A, B, q, x, y, W, DW, D2W, DtW, v, Dv, D2v, Dtv, κ,
      buShortCutoffHeatErrorSize, add_assoc] using hz
  have hL0 : 0 ≤ vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) :=
    vec3EuclideanNorm_nonneg _
  have hsq : vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2 ≤
      (A + B) ^ 2 :=
    (sq_le_sq₀ hL0 (hL0.trans hL)).2 hL
  have hG : 0 ≤ spatialGradientSq W DW z := by
    dsimp [spatialGradientSq]
    positivity
  have hy : y ^ 2 = spatialGradientSq W DW z := Real.sq_sqrt hG
  have hsum : (x + 3 * y) ^ 2 ≤
      18 * (x ^ 2 + spatialGradientSq W DW z) := by
    nlinarith only [sq_nonneg (x - 3 * y), sq_nonneg x, hy]
  have hA : A ^ 2 ≤
      18 * q ^ 2 * (x ^ 2 + spatialGradientSq W DW z) := by
    calc
      A ^ 2 = q ^ 2 * (x + 3 * y) ^ 2 := by dsimp [A]; ring
      _ ≤ q ^ 2 * (18 * (x ^ 2 + spatialGradientSq W DW z)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg q)
      _ = _ := by ring
  change vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2 ≤
    36 * q ^ 2 * (x ^ 2 + spatialGradientSq W DW z) + 2 * B ^ 2
  calc
    _ ≤ (A + B) ^ 2 := hsq
    _ ≤ 2 * (A ^ 2 + B ^ 2) := by nlinarith only [sq_nonneg (A - B)]
    _ ≤ 36 * q ^ 2 * (x ^ 2 + spatialGradientSq W DW z) +
          2 * B ^ 2 := by nlinarith only [hA]

end ESS

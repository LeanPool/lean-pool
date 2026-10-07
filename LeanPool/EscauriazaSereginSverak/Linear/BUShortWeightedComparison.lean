/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedSquareData

/-!
# Weighted cutoff error comparison

The squared heat error of the compact short-time cutoff is bounded by
its phase, shell, and lower-time majorants with no auxiliary
integrability assumptions.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- The integrated squared cutoff heat error obeys the phase and shell
comparison for fixed short-time parameters. -/
theorem bu_short_weighted_error_le_split
    (scale R ε c₁ C₁ C₂ a : ℝ)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 1 ≤ R) (hε : 0 < ε) (hc₁ : 0 ≤ c₁)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let K := buCutSupportSet
      (buShortFullCutoff scale R (by linarith only [hR]) ε)
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    (∫ z in K,
      buShortShiftedWeight scale a z *
        buShortCutoffHeatErrorSize scale R (by linarith only [hR])
          ε c₁ v Dv z ^ 2
      ∂(volume : Measure ParabolicPoint)) ≤
    (∫ z in K,
      4 * buShortShiftedWeight scale a z *
        (if z ∈ buShortWideGapRegion scale then
          buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
            (1 + z.1 2) ^ 4
        else buShortShellCoeff scale R c₁ ^ 2) *
        (vec3EuclideanNorm (v z) ^ 2 +
          spatialGradientSq v Dv z) +
      2 * buShortShiftedWeight scale a z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
      ∂(volume : Measure ParabolicPoint)) := by
  have hR0 : 0 < R := by linarith only [hR]
  let K := buCutSupportSet (buShortFullCutoff scale R hR0 ε)
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  have hbase := bu_short_weighted_error_integrable scale R ε c₁ a
    hscale hscale1 hR0 hε w Dw D2w Dtw hcont hweak hL2
  have hleft : IntegrableOn (fun z =>
      buShortShiftedWeight scale a z *
        buShortCutoffHeatErrorSize scale R hR0 ε c₁ v Dv z ^ 2)
      K volume := by
    have h := hbase.const_mul (Real.exp (-(2 * a * buShortB scale)))
    change Integrable (fun z => buShortShiftedWeight scale a z *
      buShortCutoffHeatErrorSize scale R hR0 ε c₁ v Dv z ^ 2)
      (volume.restrict K)
    convert h using 1
    funext z
    dsimp [buShortShiftedWeight]
    ring
  have hright := bu_short_weighted_split_integrable
    scale R ε c₁ C₁ C₂ a hscale hscale1 hR0 hε
    w Dw D2w Dtw hcont hweak hL2
  exact bu_short_weighted_error_integral_le_split
    scale R ε c₁ C₁ C₂ a hscale hscale1 hR hε hc₁ hC₁ hN
    hC₂ hP v Dv hleft hright

end ESS

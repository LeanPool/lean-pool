/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhaseDecay

/-!
# Vanishing shifted lower-time error

Removing the fixed normal phase from the Carleman density preserves
the vanishing lower-time transition error.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- The squared lower-time derivative contribution also vanishes for
the phase-shifted Carleman density. -/
theorem bu_short_shifted_early_error_tendsto_zero
    (M scale R a : ℝ) (hM : 0 < M)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1) (hR : 0 < R)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
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
    Tendsto (fun ε : ℝ =>
      let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
      let v := buAffineField (-scale ^ 2 / 2) scale w
      ∫ z in K, buShortShiftedWeight scale a z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
        ∂(volume : Measure ParabolicPoint))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let c := Real.exp (-(2 * a * buShortB scale))
  have hbase := bu_short_early_error_tendsto_zero M scale R a
    hM hscale hscale1 hR w Dw D2w Dtw
    hcont hinit hweak hL2 hgrowth
  have hscaled := hbase.const_mul c
  have hscaled' : Tendsto (fun ε : ℝ =>
      c * (let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
        let v := buAffineField (-scale ^ 2 / 2) scale w
        ∫ z in K, buShortCarlemanWeight a z *
          (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
            8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
          ∂(volume : Measure ParabolicPoint)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hscaled
  apply hscaled'.congr'
  filter_upwards [] with ε
  symm
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let v := buAffineField (-scale ^ 2 / 2) scale w
  change (∫ z in K, buShortShiftedWeight scale a z *
    (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
      8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
    ∂(volume : Measure ParabolicPoint)) =
    c * (∫ z in K, buShortCarlemanWeight a z *
      (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
        8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
      ∂(volume : Measure ParabolicPoint))
  rw [← integral_const_mul]
  congr 1
  funext z
  dsimp [buShortShiftedWeight, c]
  ring

end ESS

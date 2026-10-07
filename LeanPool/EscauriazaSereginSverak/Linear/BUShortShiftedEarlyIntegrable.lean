/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedSquareData

/-!
# Integrable lower-time transition density

At fixed radius and transition width, the shifted Carleman density
times the time-supported quadratic field belongs to `L¹`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- The shifted lower-time transition density is integrable on the
compact cutoff support. -/
theorem bu_short_shifted_early_integrable
    (scale R ε a : ℝ)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
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
    let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
    let v := buAffineField (-scale ^ 2 / 2) scale w
    IntegrableOn (fun z => buShortShiftedWeight scale a z *
      (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
        8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2)
      K volume := by
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let W := buShortShiftedWeight scale a
  let S : Set ParabolicPoint :=
    {z | 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε}
  have hK : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).1
  obtain ⟨hv, hDv, _, _⟩ := bu_short_support_memLp_data
    scale R ε hscale hscale1 hR hε w Dw D2w Dtw hcont hweak hL2
  have hv2 := (bu_memLp_quadratic_energy_integrable K v
    (buAffineDw (-scale ^ 2 / 2) scale Dw) hv hDv).1
  have htime : Continuous (fun z : ParabolicPoint => z.2) := by
    convert continuous_snd.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have hSmeas : MeasurableSet S := by
    change MeasurableSet ((fun z : ParabolicPoint => z.2) ⁻¹'
      Icc (1 / 2 + ε) (1 / 2 + 2 * ε))
    exact measurableSet_Icc.preimage htime.measurable
  have hvi : IntegrableOn (S.indicator
      (fun z => vec3EuclideanNorm (v z) ^ 2)) K volume :=
    hv2.indicator hSmeas
  have hWcont : ContinuousOn W K := by
    have hbase := buShortCarlemanWeight_continuousOn_support
      scale R ε a hscale hscale1 hR hε
    exact continuousOn_const.mul hbase
  have hWV := bu_integrableOn_mul_continuous_compact hK
    _ W hvi hWcont
  have h := hWV.const_mul ((8 / ε) ^ 2)
  change Integrable (fun z => W z *
    (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
      8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2)
    (volume.restrict K)
  convert h using 1
  funext z
  by_cases hz : z ∈ S
  · have ht : 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε := hz
    simp only [Set.indicator, hz, ht.1, ht.2, true_and, ite_true]
    ring
  · have ht : ¬(1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε) := hz
    simp only [Set.indicator, hz, ht, ite_false]
    ring

end ESS

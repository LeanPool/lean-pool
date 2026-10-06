/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedSquareIntegral
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedError
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEnergyL2

/-!
# Integrability of the squared cutoff error comparison

The phase and shell majorants have finite integrals on each compact
short-time cutoff support.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- The squared phase, shell, and lower-time majorants are integrable
on the support of a fixed short-time cutoff. -/
theorem bu_short_weighted_split_integrable
    (scale R ε c₁ C₁ C₂ a : ℝ)
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
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    IntegrableOn (fun z =>
      4 * buShortShiftedWeight scale a z *
        (if z ∈ buShortWideGapRegion scale then
          buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
            (1 + z.1 2) ^ 4
        else buShortShellCoeff scale R c₁ ^ 2) *
        (vec3EuclideanNorm (v z) ^ 2 +
          spatialGradientSq v Dv z) +
      2 * buShortShiftedWeight scale a z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2)
      K volume := by
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let W := buShortShiftedWeight scale a
  let Q : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
  let P : ParabolicPoint → ℝ := fun z => (1 + z.1 2) ^ 4
  let G := buShortWideGapRegion scale
  have hK : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).1
  obtain ⟨hv, hDv, _, _⟩ := bu_short_support_memLp_data
    scale R ε hscale hscale1 hR hε w Dw D2w Dtw hcont hweak hL2
  obtain ⟨hv2, hDv2⟩ := bu_memLp_quadratic_energy_integrable
    K v Dv hv hDv
  have hQ : IntegrableOn Q K volume := hv2.add hDv2
  have hWcont : ContinuousOn W K := by
    have hbase := buShortCarlemanWeight_continuousOn_support
      scale R ε a hscale hscale1 hR hε
    exact continuousOn_const.mul hbase
  have hPcont : ContinuousOn P K := by
    have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
      convert continuous_fst.comp parabolicHomeomorph.continuous using 1
      funext z
      rfl
    have hheight : Continuous (fun z : ParabolicPoint => z.1 2) :=
      (continuous_apply 2).comp hspace
    exact ((continuous_const.add hheight).pow 4).continuousOn
  have hWQ : IntegrableOn (fun z => W z * Q z) K volume :=
    bu_integrableOn_mul_continuous_compact hK Q W hQ hWcont
  have hPWQ : IntegrableOn (fun z => P z * (W z * Q z)) K volume :=
    bu_integrableOn_mul_continuous_compact hK _ P hWQ hPcont
  have hgap : IntegrableOn (fun z =>
      buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
        (P z * (W z * Q z))) K volume := hPWQ.const_mul _
  have hshell : IntegrableOn (fun z =>
      buShortShellCoeff scale R c₁ ^ 2 * (W z * Q z)) K volume :=
    hWQ.const_mul _
  have hmeas : MeasurableSet G := buShortWideGapRegion_measurable scale
  have hsplit : IntegrableOn (fun z =>
      if z ∈ G then
        buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
          (P z * (W z * Q z))
      else buShortShellCoeff scale R c₁ ^ 2 *
          (W z * Q z)) K volume := by
    have h := (hgap.indicator hmeas).add
      (hshell.indicator hmeas.compl)
    convert h using 1
    funext z
    by_cases hz : z ∈ G <;> simp [Set.indicator, hz]
  have hfirst : IntegrableOn (fun z =>
      4 * W z *
        (if z ∈ G then
          buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 * P z
        else buShortShellCoeff scale R c₁ ^ 2) * Q z) K volume := by
    have h := hsplit.const_mul 4
    change Integrable (fun z => 4 * W z *
      (if z ∈ G then buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 * P z
       else buShortShellCoeff scale R c₁ ^ 2) * Q z) (volume.restrict K)
    convert h using 1
    funext z
    by_cases hz : z ∈ G <;> simp only [hz, ↓reduceIte] <;> ring
  have hlast : IntegrableOn (fun z =>
      2 * W z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2)
      K volume := by
    let S : Set ParabolicPoint :=
      {z | 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε}
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
    have hWV := bu_integrableOn_mul_continuous_compact hK
      _ W hvi hWcont
    have h := hWV.const_mul (2 * (8 / ε) ^ 2)
    change Integrable (fun z =>
      2 * W z *
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
      ring_nf
  exact hfirst.add hlast

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortIntegralSupport

/-!
# Integrability of the Carleman left side

Compact support away from the initial time makes the half-space Carleman
mass and gradient integrands integrable for the weak cutoff field.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The half-space Carleman left integrand is integrable on the compact
support of the short-time cutoff. -/
theorem bu_short_carleman_left_integrable
    (scale R ε a : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
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
    let κ := buShortFullCutoff scale R hR ε
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    IntegrableOn (fun z => buShortCarlemanWeight a z *
      (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq W DW z / z.2)) K volume := by
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let κ := buShortFullCutoff scale R hR ε
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  have hK : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).1
  have hKsub : K ⊆ halfSpaceDomain :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).2.1
  obtain ⟨_, _, _, hW, hDW, _, _⟩ :=
    bu_short_cutoff_carleman_data scale R ε hscale hscale1 hR hε
      w Dw D2w Dtw hcont hweak hL2
  have hWK : MemLp W 2 (volume.restrict K) :=
    hW.mono_measure Measure.restrict_le_self
  have hDWK : MemLp DW 2 (volume.restrict K) :=
    hDW.mono_measure Measure.restrict_le_self
  obtain ⟨hVInt, hGInt⟩ :=
    bu_memLp_quadratic_energy_integrable K W DW hWK hDWK
  have hweight : ContinuousOn (buShortCarlemanWeight a) K :=
    buShortCarlemanWeight_continuousOn_support
      scale R ε a hscale hscale1 hR hε
  have htimeCont : Continuous (fun z : ParabolicPoint => z.2) := by
    convert continuous_snd.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have htime : ContinuousOn (fun z : ParabolicPoint => z.2) K :=
    htimeCont.continuousOn
  have htimeNe (z : ParabolicPoint) (hz : z ∈ K) : z.2 ≠ 0 :=
    ne_of_gt (hKsub hz).2.1
  have htimeSqNe (z : ParabolicPoint) (hz : z ∈ K) : z.2 ^ 2 ≠ 0 :=
    pow_ne_zero _ (htimeNe z hz)
  have hmassCoeff : ContinuousOn
      (fun z => buShortCarlemanWeight a z * a / z.2 ^ 2) K := by
    convert (hweight.mul continuousOn_const).div (htime.pow 2) htimeSqNe using 1
  have hgradCoeff : ContinuousOn
      (fun z => buShortCarlemanWeight a z / z.2) K := by
    exact hweight.div htime htimeNe
  have hmassInt : IntegrableOn
      (fun z => (buShortCarlemanWeight a z * a / z.2 ^ 2) *
        vec3EuclideanNorm (W z) ^ 2) K volume :=
    bu_integrableOn_mul_continuous_compact hK _ _ hVInt hmassCoeff
  have hgradInt : IntegrableOn
      (fun z => (buShortCarlemanWeight a z / z.2) *
        spatialGradientSq W DW z) K volume :=
    bu_integrableOn_mul_continuous_compact hK _ _ hGInt hgradCoeff
  convert hmassInt.add hgradInt using 1
  funext z
  change buShortCarlemanWeight a z *
      (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq W DW z / z.2) =
      (buShortCarlemanWeight a z * a / z.2 ^ 2) *
        vec3EuclideanNorm (W z) ^ 2 +
      (buShortCarlemanWeight a z / z.2) * spatialGradientSq W DW z
  ring

end ESS

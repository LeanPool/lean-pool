/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatL2
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCarlemanData

/-!
# Weighted compact cutoff data

For each fixed Carleman parameter the cutoff energy and weak heat energy
have finite weighted integrals on the cutoff support.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weighted quadratic field and weak heat energies are integrable
on the short-time cutoff support. -/
theorem bu_short_weighted_data_integrable
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
    let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
    let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    let D2W := buCutD2 κ v Dv D2v
    let DtW := buCutDt κ v Dtv
    IntegrableOn (fun z => buShortCarlemanWeight a z *
      (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z))
      K volume ∧
    IntegrableOn (fun z => buShortCarlemanWeight a z *
      vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2)
      K volume := by
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let κ := buShortFullCutoff scale R hR ε
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  let D2W := buCutD2 κ v Dv D2v
  let DtW := buCutDt κ v Dtv
  have hK : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).1
  obtain ⟨_, _, _, hW, hDW, hD2W, hDtW⟩ :=
    bu_short_cutoff_carleman_data scale R ε hscale hscale1 hR hε
      w Dw D2w Dtw hcont hweak hL2
  have hWK : MemLp W 2 (volume.restrict K) :=
    hW.mono_measure Measure.restrict_le_self
  have hDWK : MemLp DW 2 (volume.restrict K) :=
    hDW.mono_measure Measure.restrict_le_self
  have hD2WK : MemLp D2W 2 (volume.restrict K) :=
    hD2W.mono_measure Measure.restrict_le_self
  have hDtWK : MemLp DtW 2 (volume.restrict K) :=
    hDtW.mono_measure Measure.restrict_le_self
  obtain ⟨hVInt, hGInt⟩ :=
    bu_memLp_quadratic_energy_integrable K W DW hWK hDWK
  have hEInt : IntegrableOn (fun z =>
      vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)
      K volume := hVInt.add hGInt
  have hHeatInt : IntegrableOn (fun z =>
      vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2)
      K volume :=
    bu_memLp_heat_sq_integrable K D2W DtW hD2WK hDtWK
  have hweight := buShortCarlemanWeight_continuousOn_support
    scale R ε a hscale hscale1 hR hε
  exact ⟨bu_integrableOn_mul_continuous_compact hK _ _ hEInt hweight,
    bu_integrableOn_mul_continuous_compact hK _ _ hHeatInt hweight⟩

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGlobalError
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCoreData
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedData

/-!
# Lower bound on a cutoff plateau

Inside its open plateau, the compact cutoff field equals the shifted
source field. Its weighted energy therefore controls the source mass
on any measurable subset of that plateau.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weighted cutoff energy dominates the shifted field mass on
every measurable subset of the open cutoff plateau. -/
theorem bu_short_core_mass_le_cutoff_energy
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
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (S : Set ParabolicPoint) (hSmeas : MeasurableSet S)
    (hScore : ∀ z ∈ S,
      parabolicHomeomorph z ∈ buShortCoreRegion scale R ε) :
    let κ := buShortFullCutoff scale R hR ε
    let K := buCutSupportSet κ
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    (∫ z in S, buShortShiftedWeight scale a z *
      vec3EuclideanNorm (v z) ^ 2
      ∂(volume : Measure ParabolicPoint)) ≤
    (∫ z in K, buShortShiftedWeight scale a z *
      (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)
      ∂(volume : Measure ParabolicPoint)) := by
  let κ := buShortFullCutoff scale R hR ε
  let K := buCutSupportSet κ
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  let Weight := buShortShiftedWeight scale a
  let FV : ParabolicPoint → ℝ := fun z =>
    Weight z * vec3EuclideanNorm (v z) ^ 2
  let FE : ParabolicPoint → ℝ := fun z =>
    Weight z *
      (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)
  have hKcompact : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).1
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hSK : S ⊆ K := by
    intro z hz
    have hκ : κ (parabolicHomeomorph z) = 1 :=
      buShortFullCutoff_eq_one_on_core scale R ε
        hscale hscale1 hR hε (hScore z hz)
    change parabolicHomeomorph z ∈ tsupport κ
    exact subset_tsupport κ (Function.mem_support.mpr (by
      rw [hκ]
      norm_num))
  obtain ⟨hv, hDv, _, _⟩ := bu_short_support_memLp_data
    scale R ε hscale hscale1 hR hε w Dw D2w Dtw hcont hweak hL2
  have hv2 := (bu_memLp_quadratic_energy_integrable K v Dv hv hDv).1
  have hweight : ContinuousOn Weight K := by
    have hbase := buShortCarlemanWeight_continuousOn_support
      scale R ε a hscale hscale1 hR hε
    exact continuousOn_const.mul hbase
  have hFV : IntegrableOn FV K volume :=
    bu_integrableOn_mul_continuous_compact hKcompact _ _ hv2 hweight
  have hbase := (bu_short_weighted_data_integrable
    scale R ε a hscale hscale1 hR hε
    w Dw D2w Dtw hcont hweak hL2).1
  have hFE : IntegrableOn FE K volume := by
    have h := hbase.const_mul (Real.exp (-(2 * a * buShortB scale)))
    change Integrable (fun z => Weight z *
      (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z))
      (volume.restrict K)
    convert h using 1
    funext z
    dsimp [Weight, buShortShiftedWeight]
    ring
  have hpoint : ∀ z ∈ S, FV z ≤ FE z := by
    intro z hz
    obtain ⟨hfield, hgrad, _, _⟩ :=
      bu_short_cutoff_data_eq_on_core scale R ε
        hscale hscale1 hR hε v Dv
        (buAffineD2w (-scale ^ 2 / 2) scale D2w)
        (buAffineDtw (-scale ^ 2 / 2) scale Dtw)
        (hScore z hz)
    have hG : 0 ≤ spatialGradientSq W DW z := by
      dsimp [spatialGradientSq]
      positivity
    have hWt : 0 ≤ Weight z := by
      dsimp [Weight, buShortShiftedWeight, buShortCarlemanWeight]
      positivity
    change W z = v z at hfield
    dsimp [FV, FE]
    rw [hfield]
    nlinarith only [mul_nonneg hWt hG]
  have hfirst : (∫ z in S, FV z
      ∂(volume : Measure ParabolicPoint)) ≤
      ∫ z in S, FE z ∂(volume : Measure ParabolicPoint) :=
    setIntegral_mono_on (hFV.mono_set hSK) (hFE.mono_set hSK)
      hSmeas hpoint
  have hsecond : (∫ z in S, FE z
      ∂(volume : Measure ParabolicPoint)) ≤
      ∫ z in K, FE z ∂(volume : Measure ParabolicPoint) := by
    apply setIntegral_mono_set hFE
    · filter_upwards [ae_restrict_mem hKmeas] with z hz
      dsimp [FE]
      have hG : 0 ≤ spatialGradientSq W DW z := by
        dsimp [spatialGradientSq]
        positivity
      have hWt : 0 ≤ Weight z := by
        dsimp [Weight, buShortShiftedWeight, buShortCarlemanWeight]
        positivity
      positivity
    · exact ae_of_all _ hSK
  exact hfirst.trans hsecond

end ESS

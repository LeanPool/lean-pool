/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTraceGrowth

/-!
# Vanishing of the lower-time cutoff contribution

The normalized quadratic trace estimate eliminates the weighted error
caused by the derivative of the lower-time cutoff.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- The weighted initial-time strip majorant vanishes as the transition
width tends to zero. -/
theorem bu_short_early_weighted_majorant_tendsto_zero
    (M scale R a : ℝ) (hM : 0 < M)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1) (hR : 0 < R)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
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
      let S := spaceTimeSet (buShortTraceBall R)
        (Icc (1 / 2 + ε) (1 / 2 + 2 * ε))
      let v := buAffineField (-scale ^ 2 / 2) scale w
      let f : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
      ∫ z in K, buShortCarlemanWeight a z * (8 / ε) ^ 2 *
        S.indicator f z ∂(volume : Measure ParabolicPoint))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let B := buShortTraceBall R
  let f : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  obtain ⟨Cw, hCw, hweight⟩ :=
    buShortCarlemanWeight_fixedCylinder_bound R a hR
  have htrace := bu_short_shifted_real_trace_strip_tendsto_zero
    scale R hscale hscale1 hR w Dw D2w Dtw hcont hinit hweak hL2
  have hupperLim := bu_short_closed_strip_scaled_tendsto_zero B
    (fun q => f (parabolicHomeomorph.symm q)) (Cw * 64) htrace
  let F : ℝ → ℝ := fun ε =>
    let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
    let S := spaceTimeSet B (Icc (1 / 2 + ε) (1 / 2 + 2 * ε))
    ∫ z in K, buShortCarlemanWeight a z * (8 / ε) ^ 2 *
      S.indicator f z ∂(volume : Measure ParabolicPoint)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ F ε := by
    filter_upwards [] with ε
    dsimp [F]
    apply integral_nonneg_of_ae
    filter_upwards [] with z
    have hW : 0 ≤ buShortCarlemanWeight a z := by
      dsimp [buShortCarlemanWeight]
      positivity
    have hF : 0 ≤ (spaceTimeSet B
        (Icc (1 / 2 + ε) (1 / 2 + 2 * ε))).indicator f z := by
      change 0 ≤ if z ∈ spaceTimeSet B
          (Icc (1 / 2 + ε) (1 / 2 + 2 * ε)) then f z else 0
      split_ifs
      · exact sq_nonneg _
      · exact le_refl _
    positivity
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 / 4 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hupper : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      F ε ≤ (Cw * 64) / ε ^ 2 *
        (∫ q in B ×ˢ Icc (1 / 2 + ε) (1 / 2 + 2 * ε),
          f (parabolicHomeomorph.symm q)
          ∂(volume : Measure (Vec3 × ℝ))) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hεsmall
    let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
    let S := spaceTimeSet B (Icc (1 / 2 + ε) (1 / 2 + 2 * ε))
    have hdata := bu_short_support_memLp_data scale R ε
      hscale hscale1 hR hε w Dw D2w Dtw hcont hweak hL2
    have hfInt := bu_short_shifted_trace_integrable M scale R ε
      hM hscale hscale1 hR hε hεsmall w hcont hgrowth
    have hbound := bu_short_early_weighted_majorant_le scale R ε a Cw
      hscale hscale1 hR hε hCw hweight v Dv hdata.1 hdata.2.1 hfInt
    change F ε ≤ Cw * (8 / ε) ^ 2 *
      (∫ q in B ×ˢ Icc (1 / 2 + ε) (1 / 2 + 2 * ε),
        f (parabolicHomeomorph.symm q)
        ∂(volume : Measure (Vec3 × ℝ))) at hbound
    convert hbound using 1
    field_simp
    ring
  change Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0)
  exact squeeze_zero' hpos hupper hupperLim

end ESS

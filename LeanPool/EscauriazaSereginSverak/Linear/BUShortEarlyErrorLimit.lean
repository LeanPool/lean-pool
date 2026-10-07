/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEarlyLimit

/-!
# The lower-time derivative error

On the cutoff support the time-transition indicator agrees with the
indicator of the larger trace cylinder.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- The squared lower-time derivative contribution to the cutoff heat
error vanishes after integration. -/
theorem bu_short_early_error_tendsto_zero
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
      let v := buAffineField (-scale ^ 2 / 2) scale w
      ∫ z in K, buShortCarlemanWeight a z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
        ∂(volume : Measure ParabolicPoint))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  let v := buAffineField (-scale ^ 2 / 2) scale w
  have hmain := bu_short_early_weighted_majorant_tendsto_zero
    M scale R a hM hscale hscale1 hR
    w Dw D2w Dtw hcont hinit hweak hL2 hgrowth
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let S := spaceTimeSet (buShortTraceBall R)
    (Icc (1 / 2 + ε) (1 / 2 + 2 * ε))
  let f : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  have hKcompact : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).1
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hKsub := buShortCutSupport_subset_traceCylinder
    scale R ε hscale hscale1 hR hε
  apply setIntegral_congr_fun hKmeas
  intro z hz
  have hzB : z.1 ∈ buShortTraceBall R := (hKsub hz).1
  change buShortCarlemanWeight a z * (8 / ε) ^ 2 *
      (if z ∈ S then f z else 0) =
    buShortCarlemanWeight a z *
      (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
        8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
  by_cases ht : 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε
  · have hzS : z ∈ S := ⟨hzB, ht⟩
    simp only [ht, hzS, ite_true]
    dsimp [f]
    ring
  · have hzS : z ∉ S := by
      intro h
      exact ht h.2
    simp only [ht, hzS, ite_false]
    ring

end ESS

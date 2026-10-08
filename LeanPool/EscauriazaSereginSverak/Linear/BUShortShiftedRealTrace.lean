/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRealTraceStrip

/-!
# Real quadratic mass in the shifted initial-time strip

The shifted trace estimate is expressed as an ordinary space-time
integral for the subsequent weighted cutoff estimate.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- The shifted field has vanishing normalized real quadratic mass on
the bounded trace ball as its lower-time strip shrinks. -/
theorem bu_short_shifted_real_trace_strip_tendsto_zero
    (scale R : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R)
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
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Tendsto (fun ε : ℝ =>
      (∫ q in buShortTraceBall R ×ˢ
          Ioc (1 / 2 + ε) (1 / 2 + 2 * ε),
        vec3EuclideanNorm
          ((buAffineField (-scale ^ 2 / 2) scale w)
            (parabolicHomeomorph.symm q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let B := buShortTraceBall R
  let S : Set (Vec3 × ℝ) := B ×ˢ Ioo (1 / 2 : ℝ) 1
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let f : Vec3 × ℝ → ℝ := fun q =>
    vec3EuclideanNorm (v (parabolicHomeomorph.symm q)) ^ 2
  have hBsub := (buShortTraceBall_geometry hR).2.2
  have hcontv := bu_short_field_continuousOn scale hscale hscale1 w hcont
  have hcontProd : ContinuousOn
      (fun q : Vec3 × ℝ => v (parabolicHomeomorph.symm q)) S := by
    apply hcontv.comp parabolicHomeomorph.symm.continuous.continuousOn
    intro q hq
    exact ⟨hBsub hq.1, hq.2.1.le, hq.2.2⟩
  have hfcont : ContinuousOn f S :=
    (continuous_vec3EuclideanNorm.pow 2).comp_continuousOn hcontProd
  have hSmeas : MeasurableSet S := by
    exact ((buShortTraceBall_geometry hR).1.measurableSet).prod measurableSet_Ioo
  have hfmeas : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict (Ioo (1 / 2 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hfcont.aestronglyMeasurable hSmeas
  have hf0 (q : Vec3 × ℝ) : 0 ≤ f q := sq_nonneg _
  have hlimit := bu_short_shifted_trace_strip_tendsto_zero
    scale R hscale hscale1 hR w Dw D2w Dtw hcont hinit hweak hL2
  have hlim : Tendsto (fun ε : ℝ =>
      (∫⁻ s in Ioc (1 / 2 + ε) (1 / 2 + 2 * ε),
        ∫⁻ x, ENNReal.ofReal (f (x, s)) ∂(volume.restrict B)) /
          ENNReal.ofReal ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hlimit using 1
    ext ε
    congr 2
  exact bu_short_real_strip_of_lintegral_limit B (1 / 2) (1 / 2)
    (by norm_num) f (by convert hfmeas using 1; norm_num) hf0 hlim

end ESS

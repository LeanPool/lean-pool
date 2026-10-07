/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTraceApplied

/-!
# Translating the initial-time trace strip

The shifted field used by the half-space Carleman estimate is the
unshifted parabolic rescaling evaluated at time `s - 1/2`.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- The shifted and unshifted parabolic rescalings differ by a translation
of one half in the normalized time variable. -/
theorem bu_short_shifted_field_eq_unshifted
    (scale : ℝ) (w : ParabolicPoint → Vec3)
    (y : Vec3) (s : ℝ) :
    buAffineField (-scale ^ 2 / 2) scale w (y, s) =
      buAffineField 0 scale w (y, s - 1 / 2) := by
  apply congrArg w
  dsimp [buAffinePoint]
  apply Prod.ext
  · rfl
  · ring

/-- A time translation carries the early strip in shifted coordinates
to the initial strip in unshifted coordinates. -/
theorem bu_short_shifted_strip_lintegral
    (B : Set Vec3) (ε : ℝ) (F : Vec3 × ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioc (1 / 2 + ε) (1 / 2 + 2 * ε),
      ∫⁻ x, F (x, s - 1 / 2) ∂(volume.restrict B)) =
      ∫⁻ t in Ioc ε (2 * ε),
        ∫⁻ x, F (x, t) ∂(volume.restrict B) := by
  let T : ℝ → ℝ := fun t => t + 1 / 2
  let S : Set ℝ := Ioc (1 / 2 + ε) (1 / 2 + 2 * ε)
  let G : ℝ → ℝ≥0∞ := fun s =>
    ∫⁻ x, F (x, s - 1 / 2) ∂(volume.restrict B)
  have hpre : T ⁻¹' S = Ioc ε (2 * ε) := by
    ext t
    change (1 / 2 + ε < t + 1 / 2 ∧ t + 1 / 2 ≤ 1 / 2 + 2 * ε) ↔
      ε < t ∧ t ≤ 2 * ε
    constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
  have hpres : MeasurePreserving T volume volume := by
    exact measurePreserving_add_right volume (1 / 2)
  have hTemb : MeasurableEmbedding T := by
    exact (Homeomorph.addRight (1 / 2 : ℝ)).isClosedEmbedding.measurableEmbedding
  have h := hpres.setLIntegral_comp_preimage_emb hTemb G S
  rw [hpre] at h
  have hsimp (t : ℝ) : G (T t) =
      ∫⁻ x, F (x, t) ∂(volume.restrict B) := by
    dsimp [G, T]
    ring_nf
  simpa only [hsimp] using h.symm

/-- The shifted rescaling has vanishing normalized quadratic mass in
its early-time strip on the bounded trace ball. -/
theorem bu_short_shifted_trace_strip_tendsto_zero
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
      (∫⁻ s in Ioc (1 / 2 + ε) (1 / 2 + 2 * ε),
        ∫⁻ x,
          ENNReal.ofReal
            (vec3EuclideanNorm
              ((buAffineField (-scale ^ 2 / 2) scale w) (x, s)) ^ 2)
          ∂(volume.restrict (buShortTraceBall R))) /
        ENNReal.ofReal ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbase := bu_short_rescaled_trace_strip_tendsto_zero
    scale R hscale hscale1 hR w Dw D2w Dtw hcont hinit hweak hL2
  have hnum (ε : ℝ) :
      (∫⁻ s in Ioc (1 / 2 + ε) (1 / 2 + 2 * ε),
        ∫⁻ x,
          ENNReal.ofReal
            (vec3EuclideanNorm
              ((buAffineField (-scale ^ 2 / 2) scale w) (x, s)) ^ 2)
          ∂(volume.restrict (buShortTraceBall R))) =
      ∫⁻ t in Ioc ε (2 * ε),
        ∫⁻ x,
          ENNReal.ofReal
            (vec3EuclideanNorm ((buAffineField 0 scale w) (x, t)) ^ 2)
          ∂(volume.restrict (buShortTraceBall R)) := by
    simp_rw [bu_short_shifted_field_eq_unshifted]
    exact bu_short_shifted_strip_lintegral (buShortTraceBall R) ε
      (fun q => ENNReal.ofReal
        (vec3EuclideanNorm ((buAffineField 0 scale w) (q.1, q.2)) ^ 2))
  apply hbase.congr'
  filter_upwards [] with ε
  rw [hnum ε]

end ESS

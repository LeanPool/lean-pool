/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsFinite
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace ESS

/-- A uniform `Lᵖ` bound on finite past cylinders extends to the open
terminal-time cylinder. -/
theorem blowup_eLpNorm_bound_to_time_zero
    (A : Set Vec3) (hA : MeasurableSet A) (a : ℝ)
    (f : ParabolicPoint → ℝ) (p : ℝ≥0) (hp : p ≠ 0)
    (hf : AEStronglyMeasurable f (volume.restrict (A ×ˢ Ioo a 0)))
    (K : ℝ≥0∞) (hK : K < ⊤)
    (hbound : ∀ b : ℝ, b < 0 →
      MemLp f (p : ℝ≥0∞) (volume.restrict (A ×ˢ Ioo a b)) ∧
      eLpNorm f (p : ℝ≥0∞)
        (volume.restrict (A ×ˢ Ioo a b)) ^ (p : ℝ) ≤ K) :
    MemLp f (p : ℝ≥0∞) (volume.restrict (A ×ˢ Ioo a 0)) ∧
      eLpNorm f (p : ℝ≥0∞)
        (volume.restrict (A ×ˢ Ioo a 0)) ^ (p : ℝ) ≤ K := by
  let s : Set ParabolicPoint := A ×ˢ Ioo a 0
  let b : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 1))
  let φ : ℕ → Set ParabolicPoint := fun n => A ×ˢ Ioo a (b n)
  let μ : Measure ParabolicPoint := volume.restrict s
  have hs : MeasurableSet s := hA.prod measurableSet_Ioo
  have hbneg (n : ℕ) : b n < 0 := by dsimp [b]; exact neg_neg_of_pos (by positivity)
  have hb0 : Tendsto b atTop (nhds 0) := by
    simpa only [b, neg_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hφmeas (n : ℕ) : MeasurableSet (φ n) := hA.prod measurableSet_Ioo
  have hφsub (n : ℕ) : φ n ⊆ s := by
    intro z hz
    exact ⟨hz.1, hz.2.1, lt_trans hz.2.2 (hbneg n)⟩
  have hcover : AECover μ atTop φ := by
    apply aecover_restrict_of_ae_imp hs
    · filter_upwards [] with z hz
      have hz' : z.2 < 0 := hz.2.2
      filter_upwards [hb0.eventually (eventually_gt_nhds hz')] with n hn
      exact ⟨hz.1, hz.2.1, hn⟩
    · exact hφmeas
  have hμeq (n : ℕ) : μ.restrict (φ n) = volume.restrict (φ n) := by
    rw [show μ = volume.restrict s by rfl,
      Measure.restrict_restrict (hφmeas n), inter_eq_left.mpr (hφsub n)]
  let g : ParabolicPoint → ℝ≥0∞ := fun z => ‖f z‖ₑ ^ (p : ℝ)
  have hgmeas : AEMeasurable g μ := hf.enorm.pow_const _
  have hlin (n : ℕ) : (∫⁻ z in φ n, g z ∂μ) ≤ K := by
    rw [hμeq]
    simpa only [g, eLpNorm_nnreal_pow_eq_lintegral hp
      ((hbound (b n) (hbneg n)).1).aestronglyMeasurable] using
      (hbound (b n) (hbneg n)).2
  have htop : (∫⁻ z, g z ∂μ) ≤ K :=
    le_of_tendsto (hcover.lintegral_tendsto_of_countably_generated hgmeas)
      (Filter.Eventually.of_forall hlin)
  have hnorm : eLpNorm f (p : ℝ≥0∞) μ ^ (p : ℝ) ≤ K := by
    rw [eLpNorm_nnreal_pow_eq_lintegral hp hf]
    exact htop
  have hnormfin : eLpNorm f (p : ℝ≥0∞) μ < ⊤ := by
    by_contra hnot
    have htop' : eLpNorm f (p : ℝ≥0∞) μ = ⊤ := eq_top_iff.mpr (le_of_not_gt hnot)
    rw [htop', ENNReal.top_rpow_of_pos ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp)] at hnorm
    exact (not_le_of_gt hK) hnorm
  exact ⟨hnormfin, hnorm⟩

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Space-time `L¹` limits from fixed-time domination

A family of space-time functions converges in `L¹` of the slab once the spatial
`L¹` distances to the limit are dominated by a fixed integrable time profile and
tend to zero at almost every time. This is the dominated-convergence step of
the endpoint density passage in `lem:lps-comparison`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Slice-wise domination and slice-wise convergence of the spatial `L¹`
distances give integrability and convergence of the space-time integrals. -/
theorem lps_slab_integral_tendsto_of_slice_domination
    {T : ℝ} {F : ℕ → ParabolicPoint → ℝ} {G : ParabolicPoint → ℝ}
    {D : ℝ → ℝ≥0∞}
    (hF : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hG : Integrable G
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hD : (∫⁻ t in Ioo 0 T, D t) ≠ ⊤)
    (hbound : ∀ n, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫⁻ x : Vec3, ‖F n (x, t) - G (x, t)‖ₑ ≤ D t)
    (hlim : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      Tendsto (fun n => ∫⁻ x : Vec3, ‖F n (x, t) - G (x, t)‖ₑ) atTop (𝓝 0)) :
    (∀ n, Integrable (F n)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) ∧
    Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), F n z)
      atTop (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), G z)) := by
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  have hμ : μ = (volume : Measure Vec3).prod μt := serrin_slab_measure_eq T
  have hDiffMeas (n : ℕ) : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => F n z - G z) ((volume : Measure Vec3).prod μt) := by
    rw [← hμ]
    exact (hF n).sub hG.aestronglyMeasurable
  have hΦmeas (n : ℕ) : AEMeasurable
      (fun t : ℝ => ∫⁻ x : Vec3, ‖F n (x,t) - G (x,t)‖ₑ) μt :=
    (hDiffMeas n).enorm.lintegral_prod_left'
  have hTonelli (n : ℕ) :
      (∫⁻ z : ParabolicPoint, ‖F n z - G z‖ₑ ∂μ) =
        ∫⁻ t : ℝ, (∫⁻ x : Vec3, ‖F n (x,t) - G (x,t)‖ₑ) ∂μt := by
    rw [hμ]
    exact lintegral_prod_symm _ (hDiffMeas n).enorm
  have hDCT : Tendsto (fun n => ∫⁻ t : ℝ,
      (∫⁻ x : Vec3, ‖F n (x,t) - G (x,t)‖ₑ) ∂μt) atTop
      (𝓝 (∫⁻ t : ℝ, (0 : ℝ≥0∞) ∂μt)) :=
    tendsto_lintegral_of_dominated_convergence' D hΦmeas hbound hD hlim
  have hL1 : Tendsto (fun n => ∫⁻ z : ParabolicPoint, ‖F n z - G z‖ₑ ∂μ) atTop
      (𝓝 0) := by
    simpa [hTonelli] using hDCT
  have hFi : ∀ n, Integrable (F n) μ := by
    intro n
    have hfin : ∫⁻ z : ParabolicPoint, ‖F n z - G z‖ₑ ∂μ < ⊤ := by
      rw [hTonelli n]
      exact lt_of_le_of_lt (lintegral_mono_ae (hbound n)) hD.lt_top
    have hdiff : Integrable (fun z => F n z - G z) μ := by
      refine ⟨(hF n).sub hG.aestronglyMeasurable, ?_⟩
      exact hfin
    exact (hdiff.add hG).congr (Eventually.of_forall fun z => by simp)
  exact ⟨hFi, tendsto_integral_of_L1 G hG.1 (Eventually.of_forall hFi) hL1⟩

end ESS

end

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreWeakSobolevMultipliers.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure

/-! # Smooth compact multipliers on the independent weak Sobolev graph

These results operate on ordinary distributional gradients, without assuming
membership in the smooth-core completion. In particular they can be used in
the reverse approximation argument.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace GinibrePoincare
noncomputable section


theorem volume_absolutelyContinuous_ginibreMeasure (n : ℕ) (hn : 0 < n) :
    (volume : Measure (Configuration n)) ≪ ginibreMeasure n := by
  rw [ginibreMeasure_eq_real_withDensity hn]
  apply (withDensity_absolutelyContinuous'
    (contDiff_ginibreLebesgueDensityReal n).continuous.measurable.ennreal_ofReal.aemeasurable
    ?_).trans
    (Measure.absolutelyContinuous_smul
      (ENNReal.inv_ne_zero.mpr (ginibreMassEvaluation n hn).2.ne))
  have hcf : ∀ᵐ z ∂(volume : Measure (Configuration n)), CollisionFree z := by
    rw [ae_iff]
    have he : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z
      simp [collisionFree_iff_not_mem_collisionSet]
    rw [he]
    exact configurationVolume_collisionSet hn
  filter_upwards [hcf] with z hz
  exact (ne_of_gt ∘ ENNReal.ofReal_pos.mpr) (lt_of_le_of_ne
    (ginibreLebesgueDensityReal_nonneg n z)
    (ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn hz).symm)

/-- Equality of representatives in Ginibre L² also holds Lebesgue almost everywhere. -/
theorem ginibre_ae_eq_iff_volume (n : ℕ) (hn : 0 < n) {α : Type*}
    (f g : Configuration n → α) :
    f =ᵐ[ginibreMeasure n] g ↔ f =ᵐ[volume] g := by
  refine ⟨(volume_absolutelyContinuous_ginibreMeasure n hn).ae_eq, ?_⟩
  rw [ginibreMeasure_eq_real_withDensity hn]
  exact ((withDensity_absolutelyContinuous _ _).smul_left _).ae_eq

/-- Actual weak multiplication and its actual Leibniz gradient are square integrable. -/
theorem ginibre_weak_multiplier_memLp (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    MemLp (fun z => χ z * u z) 2 (ginibreMeasure n) ∧
    MemLp (fun z => χ z • g z + u z • ginibreEuclideanGradient χ z)
      2 (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  obtain ⟨A, hA⟩ := hχ.continuous.bounded_above_of_compact_support hc
  obtain ⟨B, hB⟩ := (continuous_ginibreEuclideanGradient χ hχ).bounded_above_of_compact_support
    (compactSupport_ginibreEuclideanGradient χ hc)
  have hA0 : 0 ≤ A := (norm_nonneg (χ 0)).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg (ginibreEuclideanGradient χ 0)).trans (hB 0)
  have hv : MemLp (fun z => χ z * u z) 2 (ginibreMeasure n) := by
    apply ((Lp.memLp u).const_mul A).of_le
      (hχ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
    exact ae_of_all _ (fun z => by
      change ‖χ z * u z‖ ≤ ‖A * u z‖
      rw [norm_mul, norm_mul, Real.norm_eq_abs A, abs_of_nonneg hA0]
      exact mul_le_mul_of_nonneg_right (hA z) (norm_nonneg (u z)))
  have hvG : MemLp (fun z => χ z • g z) 2 (ginibreMeasure n) := by
    apply ((Lp.memLp g).const_smul A).of_le
      (hχ.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable g))
    exact ae_of_all _ (fun z => by
      change ‖χ z • g z‖ ≤ ‖A • g z‖
      rw [norm_smul, norm_smul, Real.norm_eq_abs A, abs_of_nonneg hA0]
      exact mul_le_mul_of_nonneg_right (hA z) (norm_nonneg (g z)))
  have hdG : MemLp (fun z => u z • ginibreEuclideanGradient χ z) 2 (ginibreMeasure n) := by
    apply ((Lp.memLp u).const_mul B).of_le
      ((Lp.aestronglyMeasurable u).smul (continuous_ginibreEuclideanGradient χ
        hχ).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖u z • ginibreEuclideanGradient χ z‖ ≤ ‖B * u z‖
      rw [norm_smul, norm_mul, Real.norm_eq_abs B, abs_of_nonneg hB0]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB z) (norm_nonneg (u z)))
  exact ⟨hv, hvG.add hdG⟩

/-- The Leibniz rule for ordinary weak gradients under smooth compact multiplication. -/
theorem ginibre_distributional_gradient_mul (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (v : Lp ℝ 2 (ginibreMeasure n))
    (h : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hv : (v : Configuration n → ℝ) =ᵐ[ginibreMeasure n] fun z => χ z * u z)
    (hh : (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      =ᵐ[ginibreMeasure n] fun z => χ z • g z + u z • ginibreEuclideanGradient χ z) :
    IsGinibreDistributionalGradient n v h := by
  have hv' := (ginibre_ae_eq_iff_volume n hn _ _).mp hv
  have hh' := (ginibre_ae_eq_iff_volume n hn _ _).mp hh
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn v (Lp.memLp v), ?_, ?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
    have hm : MemLp (fun z => h z k) 2 (ginibreMeasure n) := P.comp_memLp h
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ hm
  · intro k θ hθ hθc hs
    have hm : ContDiff ℝ ∞ (χ * θ) := hχ.mul hθ
    have hmc : HasCompactSupport (χ * θ) := hθc.mul_left
    have hms : tsupport (χ * θ) ⊆ {z | CollisionFree z} :=
      (tsupport_mul_subset_right).trans hs
    have he := hg.2.2 k (χ * θ) hm hmc hms
    have hd (z : Configuration n) :
        fderiv ℝ (χ * θ) z (ginibreCoordinateDirection k) =
          χ z * fderiv ℝ θ z (ginibreCoordinateDirection k) +
            θ z * fderiv ℝ χ z (ginibreCoordinateDirection k) := by
      rw [fderiv_mul (hχ.differentiable (by simp)).differentiableAt
        (hθ.differentiable (by simp)).differentiableAt]
      simp only [add_apply, smul_apply, smul_eq_mul]
    have hi₁ : Integrable (fun z => g z k * (χ z * θ z)) := by
      exact integrable_mul_collisionFree_test _ _ (hg.2.1 k) hm.continuous hmc hms
    have hi₂ : Integrable (fun z => u z *
        (fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z)) := by
      have ht : Continuous (fun z => fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) :=
        ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).mul hθ.continuous
      have htc : HasCompactSupport (fun z =>
          fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) := hθc.mul_left
      have hts : tsupport (fun z =>
          fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) ⊆ {z | CollisionFree z} :=
        tsupport_mul_subset_right.trans hs
      exact integrable_mul_collisionFree_test _ _ hg.1 ht htc hts
    have hi₃ : Integrable (fun z => u z *
        (χ z * fderiv ℝ θ z (ginibreCoordinateDirection k))) := by
      have ht : Continuous (fun z => χ z * fderiv ℝ θ z (ginibreCoordinateDirection k)) :=
        hχ.continuous.mul ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)
      have htc : HasCompactSupport (fun z => χ z *
          fderiv ℝ θ z (ginibreCoordinateDirection k)) := (hθc.fderiv_apply ℝ _).mul_left
      have hts : tsupport (fun z => χ z *
          fderiv ℝ θ z (ginibreCoordinateDirection k)) ⊆ {z | CollisionFree z} :=
        tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ _).trans hs)
      exact integrable_mul_collisionFree_test _ _ hg.1 ht htc hts
    have hl : (∫ z, h z k * θ z) =
        (∫ z, g z k * (χ z * θ z)) +
          ∫ z, u z * (fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) := by
      rw [← integral_add hi₁ hi₂]
      apply integral_congr_ae
      filter_upwards [hh'] with z hz
      rw [hz]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        ginibreEuclideanGradient_coordinate]
      ring
    have hr : (∫ z, v z * fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        ∫ z, u z * (χ z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
      apply integral_congr_ae
      filter_upwards [hv'] with z hz
      rw [hz]
      ring
    have hdint : (∫ z, u z * fderiv ℝ (χ * θ) z (ginibreCoordinateDirection k)) =
        (∫ z, u z * (χ z * fderiv ℝ θ z (ginibreCoordinateDirection k))) +
          ∫ z, u z * (fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) := by
      rw [← integral_add hi₃ hi₂]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by dsimp only; rw [hd]; ring)
    rw [hdint] at he
    change (∫ z, g z k * (χ z * θ z)) = -_ at he
    rw [hl, hr]
    linarith

/-- Concrete compact multiplier pair; no approximation certificate is required. -/
def ginibreWeakMultiplierPair (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) :=
  (((ginibre_weak_multiplier_memLp n hn u g χ hχ hc).1).toLp (fun z => χ z * u z),
    ((ginibre_weak_multiplier_memLp n hn u g χ hχ hc).2).toLp
      (fun z => χ z • g z + u z • ginibreEuclideanGradient χ z))

theorem ginibreWeakMultiplierPair_distributional (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    IsGinibreDistributionalGradient n
      (ginibreWeakMultiplierPair n hn u g χ hχ hc).1
      (ginibreWeakMultiplierPair n hn u g χ hχ hc).2 :=
  ginibre_distributional_gradient_mul n hn u g hg χ hχ _ _
    (ginibre_weak_multiplier_memLp n hn u g χ hχ hc).1.coeFn_toLp
    (ginibre_weak_multiplier_memLp n hn u g χ hχ hc).2.coeFn_toLp

end
end GinibrePoincare

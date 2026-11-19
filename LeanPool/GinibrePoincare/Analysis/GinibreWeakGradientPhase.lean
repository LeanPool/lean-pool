/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreWeakGradientPhase.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePhaseCoordinates

/-! # Phase covariance of independently defined ordinary weak gradients

Tests are rotated by actual real-linear, volume-preserving coordinate phases.
The original and rotated collision-free open sets are intersected only for test
separation; no invariance of the Ginibre density under independent phases is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

/-- Rotating an ordinary weak test gives the exact directional gradient pairing. -/
theorem ginibre_radial_rotated_weak_test (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ = 1)
    (v : Configuration n) (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ (coordinatePhaseCLE n a ha) ⁻¹' {z | CollisionFree z}) :
    (∫ z, (∑ k : Fin n × Fin 2,
      ginibreDirectionCoefficient (coordinatePhase a v) k * g (coordinatePhase a z) k) * θ z) =
      -(∫ z, u z * fderiv ℝ θ z v) := by
  let e := coordinatePhaseCLE n a ha
  let η : Configuration n → ℝ := θ ∘ e.symm
  have hη : ContDiff ℝ ∞ η := hθ.comp e.symm.contDiff
  have hcη : HasCompactSupport η := hc.comp_homeomorph e.symm.toHomeomorph
  have hsη : tsupport η ⊆ {z | CollisionFree z} := by
    intro z hz
    have ht := hs (tsupport_comp_subset_preimage θ e.symm.continuous hz)
    change e (e.symm z) ∈ {z | CollisionFree z} at ht
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using ht
  have hd (z : Configuration n) : fderiv ℝ η (e z) (e v) = fderiv ℝ θ z v := by
    have he := ((hθ.differentiable (by simp)) (e.symm (e z))).hasFDerivAt.comp (e z)
        e.symm.hasFDerivAt
    change fderiv ℝ (θ ∘ e.symm) (e z) (e v) = _
    rw [he.fderiv]
    simp
  have hmp : MeasurePreserving e (volume : Measure (Configuration n)) volume :=
    measurePreserving_coordinatePhaseCLE_volume n a ha
  have hl := hmp.integral_comp e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y => (∑ k : Fin n × Fin 2, ginibreDirectionCoefficient (e v) k * g y k) * η y)
  have hp := hmp.integral_comp e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y => u y * fderiv ℝ η y (e v))
  have hu := ginibre_radial_L2_phase_ae n hn u f hf hr a ha
  calc
    _ = ∫ y, (∑ k : Fin n × Fin 2, ginibreDirectionCoefficient (e v) k * g y k) * η y := by
      change (∫ z, (∑ k : Fin n × Fin 2, ginibreDirectionCoefficient (e v) k * g (e z) k) * θ z) = _
      simpa only [η, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hl
    _ = -(∫ y, u y * fderiv ℝ η y (e v)) :=
      ginibre_distributional_gradient_directional n u g hg (e v) η hη hcη hsη
    _ = -(∫ z, u (e z) * fderiv ℝ η (e z) (e v)) := congrArg Neg.neg hp.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hu] with z hz
      rw [hd]
      exact congrArg (fun t => t * fderiv ℝ θ z v) hz

/-- Integrability of multiplication by a compact test supported in a given open set. -/
theorem integrable_mul_open_compact_test (n : ℕ)
    (U : Set (Configuration n)) (hU : IsOpen U) (f θ : Configuration n → ℝ)
    (hf : LocallyIntegrableOn f U volume) (hθ : Continuous θ)
    (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ U) :
    Integrable (fun z => f z * θ z) := by
  have hl := hf.mul_continuousOn hθ.continuousOn hU.isLocallyClosed
  have hi : IntegrableOn (fun z => f z * θ z) (tsupport θ) volume :=
    hl.integrableOn_compact_subset hs hc
  apply hi.integrable_of_forall_notMem_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- The actual ordinary weak gradient of a radial value transforms covariantly
under every fixed independent phase, in Lebesgue almost-everywhere coordinates. -/
theorem ginibre_radial_weak_gradient_phase_covariance (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    ∀ᵐ z ∂(volume : Measure (Configuration n)), ∀ k : Fin n × Fin 2,
      g z k = ∑ j : Fin n × Fin 2,
        ginibreDirectionCoefficient (coordinatePhase a (ginibreCoordinateDirection k)) j *
          g (coordinatePhase a z) j := by
  classical
  let e := coordinatePhaseCLE n a ha
  let C := {z : Configuration n | CollisionFree z}
  let U := C ∩ e ⁻¹' C
  have hC : IsOpen C := isOpen_collisionFree n
  have hU : IsOpen U := hC.inter (hC.preimage e.continuous)
  let H (k : Fin n × Fin 2) (z : Configuration n) :=
    ∑ j : Fin n × Fin 2, ginibreDirectionCoefficient (e (ginibreCoordinateDirection k)) j * g (e z)
        j
  have hH (k : Fin n × Fin 2) : LocallyIntegrableOn (H k) U volume := by
    apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
    intro K hK hc
    apply integrable_finsetSum
    intro j _
    have hl := locallyIntegrableOn_comp_volume_equiv n e
      (measurePreserving_coordinatePhaseCLE_volume n a ha) C hC (fun z => g z j) (hg.2.1 j)
    exact (hl.integrableOn_compact_subset (hK.trans Set.inter_subset_right) hc).const_mul _
  have he (k : Fin n × Fin 2) : ∀ᵐ z ∂(volume : Measure (Configuration n)),
      z ∈ U → g z k = H k z := by
    have hl := ((hg.2.1 k).mono_set Set.inter_subset_left).sub (hH k)
    have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hl (fun θ hθ hc hs => by
      have hi₁ := integrable_mul_open_compact_test n U hU (fun z => g z k) θ
        ((hg.2.1 k).mono_set Set.inter_subset_left) hθ.continuous hc hs
      have hi₂ := integrable_mul_open_compact_test n U hU (H k) θ
        (hH k) hθ.continuous hc hs
      have he₁ := hg.2.2 k θ hθ hc (hs.trans Set.inter_subset_left)
      have he₂ := ginibre_radial_rotated_weak_test n hn u g hg f hf hr a ha
        (ginibreCoordinateDirection k) θ hθ hc (hs.trans Set.inter_subset_right)
      have hi : (∫ z, θ z • ((fun z => g z k) - H k) z) =
          (∫ z, g z k * θ z) - ∫ z, H k z * θ z := by
        rw [← integral_sub hi₁ hi₂]
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by simp only [Pi.sub_apply, smul_eq_mul]; ring)
      rw [hi, he₁]
      change -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) -
        (∫ z, (∑ j : Fin n × Fin 2,
          ginibreDirectionCoefficient (coordinatePhase a (ginibreCoordinateDirection k)) j *
            g (coordinatePhase a z) j) * θ z) = 0
      rw [he₂, sub_self])
    filter_upwards [hz] with z hz
    intro hmem
    exact sub_eq_zero.mp (hz hmem)
  have hall := (ae_all_iff).mpr he
  have hcf : ∀ᵐ z ∂(volume : Measure (Configuration n)), z ∈ C := by
    rw [ae_iff]
    have heq : {z : Configuration n | z ∉ C} = collisionSet n := by
      ext z
      simp [C, collisionFree_iff_not_mem_collisionSet]
    rw [heq]
    exact configurationVolume_collisionSet hn
  have hr := (measurePreserving_coordinatePhaseCLE_volume n a ha).quasiMeasurePreserving.ae hcf
  filter_upwards [hall, hcf, hr] with z hz hzC hzeC
  intro k
  exact hz k ⟨hzC, hzeC⟩

end
end GinibrePoincare

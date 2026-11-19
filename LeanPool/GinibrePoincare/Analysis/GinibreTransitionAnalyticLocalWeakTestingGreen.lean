/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingGreen.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingLocalization
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreCompatibility
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Ginibre transition analytic local weak testing Green

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_adjoint_to_gradient_equation`.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_distributional_density_pairing (n : ℕ) (hn : 0 < n)
    (u : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)))
    (k : Fin n × Fin 2) (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    (∫ z, g z k * (θ z / ginibreLebesgueDensityReal n z) ∂ginibreMeasure n) =
      -(∫ z, u z * (fderiv ℝ θ z (ginibreCoordinateDirection k) /
        ginibreLebesgueDensityReal n z) ∂ginibreMeasure n) := by
  have he := hw k θ hθ hc hs
  have hds := (tsupport_fderiv_apply_subset ℝ (ginibreCoordinateDirection k)).trans hs
  rw [integral_collisionFree_test_eq_ginibre n hn _ θ hs,
    integral_collisionFree_test_eq_ginibre n hn _ _ hds] at he
  have hM : (ginibreNormalizingMass n).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(ginibreMassEvaluation n hn).1.ne',
      (ginibreMassEvaluation n hn).2.ne⟩
  apply mul_left_cancel₀ hM
  linarith

theorem ginibreLocalWeak_generator_divergence_ae {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) :
    (fun z => (1 / (n : ℝ)) * ∑ k : Fin n × Fin 2,
      fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
        fderiv ℝ f y (ginibreCoordinateDirection k)) z (ginibreCoordinateDirection k) /
          ginibreLebesgueDensityReal n z) =ᵐ[ginibreMeasure n] ginibrePregenerator n f := by
  have hcf := ginibre_ae_collisionFree n hn
  filter_upwards [hcf, ginibreLebesgueDensityReal_ne_zero_ae hn] with z hz hρ
  have h := ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence hn f hf z hz
  simp only [one_div]
  convert congrArg (fun t : ℝ => t / ginibreLebesgueDensityReal n z) h.symm using 1
  · rw [← Finset.sum_div, mul_div_assoc]
    simp [one_div, Fintype.sum_prod_type, Fin.sum_univ_two, ginibreCoordinateDirection]
  · exact (mul_div_cancel_left₀ _ hρ).symm

theorem ginibreLocalWeak_generator_green {n : ℕ} (hn : 0 < n)
    (u : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 (ginibreMeasure n))
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)))
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ {z | CollisionFree z})
    (hg : MemLp g 2 (volume.restrict (tsupport f))) :
    (1 / (n : ℝ)) * (∫ z, inner ℝ (g z) (ginibreEuclideanGradient f z) ∂ginibreMeasure n) =
      -(∫ z, u z*ginibrePregenerator n f z ∂ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let θ (k : Fin n × Fin 2) : Configuration n → ℝ := fun z =>
    ginibreLebesgueDensityReal n z * fderiv ℝ f z (ginibreCoordinateDirection k)
  let δ (k : Fin n × Fin 2) : Configuration n → ℝ := fun z =>
    fderiv ℝ (θ k) z (ginibreCoordinateDirection k) / ginibreLebesgueDensityReal n z
  have hθ (k) : ContDiff ℝ ∞ (θ k) := (contDiff_ginibreLebesgueDensityReal n).mul
    ((hf.contDiff_fderiv_apply (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const))
  have hcθ (k) : HasCompactSupport (θ k) := (hfc.fderiv_apply ℝ _).mul_left
  have hsθ (k) : tsupport (θ k) ⊆ {z | CollisionFree z} :=
    (tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ _)).trans hfs
  have hδ (k) : MemLp (δ k) 2 (ginibreMeasure n) := by
    have hc : HasCompactSupport (fun z => fderiv ℝ (θ k) z (ginibreCoordinateDirection k)) :=
      (hcθ k).fderiv_apply ℝ _
    have hcont : Continuous (fun z => fderiv ℝ (θ k) z (ginibreCoordinateDirection k)) :=
      ((hθ k).continuous_fderiv (by simp)).clm_apply continuous_const
    have hs := (tsupport_fderiv_apply_subset ℝ (ginibreCoordinateDirection k)).trans (hsθ k)
    have hdiv := collisionFree_test_div_density n hn _ hcont hc hs
    exact hdiv.1.memLp_of_hasCompactSupport hdiv.2
  have hdf (k) : MemLp (fun z => fderiv ℝ f z (ginibreCoordinateDirection k)) 2 (ginibreMeasure n)
      := by
    have hcont : Continuous (fun z => fderiv ℝ f z (ginibreCoordinateDirection k)) :=
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hcont.memLp_of_hasCompactSupport (hfc.fderiv_apply ℝ _)
  let G := (tsupport f).indicator g
  have hG := ginibreLocalWeak_compact_gradient_memLp hn g (tsupport f) hfc hg
  have hgk (k) : MemLp (fun z => G z k) 2 (ginibreMeasure n) := by
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
    exact P.comp_memLp' hG
  have hInt (k) : Integrable (fun z => g z k * fderiv ℝ f z (ginibreCoordinateDirection k))
      (ginibreMeasure n) := by
    apply ((hgk k).integrable_mul (hdf k)).congr
    exact ae_of_all _ (fun z => by
      by_cases hz : z ∈ tsupport f
      · simp [G, hz]
      · simp [G, hz, fderiv_of_notMem_tsupport ℝ hz])
  have hIntδ (k) : Integrable (fun z => u z * δ k z) (ginibreMeasure n) :=
    hu.integrable_mul (hδ k)
  have hpair (k) : (∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k) ∂ginibreMeasure n) =
      -(∫ z, u z * δ k z ∂ginibreMeasure n) := by
    have h := ginibreLocalWeak_distributional_density_pairing n hn u g hw k (θ k) (hθ k) (hcθ k)
        (hsθ k)
    have he : (∫ z, g z k * (θ k z / ginibreLebesgueDensityReal n z) ∂ginibreMeasure n) =
        ∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k) ∂ginibreMeasure n := by
      apply integral_congr_ae
      filter_upwards [ginibreFull_core_flux_div_density_ae hn f (ginibreCoordinateDirection k)] with
          z hz
      rw [hz]
    rw [he] at h
    exact h
  have hinner : (∫ z, inner ℝ (g z) (ginibreEuclideanGradient f z) ∂ginibreMeasure n) =
      ∑ k : Fin n × Fin 2, ∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k) ∂ginibreMeasure
          n := by
    rw [← integral_finsetSum Finset.univ (fun k _ => hInt k)]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      dsimp only
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro k hk
      rw [ginibreEuclideanGradient_coordinate]
      change fderiv ℝ f z (ginibreCoordinateDirection k)*g z k=_
      ring)
  rw [hinner]
  simp_rw [hpair]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun k _ => hIntδ k)]
  have hsum : (fun z => ∑ k : Fin n × Fin 2, u z * δ k z) =
      fun z => u z * ∑ k : Fin n × Fin 2, δ k z := by
    funext z
    exact (Finset.mul_sum _ _ _).symm
  rw [hsum]
  rw [mul_neg, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [ginibreLocalWeak_generator_divergence_ae hn f hf] with z hdiv
  change (1 / (n : ℝ)) * (u z * ∑ k : Fin n × Fin 2, δ k z) = u z * ginibrePregenerator n f z
  change (1 / (n : ℝ)) * (∑ k : Fin n × Fin 2, δ k z) = ginibrePregenerator n f z at hdiv
  rw [mul_left_comm, hdiv]

theorem ginibreLocalWeak_adjoint_to_gradient_equation {n : ℕ} (hn : 0 < n)
    (u f : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 (ginibreMeasure n))
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)))
    (hlocal : ∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
      MemLp g 2 (volume.restrict K))
    (ℓ a : ℝ)
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      a*(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n)=
        ℓ*(∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, f z*θ z ∂ginibreMeasure n)) :
    ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      ℓ*(∫ z, u z*θ z ∂ginibreMeasure n)+
      (a/(n : ℝ))*(∫ z, inner ℝ (g z) (ginibreEuclideanGradient θ z) ∂ginibreMeasure n)=
      ∫ z, f z*θ z ∂ginibreMeasure n := by
  intro θ hθ hc hs
  have hgreen := ginibreLocalWeak_generator_green hn u g hu hw θ hθ hc hs
    (hlocal (tsupport θ) hc hs)
  have hh := congrArg (fun x : ℝ => a*x) hgreen
  have he := heq θ hθ hc hs
  rw [div_eq_mul_inv] at ⊢
  simp only [one_div] at hh
  nlinarith

end
end GinibrePoincare

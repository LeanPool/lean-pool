/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorCoreCompatibility.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorComplexification
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity

/-!
# Ginibre Full Generator Core Compatibility
-/


@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

/-- Ordinary weak differentiation converted to the exact normalized weighted
pairing, for every smooth compact collision-free test. -/
theorem ginibreFull_distributional_density_pairing (n : ℕ) (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (k : Fin n × Fin 2) (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    (∫ z, g z k * (θ z / ginibreLebesgueDensityReal n z) ∂ginibreMeasure n) =
      -(∫ z, u z * (fderiv ℝ θ z (ginibreCoordinateDirection k) /
        ginibreLebesgueDensityReal n z) ∂ginibreMeasure n) := by
  have he := hu.2.2 k θ hθ hc hs
  have hds := (tsupport_fderiv_apply_subset ℝ (ginibreCoordinateDirection k)).trans hs
  rw [integral_collisionFree_test_eq_ginibre n hn _ θ hs,
    integral_collisionFree_test_eq_ginibre n hn _ _ hds] at he
  have hM : (ginibreNormalizingMass n).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(ginibreMassEvaluation n hn).1.ne',
      (ginibreMassEvaluation n hn).2.ne⟩
  apply mul_left_cancel₀ hM
  linarith

/-- The smooth core flux divided by the density is exactly the directional
 derivative almost everywhere for the actual Ginibre law. -/
theorem ginibreFull_core_flux_div_density_ae {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (v : Configuration n) :
    (fun z => (ginibreLebesgueDensityReal n z * fderiv ℝ f z v) /
      ginibreLebesgueDensityReal n z) =ᵐ[ginibreMeasure n] fun z => fderiv ℝ f z v := by
  filter_upwards [ginibreLebesgueDensityReal_ne_zero_ae hn] with z hz
  exact mul_div_cancel_left₀ _ hz

/-- The generator's divergence representation in the real Euclidean coordinate
indexing used by the full weak gradient. -/
theorem ginibreFull_core_divergence_ae {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (fun z => (1 / (n : ℝ)) * ∑ k : Fin n × Fin 2,
      fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
        fderiv ℝ f y (ginibreCoordinateDirection k)) z (ginibreCoordinateDirection k) /
          ginibreLebesgueDensityReal n z) =ᵐ[ginibreMeasure n] ginibrePregenerator n f := by
  have hcf := ginibre_ae_collisionFree n hn
  filter_upwards [hcf, ginibreLebesgueDensityReal_ne_zero_ae hn] with z hz hρ
  have h := ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence hn f hf.1 z hz
  simp only [one_div, ginibreCoordinateDirection, Fin.isValue, Fintype.sum_prod_type,
    Fin.sum_univ_two, ↓reduceIte, one_ne_zero]
  convert congrArg (fun t : ℝ => t / ginibreLebesgueDensityReal n z) h.symm using 1
  · simp_rw [← add_div]
    rw [← Finset.sum_div, mul_div_assoc]
    simp [one_div]
  · exact (mul_div_cancel_left₀ _ hρ).symm


/-- The actual weighted real L² gradient of a smooth collision-free core observable. -/
def ginibreFullCoreGradient {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) : GinibreFullGradientL2 n :=
  (ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1).2.toLp (ginibreEuclideanGradient f)

theorem ginibreFullCoreGradient_ae {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    (ginibreFullCoreGradient hn f hf : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      =ᵐ[ginibreMeasure n] ginibreEuclideanGradient f :=
  (ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1).2.coeFn_toLp

/-- Concrete real L² class of the smooth core pregenerator. -/
def ginibreFullCorePregenerator {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) : GinibreFullValueL2 n := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact ((continuous_ginibrePregenerator_of_core hf).memLp_of_hasCompactSupport
    (hasCompactSupport_ginibrePregenerator hf.2.1)).toLp (ginibrePregenerator n f)

theorem ginibreFullCorePregenerator_ae {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    (ginibreFullCorePregenerator hn f hf : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      ginibrePregenerator n f := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact ((continuous_ginibrePregenerator_of_core hf).memLp_of_hasCompactSupport
    (hasCompactSupport_ginibrePregenerator hf.2.1)).coeFn_toLp

/-- Exact integration by parts between every ordinary Ginibre weak pair and
an actual collision-free smooth core observable, with normalization `1/n`. -/
theorem ginibreFullGenerator_weak_core_green {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (1 / (n : ℝ)) * inner ℝ g (ginibreFullCoreGradient hn f hf) =
      -inner ℝ u (ginibreFullCorePregenerator hn f hf) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let θ (k : Fin n × Fin 2) : Configuration n → ℝ := fun z =>
    ginibreLebesgueDensityReal n z * fderiv ℝ f z (ginibreCoordinateDirection k)
  let δ (k : Fin n × Fin 2) : Configuration n → ℝ := fun z =>
    fderiv ℝ (θ k) z (ginibreCoordinateDirection k) / ginibreLebesgueDensityReal n z
  have hθ (k) : ContDiff ℝ ∞ (θ k) := contDiff_ginibreDirectionalFlux_core hf _
  have hcθ (k) : HasCompactSupport (θ k) := hasCompactSupport_ginibreDirectionalFlux_core hf _
  have hfs : tsupport f ⊆ {z | CollisionFree z} := fun z hz =>
    (collisionFree_iff_not_mem_collisionSet z).mpr (hf.2.2.1 hz)
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
      (hf.1.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hcont.memLp_of_hasCompactSupport (hf.2.1.fderiv_apply ℝ _)
  have hgk (k) : MemLp (fun z => g z k) 2 (ginibreMeasure n) := by
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
    exact P.comp_memLp g
  have hInt (k) : Integrable (fun z => g z k * fderiv ℝ f z (ginibreCoordinateDirection k))
      (ginibreMeasure n) := (hgk k).integrable_mul (hdf k)
  have hIntδ (k) : Integrable (fun z => u z * δ k z) (ginibreMeasure n) :=
    (Lp.memLp u).integrable_mul (hδ k)
  have hpair (k) : (∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k) ∂ginibreMeasure n) =
      -(∫ z, u z * δ k z ∂ginibreMeasure n) := by
    have h := ginibreFull_distributional_density_pairing n hn u g hu k (θ k) (hθ k) (hcθ k) (hsθ k)
    have he : (∫ z, g z k * (θ k z / ginibreLebesgueDensityReal n z) ∂ginibreMeasure n) =
        ∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k) ∂ginibreMeasure n := by
      apply integral_congr_ae
      filter_upwards [ginibreFull_core_flux_div_density_ae hn f (ginibreCoordinateDirection k)]
        with z hz
      rw [hz]
    rw [he] at h
    exact h
  have hinner : inner ℝ g (ginibreFullCoreGradient hn f hf) =
      ∑ k : Fin n × Fin 2, ∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k)
        ∂ginibreMeasure n := by
    rw [L2.inner_def, ← integral_finsetSum Finset.univ (fun k _ => hInt k)]
    apply integral_congr_ae
    filter_upwards [ginibreFullCoreGradient_ae hn f hf] with z hz
    rw [hz, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ginibreEuclideanGradient_coordinate]
    change fderiv ℝ f z (ginibreCoordinateDirection k) * g z k = _
    ring
  rw [hinner]
  simp_rw [hpair]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun k _ => hIntδ k)]
  have hsum : (fun z => ∑ k : Fin n × Fin 2, u z * δ k z) =
      fun z => u z * ∑ k : Fin n × Fin 2, δ k z := by
    funext z
    exact (Finset.mul_sum _ _ _).symm
  rw [hsum]
  rw [mul_neg, ← integral_const_mul]
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [ginibreFull_core_divergence_ae hn f hf,
    ginibreFullCorePregenerator_ae hn f hf] with z hdiv hgen
  change (1 / (n : ℝ)) * (u z * ∑ k : Fin n × Fin 2, δ k z) =
    (ginibreFullCorePregenerator hn f hf) z * u z
  rw [hgen]
  change (1 / (n : ℝ)) * (∑ k : Fin n × Fin 2, δ k z) = ginibrePregenerator n f z at hdiv
  rw [mul_left_comm, hdiv]
  ring


/-- Actual weighted real L² class of the core value. -/
def ginibreFullCoreValue {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) : GinibreFullValueL2 n :=
  (ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1).1.toLp f

theorem ginibreFullCoreValue_ae {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    (ginibreFullCoreValue hn f hf : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f :=
  (ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1).1.coeFn_toLp

/-- Every actual Theorem 1.9 core pair belongs to the full symmetric weak domain. -/
def ginibreFullCorePair {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) : ginibreFullWeakSpace n hn := by
  have hweak := ginibre_smooth_distributional_gradient n hn
    (ginibreFullCoreValue hn f hf) (ginibreFullCoreGradient hn f hf) f hf.1
    (ginibreFullCoreValue_ae hn f hf) (ginibreFullCoreGradient_ae hn f hf)
  refine ⟨(ginibreFullCoreValue hn f hf, ginibreFullCoreGradient hn f hf), hweak, ?_⟩
  obtain ⟨p, hp⟩ := ginibreFull_smoothCompact_symmetric_pair n hn f hf.isSmoothCompactSymmetric
  have hv : ginibreFullCoreValue hn f hf = p.val.1 :=
    Lp.ext ((ginibreFullCoreValue_ae hn f hf).trans hp.symm)
  have hg : ginibreFullCoreGradient hn f hf = p.val.2 :=
    ginibre_distributional_gradient_unique n hn _ _ _ hweak (by simpa only [hv] using p.property.1)
  rw [hv, hg]
  exact p.property.2

/-- The full weak form resolvent agrees exactly with `(I - A)⁻¹` on every
actual collision-free symmetric smooth core function. -/
theorem ginibreFullGenerator_resolvent_core {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreFullValueResolvent n hn
      (ginibreFullCoreValue hn f hf - ginibreFullCorePregenerator hn f hf) =
        ginibreFullCoreValue hn f hf := by
  have hpair := (ginibreFullCorePair hn f hf).property
  have heq : ∀ v : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n v h → IsGinibreSymmetricWeakPair (v, h) →
      inner ℝ (ginibreFullCoreValue hn f hf) v +
        (1 / (n : ℝ)) * inner ℝ (ginibreFullCoreGradient hn f hf) h =
        inner ℝ (ginibreFullCoreValue hn f hf - ginibreFullCorePregenerator hn f hf) v := by
    intro v h hv hs
    have hgreen := ginibreFullGenerator_weak_core_green hn v h hv f hf
    have hswap : (1 / (n : ℝ)) * inner ℝ (ginibreFullCoreGradient hn f hf) h =
        -inner ℝ (ginibreFullCorePregenerator hn f hf) v := by
      simpa only [real_inner_comm] using hgreen
    rw [hswap, inner_sub_left]
    ring
  exact (ginibreFullGenerator_resolvent_unique n hn
    (ginibreFullCoreValue hn f hf - ginibreFullCorePregenerator hn f hf)
    (ginibreFullCoreValue hn f hf) (ginibreFullCoreGradient hn f hf) hpair.1 hpair.2 heq).1.symm

end
end GinibrePoincare

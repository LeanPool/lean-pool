/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityDensityQuotient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityDensityCutoff
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityWeakProduct

/-!
# Ginibre transition analytic local regularity density quotient

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_weighted_resolvent_cutoff_gradient`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_weighted_resolvent_cutoff_gradient
    (n : ℕ) (hn : 0 < n) (ℓ : ℝ) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, ginibreLebesgueDensityReal n z*u z*ginibrePregenerator n θ z) =
        (∫ z, ginibreLebesgueDensityReal n z*(ℓ*u z-f z)*θ z))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z})
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hηK : tsupport η ⊆
        K) :
    ∃ g : (Fin n × Fin 2) → Configuration n → ℝ,
      (∀ k, MemLp (g k) 2 (volume : Measure (Configuration n))) ∧
      ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ z, θ z*g k z) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*(η z*u z)) := by
  classical
  let ρ := ginibreLebesgueDensityReal n
  obtain ⟨G, hGm, hGw⟩ := ginibreLocalRegularity_weighted_resolvent_density_cutoff_gradient
    n hn ℓ u f hu hf heq K hK hs η hη hc hηK
  obtain ⟨χ, hχ, hχc, hχs, hχone⟩ := ginibreLocalRegularity_exists_compact_interior_cutoff n hn
    (tsupport η) hc (hηK.trans hs)
  let q := fun z => χ z/ρ z
  have hqe : q = (fun z => ρ z*(χ z/ρ z^2)) := by
    funext z
    dsimp only [q]
    by_cases hz : ρ z = 0
    · simp [hz]
    · field_simp
  have hq : ContDiff ℝ ∞ q := by
    rw [hqe]
    exact (contDiff_ginibreLebesgueDensityReal n).mul
      (contDiff_collisionFree_test_div_density_sq hn χ hχ hχs)
  have hqc : HasCompactSupport q := by
    have he : q = χ*(fun z => (ρ z)⁻¹) := by
      funext z
      simp only [q, Pi.mul_apply, div_eq_mul_inv]
    rw [he]
    exact hχc.mul_right
  have hw : MemLp (fun z => η z*(ρ z*u z)) 2 (volume : Measure (Configuration n)) := by
    have hρw := (ginibreLocalRegularity_density_resolvent_data_memLp n hn ℓ u f hu hf K hK hs).1
    have hip : MemLp (K.indicator (fun z => ρ z*u z)) 2 (volume : Measure (Configuration n)) :=
      (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).mpr hρw
    have hi := (hη.continuous.memLp_top_of_hasCompactSupport hc volume).fun_mul (r := 2) hip
    apply MemLp.ae_eq (hf_Lp := hi)
    exact ae_of_all volume fun z => by
      dsimp only
      by_cases hz : z ∈ K
      · simp only [Set.indicator_of_mem hz]
      · have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hηK ht))
        simp [hηz]
  have hsource (z) : q z*(η z*(ρ z*u z)) = η z*u z := by
    by_cases hz : z ∈ tsupport η
    · have hρz : ρ z ≠ 0 := ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn (hs (hηK hz))
      have hχz : χ z = 1 := (hχone z hz).eq_of_nhds
      dsimp only [q]
      rw [hχz]
      field_simp
    · have hηz := image_eq_zero_of_notMem_tsupport hz
      simp [hηz]
  let g := fun k z => q z*G k z+(η z*(ρ z*u z))*fderiv ℝ q z (ginibreCoordinateDirection k)
  have hg (k) := ginibreLocalRegularity_scalar_weak_product (fun z => η z*(ρ z*u z)) (G k) q hw
    (hGm k) (ginibreCoordinateDirection k) hq hqc (hGw k)
  refine ⟨g, fun k => (hg k).1,?_⟩
  intro k θ hθ hθc
  simpa only [hsource] using (hg k).2 θ hθ hθc

end
end GinibrePoincare

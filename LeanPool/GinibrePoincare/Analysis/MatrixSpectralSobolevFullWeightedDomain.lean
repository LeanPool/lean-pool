/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevFullWeightedDomain.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevCompactWeightedDomain
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevSpatialPairs
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevWeakMultiplier

/-! # Full ordinary weak Sobolev domain equals the smooth weighted graph closure

Multiply the weak value by an expanding spatial cutoff. The product-rule
gradient is `χ • g + u • gradient χ`; both components remain in weighted L²
and have compact support. Positivity and continuity of the density give local
volume integrability, allowing the ordinary weak product rule to be applied.
The compact weighted-domain approximation theorem places each truncated pair
in the smooth graph closure. Their value and gradient converge in weighted L²,
so closedness gives membership for the original unrestricted weak pair.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace GinibrePoincare
noncomputable section

/-- The `i`-th coordinate of a vector in `EuclideanSpace ℝ (Fin m × Fin 2)`, as a continuous
linear functional. -/
def configurationGradientComponent (m : ℕ) (i : Fin m × Fin 2) :
    EuclideanSpace ℝ (Fin m × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 _ i

/-- Full weak gradient pairs under actual positive bounded finite densities
belong to the genuine compact smooth value/gradient graph completion. -/
theorem positive_density_full_weak_pair_mem_closure (m : ℕ)
    (μ : Measure (Configuration m)) [IsFiniteMeasure μ] (w : Configuration m → ℝ)
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (hμ : μ = (volume : Measure (Configuration m)).withDensity (fun x => ENNReal.ofReal (w x)))
    (c : ℝ≥0∞) (hc : c ≠ (⊤ : ℝ≥0∞))
    (hbound : μ ≤ c • (volume : Measure (Configuration m)))
    (u : Lp ℝ 2 μ) (g : Lp (EuclideanSpace ℝ (Fin m × Fin 2)) 2 μ)
    (hweak : ∀ i : Fin m × Fin 2, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i))) :
    (u, fun i => (configurationGradientComponent m i).compLpL 2 μ g) ∈
      closure (weightedConfigurationCompactDirectionalPairs m (Fin m × Fin 2)
        ginibreCoordinateDirection μ) := by
  let p := configurationWeakSpatialTruncation m μ u g
  let Φ := fun q : Lp ℝ 2 μ × Lp (EuclideanSpace ℝ (Fin m × Fin 2)) 2 μ =>
    (q.1, fun i => (configurationGradientComponent m i).compLpL 2 μ q.2)
  have hΦ : Continuous Φ := continuous_fst.prodMk (continuous_pi fun i =>
    ((configurationGradientComponent m i).compLpL 2 μ).continuous.comp continuous_snd)
  apply isClosed_closure.mem_of_tendsto (hΦ.tendsto (u, g) |>.comp
    (configurationWeakSpatialTruncation_tendsto m μ u g))
  apply Eventually.of_forall
  intro k
  let χ := ginibreSpatialCutoff m k
  have hχ : ContDiff ℝ ∞ χ := ginibreSpatialCutoff_smooth m k
  have hχc : HasCompactSupport χ := ginibreSpatialCutoff_compact m k
  let f := fun x : Configuration m => χ x * u x
  let G := fun x : Configuration m => χ x • g x + u x • ginibreEuclideanGradient χ x
  obtain ⟨hf, hG⟩ := configuration_weak_multiplier_memLp m μ u g
    (Lp.memLp u) (Lp.memLp g) χ hχ hχc
  have hfc : HasCompactSupport f := hχc.mul_right (f' := (fun x => u x))
  have hGc₁ : HasCompactSupport (fun x => χ x • g x) :=
    hχc.smul_right (f' := fun x => g x)
  have hGc₂ : HasCompactSupport (fun x => u x • ginibreEuclideanGradient χ x) :=
    (compactSupport_ginibreEuclideanGradient χ hχc).smul_left (f := fun x => u x)
  have hGc : HasCompactSupport G := hGc₁.add hGc₂
  have hg (i : Fin m × Fin 2) : MemLp (fun x => G x i) 2 μ :=
    (configurationGradientComponent m i).comp_memLp' hG
  have hgc (i : Fin m × Fin 2) : HasCompactSupport (fun x => G x i) :=
    hGc.comp_left (g := fun z : EuclideanSpace ℝ (Fin m × Fin 2) => z i) (by rfl)
  have huLocal : LocallyIntegrable (fun x : Configuration m => u x) volume :=
    positive_density_integrable_locallyIntegrable volume w _ hw hpos
      (by rw [← hμ]; exact (Lp.memLp u).integrable (by norm_num))
  have hgLocal (i : Fin m × Fin 2) : LocallyIntegrable (fun x => g x i) volume :=
    positive_density_integrable_locallyIntegrable volume w _ hw hpos (by
      rw [← hμ]
      exact ((configurationGradientComponent m i).comp_memLp' (Lp.memLp g)).integrable (by
          norm_num))
  have htweak (i : Fin m × Fin 2) (θ : Configuration m → ℝ)
      (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
      (∫ x, G x i * θ x) = -(∫ x, f x * fderiv ℝ θ x (ginibreCoordinateDirection i)) := by
    have ht := configuration_weak_directional_derivative_mul m u (fun x => g x i) χ
      (ginibreCoordinateDirection i) huLocal (hgLocal i) hχ (hweak i) θ hθ hθc
    simpa only [G, f, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      ginibreEuclideanGradient_coordinate] using ht
  have hcl := positive_density_compact_weak_pair_mem_closure m
    ginibreCoordinateDirection μ w hw hpos hμ c hc hbound f (fun i x => G x i)
    hf hg hfc hgc htweak
  have hv : hf.toLp f = (p k).1 := rfl
  have hd (i : Fin m × Fin 2) : (hg i).toLp (fun x => G x i) =
      (configurationGradientComponent m i).compLpL 2 μ (p k).2 := by
    apply Lp.ext
    filter_upwards [(hg i).coeFn_toLp,
      (configurationGradientComponent m i).coeFn_compLpL ((p k).2),
      configurationWeakSpatialTruncation_gradient_ae m μ u g k] with x hx hy hz
    rw [hx, hy, hz]
    rfl
  change ((p k).1, fun i => (configurationGradientComponent m i).compLpL 2 μ (p k).2) ∈ _
  simpa only [hv, hd] using hcl

end
end GinibrePoincare

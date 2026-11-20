/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiCompactGraphApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiWeightedMollification
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiDerivativeKernel
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Non quadratic pi compact graph approximation

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoSubharmonicPotential_pi_full_compact_gap`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- The integral, against `f a`, of the weighted `∂̄`-graphs of the pure tensors of the
normalised bump `φ` translated to the points `a i`. -/
def planarPiCompactGraphAverage {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ : ContDiffBump (0 : ℂ)) (f : Configuration (d + 1) → ℂ) : PlanarPiDbarGraphSpace (d+1) :=
  ∫ a, f a • planarPiPureDbarGraph n V hV
    (fun i => planarComplexTestTranslate (planarPiNormalizedBumpTest φ) (a i))
    ∂Measure.pi (fun _ => (volume : Measure ℂ))

theorem planarPiCompactGraphAverage_mem {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ : ContDiffBump (0 : ℂ)) (f : Configuration (d + 1) → ℂ) (hf : Continuous f) (hc :
        HasCompactSupport f) :
    planarPiCompactGraphAverage n V hV φ f ∈ planarPiDbarClosedGraph n V hV :=
  planarPiTranslatedGraph_integral_mem n V hV _ f hf hc

theorem planarPiCompactGraphAverage_dbar {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ : ContDiffBump (0 : ℂ)) (f : Configuration (d + 1) → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (i : Fin (d + 1)) :
    (planarPiCompactGraphAverage n V hV φ f).2 i = weightedPiBumpAverage n V hV φ (piComplexDbar i
        f) := by
  have he := planarPiTranslatedGraph_integral_dbar_ae n V hV
    (fun _ => planarPiNormalizedBumpTest φ) f hf.continuous hc i
  have hw := weightedPiBumpAverage_coeFn n V hV φ (piComplexDbar i f)
    (piComplexDbar_continuous i f hf) (piComplexDbar_compact i f hc)
  simp only [← MeasureTheory.volume_pi] at he
  apply Lp.ext
  filter_upwards [he, hw] with x hx hy
  change (planarPiCompactGraphAverage n V hV φ f).2 i x = _ at hx
  rw [hx, hy]
  congr 1
  rw [piSeparated_dbar_convolution_transfer f hf hc (fun _ => planarPiNormalizedBumpTest φ) i x]
  simp only [planarPiNormalizedBumpTest, piPlanarBump, Complex.ofReal_prod, Pi.sub_apply]

/-- The weighted `∂̄`-graph of a compactly supported `C¹` function `f`: the `L²` classes of
`f * w` and of `∂̄_i f * w` for every coordinate `i`, where `w = piPotentialHalfWeight`. -/
def piCompactWeightedDbarGraph {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : Configuration (d + 1) → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    PlanarPiDbarGraphSpace (d+1) :=
  (piCompactFunctionL2 (d+1) (fun x => f x * piPotentialHalfWeight (d+1) n V x)
    (hf.continuous.mul (piPotentialHalfWeight_continuous (d+1) n V hV)) hc.mul_right,
   fun i => piCompactFunctionL2 (d+1) (fun x => piComplexDbar i f x * piPotentialHalfWeight (d+1) n
       V x)
    ((piComplexDbar_continuous i f hf).mul (piPotentialHalfWeight_continuous (d+1) n V hV))
    (piComplexDbar_compact i f hc).mul_right)

theorem planarPiCompactGraphAverage_tendsto {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (f : Configuration (d + 1) → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Tendsto (fun m => planarPiCompactGraphAverage n V hV (φ m) f) atTop
      (𝓝 (piCompactWeightedDbarGraph n V hV f hf hc)) := by
  have h1 := weightedPiBumpAverage_tendsto n V hV φ hφ f hf.continuous hc
  have h2 : Tendsto (fun m => (planarPiCompactGraphAverage n V hV (φ m) f).2) atTop
      (𝓝 (piCompactWeightedDbarGraph n V hV f hf hc).2) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simp only [planarPiCompactGraphAverage_dbar n V hV _ f hf hc i]
    exact weightedPiBumpAverage_tendsto n V hV φ hφ (piComplexDbar i f)
      (piComplexDbar_continuous i f hf) (piComplexDbar_compact i f hc)
  exact h1.prodMk_nhds h2

/-- The planar bump at `0` with inner radius `1 / (2 (m + 1))` and outer radius `1 / (m + 1)`,
shrinking to the origin as `m → ∞`. -/
def planarPiShrinkingBump (m : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨(1 / ((m : ℝ) + 1)) / 2, 1 / ((m : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩

theorem planarPiShrinkingBump_rOut_tendsto :
    Tendsto (fun m => (planarPiShrinkingBump m).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every full compact C¹ configuration test has its genuine weighted value
and all genuine Wirtinger derivatives in the actual separated-core closure. -/
theorem piCompactWeightedDbarGraph_mem {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : Configuration (d + 1) → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    piCompactWeightedDbarGraph n V hV f hf hc ∈ planarPiDbarClosedGraph n V hV :=
  (planarPiDbarGraphMap n V hV).range.isClosed_topologicalClosure.mem_of_tendsto
    (planarPiCompactGraphAverage_tendsto n V hV planarPiShrinkingBump
      planarPiShrinkingBump_rOut_tendsto f hf hc)
    (Eventually.of_forall (fun _ => planarPiCompactGraphAverage_mem n V hV _ f hf.continuous hc))

theorem rhoSubharmonicPotential_pi_full_compact_gap {d : ℕ}
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (f : Configuration (d + 1) → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let x := piCompactWeightedDbarGraph n V hV.continuous f hf hc
    ‖x.1 - planarPiBergmanProjection n V hV x.1‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * ((List.finRange (d+1)).map (fun i => ‖x.2 i‖ ^ 2)).sum :=
  rhoSubharmonicPotential_pi_closed_graph_gap n hn V ρ hρpos hV hρ _
    (piCompactWeightedDbarGraph_mem n V hV.continuous f hf hc)
end
end GinibrePoincare

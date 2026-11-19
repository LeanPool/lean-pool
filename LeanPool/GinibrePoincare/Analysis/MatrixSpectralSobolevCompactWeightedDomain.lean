/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevCompactWeightedDomain.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLocalIntegrability
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevWeightedCompact

/-! # Unconditional compact weak graph approximation for positive bounded densities -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace GinibrePoincare
noncomputable section

theorem positive_density_compact_weak_pair_mem_closure (m : ℕ)
    {I : Type*} [Finite I] (v : I → Configuration m)
    (μ : Measure (Configuration m)) (w : Configuration m → ℝ)
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (hμ : μ = (volume : Measure (Configuration m)).withDensity (fun x => ENNReal.ofReal (w x)))
    (c : ℝ≥0∞) (hc : c ≠ (⊤ : ℝ≥0∞))
    (hbound : μ ≤ c • (volume : Measure (Configuration m)))
    (f : Configuration m → ℝ) (g : I → Configuration m → ℝ)
    (hf : MemLp f 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hfc : HasCompactSupport f) (hgc : ∀ i, HasCompactSupport (g i))
    (hweak : ∀ i, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g i x * θ x) = -(∫ x, f x * fderiv ℝ θ x (v i))) :
    (hf.toLp f, fun i => (hg i).toLp (g i)) ∈
      closure (weightedConfigurationCompactDirectionalPairs m I v μ) := by
  have := Fintype.ofFinite I
  have hfv : MemLp f 2 volume :=
    positive_density_memLp_volume_of_compactSupport volume w hw hpos f
      (by rwa [← hμ]) hfc
  have hgv (i : I) : MemLp (g i) 2 volume :=
    positive_density_memLp_volume_of_compactSupport volume w hw hpos (g i)
      (by rw [← hμ]; exact hg i) (hgc i)
  exact weighted_configuration_compact_weak_pair_mem_closure m v μ c hc hbound
    f g hfv hgv hfc hgc hweak

end
end GinibrePoincare

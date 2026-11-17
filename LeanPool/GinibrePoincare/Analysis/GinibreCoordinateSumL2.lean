/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityFirstQuotient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EquilibriumProbability
public import LeanPool.GinibrePoincare.Analysis.PermutationLp

/-! # The coordinate sum in symmetric Ginibre L² -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped Topology ContDiff

/-- The coordinate sum has a Gaussian law, so it belongs to Ginibre L². -/
theorem memLp_coordinateSum (n : ℕ) (hn : 0 < n) :
    MemLp (coordinateSum : Configuration n → ℂ) 2 (ginibreMeasure n) := by
  have hgauss : Integrable (fun s : ℂ => ‖s‖ ^ 2) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure] using
      integrable_norm_pow_complexCoordinateGaussianProbability 1 2
  have hpush : Integrable (fun s : ℂ => ‖s‖ ^ 2)
      ((ginibreMeasure n).map coordinateSum) := by
    rw [coordinateSum_ginibre_gaussian n hn]
    exact hgauss
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_coordinateSum n).aestronglyMeasurable).mpr
      (hpush.comp_aemeasurable (measurable_coordinateSum n).aemeasurable)

/-- The coordinate sum represents a particle-symmetric Ginibre L² class. -/
theorem ginibreSymmetricL2_coordinateSum (n : ℕ) (hn : 0 < n) :
    ∃ s : ginibreSymmetricL2 n,
      (s.val : Configuration n → ℂ) =ᵐ[ginibreMeasure n] coordinateSum := by
  let hm := memLp_coordinateSum n hn
  let u := hm.toLp coordinateSum
  have hu : (u : Configuration n → ℂ) =ᵐ[ginibreMeasure n] coordinateSum := hm.coeFn_toLp
  have hs : u ∈ ginibreSymmetricL2 n := by
    intro σ
    apply Lp.ext
    have hp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hu
    filter_upwards [Lp.coeFn_compMeasurePreserving u
      (ginibre_measurePreserving_permute σ), hp, hu] with z hz hpz huz
    change (ginibrePermutationL2 σ u) z = u z
    change (Lp.compMeasurePreserving (permute σ)
      (ginibre_measurePreserving_permute σ) u) z = u z
    rw [hz, huz]
    simpa only [Function.comp_apply, coordinateSum_permute] using hpz
  exact ⟨⟨u, hs⟩, hu⟩

end GinibrePoincare

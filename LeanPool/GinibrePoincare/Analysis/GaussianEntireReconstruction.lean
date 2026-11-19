/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianEntireReconstruction.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireRepresentatives
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireDifferentiability
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireHilbertIdentification

/-! # Reconstructing an entire representative of the zero mode

The representative is the holomorphic Hermite series with coefficients taken
from the original Gaussian L² vector. `GaussianEntireHilbertIdentification`
identifies this series with the zero-mode projection almost everywhere;
`GaussianEntireDifferentiability` supplies genuine entire differentiability.
The endpoint packages both facts in `IsGaussianEntireRepresentative`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Every holomorphic Hermite zero mode has an actual multivariate entire
representative, with no regularity hypothesis on the input class. -/
theorem gaussianZeroMode_has_entire_representative {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteMode hn 0 u ∈ gaussianEntireL2 n := by
  refine ⟨fun z => ∑' p, gaussianHermiteCoefficient hn u (p, 0) *
    ComplexHermite.multivariateNormalized n hn p 0 z, ?_, ?_⟩
  · exact differentiable_holomorphicHermite_series n hn _
      (fun p => gaussianHermiteCoefficient_norm_le hn u (p, 0))
  · exact gaussianZeroMode_holomorphic_series_ae hn u

end
end GinibrePoincare

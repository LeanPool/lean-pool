/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorRealErgodicity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorErgodicity
/-!
# Correspondence operator real ergodicity

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorRealEvolution_ergodic`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
/-- Strong convergence of the unrestricted real diffusion to its actual mean. -/
theorem correspondenceOperatorRealEvolution_ergodic {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) :
    Tendsto (fun t : ℝ≥0 => correspondenceOperatorRealEvolution n hn t u) atTop
      (𝓝 (ginibreRealConstantL2 n hn (∫z, u z∂ginibreMeasure n))) := by
  have hm : (∫z, ginibreFullComplexOfReal n u z∂ginibreMeasure n) =
      ((∫z, u z∂ginibreMeasure n : ℝ) : ℂ) := by
    rw [integral_congr_ae (ginibreFullComplexOfReal_ae n u), integral_complex_ofReal]
  have h := (ginibreFullComplexRe n).continuous.tendsto _ |>.comp
    (correspondenceOperatorEvolution_ergodic hn (ginibreFullComplexOfReal n u))
  rw [hm] at h
  have hc : ginibreFullComplexRe n (ginibreFullConstant n hn
      ((∫z, u z∂ginibreMeasure n : ℝ) : ℂ)).val =
      ginibreRealConstantL2 n hn (∫z, u z∂ginibreMeasure n) :=
    by
      have hh : ginibreFullComplexRe n (ginibreFullConstant n hn
          ((∫z, u z∂ginibreMeasure n : ℝ) : ℂ)).val =
          ginibreRealConstantL2 n hn (((∫z, u z∂ginibreMeasure n : ℝ) : ℂ).re) :=
        ginibreFullConstant_re n hn _
      simpa using hh
  rw [hc] at h
  exact h
end
end GinibrePoincare

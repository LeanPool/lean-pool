/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianGlobal.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicGaussianProcess
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobalCovariance
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobalCoordinates
public import Mathlib.Probability.BrownianMotion.Basic
/-!
# Alternative Bakry Emery Brownian global

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianCoordinate_isBrownian`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem bakryBrownianGlobalProcess_isBrownian :
    IsBrownianReal bakryBrownianGlobalProcess bakryBrownianGlobalMeasure := by
  have hL := bakryBrownianDyadicCompletedPath_memLp_of_original bakryBrownianDyadicPath_memLp_two
  have hC := bakryBrownianDyadicCompletedPath_covariance_of_original
      bakryBrownianDyadicPath_covariance
  have hM := bakryBrownianDyadicCompletedPath_mean_of_original bakryBrownianDyadicPath_mean
  have hG := bakryBrownianGlobalProcess_isGaussian_of_unit
    (bakryBrownianDyadicCompletedPath_isGaussian_of_original
        bakryBrownianDyadicPath_isGaussianProcess)
  refine ⟨hG.isPreBrownianReal_of_covariance
    (bakryBrownianGlobalProcess_mean_of_unit hL hM) ?_,?_⟩
  · intro s t hst
    rw [bakryBrownianGlobalProcess_covariance_of_unit hL hC, min_eq_left]
    exact_mod_cast hst
  · exact ae_of_all _ bakryBrownianGlobalProcess_continuous

theorem bakryBrownianCoordinate_isBrownian (ι : Type*) [Fintype ι] :
    ∀ i, IsBrownianReal (bakryBrownianCoordinateProcess ι i) (bakryBrownianCoordinateMeasure ι) :=
  bakryBrownianCoordinate_isBrownian_of_scalar ι bakryBrownianGlobalProcess_isBrownian

end
end GinibrePoincare

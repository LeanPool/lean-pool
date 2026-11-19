/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalCoordinateLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalPiGaussianLaw

/-!
# Brownian orthogonal coordinate law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `isotropicGaussian_coordinates_independent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem scaledStandardGaussian_toPi (ι : Type*) [Fintype ι] (v : ℝ≥0) :
    (scaledStandardGaussian (EuclideanSpace ℝ ι) v).map
      (fun x : EuclideanSpace ℝ ι => fun i => x i) =
      Measure.pi (fun _ : ι => gaussianReal 0 v) := by
  rw [← piGaussianReal_map_toLp_scaledStandard ι v]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

theorem isotropicGaussian_coordinates_independent {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (v : ℝ≥0) (X : Ω → EuclideanSpace ℝ ι)
    (hX : HasLaw X (scaledStandardGaussian (EuclideanSpace ℝ ι) v) P) :
    (∀ i, HasLaw (fun ω => X ω i) (gaussianReal 0 v) P) ∧
      iIndepFun (fun i ω => X ω i) P := by
  have hp : HasLaw (fun ω i => X ω i) (Measure.pi (fun _ : ι => gaussianReal 0 v)) P :=
    (show HasLaw (fun x : EuclideanSpace ℝ ι => fun i => x i)
      (Measure.pi (fun _ : ι => gaussianReal 0 v))
      (scaledStandardGaussian (EuclideanSpace ℝ ι) v) from
        ⟨by fun_prop, scaledStandardGaussian_toPi ι v⟩).fun_comp hX
  have hi (i : ι) : HasLaw (fun ω => X ω i) (gaussianReal 0 v) P :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 v) i).comp_hasLaw hp
  exact ⟨hi, (iIndepFun_iff_hasLaw_pi_pi hi).mpr hp⟩

end
end GinibrePoincare

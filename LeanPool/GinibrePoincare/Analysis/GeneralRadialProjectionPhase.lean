/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralRadialProjectionPhase.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBergmanPhase
public import LeanPool.GinibrePoincare.Analysis.GeneralRadialProjectionFourier
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# General radial projection phase

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarLebesgue_mem_closed_span_phase_fourier`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The actual pullback action of circle rotations is strongly continuous
on all planar Lebesgue L² vectors. -/
theorem planarLebesguePhase_circle_continuous {T : ℝ}
    (u : PlanarLebesgueL2) :
    Continuous (fun t : AddCircle T => planarLebesguePhase (AddCircle.toCircle t)
      (Circle.norm_coe _) u) := by
  let g : AddCircle T → C(ℂ, ℂ) := fun t =>
    ⟨fun z => (AddCircle.toCircle t : ℂ) * z, continuous_const.mul continuous_id⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_subtype_val.comp AddCircle.continuous_toCircle).comp continuous_fst).mul
        continuous_snd
  have hmp : ∀ t, MeasurePreserving (g t) (volume : Measure ℂ) volume := fun t =>
    measurePreserving_complex_mul_of_norm_one _ (Circle.norm_coe _)
  exact continuous_const.compMeasurePreservingLp hg hmp (by norm_num : (2 : ENNReal) ≠ ⊤)

/-- Every actual L² vector is in the closed span of the Fourier modes of
its own continuous rotation orbit. -/
theorem planarLebesgue_mem_closed_span_phase_fourier {T : ℝ} [Fact (0 < T)]
    (u : PlanarLebesgueL2) :
    u ∈ (Submodule.span ℂ (range (fourierCoeff (fun t : AddCircle T =>
      planarLebesguePhase (AddCircle.toCircle t) (Circle.norm_coe _) u)))).topologicalClosure := by
  have h := continuous_circle_mem_closed_span_fourierCoeff _
    (planarLebesguePhase_circle_continuous (T := T) u) 0
  convert h using 1
  simp only [AddCircle.toCircle_zero]
  symm
  simp only [planarLebesguePhase, l2PullbackEquiv, Circle.coe_one]
  change Lp.compMeasurePreserving (complexMulMeasurableEquiv 1 _) _ u = u
  have he : (complexMulMeasurableEquiv 1 (by simp) : ℂ → ℂ) = id := funext one_mul
  simp only [he]
  exact Lp.compMeasurePreserving_id_apply u

end
end GinibrePoincare

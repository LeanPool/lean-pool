/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathOUProjection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOU

/-! # Continuous linear projections of actual OU convolutions -/

@[expose] public section
open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem drivenOUPath_continuousLinearMap (L : E →L[ℝ] F) (κ : ℝ) (x : E)
    (N : ℝ → E) (hN : Continuous N) (t : ℝ) :
    L (drivenOUPath κ x N t) = drivenOUPath κ (L x) (fun s => L (N s)) t := by
  have hc : Continuous (fun s : ℝ => Real.exp (κ * s) • N s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul hN
  simp only [drivenOUPath, drivenOUCorrection, map_add, map_smul, map_sub]
  rw [← L.intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  simp only [map_smul]

end
end GinibrePoincare

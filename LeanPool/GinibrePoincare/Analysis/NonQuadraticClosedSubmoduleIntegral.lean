/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticClosedSubmoduleIntegral.lean.
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

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Genuine Bochner integrals in closed linear subspaces -/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- A Bochner integral of an actual integrable subspace-valued function
belongs to the same closed subspace. The quotient map proves this for
Banach spaces, including the product norm used by derivative graphs. -/
theorem bochner_integral_mem_closed_submodule
    {A H : Type*} [MeasurableSpace A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (K : Submodule ℝ H) (hK : IsClosed (K : Set H)) (μ : Measure A)
    (f : A → H) (hf : Integrable f μ) (hmem : ∀ a, f a ∈ K) :
    (∫ a, f a ∂μ) ∈ K := by
  let : IsClosed (K : Set H) := hK
  have he : K.mkQL (∫ a, f a ∂μ) = 0 := by
    rw [← K.mkQL.integral_comp_comm hf]
    have hz : (fun a => K.mkQL (f a)) = 0 := by
      funext a
      exact (Submodule.Quotient.mk_eq_zero K).mpr (hmem a)
    rw [hz]
    change (∫ a, (0 : H ⧸ K) ∂μ) = 0
    exact integral_zero _ _
  exact (Submodule.Quotient.mk_eq_zero K).mp he
end
end GinibrePoincare

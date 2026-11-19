/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticProductDbarClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticProductDbar

/-! # The closed actual product ∂bar graph
The sharp product estimate extends to the genuine graph completion of
finite separated compact tests, with both derivative coordinates retained. -/

@[expose] public section
open MeasureTheory
open scoped ContDiff InnerProductSpace TensorProduct
namespace GinibrePoincare
noncomputable section

/-- The graph space of the two-variable `∂̄` operator: a value and its left and right `∂̄`
components, all in `L²(ℂ × ℂ)`. -/
abbrev PlanarProductDbarGraphSpace :=
  PlanarProductLebesgueL2 × (PlanarProductLebesgueL2 × PlanarProductLebesgueL2)

/-- The weighted `∂̄`-graph map on tensors of tests: the weighted value together with the
weighted left and right `∂̄` derivatives. -/
def planarProductDbarGraphMap (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarProductCompactTensor →ₗ[ℂ] PlanarProductDbarGraphSpace :=
  (planarProductWeightedValue n V hV).prod
    ((planarProductWeightedDbarLeft n V hV).prod (planarProductWeightedDbarRight n V hV))

/-- The genuine closure of the value-and-two-derivatives graph. -/
def planarProductDbarClosedGraph (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    Submodule ℂ PlanarProductDbarGraphSpace :=
  (planarProductDbarGraphMap n V hV).range.topologicalClosure

/-- The exact product Hörmander constant survives closure in the actual
L² value-and-derivative graph, without any new inequality hypothesis. -/
theorem rhoSubharmonicPotential_product_closed_graph_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (x : PlanarProductDbarGraphSpace)
    (hx : x ∈ planarProductDbarClosedGraph n V hV.continuous) :
    ‖x.1 - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV x.1)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * (‖x.2.1‖ ^ 2 + ‖x.2.2‖ ^ 2) := by
  let S : Set PlanarProductDbarGraphSpace := {x |
    ‖x.1 - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV x.1)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * (‖x.2.1‖ ^ 2 + ‖x.2.2‖ ^ 2)}
  have hc : IsClosed S := isClosed_le
    ((continuous_fst.sub ((planarLeftBergmanProjection n V hV).continuous.comp
      ((planarRightBergmanProjection n V hV).continuous.comp continuous_fst))).norm.pow 2)
    (continuous_const.mul (((continuous_fst.comp continuous_snd).norm.pow 2).add
      ((continuous_snd.comp continuous_snd).norm.pow 2)))
  have hi : ((planarProductDbarGraphMap n V hV.continuous).range : Set PlanarProductDbarGraphSpace)
      ⊆ S := by
    rintro _ ⟨f, rfl⟩
    exact rhoSubharmonicPotential_product_compact_tensor_gap n hn V ρ hρpos hV hρ f
  exact hc.closure_subset_iff.mpr hi hx
end
end GinibrePoincare

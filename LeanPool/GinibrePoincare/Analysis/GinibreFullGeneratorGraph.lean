/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorComplexification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupGenerator

/-! # The generator graph of the concrete symmetric Ginibre weak resolvent -/

@[expose] public section

open scoped LinearPMap
namespace GinibrePoincare
noncomputable section

/-- The maximal generator determined by the concrete full weak Dirichlet resolvent. -/
def ginibreFullGenerator (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n →ₗ.[ℂ] ginibreSymmetricL2 n :=
  resolventGenerator (ginibreFullComplexResolvent n hn) (ginibreFullComplexResolvent_injective n hn)

/-- Full generator membership is an exact equation in the actual weak resolvent. -/
theorem ginibreFullGenerator_graph_iff (n : ℕ) (hn : 0 < n) (u v : ginibreSymmetricL2 n) :
    (u, v) ∈ (ginibreFullGenerator n hn).graph ↔ ginibreFullComplexResolvent n hn (u - v) = u := by
  rw [ginibreFullGenerator, resolventGenerator_graph _ (ginibreFullComplexResolvent_injective n hn)]
  rfl

theorem ginibreFullGenerator_dense_domain (n : ℕ) (hn : 0 < n) :
    Dense ((ginibreFullGenerator n hn).domain : Set (ginibreSymmetricL2 n)) :=
  resolventGenerator_dense_domain _ (ginibreFullComplexResolvent_injective n hn)
    (ginibreFullComplexResolvent_denseRange n hn)

/-- Self-adjointness of the full symmetric weak diffusion generator. -/
theorem ginibreFullGenerator_selfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (ginibreFullGenerator n hn) :=
  resolventGenerator_selfAdjoint _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) (ginibreFullComplexResolvent_denseRange n hn)

theorem ginibreFullGenerator_isClosed (n : ℕ) (hn : 0 < n) :
    (ginibreFullGenerator n hn).IsClosed := (ginibreFullGenerator_selfAdjoint n hn).isClosed

end
end GinibrePoincare

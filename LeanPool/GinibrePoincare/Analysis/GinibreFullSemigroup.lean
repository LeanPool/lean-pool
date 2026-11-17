/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroup.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorComplexification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupInfinitesimal

/-! # The actual full symmetric Ginibre weak diffusion semigroup

The input resolvent is constructed from the concrete weak Dirichlet form.
The generator and semigroup act on the full symmetric Ginibre L² space.
-/


@[expose] public section


open scoped NNReal LinearPMap
namespace GinibrePoincare
noncomputable section

/-- Full-space contraction semigroup constructed from the actual weak resolvent. -/
def ginibreFullEvolution (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    ginibreSymmetricL2 n →L[ℂ] ginibreSymmetricL2 n :=
  resolventCfcEvolution (ginibreFullComplexResolvent n hn) t

@[simp] theorem ginibreFullEvolution_zero (n : ℕ) (hn : 0 < n) :
    ginibreFullEvolution n hn 0 = 1 :=
  resolventCfcEvolution_zero _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)

theorem ginibreFullEvolution_add (n : ℕ) (hn : 0 < n) (s t : ℝ≥0) :
    ginibreFullEvolution n hn (s + t) = ginibreFullEvolution n hn s * ginibreFullEvolution n hn t :=
  resolventCfcEvolution_add _ s t

theorem ginibreFullEvolution_norm_le (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    ‖ginibreFullEvolution n hn t‖ ≤ 1 :=
  resolventCfcEvolution_norm_le _ (ginibreFullComplexResolvent_spectrum n hn) t

theorem ginibreFullEvolution_contracts (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (f : ginibreSymmetricL2 n) : ‖ginibreFullEvolution n hn t f‖ ≤ ‖f‖ :=
  resolventCfcEvolution_contracts _ (ginibreFullComplexResolvent_spectrum n hn) t f

/-- Strong continuity holds for every actual symmetric Ginibre L² observable. -/
theorem continuous_ginibreFullEvolution (n : ℕ) (hn : 0 < n) (f : ginibreSymmetricL2 n) :
    Continuous (fun t : ℝ≥0 => ginibreFullEvolution n hn t f) :=
  continuous_resolventCfcEvolution _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_spectrum n hn) (ginibreFullComplexResolvent_denseRange n hn) f

/-- Every full evolution operator is self-adjoint. -/
theorem ginibreFullEvolution_selfAdjoint (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    IsSelfAdjoint (ginibreFullEvolution n hn t) :=
  resolventCfcEvolution_selfAdjoint _ t

/-- Hilbert-space positivity of every full evolution operator. -/
theorem ginibreFullEvolution_isPositive (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    (ginibreFullEvolution n hn t).IsPositive :=
  resolventCfcEvolution_isPositive _ (ginibreFullComplexResolvent_spectrum n hn) t

/-- The maximal generator determined by the concrete full weak Dirichlet resolvent. -/
def ginibreFullGenerator (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n →ₗ.[ℂ] ginibreSymmetricL2 n :=
  resolventGenerator (ginibreFullComplexResolvent n hn)

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

/-- The full-space generator is exactly the semigroup's right infinitesimal generator. -/
theorem ginibreFullGenerator_graph_iff_right_derivative (n : ℕ) (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) :
    (u, v) ∈ (ginibreFullGenerator n hn).graph ↔
      HasDerivWithinAt (fun t : ℝ => ginibreFullEvolution n hn (Real.toNNReal t) u)
        v (Set.Ici 0) 0 :=
  resolventGenerator_graph_iff_right_derivative _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) (ginibreFullComplexResolvent_spectrum n hn)
    (ginibreFullComplexResolvent_denseRange n hn) u v

/-- Full generator graph preservation, with no restriction to polynomial observables. -/
theorem ginibreFullEvolution_preserves_generator_graph (n : ℕ) (hn : 0 < n)
    (t : ℝ≥0) (u v : ginibreSymmetricL2 n) (hp : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    (ginibreFullEvolution n hn t u, ginibreFullEvolution n hn t v) ∈ (ginibreFullGenerator n
      hn).graph :=
  resolventCfcEvolution_preserves_generator_graph _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) t u v hp

end
end GinibrePoincare

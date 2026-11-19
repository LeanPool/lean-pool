/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLaplaceOperator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLaplaceBounds

/-!
# Ginibre transition analytic Laplace operator

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `actualContractionLaplaceLinear_norm_bound`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Literal normalized Laplace integration is a genuine linear map. -/
def actualContractionLaplaceLinear {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖) (c : ℝ) (hc : 0 < c) : E →ₗ[ℝ] E where
  toFun u := ∫ s in Ioi (0 : ℝ), (c*Real.exp (-c*s)) • A s.toNNReal u
  map_add' u v := by
    simp only [map_add, smul_add]
    exact integral_add (actualContractionLaplace_integrable A hcont hbound c hc u)
      (actualContractionLaplace_integrable A hcont hbound c hc v)
  map_smul' d u := by
    simp only [map_smul, RingHom.id_apply]
    have he : (fun s : ℝ => (c*Real.exp (-c*s)) • d • A s.toNNReal u)=
        (fun s => d • (c*Real.exp (-c*s)) • A s.toNNReal u) := by
      funext s
      exact smul_comm _ _ _
    rw [he, integral_smul]

/-- The literal normalized Laplace operator is a contraction, internally
bounded using the true mass-one exponential weight. -/
theorem actualContractionLaplaceLinear_norm_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖) (c : ℝ) (hc : 0 < c) (u : E) :
    ‖actualContractionLaplaceLinear A hcont hbound c hc u‖≤‖u‖ := by
  exact (actualNormalizedLaplaceIntegral_norm_bound
    (fun s : ℝ => A s.toNNReal u) c ‖u‖ hc
    (((hcont u).comp continuous_real_toNNReal).aestronglyMeasurable)
    (ae_of_all _ fun s => hbound _ _)).2

/-- The actual normalized Bochner Laplace transform, as a continuous linear
operator on the original Hilbert space. -/
def actualContractionLaplaceOperator {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖) (c : ℝ) (hc : 0 < c) : E →L[ℝ] E :=
  (actualContractionLaplaceLinear A hcont hbound c hc).mkContinuous 1
    (fun u => by simpa only [one_mul] using
      actualContractionLaplaceLinear_norm_bound A hcont hbound c hc u)

end
end GinibrePoincare

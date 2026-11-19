/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupDynamics.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConservation
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDifferentiability

/-! # Actual full generator-domain diffusion evolution -/

@[expose] public section
open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Full generator-domain observables evolve differentiably at every positive time. -/
theorem ginibreFullEvolution_hasDerivAt (n : ℕ) (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hp : (u, v) ∈ (ginibreFullGenerator n hn).graph)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ginibreFullEvolution n hn (Real.toNNReal s) u)
      (ginibreFullEvolution n hn (Real.toNNReal t) v) t :=
  resolventGenerator_orbit_hasDerivAt _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) (ginibreFullComplexResolvent_spectrum n hn)
    (ginibreFullComplexResolvent_denseRange n hn) u v hp ht

/-- The full diffusion equation in integrated Hilbert-space form. -/
theorem ginibreFullEvolution_integral_equation (n : ℕ) (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hp : (u, v) ∈ (ginibreFullGenerator n hn).graph)
    {t : ℝ} (ht : 0 ≤ t) :
    ginibreFullEvolution n hn (Real.toNNReal t) u = u +
      ∫ s in (0 : ℝ)..t, ginibreFullEvolution n hn (Real.toNNReal s) v :=
  resolventGenerator_orbit_integral _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) (ginibreFullComplexResolvent_spectrum n hn)
    (ginibreFullComplexResolvent_denseRange n hn) u v hp ht

/-- Exact exponential action on every genuine full-generator eigenfunction. -/
theorem ginibreFullEvolution_eigenvector (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (rate : ℝ) (hRate : 0 ≤ rate) (u : ginibreSymmetricL2 n)
    (hu : (u, -(rate : ℂ) • u) ∈ (ginibreFullGenerator n hn).graph) :
    ginibreFullEvolution n hn t u = Real.exp (-rate * (t : ℝ)) • u :=
  resolventCfcEvolution_generator_eigenvector _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) t rate hRate u hu

end
end GinibrePoincare

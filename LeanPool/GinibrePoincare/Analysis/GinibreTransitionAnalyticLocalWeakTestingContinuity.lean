/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingContinuity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingApproximation

/-!
# Ginibre transition analytic local weak testing continuity

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_pairing_limit`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Compact weak equations extend to genuine Sobolev limits by continuity
of the actual weighted L² pairings. -/
theorem ginibreLocalWeak_pairing_limit {n : ℕ}
    (A C H : Lp ℝ 2 (ginibreMeasure n))
    (B : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (ℓ c : ℝ)
    (q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (v : Lp ℝ 2 (ginibreMeasure n))
    (G : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hq : Tendsto q atTop (𝓝 (v, G)))
    (heq : ∀ m, ℓ * inner ℝ A (q m).1 + c * inner ℝ B (q m).2 +
      c * inner ℝ H (q m).1 = inner ℝ C (q m).1) :
    ℓ*inner ℝ A v+c*inner ℝ B G+c*inner ℝ H v=inner ℝ C v := by
  have hA : Tendsto (fun m => inner ℝ A (q m).1) atTop (𝓝 (inner ℝ A v)) :=
    tendsto_const_nhds.inner (hq.fst_nhds)
  have hB : Tendsto (fun m => inner ℝ B (q m).2) atTop (𝓝 (inner ℝ B G)) :=
    tendsto_const_nhds.inner (hq.snd_nhds)
  have hH : Tendsto (fun m => inner ℝ H (q m).1) atTop (𝓝 (inner ℝ H v)) :=
    tendsto_const_nhds.inner (hq.fst_nhds)
  have hl : Tendsto (fun m => ℓ*inner ℝ A (q m).1+c*inner ℝ B (q m).2+
      c*inner ℝ H (q m).1) atTop
      (𝓝 (ℓ*inner ℝ A v+c*inner ℝ B G+c*inner ℝ H v)) := ((tendsto_const_nhds.mul hA).add
          (tendsto_const_nhds.mul hB)).add
    (tendsto_const_nhds.mul hH)
  have hr : Tendsto (fun m => inner ℝ C (q m).1) atTop (𝓝 (inner ℝ C v)) :=
    tendsto_const_nhds.inner (hq.fst_nhds)
  exact tendsto_nhds_unique (hl.congr' (Eventually.of_forall heq)) hr

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingLocalIntegrability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingLocalization

/-!
# Ginibre transition analytic local weak testing local integrability

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_compact_L2_coordinates_locallyIntegrable`.
-/

@[expose] public section

open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_compact_L2_locallyIntegrable
    {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (g : Configuration n → V)
    (hg : ∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
      MemLp g 2 (volume.restrict K)) :
    LocallyIntegrableOn g {z : Configuration n | CollisionFree z} volume := by
  apply (locallyIntegrableOn_iff (isOpen_collisionFree n).isLocallyClosed).mpr
  intro K hs hc
  let : IsFiniteMeasure (volume.restrict K : Measure (Configuration n)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hc.measure_lt_top⟩
  exact (hg K hc hs).integrable (by norm_num)

theorem ginibreLocalWeak_compact_L2_coordinates_locallyIntegrable
    {n : ℕ} (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hg : ∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
      MemLp g 2 (volume.restrict K)) :
    ∀ k : Fin n × Fin 2,
      LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume := by
  intro k
  let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
  exact P.locallyIntegrableOn_comp (ginibreLocalWeak_compact_L2_locallyIntegrable g hg)

end
end GinibrePoincare

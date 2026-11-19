/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalFreeInitial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalGlobalPathElement
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoffEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff

/-!
# Brownian orthogonal free initial

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreFreeInitialVersion_measurable`, `ginibreFreeInitialVersion_ae_eq`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- A collision-free version of an initial configuration, changing only collisions. -/
def ginibreFreeInitialVersion {n : ℕ} (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (z : Configuration n) : {z : Configuration n // CollisionFree z} := by
  classical
  exact if h : CollisionFree z then ⟨z, h⟩ else ⟨z₀, hz₀⟩

theorem ginibreFreeInitialVersion_measurable {n : ℕ}
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀) :
    Measurable (ginibreFreeInitialVersion z₀ hz₀) := by
  classical
  apply Measurable.subtype_mk
  have hm : Measurable (fun z : Configuration n => if CollisionFree z then z else z₀) :=
    measurable_id.ite (isOpen_collisionFree n).measurableSet
    (measurable_const (a := z₀))
  convert hm using 1
  funext z
  change (if h : CollisionFree z then (⟨z, h⟩ : {z : Configuration n // CollisionFree z})
    else ⟨z₀, hz₀⟩).val = (if CollisionFree z then z else z₀)
  by_cases hz : CollisionFree z
  · rw [dite_eq_left hz, ite_eq_left hz]
  · rw [dite_eq_right hz, ite_eq_right hz]

theorem ginibreFreeInitialVersion_ae_eq {n : ℕ} (hn : 0 < n)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀) :
    (fun z => (ginibreFreeInitialVersion z₀ hz₀ z).val) =ᵐ[ginibreMeasure n] id := by
  classical
  filter_upwards [ginibre_ae_collisionFree n hn] with z hz
  simp [ginibreFreeInitialVersion, hz]

end
end GinibrePoincare

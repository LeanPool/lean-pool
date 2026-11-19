/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalGlobalPathElement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalJointOUFunctional

/-!
# Brownian orthogonal global path element

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreDrivenGlobalPathElement_measurable`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The genuine joint event that a canonical driven solution is global. -/
theorem ginibreDriven_global_joint_measurableSet {n : ℕ} (hn : 0 < n) (α : ℝ) :
    MeasurableSet {p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n |
      ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤} := by
  have he : {p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n |
      ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤} =
      ⋂ k : ℕ, {p | ((k : ℝ≥0) : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α p.2.val p.1.val} := by
    ext p
    simp only [Set.mem_ofPred_eq, mem_iInter]
    constructor
    · intro h k
      rw [h]
      exact ENNReal.coe_lt_top
    · intro h
      apply top_unique
      rw [← ENNReal.iSup_natCast]
      apply iSup_le
      intro k
      exact (h k).le
  rw [he]
  exact MeasurableSet.iInter fun k => (ginibreDrivenMaximalLifetime_joint_alive_isOpen hn α
      k).measurableSet

/-- Canonical global paths bundled in the actual continuous-path space;
 nonglobal inputs use the constant initial path. -/
def ginibreDrivenGlobalPathElement {n : ℕ} (α : ℝ)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n) :
    C(ℝ, Configuration n) := by
  classical
  exact if h : ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤ then
    ⟨fun t => ginibreDrivenMaximalValue n α p.2.val p.1.val (Real.toNNReal t),
      (continuous_iff_continuousAt.mpr fun t =>
        ginibreDrivenMaximalValue_continuousAt_time t (by rw [h]; exact ENNReal.coe_lt_top)).comp
          continuous_real_toNNReal⟩
    else ContinuousMap.const ℝ p.1.val

/-- Genuine joint Borel measurability of the actual global canonical path element. -/
theorem ginibreDrivenGlobalPathElement_measurable {n : ℕ} (hn : 0 < n) (α : ℝ) :
    @Measurable _ C(ℝ, Configuration n) _ (borel _) (ginibreDrivenGlobalPathElement α) := by
  classical
  let : MeasurableSpace C(ℝ, Configuration n) := borel _
  let : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  have hm : Measurable (fun p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n
      =>
      if ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤ then
        ginibreDrivenMaximalValue n α p.2.val p.1.val (Real.toNNReal t) else p.1.val) :=
    (ginibreDrivenMaximalValue_joint_measurable hn α (Real.toNNReal t)).ite
    (ginibreDriven_global_joint_measurableSet hn α)
    (continuous_subtype_val.comp continuous_fst).measurable
  convert hm using 1
  funext p
  simp only [ginibreDrivenGlobalPathElement]
  split <;> rfl

end
end GinibrePoincare

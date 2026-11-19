/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianStateTransitionKernel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianTransitionKernel

/-!
# Ginibre Hamiltonian state transition kernel

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreCanonicalStateTransitionKernel_isMarkov`,
`ginibreCanonicalStateTransitionKernel_apply`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenMaximalValue_collisionFree {n : ℕ} (α : ℝ)
    (N : GinibreContinuousNoise n) (z : {z : Configuration n // CollisionFree z}) (t : ℝ≥0) :
    CollisionFree (ginibreDrivenMaximalValue n α N.val z.val t) := by
  by_cases ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N.val z.val
  · have hd : (t : ℝ) ∈ ginibreDrivenMaximalDomain n α N.val z.val :=
      ⟨t.property, by simpa using ht⟩
    simpa only [ginibreDrivenMaximalPath, Real.toNNReal_coe] using
      (ginibreDrivenMaximalPath_equation hd).1
  · rw [show ginibreDrivenMaximalValue n α N.val z.val t=z.val from dite_eq_right ht]
    exact z.property

/-- The maximal driven Ginibre value at time `t` from the collision-free start `p.1` with noise
`p.2`, as a collision-free configuration. -/
def ginibreCanonicalStateValue {n : ℕ} (α : ℝ) (t : ℝ≥0)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n) :
    {z : Configuration n // CollisionFree z} :=
  ⟨ginibreDrivenMaximalValue n α p.2.val p.1.val t,
    ginibreDrivenMaximalValue_collisionFree α p.2 p.1 t⟩

theorem ginibreCanonicalStateValue_measurable {n : ℕ} (hn : 0 < n) (α : ℝ) (t : ℝ≥0) :
    Measurable (ginibreCanonicalStateValue (n := n) α t) :=
  (ginibreDrivenMaximalValue_joint_measurable hn α t).subtype_mk

/-- The time-`t` transition kernel on collision-free configurations: the image of
`δ z ⊗ μ` under `ginibreCanonicalStateValue α t`, for a noise law `μ`. -/
def ginibreCanonicalStateTransitionKernel {n : ℕ} (α : ℝ) (t : ℝ≥0)
    (μ : Measure (GinibreContinuousNoise n)) :
    Kernel {z : Configuration n // CollisionFree z} {z : Configuration n // CollisionFree z} :=
  ((Kernel.id : Kernel {z : Configuration n // CollisionFree z} _) |>.prod
    (Kernel.const {z : Configuration n // CollisionFree z} μ)).map (ginibreCanonicalStateValue α t)

theorem ginibreCanonicalStateTransitionKernel_isMarkov {n : ℕ} (hn : 0 < n)
    (α : ℝ) (t : ℝ≥0) (μ : Measure (GinibreContinuousNoise n)) [IsProbabilityMeasure μ] :
    IsMarkovKernel (ginibreCanonicalStateTransitionKernel (n := n) α t μ) := by
  unfold ginibreCanonicalStateTransitionKernel
  exact Kernel.IsMarkovKernel.map _ (ginibreCanonicalStateValue_measurable hn α t)

theorem ginibreCanonicalStateTransitionKernel_apply {n : ℕ} (hn : 0 < n) (α : ℝ)
    (t : ℝ≥0) (μ : Measure (GinibreContinuousNoise n)) [IsProbabilityMeasure μ]
    (z : {z : Configuration n // CollisionFree z}) :
    ginibreCanonicalStateTransitionKernel α t μ z =
      μ.map (fun N => ginibreCanonicalStateValue α t (z, N)) := by
  unfold ginibreCanonicalStateTransitionKernel
  rw [Kernel.map_apply _ (ginibreCanonicalStateValue_measurable hn α t),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (ginibreCanonicalStateValue_measurable hn α t) measurable_prodMk_left]
  rfl

end
end GinibrePoincare

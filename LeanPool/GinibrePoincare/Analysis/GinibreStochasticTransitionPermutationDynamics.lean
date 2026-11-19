/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionPermutationDynamics.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalLifetime
public import LeanPool.GinibrePoincare.Analysis.GinibrePermutationGradient
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Ginibre stochastic transition permutation dynamics

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreDrivenSegment_permute`.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The relabeling of particles by the permutation `σ`, as a continuous linear map on
configurations. -/
def ginibreParticlePermutationCLM {n : ℕ} (σ : ParticlePermutation n) :
    Configuration n →L[ℝ] Configuration n :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) σ.symm).toContinuousLinearMap

theorem ginibreParticlePermutationCLM_apply {n : ℕ} (σ : ParticlePermutation n) (z : Configuration
    n) :
    ginibreParticlePermutationCLM σ z=permute σ z := by
  funext i
  simp [ginibreParticlePermutationCLM, ContinuousLinearEquiv.piCongrLeft, 
    Equiv.piCongrLeft_apply, permute]

theorem ginibreCoulombInteraction_permute {n : ℕ} (σ : ParticlePermutation n) (z : Configuration n)
    :
    ginibreCoulombInteraction n (permute σ z)=permute σ (ginibreCoulombInteraction n z) := by
  funext i
  exact Equiv.sum_comp σ (fun k => (z (σ i)-z k)/(Complex.normSq (z (σ i)-z k) : ℂ))

theorem ginibreLangevinDrift_permute {n : ℕ} (σ : ParticlePermutation n) (α : ℝ) (z : Configuration
    n) :
    ginibreLangevinDrift n α (permute σ z)=permute σ (ginibreLangevinDrift n α z) := by
  rw [show ginibreLangevinDrift n α (permute σ z)=
    fun i => -(2*α/(n : ℝ)) • permute σ z i+(2*α/(n : ℝ)^2) •
      ginibreCoulombInteraction n (permute σ z) i from rfl, ginibreCoulombInteraction_permute]
  rfl

theorem ginibreCollisionFree_permute {n : ℕ} (σ : ParticlePermutation n) {z : Configuration n}
    (hz : CollisionFree z) : CollisionFree (permute σ z) := by
  intro i j hij
  exact σ.injective (hz hij)

theorem ginibreDrivenSegment_permute {n : ℕ} {α : ℝ} {N X : ℝ → Configuration n}
    {z : Configuration n} {T : ℝ≥0} (hX : GinibreDrivenSegment n α N z T X)
    (σ : ParticlePermutation n) :
    GinibreDrivenSegment n α (fun s => permute σ (N s)) (permute σ z) T
      (fun s => permute σ (X s)) := by
  let P := ginibreParticlePermutationCLM σ
  have hP : ∀ w, P w=permute σ w := ginibreParticlePermutationCLM_apply σ
  refine ⟨?_,?_,?_⟩
  · simpa only [Function.comp_def, hP] using P.continuous.comp_continuousOn hX.1
  · change permute σ (X 0)=permute σ z
    rw [hX.2.1]
  · intro t ht
    obtain ⟨hcf, hInt, hEq⟩ := hX.2.2 t ht
    refine ⟨ginibreCollisionFree_permute σ hcf,?_,?_⟩
    · have hi : IntervalIntegrable (fun s => P (ginibreLangevinDrift n α (X s))) volume 0 t :=
        ⟨P.integrable_comp hInt.1, P.integrable_comp hInt.2⟩
      simpa only [hP, ginibreLangevinDrift_permute] using hi
    · have he := congrArg P hEq
      rw [map_add, map_add] at he
      rw [← P.intervalIntegral_comp_comm hInt] at he
      simpa only [hP, ginibreLangevinDrift_permute] using he

end
end GinibrePoincare

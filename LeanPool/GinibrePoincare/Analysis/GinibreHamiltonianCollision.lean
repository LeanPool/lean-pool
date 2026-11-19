/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianCollision.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonian

/-! Genuine divergence of the Hamiltonian along collision-free paths to a collision. -/

@[expose] public section
open scoped Topology
open Filter
namespace GinibrePoincare
noncomputable section

theorem ginibreHamiltonian_tendsto_collision {n : ℕ} {ι : Type*}
    {l : Filter ι} {Z : ι → Configuration n} {z : Configuration n}
    (hZ : Tendsto Z l (𝓝 z)) (hz : z ∈ collisionSet n)
    (hfree : ∀ᶠ t in l, CollisionFree (Z t)) :
    Tendsto (fun t => ginibreHamiltonian n (Z t)) l atTop := by
  have hv : Tendsto (fun t => vandermondeWeight (Z t)) l (𝓝 (0 : ℝ)) := by
    have h : Tendsto (vandermondeWeight : Configuration n → ℝ) (𝓝 z)
        (𝓝 (vandermondeWeight z)) := (contDiff_vandermondeWeight n).continuous.continuousAt
    rw [(vandermondeWeight_eq_zero_iff z).mpr hz] at h
    exact h.comp hZ
  have hp : ∀ᶠ t in l, vandermondeWeight (Z t) ∈ Set.Ioi (0 : ℝ) :=
    hfree.mono (fun t ht => vandermondeWeight_pos_of_collisionFree (Z t) ht)
  have hl : Tendsto (fun t => Real.log (vandermondeWeight (Z t))) l atBot :=
    Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hv, hp⟩)
  have hr : Tendsto (fun t => (n : ℝ) * configurationNormSq (Z t)) l
      (𝓝 ((n : ℝ) * configurationNormSq z)) :=
    tendsto_const_nhds.mul
      ((contDiff_configurationNormSq (n := n)).continuous.continuousAt.tendsto.comp hZ)
  convert hr.add_atTop (tendsto_neg_atBot_atTop.comp hl) using 1
  funext t
  exact sub_eq_add_neg _ _

end
end GinibrePoincare

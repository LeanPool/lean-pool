/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianJointStability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCompactDrift

/-!
# Ginibre Hamiltonian joint stability

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.
-/

@[expose] public section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
theorem ginibreDrivenSegment_joint_stability_in_extension {n : ℕ} {α : ℝ}
    {N M : ℝ → Configuration n} {z w : Configuration n} {T : ℝ≥0} {X Y : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (hY : GinibreDrivenSegment n α M w T Y)
    {K : Set (Configuration n)} {L : ℝ≥0} {g : Configuration n → Configuration n}
    (hg : LipschitzWith L g) (he : EqOn g (ginibreLangevinDrift n α) K)
    (hXK : ∀ t ∈ Icc 0 (T : ℝ), X t ∈ K) (hYK : ∀ t ∈ Icc 0 (T : ℝ), Y t ∈ K)
    {δ : ℝ} (hδ : 0 ≤ δ) (hnoise : ∀ t ∈ Icc 0 (T : ℝ), ‖z - w‖ + ‖N t - M t‖ ≤ δ) :
    ∀ t ∈ Icc 0 (T : ℝ), ‖X t-Y t‖ ≤ δ*Real.exp ((L : ℝ)*(T : ℝ)) := by
  have hXg (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : X t = z+N t+∫ u in (0 : ℝ)..t, g (X u) := by
    rw [(hX.2.2 t ht).2.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact (he (hXK u ⟨hu.1, hu.2.trans ht.2⟩)).symm
  have hYg (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : Y t = z+(M t+(w-z))+∫ u in (0 : ℝ)..t, g (Y u) := by
    have hh := (hY.2.2 t ht).2.2
    have heI : (∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (Y u)) = ∫ u in (0 : ℝ)..t, g (Y u) :=
        by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      exact (he (hYK u ⟨hu.1, hu.2.trans ht.2⟩)).symm
    rw [heI] at hh
    rw [hh]
    abel
  have hnm (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : ‖N t-(M t+(w-z))‖ ≤ δ := by
    calc
      ‖N t-(M t+(w-z))‖ = ‖(z-w)+(N t-M t)‖ := by congr 1; abel
      _ ≤ ‖z-w‖+‖N t-M t‖ := norm_add_le _ _
      _ ≤ δ := hnoise t ht
  exact drivenVolterra_lipschitz_stability_on g L hg z N (fun t => M t+(w-z)) X Y T δ T.property hδ
    hX.1 hY.1 hXg hYg hnm

end
end GinibrePoincare

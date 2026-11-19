/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianCompactDrift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalPast
public import Mathlib.Topology.MetricSpace.Thickening

/-! Actual compact tube drift extensions and quantitative noise stability. -/

@[expose] public section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreLangevinDrift_compact_extension (n : ℕ) (α : ℝ)
    (K : Set (Configuration n)) (hK : IsCompact K)
    (hcf : ∀ z ∈ K, CollisionFree z) :
    ∃ L : ℝ≥0, ∃ g : Configuration n → Configuration n,
      LipschitzWith L g ∧ EqOn g (ginibreLangevinDrift n α) K := by
  obtain ⟨L, hb⟩ := ginibreLangevinDrift_lipschitzOn_compact n α K hK hcf
  obtain ⟨g, hg, heq⟩ := hb.extend_finite_dimension
  exact ⟨_, g, hg, fun z hz => (heq hz).symm⟩

theorem ginibreLangevinDrift_compact_tube (n : ℕ) (α : ℝ)
    (K : Set (Configuration n)) (hK : IsCompact K)
    (hcf : ∀ z ∈ K, CollisionFree z) :
    ∃ r > (0 : ℝ), ∃ L : ℝ≥0, ∃ g : Configuration n → Configuration n,
      IsCompact (cthickening r K) ∧ (∀ z ∈ cthickening r K, CollisionFree z) ∧
      LipschitzWith L g ∧ EqOn g (ginibreLangevinDrift n α) (cthickening r K) := by
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_collisionFree n) hcf
  obtain ⟨L, g, hg, he⟩ := ginibreLangevinDrift_compact_extension n α _ hK.cthickening hsub
  exact ⟨r, hr, L, g, hK.cthickening, hsub, hg, he⟩

theorem ginibreDrivenSegment_noise_stability_in_extension {n : ℕ} {α : ℝ}
    {N M : ℝ → Configuration n} {z : Configuration n} {T : ℝ≥0} {X Y : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (hY : GinibreDrivenSegment n α M z T Y)
    {K : Set (Configuration n)} {L : ℝ≥0} {g : Configuration n → Configuration n}
    (hg : LipschitzWith L g) (he : EqOn g (ginibreLangevinDrift n α) K)
    (hXK : ∀ t ∈ Icc 0 (T : ℝ), X t ∈ K) (hYK : ∀ t ∈ Icc 0 (T : ℝ), Y t ∈ K)
    {δ : ℝ} (hδ : 0 ≤ δ) (hnoise : ∀ t ∈ Icc 0 (T : ℝ), ‖N t - M t‖ ≤ δ) :
    ∀ t ∈ Icc 0 (T : ℝ), ‖X t-Y t‖ ≤ δ*Real.exp ((L : ℝ)*(T : ℝ)) := by
  have hXg (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : X t = z+N t+∫ u in (0 : ℝ)..t, g (X u) := by
    rw [(hX.2.2 t ht).2.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact (he (hXK u ⟨hu.1, hu.2.trans ht.2⟩)).symm
  have hYg (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : Y t = z+M t+∫ u in (0 : ℝ)..t, g (Y u) := by
    rw [(hY.2.2 t ht).2.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact (he (hYK u ⟨hu.1, hu.2.trans ht.2⟩)).symm
  exact drivenVolterra_lipschitz_stability_on g L hg z N M X Y T δ T.property hδ
    hX.1 hY.1 hXg hYg hnoise

end
end GinibrePoincare

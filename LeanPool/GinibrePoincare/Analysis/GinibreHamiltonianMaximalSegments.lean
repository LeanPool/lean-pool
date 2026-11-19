/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianMaximalSegments.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianPathUniqueness

/-! Actual finite solution segments and their canonical maximal lifespan. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- A genuine solution of the original additive-noise equation on a closed interval. -/
def GinibreDrivenSegment (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) (T : ℝ≥0) (X : ℝ → Configuration n) : Prop :=
  ContinuousOn X (Icc 0 (T : ℝ)) ∧ X 0 = z ∧
    ∀ t ∈ Icc 0 (T : ℝ), CollisionFree (X t) ∧
      IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t ∧
      X t = z+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u)

/-- The horizons `T` on which the noise-driven Ginibre Langevin equation started at `z` admits a
solution segment. -/
def ginibreDrivenHorizons (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) : Set ℝ≥0 :=
  {T | ∃ X, GinibreDrivenSegment n α N z T X}

/-- The maximal lifetime of the noise-driven Ginibre Langevin equation started at `z`: the
supremum of the horizons admitting a solution segment. -/
def ginibreDrivenMaximalLifetime (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) : ℝ≥0∞ :=
  ⨆ T : ginibreDrivenHorizons n α N z, (T.val : ℝ≥0∞)

theorem GinibreDrivenSegment.eqOn {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} {T U : ℝ≥0} {X Y : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (hY : GinibreDrivenSegment n α N z U Y) :
    EqOn X Y (Icc 0 (min T U : ℝ≥0)) := by
  have hTX : Icc (0 : ℝ) (min T U : ℝ≥0) ⊆ Icc (0 : ℝ) (T : ℝ) :=
    Icc_subset_Icc_right (by exact_mod_cast min_le_left T U)
  have hTY : Icc (0 : ℝ) (min T U : ℝ≥0) ⊆ Icc (0 : ℝ) (U : ℝ) :=
    Icc_subset_Icc_right (by exact_mod_cast min_le_right T U)
  exact ginibreDrivenPath_finite_interval_unique n α z N X Y _ (min T U).property
    (hX.1.mono hTX) (hY.1.mono hTY) (fun t ht => (hX.2.2 t (hTX ht)).1)
    (fun t ht => (hY.2.2 t (hTY ht)).1) (fun t ht => (hX.2.2 t (hTX ht)).2.2)
    (fun t ht => (hY.2.2 t (hTY ht)).2.2)

theorem ginibreDrivenMaximalLifetime_pos (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (hN : Continuous N) (hN0 : N 0 = 0) (z : Configuration n) (hz : CollisionFree z) :
    0 < ginibreDrivenMaximalLifetime n α N z := by
  obtain ⟨T, hT, X, hX⟩ := ginibreDrivenPath_continuous_noise_local_exists n α z hz N hN hN0
  let t : ℝ≥0 := ⟨T, hT.le⟩
  have ht : t ∈ ginibreDrivenHorizons n α N z := ⟨X, hX⟩
  have hle : (t : ℝ≥0∞) ≤ ginibreDrivenMaximalLifetime n α N z := le_iSup_of_le ⟨t, ht⟩ le_rfl
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr (by exact_mod_cast hT)) hle

theorem ginibreDrivenMaximalLifetime_exists_horizon {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} (t : ℝ≥0) (ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    ∃ T ∈ ginibreDrivenHorizons n α N z, t < T := by
  obtain ⟨T, hT⟩ := lt_iSup_iff.mp ht
  exact ⟨T.val, T.property, ENNReal.coe_lt_coe.mp hT⟩

end
end GinibrePoincare

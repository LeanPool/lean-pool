/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitMartingale
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual countable-range upper approximations of continuous-time stopping times. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The upward rounding `⌈(m + 1) t⌉ / (m + 1)` of a time `t` to the grid `ℕ / (m + 1)`. -/
def stoppingUpperGrid (m : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (Nat.ceil (((m+1 : ℕ) : ℝ≥0)*t) : ℝ≥0)/((m+1 : ℕ) : ℝ≥0)

theorem stoppingUpperGrid_le_iff (m : ℕ) (t u : ℝ≥0) :
    stoppingUpperGrid m t ≤ u ↔
      t ≤ (Nat.floor (((m+1 : ℕ) : ℝ≥0)*u) : ℝ≥0)/((m+1 : ℕ) : ℝ≥0) := by
  have hm : 0 < ((m+1 : ℕ) : ℝ≥0) := by positivity
  unfold stoppingUpperGrid
  rw [div_le_iff₀ hm, le_div_iff₀ hm]
  rw [← Nat.le_floor_iff (by positivity), Nat.ceil_le]
  simp only [mul_comm]

theorem stoppingUpperGrid_isStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (m : ℕ) :
    IsStoppingTime ℱ (fun ω => (stoppingUpperGrid m (τ ω) : WithTop ℝ≥0)) := by
  intro u
  have hm : 0 < ((m+1 : ℕ) : ℝ≥0) := by positivity
  let v : ℝ≥0 := (Nat.floor (((m+1 : ℕ) : ℝ≥0)*u) : ℝ≥0)/((m+1 : ℕ) : ℝ≥0)
  have hv : v ≤ u := by
    apply (div_le_iff₀ hm).mpr
    exact (Nat.floor_le (by positivity)).trans_eq (mul_comm _ _)
  have hs := ℱ.mono hv _ (hτ v)
  convert hs using 1
  ext ω
  simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, stoppingUpperGrid_le_iff]
  rfl

theorem stoppingUpperGrid_countable_range (m : ℕ) {Ω : Type*} (τ : Ω → ℝ≥0) :
    (Set.range (fun ω => (stoppingUpperGrid m (τ ω) : WithTop ℝ≥0))).Countable := by
  apply (Set.countable_range (fun k : ℕ =>
    (((k : ℝ≥0)/((m+1 : ℕ) : ℝ≥0)) : WithTop ℝ≥0))).mono
  rintro x ⟨ω, rfl⟩
  exact ⟨Nat.ceil (((m+1 : ℕ) : ℝ≥0)*τ ω), rfl⟩

theorem stoppingUpperGrid_tendsto (t : ℝ≥0) :
    Tendsto (fun m : ℕ => stoppingUpperGrid m t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  have hm : Tendsto (fun m : ℕ => ((m+1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_atTop_mono (fun m => by exact_mod_cast (Nat.le_succ m))
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
  have ht := (tendsto_nat_ceil_mul_div_atTop (a := (t : ℝ)) t.property).comp hm
  convert ht using 1
  funext m
  simp only [stoppingUpperGrid, NNReal.coe_div, NNReal.coe_natCast]
  congr 1
  congr 1
  change Nat.ceil (((m+1 : ℕ) : ℝ)*(t : ℝ)) = Nat.ceil ((t : ℝ)*((m+1 : ℕ) : ℝ))
  rw [mul_comm]

end
end GinibrePoincare

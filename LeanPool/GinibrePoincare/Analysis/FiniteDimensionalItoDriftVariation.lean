/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoDriftVariation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoPathMesh

/-!
# Finite dimensional Ito drift variation

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoUniformDriftIncrement_eq_volterra_difference`,
`itoUniformDriftIncrement_variation_le`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral of the drift `b` over the `i`-th cell of the uniform partition of `[0, T]` into
`n + 1` steps. -/
def itoUniformDriftIncrement (b : ℝ → E) (T : ℝ≥0) (n : ℕ) (i : Fin (n + 1)) : E :=
  ∫ s in (ginibreUniformBrownianTime T n i : ℝ)..
    (ginibreUniformBrownianTime T n (i.val+1) : ℝ), b s

/-- Actual differences of the Volterra integral are exactly the partition drift increments. -/
theorem itoUniformDriftIncrement_eq_volterra_difference (b : ℝ → E) (T : ℝ≥0)
    (hb : ContinuousOn b (Set.Icc (0 : ℝ) T)) (n : ℕ) (i : Fin (n + 1)) :
    (∫ s in (0 : ℝ)..(ginibreUniformBrownianTime T n (i.val+1) : ℝ), b s) -
      (∫ s in (0 : ℝ)..(ginibreUniformBrownianTime T n i : ℝ), b s) =
      itoUniformDriftIncrement b T n i := by
  have ht (j : ℕ) (hj : j ≤ n+1) :
      IntervalIntegrable b volume 0 (ginibreUniformBrownianTime T n j : ℝ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (NNReal.coe_nonneg _)
    apply hb.mono
    intro s hs
    exact ⟨hs.1, hs.2.trans (ginibreUniformBrownianTime_le_end T n j hj)⟩
  exact intervalIntegral.integral_interval_sub_left
    (ht _ (Nat.succ_le_of_lt i.is_lt)) (ht _ (Nat.le_of_lt i.is_lt))

/-- The actual Volterra drift increment is bounded by the time step times its drift bound. -/
theorem itoUniformDriftIncrement_norm_le (b : ℝ → E) (T : ℝ≥0) (n : ℕ)
    (M : ℝ) (hb : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖b s‖ ≤ M) (i : Fin (n + 1)) :
    ‖itoUniformDriftIncrement b T n i‖ ≤ M * ((T : ℝ)/((n : ℝ)+1)) := by
  have hmono : (ginibreUniformBrownianTime T n i : ℝ) ≤
      (ginibreUniformBrownianTime T n (i.val+1) : ℝ) :=
    ginibreUniformBrownianTime_mono T n (Nat.le_succ i.val)
  have hl : (0 : ℝ) ≤ (ginibreUniformBrownianTime T n i : ℝ) := NNReal.coe_nonneg _
  have hu : (ginibreUniformBrownianTime T n (i.val+1) : ℝ) ≤ T :=
    ginibreUniformBrownianTime_le_end T n _ (Nat.succ_le_of_lt i.is_lt)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s (hs : s ∈ Set.uIoc (ginibreUniformBrownianTime T n i : ℝ)
      (ginibreUniformBrownianTime T n (i.val+1) : ℝ)) => hb s (by
        rw [Set.uIoc_of_le hmono] at hs
        exact ⟨hl.trans hs.1.le, hs.2.trans hu⟩))
  unfold itoUniformDriftIncrement
  convert hh using 1
  rw [abs_of_nonneg (sub_nonneg.mpr hmono), ginibreUniformBrownianTime_coe,
    ginibreUniformBrownianTime_coe, ginibreUniformTime_increment]

/-- The total actual drift variation on a uniform partition stays bounded by M T. -/
theorem itoUniformDriftIncrement_variation_le (b : ℝ → E) (T : ℝ≥0) (n : ℕ)
    (M : ℝ) (hb : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖b s‖ ≤ M) :
    ∑ i : Fin (n+1), ‖itoUniformDriftIncrement b T n i‖ ≤ M * (T : ℝ) := by
  calc
    _ ≤ ∑ i : Fin (n+1), M*((T : ℝ)/((n : ℝ)+1)) :=
      Finset.sum_le_sum (fun i hi => itoUniformDriftIncrement_norm_le b T n M hb i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      have hn : (n : ℝ)+1 ≠ 0 := by positivity
      field_simp

end
end GinibrePoincare

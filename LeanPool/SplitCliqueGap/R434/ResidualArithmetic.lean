/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! # Arithmetic estimates for residual clique partitions -/

@[expose] public section

namespace GapExtremal.R434

/-- Three times the slack of a piece with v vertices and e tripartite edges. -/
def slack3 (v e : ℕ) : ℤ := 3 * (v * (v - 1) / 2 + 1 : ℕ) - 4 * (e : ℤ)

theorem small_slack_check :
    ∀ v : Fin 9, ∀ e : Fin 22, 2 ≤ v.val → 3 * e.val ≤ v.val ^ 2 →
      0 ≤ slack3 v.val e.val ∧
      (slack3 v.val e.val = 0 → (v.val = 3 ∧ e.val = 3) ∨ (v.val = 6 ∧ e.val = 12)) ∧
      (slack3 v.val e.val ≠ 0 → (e.val : ℤ) ≤ 9 * slack3 v.val e.val) := by
  decide +kernel

theorem large_tripartite_slack (v e : ℝ) (hv : 9 ≤ v) (he : 0 ≤ e)
    (h : 3 * e ≤ v ^ 2) :
    0 < v * (v - 1) / 2 + 1 - 4 * e / 3 ∧
      e / 27 ≤ v * (v - 1) / 2 + 1 - 4 * e / 3 := by
  have hpos : 0 ≤ (v - 9) * (7 * v - 18) := mul_nonneg (by linarith) (by linarith)
  have hb : e / 27 ≤ v * (v - 1) / 2 + 1 - 4 * e / 3 := by nlinarith
  refine ⟨?_, hb⟩
  rcases he.eq_or_lt with h0 | h0
  · have hv' : 0 ≤ v * (v - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  · linarith

/-- The energy and incidence budgets imply the signed defect bound. -/
theorem signed_gap_of_budgets (τ x z R δ loss : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hcover : τ ≤ x + 3 * z) (hcharge : δ * z ≤ (2 * R / 3) * x)
    (hslack : x ≤ 27 * loss) :
    τ / (27 * (1 + 2 * R / δ)) ≤ loss := by
  have hcoef : 0 ≤ 2 * R / δ := by positivity
  have hd : 0 < 27 * (1 + 2 * R / δ) := by positivity
  have hz : 3 * z ≤ (2 * R / δ) * x := by
    apply (mul_le_mul_iff_left₀ hδ).mp
    have hcancel : (2 * R / δ * x) * δ = 2 * R * x := by
      rw [mul_right_comm, div_mul_cancel₀ _ hδ.ne']
    rw [hcancel]
    nlinarith only [hcharge]
  apply (div_le_iff₀ hd).mpr
  calc
    τ ≤ x + 3 * z := hcover
    _ ≤ (1 + 2 * R / δ) * x := by linarith only [hz, show
      (1 + 2 * R / δ) * x = x + (2 * R / δ) * x by ring]
    _ ≤ (1 + 2 * R / δ) * (27 * loss) :=
      mul_le_mul_of_nonneg_left hslack (by linarith)
    _ = loss * (27 * (1 + 2 * R / δ)) := by ring

theorem signed_price_bounds (m M f : ℝ) (hlo : m ≤ f) (hhi : f ≤ M) :
    -(2 * (M - m) / 3) ≤ f - (m + 2 * M) / 3 ∧
    -(2 * (M - m) / 3) ≤ -2 * (f - (m + 2 * M) / 3) := by
  constructor <;> linarith

end GapExtremal.R434

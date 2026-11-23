/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.BellmanDrift
public import LeanPool.Egyptian.BellmanSplit

/-! Real rewards for finite terminal decompositions. -/

@[expose] public section

namespace Egyptian.Control

/-- The real-valued payoff for a terminal denominator discounted by the control length. -/
noncomputable def score (xs : List ℕ) (T : ℕ) : ℝ :=
  Payoff.value T / (2 : ℝ)^xs.length

theorem score_as_mul (xs : List ℕ) (T : ℕ) :
    score xs T = (1/2 : ℝ)^xs.length * Payoff.value T := by
  simp [score, div_eq_mul_inv, mul_comm]

theorem score_append (xs ys : List ℕ) (T : ℕ) :
    score (xs ++ ys) T = score ys T / (2:ℝ)^xs.length := by
  simp [score, pow_add, div_div, mul_comm]

/-- A terminal list whose score dominates every terminal list from the same state. -/
def Wins (σ : Convention) (s : State) (xs : List ℕ) (T : ℕ) : Prop :=
  Terminal σ s xs T ∧ ∀ ys U, Terminal σ s ys U → score ys U ≤ score xs T

theorem wins_suffix {σ s b ys T} (h : Wins σ s (b ++ ys) T) :
    Wins σ (finish s b) ys T := by
  obtain ⟨hc, ht⟩ := (terminal_append ..).mp h.1
  refine ⟨ht, ?_⟩
  intro zs U hzs
  have h' := h.2 (b ++ zs) U ((terminal_append ..).2 ⟨hc,hzs⟩)
  simpa only [score_append, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ b.length)]
    using h'

theorem wins_value {σ s xs T} (h : Wins σ s xs T) :
    value σ (fun T => Payoff.value T) s = (score xs T : EReal) := by
  apply le_antisymm
  · refine iSup_le fun ys => iSup_le fun U => iSup_le fun ht => ?_
    simpa only [reward, ← score_as_mul] using EReal.coe_le_coe (h.2 ys U ht)
  · simpa only [reward, ← score_as_mul] using reward_le_value (H := fun T => Payoff.value T) h.1

end Egyptian.Control

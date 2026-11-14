/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Pack.Scaled

/-!
# From the block inequality to the bound for fractional packings

`AaronsonAmbainis.packingBound_of_block : BlockInequality → PackingBound`: the packing bound
(Lemma 6.5 of the paper) follows from the block inequality (Lemma 6.4). This file contains the
limit `M → ∞` (`Pack.le_of_scaled`); the inequality for a fixed `M` is `Pack.scaled_bound` in
`Pack/Scaled.lean`.
-/

@[expose] public section

namespace AaronsonAmbainis.Pack

/-- The limit step: if `M² L ≤ d² (π M + 2)² + C` for every natural `M ≥ 1`, then
`L ≤ π² d²`. -/
theorem le_of_scaled (L C : ℝ) (d : ℕ)
    (key : ∀ M : ℕ, 0 < M → (M : ℝ) ^ 2 * L ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + C) :
    L ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 := by
  by_contra hcon
  have hεpos : 0 < L - Real.pi ^ 2 * (d : ℝ) ^ 2 := by linarith [not_le.mp hcon]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  -- `C ≥ 0` is not assumed; `|C|` is used instead
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * (d : ℝ) ^ 2 * Real.pi + 4 * (d : ℝ) ^ 2 + |C| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 * Real.pi :=
      mul_nonneg (mul_nonneg (by norm_num) hd2) hpi.le
    have h2 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 := mul_nonneg (by norm_num) hd2
    linarith [abs_nonneg C]
  obtain ⟨M, hMgt⟩ := exists_nat_gt (K / (L - Real.pi ^ 2 * (d : ℝ) ^ 2))
  have hMr : (0 : ℝ) < (M : ℝ) := lt_of_le_of_lt (div_nonneg hK0 hεpos.le) hMgt
  have hMpos : 0 < M := Nat.cast_pos.mp hMr
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hMpos
  have h1 := key M hMpos
  -- `M² ε ≤ 4 d² π M + 4 d² + C`
  have h2 : (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)
      ≤ 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C := by
    have hexp : (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + C
        = (M : ℝ) ^ 2 * (Real.pi ^ 2 * (d : ℝ) ^ 2)
          + (4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C) := by ring
    rw [hexp] at h1
    calc (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)
        = (M : ℝ) ^ 2 * L - (M : ℝ) ^ 2 * (Real.pi ^ 2 * (d : ℝ) ^ 2) := by ring
      _ ≤ 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C := by linarith
  -- `4 d² π M + 4 d² + C ≤ K M` because `M ≥ 1`
  have h3 : 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C ≤ K * (M : ℝ) := by
    have ha : 4 * (d : ℝ) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (M : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg (by norm_num) hd2) hM1
    have hb : C ≤ |C| * (M : ℝ) :=
      (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hM1)
    have hc : K * (M : ℝ) = 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 * (M : ℝ)
        + |C| * (M : ℝ) := by rw [hK]; ring
    rw [hc]; linarith
  -- divide by `M`
  have h4 : (M : ℝ) * ((M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)) ≤ (M : ℝ) * K := by
    calc (M : ℝ) * ((M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2))
        = (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) := by ring
      _ ≤ K * (M : ℝ) := h2.trans h3
      _ = (M : ℝ) * K := mul_comm _ _
  have h5 : (M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) ≤ K := le_of_mul_le_mul_left h4 hMr
  have h6 : K < (M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) := (div_lt_iff₀ hεpos).mp hMgt
  exact absurd h5 (not_le.mpr h6)

end AaronsonAmbainis.Pack

namespace AaronsonAmbainis

/-- The bound for fractional packings follows from the block inequality. -/
theorem packingBound_of_block : BlockInequality → PackingBound := by
  intro hB ι _ _ d f hf hd x κ hκ hpack
  exact Pack.le_of_scaled _ (∑ S, |f x - f (flipSet x S)|) d
    (fun M hM => Pack.scaled_bound hB ι d f hf hd x κ hκ hpack M hM)

end AaronsonAmbainis

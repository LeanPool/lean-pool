/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Nat.Even

/-!
# The constants in the main proof of Graph Minors XVI

Section 9 chooses the battlefield size before clearing the discs. The bounds
below check that this choice leaves enough order for every clearing and for
the later freeness argument. They also check that all the annuli used near
the end of the proof exist.
-/

public section
namespace GraphMinor.GM16

private theorem hairs_le_section9_kappa (δ φ : ℕ) (hφ : 3 ≤ φ) :
    δ ≤ δ ^ 2 * φ ^ 2 / 2 + 1 := by
  by_cases hδ : δ = 0
  · subst δ
    simp
  have hδpos : 1 ≤ δ := by omega
  have hsquare : δ ≤ δ ^ 2 := by nlinarith
  have hφsquare : 2 ≤ φ ^ 2 := by nlinarith
  have hprod : 2 * δ ≤ δ ^ 2 * φ ^ 2 := by
    calc
      2 * δ = δ * 2 := Nat.mul_comm _ _
      _ ≤ δ * φ ^ 2 := Nat.mul_le_mul_left δ hφsquare
      _ ≤ δ ^ 2 * φ ^ 2 := Nat.mul_le_mul_right _ hsquare
  omega

private theorem section9_order_bounds (δ β : ℕ) (hδβ : δ ≤ β) :
    (12 * β + 14) * δ < 12 * (δ + 3) * (β + 1) ∧
    16 * β + 17 ≤ 12 * (δ + 3) * (β + 1) ∧
    2 * β + 5 * (3 * β + 3) + 2 <
      12 * (δ + 3) * (β + 1) - (12 * β + 14) * (δ - 1) - 1 := by
  have hδ : δ - 1 ≤ δ := Nat.sub_le _ _
  have hmul : (12 * β + 14) * (δ - 1) ≤ (12 * β + 14) * δ :=
    Nat.mul_le_mul_left _ hδ
  by_cases hz : δ = 0
  · subst δ
    simp only [Nat.zero_add, Nat.sub_zero, Nat.mul_zero, Nat.zero_sub]
    constructor
    · nlinarith
    constructor
    · nlinarith
    · omega
  · have hstep : δ - 1 + 1 = δ := by omega
    constructor
    · nlinarith
    constructor
    · nlinarith
    · have heq : (12 * β + 14) * (δ - 1) + (12 * β + 14) = (12 * β + 14) * δ := by
        calc
          _ = (12 * β + 14) * ((δ - 1) + 1) := by ring
          _ = _ := by rw [hstep]
      have hbefore : 2 * β + 5 * (3 * β + 3) + 2 +
          (12 * β + 14) * (δ - 1) + 1 < 12 * (δ + 3) * (β + 1) := by nlinarith
      omega

/-- The choices in Graph Minors XVI, proof of (8.1), pages 71–74, satisfy the
order and index bounds used in Claims (2), (3), and the annulus selection. -/
theorem section9_parameters (δ φ ψ : ℕ) (hφ : 3 ≤ φ) (hψ : 3 ≤ ψ) :
    ∃ κ β γ θ : ℕ,
      κ = δ ^ 2 * φ ^ 2 / 2 + 1 ∧ 1 ≤ κ ∧
      Even β ∧ κ * (ψ + 6) ≤ β ∧ β ≤ κ * (ψ + 6) + 1 ∧
      γ = 3 * β + 3 ∧ θ = 12 * (δ + 3) * (β + 1) ∧
      4 ≤ β ∧ (4 * γ + 2) * δ < θ ∧ 16 * β + 17 ≤ θ ∧
      2 * β + 5 * γ + 2 < θ - (4 * γ + 2) * (δ - 1) - 1 ∧
      κ + (κ - 1) * (ψ + 5) ≤ β - ψ - 5 := by
  let κ := δ ^ 2 * φ ^ 2 / 2 + 1
  let β := 2 * ((κ * (ψ + 6) + 1) / 2)
  have hκ : 1 ≤ κ := by dsimp [κ]; omega
  have hlow : κ * (ψ + 6) ≤ β := by dsimp [β]; omega
  have hhigh : β ≤ κ * (ψ + 6) + 1 := by dsimp [β]; omega
  have hκβ : κ ≤ β := by
    have hb := Nat.mul_le_mul_left κ (show 1 ≤ ψ + 6 by omega)
    omega
  have hδβ : δ ≤ β := (hairs_le_section9_kappa δ φ hφ).trans hκβ
  obtain ⟨hclear, hbig, hfree⟩ := section9_order_bounds δ β hδβ
  refine ⟨κ, β, 3 * β + 3, 12 * (δ + 3) * (β + 1), rfl, hκ,
    ⟨(κ * (ψ + 6) + 1) / 2, by dsimp [β]; omega⟩, hlow, hhigh, rfl, rfl, ?_, ?_, hbig, ?_, ?_⟩
  · have hb := Nat.mul_le_mul_right (ψ + 6) hκ
    omega
  · rw [show 4 * (3 * β + 3) + 2 = 12 * β + 14 by omega]
    exact hclear
  · rw [show 4 * (3 * β + 3) + 2 = 12 * β + 14 by omega]
    exact hfree
  · have hstep : κ - 1 + 1 = κ := by omega
    have heq : κ + (κ - 1) * (ψ + 5) + ψ + 5 = κ * (ψ + 6) := by nlinarith
    omega

/-- Section 9's order bound leaves room to preserve a free boundary set
through all the other clearings in Claim (3). The triangle inequality
through its own centre gives this slightly stronger numerical check. -/
theorem section9_free_bound (δ β : ℕ) (hδβ : δ ≤ β) :
    2 * β + 6 * (3 * β + 3) + 2 + (4 * (3 * β + 3) + 2) * δ <
      12 * (δ + 3) * (β + 1) := by
  nlinarith

/-- The number of centres is at most the separator parameter chosen
in Section 9, including the empty-family case. -/
theorem section9_hairs_le_kappa (δ φ : ℕ) (hφ : 3 ≤ φ) :
    δ ≤ δ ^ 2 * φ ^ 2 / 2 + 1 := hairs_le_section9_kappa δ φ hφ

/-- The constants of Section 9 leave room for Claim (11), and the
separation is larger than the two battlefield radii and short segments. -/
theorem section9_path_bounds {κ β ψ θ θspan : ℕ}
    (hκ : 1 ≤ κ) (hβ : κ * (ψ + 6) ≤ β) (hψ : 3 ≤ ψ)
    (hθ : 16 * β + 17 ≤ θ) (hspan : θ ≤ θspan) :
    ψ ≤ β ∧ κ + 3 ≤ β ∧ β < θspan ∧
      κ + (3 * β + 3) < θspan ∧ 2 * (3 * β + 3) + 2 * ψ < θ := by
  have hNine : κ * 9 ≤ β :=
    (Nat.mul_le_mul_left κ (show 9 ≤ ψ + 6 by omega)).trans hβ
  have hPsi : ψ + 6 ≤ β := by
    have h := Nat.mul_le_mul_right (ψ + 6) hκ
    simpa only [one_mul] using h.trans hβ
  omega

end GraphMinor.GM16

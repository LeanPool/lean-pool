/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.ProjectedHopping
public import LeanPool.HubbardMoments.Torus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Projected hopping moments on the square-lattice torus -/

@[expose] public section

namespace HubbardMoments

open Finset

/-- On the `L × L` torus (`L ≥ 3`, `N = L²`, `z = 4`) the average hop count of `n`
particles is `4n(L² - n)/(L² - 1)`. -/
theorem average_card_hops_torus (L : ℕ) (hL : 3 ≤ L) (n : ℕ) (hn : n ≤ L * L) :
    ((∑ S ∈ powersetCard n (univ : Finset (Fin L × Fin L)), (hops (torus L) S).card : ℕ) : ℚ) /
        (L * L).choose n =
      4 * n * (L * L - n) / (L * L - 1) := by
  have hcard : Fintype.card (Fin L × Fin L) = L * L := by simp
  have h := average_card_hops_regular (torus L) (torus_isRegularOfDegree_of_fintype L hL) n
    (by rw [hcard]; exact hn) (by rw [hcard]; nlinarith)
  rw [hcard] at h
  push_cast at h ⊢
  rw [h]
  ring

/-- `L = 4`, `n = 4`: the average hop count is `64/5 = 12.8`. -/
theorem average_card_hops_torus_L4_n4 :
    ((∑ S ∈ powersetCard 4 (univ : Finset (Fin 4 × Fin 4)), (hops (torus 4) S).card : ℕ) : ℚ) /
        (4 * 4).choose 4 = 64 / 5 := by
  rw [average_card_hops_torus 4 (by norm_num) 4 (by norm_num)]
  norm_num

/-- `L = 5`, `n = 4`: the average hop count is `14`. -/
theorem average_card_hops_torus_L5_n4 :
    ((∑ S ∈ powersetCard 4 (univ : Finset (Fin 5 × Fin 5)), (hops (torus 5) S).card : ℕ) : ℚ) /
        (5 * 5).choose 4 = 14 := by
  rw [average_card_hops_torus 5 (by norm_num) 4 (by norm_num)]
  norm_num

/-- **On the `L × L` torus** (`L ≥ 3`, `N = L²`, `z = 4`),
`μ₂ = t² · 4n(L² - n)/(L² - 1)`. -/
theorem second_moment_torus {σ : Type*} [Fintype σ] [DecidableEq σ] {L : ℕ} (hL : 3 ≤ L)
    {t : ℝ} {H : Matrix (Config (Fin L × Fin L) σ) (Config (Fin L × Fin L) σ) ℂ}
    (hH : IsProjectedHopping (torus L) t H) (n : σ → ℕ)
    (hB : (basis (Fin L × Fin L) n).Nonempty) :
    secondMoment (basis (Fin L × Fin L) n) H =
      (t : ℂ) ^ 2 * 4 * (∑ s, n s : ℕ) * ((L : ℂ) * L - (∑ s, n s : ℕ)) /
        ((L : ℂ) * L - 1) := by
  have h := second_moment_regular hH (torus_isRegularOfDegree_of_fintype L hL) n hB
    (by simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  push_cast at h ⊢
  rw [h]
  ring

end HubbardMoments

/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.StableMatching.Optimality
public import LeanPool.StableMatching.Impossibility
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Examples

Roth's 2 × 2 market (A. E. Roth, *Deferred acceptance algorithms: history, theory, practice, and
open questions*, Internat. J. Game Theory 36 (2008), after Theorem 6): men `m₀: w₀ > w₁`,
`m₁: w₁ > w₀`, women `w₀: m₁ > m₀`, `w₁: m₀ > m₁`, everyone acceptable. Both the matching
`(m₀, w₀), (m₁, w₁)` and the matching `(m₀, w₁), (m₁, w₀)` are stable; deferred acceptance with
the men proposing returns the first and with the women proposing the second. The outcomes are
derived from the optimality theorems rather than by evaluating the algorithm.
-/

@[expose] public section

noncomputable section

namespace LeanPool.StableMatching

open Market

/-- Roth's 2 × 2 market: each man prefers a different woman, and each woman prefers the man who
does not prefer her. -/
def roth22 : Market (Fin 2) (Fin 2) where
  rankM m := if m = 0 then rankTwo Fin.val 0 1 else rankTwo Fin.val 1 0
  rankW w := if w = 0 then rankTwo Fin.val 1 0 else rankTwo Fin.val 0 1
  rankM_injective m := by
    split_ifs
    exacts [rankTwo_injective Fin.val_injective (by decide),
      rankTwo_injective Fin.val_injective (by decide)]
  rankW_injective w := by
    split_ifs
    exacts [rankTwo_injective Fin.val_injective (by decide),
      rankTwo_injective Fin.val_injective (by decide)]

theorem roth22_isStable_refl : roth22.IsStable (PEquiv.refl (Fin 2)) := by
  unfold Market.IsStable IsIndividuallyRational Blocks roth22
  decide

theorem roth22_isStable_swap : roth22.IsStable (Equiv.swap 0 1).toPEquiv := by
  unfold Market.IsStable IsIndividuallyRational Blocks roth22
  decide

/-- In Roth's 2 × 2 market, men-proposing deferred acceptance gives every man his first choice:
it returns `(m₀, w₀), (m₁, w₁)`. -/
theorem roth22_deferredAcceptance (m : Fin 2) : roth22.deferredAcceptance m = some m := by
  have h := rankM_deferredAcceptance_le roth22_isStable_refl m
  have h0 : roth22.rankM m (some m) = 0 := (by decide : ∀ m : Fin 2, roth22.rankM m (some m) = 0) m
  rw [PEquiv.refl_apply, h0, Nat.le_zero, ← h0] at h
  exact roth22.rankM_injective m h

/-- In Roth's 2 × 2 market, women-proposing deferred acceptance gives every woman her first
choice: it returns `(m₀, w₁), (m₁, w₀)`, so the market has two different stable matchings. -/
theorem roth22_swap_deferredAcceptance (w : Fin 2) :
    roth22.swap.deferredAcceptance w = some (Equiv.swap 0 1 w) := by
  have h := rankW_deferredAcceptance_swap_le roth22_isStable_swap w
  have h0 : roth22.rankW w ((Equiv.swap 0 1).toPEquiv.symm w) = 0 :=
    (by decide : ∀ w : Fin 2, roth22.rankW w ((Equiv.swap 0 1).toPEquiv.symm w) = 0) w
  have h1 : roth22.rankW w (some (Equiv.swap 0 1 w)) = 0 :=
    (by decide : ∀ w : Fin 2, roth22.rankW w (some (Equiv.swap 0 1 w)) = 0) w
  rw [h0, Nat.le_zero, ← h1] at h
  exact roth22.rankW_injective w h

/-- In Roth's 2 × 2 market, if woman `w₀` declares `m₀` unacceptable, every stable matching
gives her her first choice `m₁`: truth-telling is not dominant for the women under men-proposing
deferred acceptance, which gives her `m₀`. -/
theorem roth22_updateWoman_symm_eq {ν : Fin 2 ≃. Fin 2}
    (hν : (roth22.updateWoman 0 (rankOne Fin.val 1 0)
      (rankOne_injective Fin.val_injective (by decide))).IsStable ν) :
    ν.symm 0 = some 1 :=
  symm_eq_some_of_isStable (eX := Fin.val) (eY := Fin.val) (x₁ := 0) (x₂ := 1) (y₁ := 0)
    (y₂ := 1) (by decide) (by decide) rfl rfl (by simp)
    (by rw [updateWoman_rankW_of_ne (by decide)]; rfl) hν

end LeanPool.StableMatching

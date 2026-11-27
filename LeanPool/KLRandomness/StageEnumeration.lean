/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StrategyCountability
import Mathlib.Tactic.NormNum

/-!
# A classical enumeration of every total betting strategy

Only a countable covering enumeration is needed by the stage construction.
Each finite protected list contains individually computable strategies; no
effective enumeration of all total programs is claimed or used.
-/

@[expose] public section

namespace Klr.StageEnumeration

/-- A strategy which scans in order and never changes its unit capital. -/
def idle : BettingStrategy where
  scan := ScanRule.monotone
  capital := {
    value := fun _ => 1
    initial := rfl
    nonneg := fun _ => by norm_num
    fair := fun _ => by norm_num }
  computable_capital := by
    refine ⟨fun _ _ => 1, Computable.const ((1 : ℚ).num, (1 : ℚ).den), ?_⟩
    intro v n
    simp

/-- The genuinely countable total-strategy type has a surjective natural
enumeration, chosen classically. This is not an effective program listing. -/
theorem exists_surjective : ∃ s : ℕ → BettingStrategy, Function.Surjective s := by
  classical
  let : Encodable BettingStrategy := Encodable.ofCountable BettingStrategy
  let s (n : ℕ) : BettingStrategy := (Encodable.decode n).getD idle
  refine ⟨s, fun t => ⟨Encodable.encode t, ?_⟩⟩
  simp [s]

end Klr.StageEnumeration

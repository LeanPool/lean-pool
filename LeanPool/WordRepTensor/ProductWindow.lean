/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.OddCycles
public import LeanPool.WordRepTensor.CycleFolding

/-! Internal contracts for the mixed seven-vertex window route. -/

@[expose] public section

namespace WordRepTensor

open SimpleGraph

/-- Fold the index, preserving the top/shadow/root role. -/
def foldVertex {k K : ℕ} (hk : 3 ≤ k) :
    Fin K ⊕ Fin K ⊕ Unit → Fin k ⊕ Fin k ⊕ Unit
  | .inl i => .inl (fold hk i)
  | .inr (.inl i) => .inr (.inl (fold hk i))
  | .inr (.inr u) => .inr (.inr u)

/-- The original seven labels paired with their folded copies. -/
def productWinMap {k K : ℕ} [NeZero K] (hk : 3 ≤ k) (i : Fin K) (x : Fin 7) :
    (Fin k ⊕ Fin k ⊕ Unit) × (Fin K ⊕ Fin K ⊕ Unit) :=
  (foldVertex hk (winMap i x), winMap i x)

end WordRepTensor

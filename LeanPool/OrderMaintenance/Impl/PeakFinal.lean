/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakCap


/-!
# Theorem W, option (A), stage A4: the word size in the number of operations

`theoremW_M` states Theorem W at Level M without Level F notions: for `4 ≤ K_B < 2^512` (in local
`kb`) and every valid operation sequence `ops`, initialization computes no value at or above
`2^1029`, and the machine code of operation `i`, run from the machine state before it, computes
no value at or above

  `2^(128·⌊log₂(i + 1)⌋ + 1285) + 2·(i + 1)`.

So operation `i` runs on words of `128·⌊log₂(i + 1)⌋ + 1286` bits: `O(log i)`, the word RAM's
`w = Θ(log n)`. The proof is `theoremABW_M` with `wKom om ≤ 64·(⌊log₂(i + 1)⌋ + 8)` (`wKom_le`,
from the capacity bound `N ≤ 24·i + 64` of `reachW_cap`).

`theoremW_M_peak` is the cumulative form, by `peak_exec`: after initialization and the whole
sequence, the machine's recorded peak is at most `max m₀.peak (2^(128·⌊log₂(t + 1)⌋ + 1285) +
2·(t + 1))`, `t = ops.length`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

/-- **Theorem W at Level M.** For `4 ≤ K_B < 2^512` in local `kb` and every valid operation
sequence: initialization computes no value at or above `2^1029`, and operation `i`, run from the
machine state before it, computes no value at or above `2^(128·⌊log₂(i + 1)⌋ + 1285) + 2·(i +
  1)`. -/
theorem theoremW_M {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 : KB < 2
  ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops) :
    dpk initWS m₀ < 2 ^ 1029 ∧
    ∀ i (hi : i < ops.length),
      dpk (opS ops[i]) (runSt (exec initWS m₀).st (ops.take i)) < 2 ^ (128 * Nat.log2 (i + 1) +
        1285) + 2 * (i + 1) := by
  obtain ⟨-, hinit, hops⟩ := theoremABW_M hkb h4 h512 ops hv
  refine ⟨hinit, fun i hi => ?_⟩
  obtain ⟨om, p, hR, -, hpk⟩ := hops i hi
  have hw := wKom_le h4 hR
  have : 2 ^ (2 * (wKom om + 128) + 5) ≤ 2 ^ (128 * Nat.log2 (i + 1) + 1285) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ### The cumulative peak -/

/-- The peak after a run is at most the initial peak or a bound on every operation's peak. -/
theorem runSt_peak {B : Nat} : ∀ (ops : List OrderMaintenance.Spec.Op) (m : State),
    (∀ i (hi : i < ops.length), dpk (opS ops[i]) (runSt m (ops.take i)) ≤ B) → (runSt m
      ops).peak ≤ max m.peak B
  | [], m, _ => le_max_left _ _
  | op :: ops, m, h => by
    have h0 : dpk (opS op) m ≤ B := h 0 (by simp)
    have ih := runSt_peak ops (exec (opS op) m).st (fun i hi => h (i + 1) (by simpa using hi))
    have e := Machine.peak_exec (opS op) m
    change (runSt (exec (opS op) m).st ops).peak ≤ _
    refine le_trans ih (max_le ?_ (le_max_right _ _))
    rw [e]; exact max_le (le_max_left _ _) (le_trans h0 (le_max_right _ _))

theorem pow2_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 (a + 1) ≤ Nat.log2 (b + 1) := by
  have h1 : b + 1 < 2 ^ (Nat.log2 (b + 1) + 1) := Nat.lt_log2_self
  have := (Nat.log2_lt (n := a + 1) (by omega)).2 (by omega : a + 1 < 2 ^ (Nat.log2 (b + 1) + 1))
  omega

/-- **Theorem W at Level M, cumulative.** After initialization and the whole valid sequence of
`t` operations, the largest value the machine has computed is at most the initial peak or
`2^(128·⌊log₂(t + 1)⌋ + 1285) + 2·(t + 1)`. -/
theorem theoremW_M_peak {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 :
  KB < 2 ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops) :
    (runSt (exec initWS m₀).st ops).peak ≤
      max m₀.peak (2 ^ (128 * Nat.log2 (ops.length + 1) + 1285) + 2 * (ops.length + 1)) := by
  obtain ⟨hinit, hops⟩ := theoremW_M hkb h4 h512 ops hv
  set B := 2 ^ (128 * Nat.log2 (ops.length + 1) + 1285) + 2 * (ops.length + 1)
  have hle : ∀ i, i ≤ ops.length → 2 ^ (128 * Nat.log2 (i + 1) + 1285) + 2 * (i + 1) ≤ B := fun
    i hi => by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num)
      (show 128 * Nat.log2 (i + 1) + 1285 ≤ 128 * Nat.log2 (ops.length + 1) + 1285 by
        have := log2_mono hi; omega)
    omega
  have h0 : dpk initWS m₀ ≤ B := by
    have h1 := hle 0 (Nat.zero_le _)
    generalize Nat.log2 (0 + 1) = k at h1
    have h2 := pow2_mono (a := 1029) (b := 128 * k + 1285) (le_trans (by norm_num)
      (Nat.le_add_left _ _))
    omega
  have hr := runSt_peak ops (exec initWS m₀).st (fun i hi => le_trans (le_of_lt (hops i hi))
    (hle i (le_of_lt hi)))
  refine le_trans hr (max_le ?_ (le_max_right _ _))
  rw [Machine.peak_exec]; exact max_le (le_max_left _ _) (le_trans h0 (le_max_right _ _))

end OrderMaintenance.Impl

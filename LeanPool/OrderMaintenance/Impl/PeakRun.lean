/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakFinal


/-!
# Theorems A, B and W with one runner, and the clean word-size bound

* **One runner** (`runMW`). `runM` (Theorems A and B) and `runSt` (Theorem W) are separate
  runners. `runMW` is `runM` with a third output: for each operation, the largest value its machine
  code computes (`dpk`, the run's peak with the peak reset to 0). `theoremABW_MW` states
  correctness, the step bounds and the word-size bound in terms of `runMW` alone: the answers are
  the specification's, every operation's cost is at most `opB K_B`, and operation `i`'s peak is
  below `2^(128·⌊log₂(i + 1)⌋ + 1286)`. `runMW_eq` relates it to `runM`; `pks_get` identifies
  its peaks with `theoremW_M`'s (the states `runSt m (ops.take i)`).
* **The clean bound** (`theoremW_M_clean`, `theoremW_M_peak_clean`, `theoremW_M_run`). The term
  `2·(i + 1)` of `theoremW_M` is below `2^(128·⌊log₂(i + 1)⌋ + 1285)`, so operation `i` computes no
  value `≥ 2^(128·⌊log₂(i + 1)⌋ + 1286)`. For a run of `t` operations, initialization and every
  operation compute no value `≥ 2^(128·⌊log₂(t + 1)⌋ + 1286)`.

The existing theorems are unchanged. Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

/-! ### The clean bound -/

/-- `2·(i + 1)` is absorbed by the power. -/
theorem clean_le (i : Nat) :
    2 ^ (128 * Nat.log2 (i + 1) + 1285) + 2 * (i + 1) ≤ 2 ^ (128 * Nat.log2 (i + 1) + 1286) := by
  have h1 : i + 1 < 2 ^ (Nat.log2 (i + 1) + 1) := Nat.lt_log2_self
  have h2 := pow2_mono (show Nat.log2 (i + 1) + 1 ≤ 128 * Nat.log2 (i + 1) + 1284 by omega)
  have e1 : 2 ^ (128 * Nat.log2 (i + 1) + 1285) = 2 ^ (128 * Nat.log2 (i + 1) + 1284) * 2 :=
    pow_succ _ _
  have e2 : 2 ^ (128 * Nat.log2 (i + 1) + 1286) = 2 ^ (128 * Nat.log2 (i + 1) + 1285) * 2 :=
    pow_succ _ _
  omega

/-- The bound of operation `i` is monotone in `i`. -/
theorem clean_mono {i t : Nat} (h : i ≤ t) :
    2 ^ (128 * Nat.log2 (i + 1) + 1286) ≤ 2 ^ (128 * Nat.log2 (t + 1) + 1286) :=
  pow2_mono (by
    have := log2_mono h
    omega)

/-- **Theorem W at Level M, clean form.** For `4 ≤ K_B < 2^512` in local `kb` and every valid
operation sequence: initialization computes no value at or above `2^1029`, and operation `i`, run
from the machine state before it, computes no value at or above `2^(128·⌊log₂(i + 1)⌋ + 1286)`. -/
theorem theoremW_M_clean {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 :
  KB < 2 ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops) :
    dpk initWS m₀ < 2 ^ 1029 ∧
    ∀ i (hi : i < ops.length),
      dpk (opS ops[i]) (runSt (exec initWS m₀).st (ops.take i)) < 2 ^ (128 * Nat.log2 (i + 1) +
        1286) := by
  obtain ⟨hinit, hops⟩ := theoremW_M hkb h4 h512 ops hv
  exact ⟨hinit, fun i hi => lt_of_lt_of_le (hops i hi) (clean_le i)⟩

/-- **Theorem W for a run of `t` operations.** Initialization and every operation of a valid
sequence of `t = ops.length` operations compute no value at or above
`2^(128·⌊log₂(t + 1)⌋ + 1286)`; so neither does the whole run (its peak from a reset peak). -/
theorem theoremW_M_run {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 : KB
  < 2 ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops) :
    dpk initWS m₀ < 2 ^ (128 * Nat.log2 (ops.length + 1) + 1286) ∧
    (∀ i (hi : i < ops.length),
      dpk (opS ops[i]) (runSt (exec initWS m₀).st (ops.take i)) < 2 ^ (128 * Nat.log2
        (ops.length + 1) + 1286)) ∧
    (runSt (exec initWS {
      m₀ with
      peak := 0
    }).st ops).peak < 2 ^ (128 * Nat.log2 (ops.length +
      1) + 1286) := by
  have run : ∀ m : State, m.loc "kb" = KB →
      dpk initWS m < 2 ^ (128 * Nat.log2 (ops.length + 1) + 1286) ∧
      ∀ i (hi : i < ops.length), dpk (opS ops[i]) (runSt (exec initWS m).st (ops.take i)) <
        2 ^ (128 * Nat.log2 (ops.length + 1) + 1286) := fun m hk => by
    obtain ⟨hinit, hops⟩ := theoremW_M_clean hk h4 h512 ops hv
    refine ⟨lt_of_lt_of_le hinit (pow2_mono (by omega)), fun i hi => ?_⟩
    exact lt_of_lt_of_le (hops i hi) (clean_mono (le_of_lt hi))
  obtain ⟨hinit, hops⟩ := run m₀ hkb
  refine ⟨hinit, hops, ?_⟩
  obtain ⟨hinit', hops'⟩ := run {
    m₀ with
    peak := 0
  } hkb
  have hr := runSt_peak (B := 2 ^ (128 * Nat.log2 (ops.length + 1) + 1286) - 1) ops
    (exec initWS {
      m₀ with
      peak := 0
    }).st (fun i hi => by have := hops' i hi; omega)
  have e := Machine.peak_exec initWS {
    m₀ with
    peak := 0
  }
  have h0 : (exec initWS {
    m₀ with
    peak := 0
  }).st.peak < 2 ^ (128 * Nat.log2 (ops.length + 1) +
    1286) := by
    rw [e]; exact max_lt (Nat.two_pow_pos _) hinit'
  have hp := Nat.two_pow_pos (128 * Nat.log2 (ops.length + 1) + 1286)
  omega

/-- **Theorem W at Level M, cumulative, clean form.** After initialization and the whole valid
sequence of `t` operations, the machine's recorded peak is at most the initial peak or
`2^(128·⌊log₂(t + 1)⌋ + 1286) − 1`: every value computed is below `2^(128·⌊log₂(t + 1)⌋ + 1286)`. -/
theorem theoremW_M_peak_clean {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB)
    (h512 : KB < 2 ^ 512) (ops : List OrderMaintenance.Spec.Op) (hv :
      OrderMaintenance.Spec.Valid OrderMaintenance.Spec.State.empty ops) :
    (runSt (exec initWS m₀).st ops).peak ≤ max m₀.peak (2 ^ (128 * Nat.log2 (ops.length + 1) +
      1286) - 1) := by
  obtain ⟨hinit, hops, -⟩ := theoremW_M_run hkb h4 h512 ops hv
  have hr := runSt_peak (B := 2 ^ (128 * Nat.log2 (ops.length + 1) + 1286) - 1) ops
    (exec initWS m₀).st (fun i hi => by have := hops i hi; omega)
  refine le_trans hr (max_le ?_ (le_max_right _ _))
  rw [Machine.peak_exec]
  exact max_le (le_max_left _ _) (le_trans (by omega) (le_max_right _ _))

/-! ### One runner for answers, costs and peaks -/

/-- **The machine run with peaks**: `runM`, which returns the answers and the cost of each
operation, together with the largest value each operation's machine code computes (`dpk`: the
peak of its run with the peak reset to 0). `none` if an operation fails or reaches an error. -/
def runMW : State → List OrderMaintenance.Spec.Op → Option (List OrderMaintenance.Spec.Ans ×
  List Nat × List Nat)
  | _, [] => some ([], [], [])
  | m, op :: ops =>
    if (exec (opS op) m).status = .ok then
      (runMW (exec (opS op) m).st ops).map fun r =>
        (ansOf op (exec (opS op) m).st :: r.1, (exec (opS op) m).cost :: r.2.1, dpk (opS op) m
          :: r.2.2)
    else none

/-- The peaks of the operations along the run from `m` (the recursion of `runSt`). -/
def pks : State → List OrderMaintenance.Spec.Op → List Nat
  | _, [] => []
  | m, op :: ops => dpk (opS op) m :: pks (exec (opS op) m).st ops

/-- **`runMW` is `runM` with the peaks.** -/
theorem runMW_eq : ∀ (ops : List OrderMaintenance.Spec.Op) (m : State),
    runMW m ops = (runM m ops).map fun r => (r.1, r.2, pks m ops)
  | [], _ => rfl
  | op :: ops, m => by
    simp only [runMW, runM, pks]
    split
    · rw [runMW_eq ops]; cases runM (exec (opS op) m).st ops <;> rfl
    · rfl

theorem pks_length : ∀ (ops : List OrderMaintenance.Spec.Op) (m : State), (pks m ops).length =
  ops.length
  | [], _ => rfl
  | _ :: ops, _ => by simp only [pks, List.length_cons, pks_length ops]

/-- **The peaks of `runMW` are those of `runSt`'s states**: entry `i` is the peak of operation `i`
run from `runSt m (ops.take i)`. -/
theorem pks_get : ∀ (ops : List OrderMaintenance.Spec.Op) (m : State) (i : Nat) (hi : i <
  ops.length),
    (pks m ops)[i]'(by
      rw [pks_length]
      exact hi) = dpk (opS ops[i]) (runSt m (ops.take i))
  | [], _, _, hi => by simp at hi
  | _ :: _, _, 0, _ => rfl
  | _ :: ops, m, i + 1, hi => pks_get ops _ i (by simpa using hi)

theorem runM_length : ∀ (ops : List OrderMaintenance.Spec.Op) (m : State) {as : List
  OrderMaintenance.Spec.Ans} {cs : List Nat},
    runM m ops = some (as, cs) → cs.length = ops.length
  | [], _, _, _, h => by simp only [runM, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl
  | op :: ops, m, as, cs, h => by
    simp only [runM] at h
    split at h
    · cases hr : runM (exec (opS op) m).st ops with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2, List.length_cons, runM_length ops _ (as := r.1) (cs := r.2) hr]; rfl
    · cases h

/-- **Theorems A, B and W at Level M, with one runner.** For `4 ≤ K_B < 2^512` (in local `kb`) and
every valid operation sequence: initialization ends normally within `initB` steps and computes no
value at or above `2^1029`; the run `runMW` of the operations returns exactly the specification's
answers, every operation takes at most `opB K_B` steps, and operation `i` computes no value at or
above `2^(128·⌊log₂(i + 1)⌋ + 1286)`. -/
theorem theoremABW_MW {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 : KB
  < 2 ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops) :
    (exec initWS m₀).status = .ok ∧ (exec initWS m₀).cost ≤ initB ∧ dpk initWS m₀ < 2 ^ 1029 ∧
    ∃ cs ps, runMW (exec initWS m₀).st ops = some (OrderMaintenance.Spec.run
      OrderMaintenance.Spec.State.empty ops, cs, ps) ∧
      cs.length = ops.length ∧ ps.length = ops.length ∧
      (∀ c ∈ cs, c ≤ opB KB) ∧
      ∀ i (hi : i < ps.length), ps[i] < 2 ^ (128 * Nat.log2 (i + 1) + 1286) := by
  obtain ⟨hst, hk, cs, hrun, hcs⟩ := theoremAB_M hkb h4 ops hv
  obtain ⟨hinit, hops⟩ := theoremW_M_clean hkb h4 h512 ops hv
  refine ⟨hst, hk, hinit, cs, pks (exec initWS m₀).st ops, ?_, runM_length ops _ hrun,
    pks_length _ _, hcs,
    fun i hi => ?_⟩
  · rw [runMW_eq, hrun]; rfl
  · have hi' : i < ops.length := by rw [pks_length] at hi; exact hi
    rw [pks_get ops _ i hi']
    exact hops i hi'

end OrderMaintenance.Impl

/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Machine.Flat
public import LeanPool.OrderMaintenance.Impl.PeakWord


/-!
# Theorems A and B on a RAM without `alloc`

The flat program (`Machine/Flat.lean`) of the machine program: `initFlat M` (the prelude, which sets
the heap pointer to `M`, then `flatten initWS`) once, then `flatten (opS op)` for each operation.
It uses only array 0, the RAM's memory, and contains no `alloc`. It runs on `exec`, from any state
whose memory array has capacity `M` and is zero-filled, and whose local `kb` holds `K_B`. As for
the word width in `theoremAB_word`, `M` is fixed before the run from its length `t`.

* `maxArr_initWS`, `maxArr_opS`: the program's array names are at most `2011` (checked by the
  kernel), so the table takes cells `1 … 2012` and the heap starts at `2013`.
* `runFlat`: `runM` (Theorem A's runner) for the flat program; `runFlatW w`: the same on `w`-bit
  words.
* `theoremAB_flat`: for `4 ≤ K_B < 2^512`, every valid sequence of `t` operations, and
  `M ≥ memFlat t K_B = 2013 + (initB + t·opB K_B)·2^(128·⌊log₂(t + 1)⌋ + 1286)`, the flat program
  returns exactly the specification's answers; initialization takes at most `5·initB + 3` steps and
  each operation at most `5·opB K_B` steps. The heap needs room for `cost × peak` cells per run, and
  Theorem W bounds every peak by `2^(128·⌊log₂(t + 1)⌋ + 1286)`. `memFlat t K_B` has `O(log t)`
    bits.
* `theoremAB_flat_word`: the same on `w`-bit words, for every `w` with `M < 2^w`; for
  `M = memFlat t K_B`, `w = wFlat t K_B = 128·⌊log₂(t + 1)⌋ + 1287 + ⌊log₂(initB + t·opB K_B +
    2013)⌋`
  suffices (`memFlat_lt`).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec execW Stmt Expr wp dpk flatten prelude
  FRel heapPtr flatten_sim
  flatten_dpk flatten_noAlloc)

/-! ### The program's array names -/

-- Kernel reduction checks these finite syntax trees without trusting a compiled evaluator.
theorem maxArr_initWS : initWS.maxArr ≤ 2011 := by decide +kernel
theorem maxArr_insertWS : insertWS.maxArr ≤ 2011 := by decide +kernel
theorem maxArr_deleteWS : deleteWS.maxArr ≤ 2011 := by decide +kernel
theorem maxArr_orderWS : orderWS.maxArr ≤ 2011 := by decide +kernel

/-- **The array names of an operation's machine code** are at most `2011`. -/
theorem maxArr_opS (op : OrderMaintenance.Spec.Op) : (opS op).maxArr ≤ 2011 := by
  have := maxArr_insertWS; have := maxArr_deleteWS; have := maxArr_orderWS
  cases op <;> simp only [opS, Stmt.maxArr, Expr.maxArr] <;> omega

/-! ### The flat program and its runner -/

/-- **The flat initialization**: the prelude (heap pointer `:= M`), then the flattened `initWS`. -/
def initFlat (M : Nat) : Stmt := .seq (prelude M) (flatten initWS)

/-- **`runM` for the flat program**: the answers and the cost of each operation's flattened
machine code (`none` if an operation fails or reaches an error). -/
def runFlat : State → List OrderMaintenance.Spec.Op → Option (List OrderMaintenance.Spec.Ans ×
  List Nat)
  | _, [] => some ([], [])
  | m, op :: ops =>
    if (exec (flatten (opS op)) m).status = .ok then
      (runFlat (exec (flatten (opS op)) m).st ops).map fun r =>
        (ansOf op (exec (flatten (opS op)) m).st :: r.1, (exec (flatten (opS op)) m).cost :: r.2)
    else none

/-- `runFlat` on the `w`-bit machine. -/
def runFlatW (w : Nat) : State → List OrderMaintenance.Spec.Op → Option (List
  OrderMaintenance.Spec.Ans × List Nat)
  | _, [] => some ([], [])
  | m, op :: ops =>
    if (execW w (flatten (opS op)) m).status = .ok then
      (runFlatW w (execW w (flatten (opS op)) m).st ops).map fun r =>
        (ansOf op (execW w (flatten (opS op)) m).st :: r.1, (execW w (flatten (opS op)) m).cost
          :: r.2)
    else none

/-- **The memory the flat run of `t` operations needs**: the table (cells `0 … 2012`), and
room for `cost × peak` cells for initialization and each operation. -/
def memFlat (t KB : Nat) : Nat := 2013 + (initB + t * opB KB) * 2 ^ (128 * Nat.log2 (t + 1) + 1286)

/-- **A word width for `memFlat t K_B`**: `O(log t)` bits for fixed `K_B`. -/
def wFlat (t KB : Nat) : Nat := 128 * Nat.log2 (t + 1) + 1287 + Nat.log2 (initB + t * opB KB + 2013)

theorem memFlat_lt (t KB : Nat) : memFlat t KB < 2 ^ wFlat t KB := by
  have key : ∀ X E : Nat, 2013 + X * 2 ^ E < 2 ^ (E + 1 + Nat.log2 (X + 2013)) := fun X E => by
    have h1 : X + 2013 < 2 ^ (Nat.log2 (X + 2013) + 1) := Nat.lt_log2_self
    have h2 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    have e : 2 ^ (E + 1 + Nat.log2 (X + 2013)) = 2 ^ (Nat.log2 (X + 2013) + 1) * 2 ^ E := by
      rw [← pow_add]; congr 1; omega
    have h3 : 2013 ≤ 2013 * 2 ^ E := Nat.le_mul_of_pos_right _ (by omega)
    have h4 := Nat.mul_lt_mul_of_pos_right h1 (show 0 < 2 ^ E by omega)
    rw [Nat.add_mul] at h4; rw [e]; omega
  have := key (initB + t * opB KB) (128 * Nat.log2 (t + 1) + 1286)
  unfold memFlat wFlat
  rwa [show 128 * Nat.log2 (t + 1) + 1287 = 128 * Nat.log2 (t + 1) + 1286 + 1 by omega]

/-! ### The run -/

theorem ansOf_loc {m m' : State} (h : m'.loc = m.loc) (op : OrderMaintenance.Spec.Op) : ansOf op
  m' = ansOf op m := by
  cases op <;> simp [ansOf, h]

/-- **The operations, simulated**: from a flat state related to the original state before the
operations, with room for `t × B × P` cells (`B` bounding each operation's cost, `P` its peak),
the flat run returns the same answers, each operation within `5 B` steps; on `w`-bit words with
`M, P < 2^w` it agrees with `runFlat`. -/
theorem runFlat_sim {M P B : Nat} : ∀ (ops : List OrderMaintenance.Spec.Op) (m f : State) (as :
  List OrderMaintenance.Spec.Ans) (cs : List Nat),
    runM m ops = some (as, cs) → (∀ c ∈ cs, c ≤ B) →
    (∀ i (hi : i < ops.length), dpk (opS ops[i]) (runSt m (ops.take i)) ≤ P) →
    FRel 2011 M m f → 2013 + ops.length * (B * P) ≤ heapPtr f →
    (∃ cs', runFlat f ops = some (as, cs') ∧ ∀ c ∈ cs', c ≤ 5 * B) ∧
      ∀ w, M < 2 ^ w → P < 2 ^ w → runFlatW w f ops = runFlat f ops
  | [], m, f, as, cs, h, _, _, _, _ => by
    simp only [runM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨[], rfl, fun _ h => by cases h⟩, fun _ _ _ => rfl⟩
  | op :: ops, m, f, as, cs, h, hB, hP, hR, hmem => by
    simp only [runM] at h
    split at h
    · next hst =>
      cases hr : runM (exec (opS op) m).st ops with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨em, el, ec, eco, est⟩ := Machine.exec_reset (opS op) m
        have hR0 : FRel 2011 M {
          m with
          peak := 0
        } f := hR.congr rfl rfl rfl rfl hR.loc
        have hP0 : dpk (opS op) m ≤ P := hP 0 (by simp)
        have hcB : (exec (opS op) m).cost ≤ B := hB _ (List.mem_cons_self ..)
        have hBP : (exec (opS op) m).cost * P ≤ B * P := Nat.mul_le_mul_right P hcB
        have hlen : (op :: ops).length * (B * P) = ops.length * (B * P) + B * P := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        rw [hlen] at hmem
        have herr : (exec (opS op) {
          m with
          peak := 0
        }).status ≠ .err := by rw [← est, hst]; simp
        obtain ⟨s1, s2, s3, s4, -⟩ := flatten_sim (maxArr_opS op) hR0 (P := P) herr hP0 (by
          rw [← eco]
          omega)
        rw [← eco] at s3 s4
        have hfst : (exec (flatten (opS op)) f).status = .ok := by rw [s1, ← est, hst]
        have hR1 : FRel 2011 M (exec (opS op) m).st (exec (flatten (opS op)) f).st :=
          s2.congr em ec rfl rfl (by rw [s2.loc, el])
        obtain ⟨⟨cs', hrun, hcs⟩, hw⟩ := runFlat_sim ops _ _ r.1 r.2 hr (fun c hc => hB c
          (List.mem_cons_of_mem _ hc))
          (fun i hi => hP (i + 1) (by simpa using hi)) hR1 (by omega)
        refine ⟨⟨(exec (flatten (opS op)) f).cost :: cs', ?_, ?_⟩, fun w hM hPw => ?_⟩
        · simp only [runFlat, hfst, ↓reduceIte, hrun, Option.map_some, ansOf_loc hR1.loc]
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · omega
          · exact hcs c hc
        · have hd := flatten_dpk (maxArr_opS op) hR (P := P) (by
          rw [hst]
          simp) hP0 (by omega)
          have hd' : dpk (flatten (opS op)) f < 2 ^ w := lt_of_le_of_lt hd (max_lt (by omega) hM)
          simp only [runFlatW, runFlat, Machine.execW_agree hd', hw w hM hPw]
    · cases h

/-- **Initialization, simulated**: from a zero-filled memory of capacity `M`, the prelude and the
flattened `initWS` reach a state related to the original's after `initWS` from the state `m₀`
with the same locals and no arrays, within `5 · cost + 3` steps, the heap pointer at most
`cost × P` below `M`. -/
theorem initFlat_sim {f₀ : State} {M P : Nat} (hcap : f₀.cap 0 = M) (hzero : ∀ i, f₀.mem 0 i = 0)
    (herr : (exec initWS ⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩).status ≠ .err)
    (hP : dpk initWS ⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩ ≤ P)
    (hM : 2013 + (exec initWS ⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩).cost * P ≤ M) :
    (exec (initFlat M) f₀).status = (exec initWS ⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩).status ∧
    FRel 2011 M (exec initWS ⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩).st (exec (initFlat M) f₀).st ∧
    (exec (initFlat M) f₀).cost ≤ 5 * (exec initWS ⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩).cost + 3 ∧
    M ≤ heapPtr (exec (initFlat M) f₀).st + (exec initWS ⟨fun _ _ => 0, fun _ => 0, f₀.loc,
      0⟩).cost * P ∧
    dpk (initFlat M) f₀ ≤ max P M := by
  set m₀ : State := ⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩
  -- the prelude, from any peak
  have pre : ∀ g : State, g.cap 0 = M → g.mem 0 = f₀.mem 0 → g.loc = f₀.loc →
      exec (prelude M) g = ⟨((g.bump 0).bump M).write 0 0 M, 1 + 1 + 1, .ok⟩ ∧
      FRel 2011 M m₀ (((g.bump 0).bump M).write 0 0 M) := fun g hc hm hl => by
    refine ⟨Machine.exec_store_some rfl rfl (by omega), ⟨by simp [State.write, State.bump, hl,
      m₀], ?_, ?_, ?_,
      fun a _ j hj => absurd hj (Nat.not_lt_zero _), fun a _ j hj => absurd hj (Nat.not_lt_zero _),
      fun a _ b _ _ j hj => absurd hj (Nat.not_lt_zero _), fun i hi _ => ?_⟩⟩
    · simp [State.write, State.bump, hc]
    · simp [heapPtr, State.write, State.upd]; omega
    · simp [heapPtr, State.write, State.upd]
    · simp [State.write, State.bump, State.upd, hm, hzero]; omega
  have hm0 : (exec initWS m₀).st.peak ≤ P := by
    rw [Machine.peak_exec]; exact max_le (Nat.zero_le _) hP
  obtain ⟨x0, hR⟩ := pre f₀ hcap rfl rfl
  have hp0 : heapPtr (((f₀.bump 0).bump M).write 0 0 M) = M := by
    simp [heapPtr, State.write, State.upd]
  obtain ⟨s1, s2, s3, s4, -⟩ := flatten_sim maxArr_initWS hR herr hm0 (by
    rw [hp0]
    exact hM)
  have xi : exec (initFlat M) f₀ = ⟨(exec (flatten initWS) (((f₀.bump 0).bump M).write 0 0 M)).st,
      3 + (exec (flatten initWS) (((f₀.bump 0).bump M).write 0 0 M)).cost,
      (exec (flatten initWS) (((f₀.bump 0).bump M).write 0 0 M)).status⟩ := by
    change (exec (prelude M) f₀).bind (exec (flatten initWS)) = _
    rw [x0, Machine.Out.bind_ok rfl]
  rw [xi]
  refine ⟨s1, s2, by simp only; omega, by rw [hp0] at s4; exact s4, ?_⟩
  -- the values computed, from a reset peak
  obtain ⟨x0', hR'⟩ := pre {
    f₀ with
    peak := 0
  } hcap rfl rfl
  have hd := flatten_dpk maxArr_initWS hR' herr hP (by
    simp only [Nat.reduceAdd, State.write, State.bump, max_self, zero_le, sup_of_le_right]
    exact hM)
  have xi' : dpk (initFlat M) f₀ = (exec (flatten initWS) (({
    f₀ with
    peak := 0
  }.bump 0).bump M
    |>.write 0 0 M)).st.peak := by
    change ((exec (prelude M) {
      f₀ with
      peak := 0
    }).bind (exec (flatten initWS))).st.peak = _
    rw [x0', Machine.Out.bind_ok rfl]
  rw [xi', Machine.peak_exec]
  have hd0 : dpk initWS m₀ ≤ P := hP
  refine max_le ?_ (le_trans hd (by omega))
  simp [State.write, State.bump]

/-- **Theorems A and B on a RAM without `alloc`.** For `4 ≤ K_B < 2^512` and every valid sequence
of `t` operations, let the flat machine start from a state whose memory, array 0, has capacity
`M ≥ memFlat t K_B` and is zero-filled, with `K_B` in local `kb`. The flattened programs contain no
`alloc`; the flat run of initialization (`initFlat M`: the prelude, then `flatten initWS`) and
  of the
operations (`flatten (opS op)`) returns exactly the specification's answers; initialization takes
at most `5·initB + 3` steps and each operation at most `5·opB K_B` steps. -/
theorem theoremAB_flat {f₀ : State} {KB M : Nat} (hkb : f₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 :
  KB < 2 ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops)
    (hcap : f₀.cap 0 = M) (hzero : ∀ i, f₀.mem 0 i = 0) (hM : memFlat ops.length KB ≤ M) :
    ((initFlat M).hasAlloc = false ∧ ∀ op, (flatten (opS op)).hasAlloc = false) ∧
    (exec (initFlat M) f₀).status = .ok ∧ (exec (initFlat M) f₀).cost ≤ 5 * initB + 3 ∧
    ∃ cs, runFlat (exec (initFlat M) f₀).st ops = some (OrderMaintenance.Spec.run
      OrderMaintenance.Spec.State.empty ops, cs) ∧
      ∀ c ∈ cs, c ≤ 5 * opB KB := by
  have hna : (initFlat M).hasAlloc = false := by
    simp [initFlat, prelude, Stmt.hasAlloc, flatten_noAlloc]
  have hkb0 : (⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩ : State).loc "kb" = KB := hkb
  obtain ⟨hst, hk, cs, hrun, hcs⟩ := theoremAB_M hkb0 h4 ops hv
  obtain ⟨hinit, hops, -⟩ := theoremW_M_run hkb0 h4 h512 ops hv
  unfold memFlat at hM
  generalize 2 ^ (128 * Nat.log2 (ops.length + 1) + 1286) = W at hinit hops hM
  have hIW := Nat.mul_le_mul_right W hk
  have hM' : 2013 + initB * W + ops.length * (opB KB * W) ≤ M := by
    rw [Nat.add_mul, Nat.mul_assoc] at hM; omega
  obtain ⟨i1, i2, i3, i4, -⟩ := initFlat_sim (P := W) hcap hzero (by
    rw [hst]
    simp) (le_of_lt hinit) (by omega)
  obtain ⟨⟨cs', hrun', hcs'⟩, -⟩ := runFlat_sim (B := opB KB) (P := W) ops _ _ _ cs hrun hcs
    (fun i hi => le_of_lt (hops i hi)) i2 (by omega)
  exact ⟨⟨hna, fun op => flatten_noAlloc _⟩, by rw [i1, hst], by omega, cs', hrun', hcs'⟩

/-- **Theorems A and B on a RAM without `alloc`, with `w`-bit words.** Under the hypotheses of
`theoremAB_flat`, for every `w` with `M < 2^w` the `w`-bit machine runs the flat program exactly
as `exec` does, so the conclusion of `theoremAB_flat` holds verbatim for it. For `M = memFlat t
  K_B`,
`w = wFlat t K_B` suffices (`memFlat_lt`): `O(log t)` bits for fixed `K_B`. -/
theorem theoremAB_flat_word {f₀ : State} {KB M w : Nat} (hkb : f₀.loc "kb" = KB) (h4 : 4 ≤ KB)
    (h512 : KB < 2 ^ 512) (ops : List OrderMaintenance.Spec.Op) (hv :
      OrderMaintenance.Spec.Valid OrderMaintenance.Spec.State.empty ops)
    (hcap : f₀.cap 0 = M) (hzero : ∀ i, f₀.mem 0 i = 0) (hM : memFlat ops.length KB ≤ M) (hw : M
      < 2 ^ w) :
    (execW w (initFlat M) f₀ = exec (initFlat M) f₀ ∧
      runFlatW w (exec (initFlat M) f₀).st ops = runFlat (exec (initFlat M) f₀).st ops) ∧
    (execW w (initFlat M) f₀).status = .ok ∧ (execW w (initFlat M) f₀).cost ≤ 5 * initB + 3 ∧
    ∃ cs, runFlatW w (execW w (initFlat M) f₀).st ops = some (OrderMaintenance.Spec.run
      OrderMaintenance.Spec.State.empty ops, cs) ∧
      ∀ c ∈ cs, c ≤ 5 * opB KB := by
  have hkb0 : (⟨fun _ _ => 0, fun _ => 0, f₀.loc, 0⟩ : State).loc "kb" = KB := hkb
  obtain ⟨hst, hk, cs, hrun, hcs⟩ := theoremAB_M hkb0 h4 ops hv
  obtain ⟨hinit, hops, -⟩ := theoremW_M_run hkb0 h4 h512 ops hv
  have hM0 := hM
  unfold memFlat at hM
  generalize 2 ^ (128 * Nat.log2 (ops.length + 1) + 1286) = W at hinit hops hM
  have hIW := Nat.mul_le_mul_right W hk
  have hM' : 2013 + initB * W + ops.length * (opB KB * W) ≤ M := by
    rw [Nat.add_mul, Nat.mul_assoc] at hM; omega
  have hWM : W < 2 ^ w := by
    have : W ≤ M := by
      have : 1 ≤ initB := by unfold initB; omega
      have : W ≤ initB * W := Nat.le_mul_of_pos_left W (by omega)
      omega
    omega
  obtain ⟨-, i2, -, i4, i5⟩ := initFlat_sim (P := W) hcap hzero (by
    rw [hst]
    simp) (le_of_lt hinit) (by omega)
  obtain ⟨-, hagree⟩ := runFlat_sim (B := opB KB) (P := W) ops _ _ _ cs hrun hcs
    (fun i hi => le_of_lt (hops i hi)) i2 (by omega)
  have hi : execW w (initFlat M) f₀ = exec (initFlat M) f₀ :=
    Machine.execW_agree (lt_of_le_of_lt i5 (max_lt hWM hw))
  have hr := hagree w hw hWM
  rw [hi, hr]
  exact ⟨⟨rfl, rfl⟩, (theoremAB_flat hkb h4 h512 ops hv hcap hzero hM0).2⟩

end OrderMaintenance.Impl

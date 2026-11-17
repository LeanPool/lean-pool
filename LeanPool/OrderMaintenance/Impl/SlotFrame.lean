/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Sim
public import LeanPool.OrderMaintenance.Machine.Frame


/-!
# M6: compiled code stays in its slot

The compiled code of slot `p` stores only to the arrays `1000·p + code` with `code < 1000`
(`Stm.compile_arrs`). So it leaves the other slot and the wrapper's arrays alone, and the
encoding of a core in another slot survives it (`Enc.of_other`).
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same exec_frame)

/-- Array `b` belongs to slot `p`. -/
def InSlot (p b : Nat) : Prop := 1000 * p ≤ b ∧ b < 1000 * p + 1000

theorem arr_inSlot (p : Nat) (sl : Slot) : InSlot p (arr p sl) := by
  have := Slot.code_lt sl
  change 1000 * p ≤ 1000 * p + sl.code ∧ 1000 * p + sl.code < 1000 * p + 1000
  omega

theorem st1_arrs (a : Arr) (e : OrderMaintenance.Machine.Expr) : (st1 a e).arrs = [a] := rfl

/-- **The compiled code of slot `p` stores only to slot `p`.** -/
theorem Stm.compile_arrs (p : Nat) (κ : Caps) :
    ∀ (c : Stm), ∀ b ∈ (c.compile p κ).arrs, InSlot p b := by
  intro c
  induction c with
  | seq c d ihc ihd =>
    intro b hb; simp only [Stm.compile, Stmt.arrs, List.mem_append] at hb
    exact hb.elim (ihc b) (ihd b)
  | ite e t f iht ihf =>
    intro b hb; simp only [Stm.compile, Stmt.arrs, List.mem_append] at hb
    exact hb.elim (iht b) (ihf b)
  | loop x n body ih => intro b hb; exact ih b hb
  | call nm ps body rs args ds ih => intro b hb; exact ih b hb
  | «catch» c h ihc ihh =>
    intro b hb; simp only [Stm.compile, Stmt.arrs, List.mem_append] at hb
    exact hb.elim (ihc b) (ihh b)
  | _ =>
    intro b hb
    simp only [compile, Stmt.arrs, List.not_mem_nil, List.mem_cons, or_false, List.nil_append,
        List.cons_append, st1, List.map_cons, List.map_nil] at hb
    repeat' rcases hb with rfl | hb
    all_goals exact arr_inSlot _ _

theorem inSlot_disj {p q : Nat} (hpq : p ≠ q) {b : Arr} (hp : InSlot p b)
    (hq : InSlot q b) : False := by
  obtain ⟨h1, h2⟩ := hp
  obtain ⟨h3, h4⟩ := hq
  omega

/-- Running slot `p`'s compiled code leaves every array outside slot `p` unchanged. -/
theorem compile_frame (p : Nat) (κ : Caps) (c : Stm) (s : State) {b : Arr} (hb : ¬ InSlot p b) :
    Same b s (exec (c.compile p κ) s).st :=
  exec_frame _ s b fun h => hb (Stm.compile_arrs p κ c b h)

/-- The encoding of a core in another slot depends only on that slot's arrays. -/
theorem Enc.of_same {q : Nat} {κ : Caps} {n : Core} {m m' : State} (h : Enc q κ n m)
    (hs : ∀ b, InSlot q b → Same b m m') : Enc q κ n m' := by
  have hS : ∀ sl, Same (arr q sl) m m' := fun sl => hs _ (arr_inSlot q sl)
  refine ⟨fun f => ?_, fun f i hi => ?_, fun t => ?_, fun t => ?_, h.sle, ?_,
    fun k => ?_, fun k b => ?_,
    fun k => ?_, fun k i hi => ?_, fun k i hi j hj => ?_, ?_, fun c hc j hj => ?_,
    fun o => ?_, fun o => ?_,
    h.prepC, h.pwH, h.frec⟩
  · rw [(hS _).2]; exact h.cap f
  · rw [(hS _).1]; exact h.mem f i hi
  · rw [(hS _).2]; exact h.scap t
  · rw [(hS _).1]; exact h.smem t
  · rw [(hS _).2]; exact h.pcap
  · rw [(hS _).1]; exact h.pmem k
  · rw [(hS _).2]; exact h.lcapA k b
  · rw [(hS _).2]; exact h.lcapN k
  · rw [(hS _).1]; exact h.llen k i hi
  · rw [(hS _).1, (hS _).1]; exact h.lmem k i hi j hj
  · rw [(hS _).2]; exact h.wcap
  · rw [(hS _).1]; exact h.wmem c hc j hj
  · rw [(hS _).2]; exact h.ocap o
  · rw [(hS _).1]; exact h.omem o

/-- **A core in another slot survives the compiled code of slot `p`.** -/
theorem Enc.of_other {p q : Nat} (hpq : p ≠ q) {κ κ' : Caps} {n : Core} {m : State}
    (h : Enc q κ' n m)
    (c : Stm) : Enc q κ' n (exec (c.compile p κ) m).st :=
  h.of_same fun _b hb => compile_frame p κ c m (fun hp => inSlot_disj hpq hp hb)

end OrderMaintenance.Impl

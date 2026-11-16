/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakTheoremW


/-!
# Theorem W, option (A), stage A4: the final theorem

`theoremABW_M` is `theoremAB_M` (correctness and the step bounds) together with the peak bounds of
stage A3 along the whole run:

* `runSt m ops`: the machine state after the machine code of `ops`, run in order from `m` (the
  recursion of `runM`). The state before operation `i` is `runSt m₁ (ops.take i)`, with `m₁` the
  state after initialization; the specification state before it is `Spec.final ∅ (ops.take i)`.
* `step_reachW`, `run_reachW`: the threading of option (B)'s `ReachW` (the wrapper state is
  reached by initialization and `i` valid operations) together with the encoding `WEnc`; the
  wrapper state after an operation is `OrderMaintenance.apply`'s result (`ReachW.step`).
* `theoremABW_M`: for every valid sequence, the conclusion of `theoremAB_M`, the initialization's
  peak `< 2^1029`, and for each operation `i` a reached wrapper state `om` encoded by the machine
  state before it, with the operation's peak `< 2^(2·(wKom om + 128) + 5) + 2·(i + 1)`.

`run_reach` and `theoremAB_M` are unchanged. Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

/-- **The machine state after the machine code of `ops`**, run in order from `m` (as `runM`). -/
def runSt : State → List OrderMaintenance.Spec.Op → State
  | m, [] => m
  | m, op :: ops => runSt (exec (opS op) m).st ops

/-! ### One operation -/

/-- **One operation keeps `ReachW` and the encoding**: the wrapper state after it is
`OrderMaintenance.apply`'s. -/
theorem step_reachW {KB t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} {m :
  State} {p : Nat} (h4 : 4 ≤ KB)
    (hR : ReachW KB t om Sp) (h : WEnc om m p) {op : OrderMaintenance.Spec.Op} (hv : op.Valid Sp) :
    wp (opS op) (fun m' _ => ∃ om' p', ReachW KB (t + 1) om' (OrderMaintenance.Spec.step Sp
      op).1 ∧ WEnc om' m' p') m := by
  obtain ⟨hI, -, -⟩ := reachW_inv h4 hR
  have fin : ∀ {om' : OrderMaintenance} {m' : State}, ReachW KB (t + 1) om'
    (OrderMaintenance.Spec.step Sp op).1 →
      (WEnc om' m' 0 ∨ WEnc om' m' 1) → ∃ om'' p', ReachW KB (t + 1) om''
        (OrderMaintenance.Spec.step Sp op).1 ∧
        WEnc om'' m' p' := fun hR' h' => by
    rcases h' with h' | h'
    · exact ⟨_, 0, hR', h'⟩
    · exact ⟨_, 1, hR', h'⟩
  cases op <;> unfold opS
  case insertFirst =>
    rw [Machine.wp_seq]
    refine wp_assign_g 0 rfl (fun s1 hl1 hm1 hc1 => ?_)
    obtain ⟨om', hins, -, -, hwp⟩ := insertW_ok (h.congr hm1 hc1) hI (hx := none) hv
      (by
        rw [hl1]
        simp [Machine.State.upd, b2n]) (fun x e => by cases e)
    have hap : om.apply proofParams .insertFirst = .ok (.inserted, om') := by
      simp only [OrderMaintenance.apply, bind, Except.bind, hins]; rfl
    exact Machine.wp_mono (fun m' _ ⟨h', _, _⟩ => fin (ReachW.step hR hv hap) h') hwp
  case insertAfter x =>
    rw [Machine.wp_seq]
    refine wp_assign_g 1 rfl (fun s1 hl1 hm1 hc1 => ?_)
    rw [Machine.wp_seq]
    refine wp_assign_g x rfl (fun s2 hl2 hm2 hc2 => ?_)
    obtain ⟨om', hins, -, -, hwp⟩ := insertW_ok ((h.congr hm1 hc1).congr hm2 hc2) hI (hx := some
      x) hv
      (by
        rw [hl2, hl1]
        simp [Machine.State.upd, b2n]) (fun x' e => by
        cases e; rw [hl2]; simp [Machine.State.upd])
    have hap : om.apply proofParams (.insertAfter x) = .ok (.inserted, om') := by
      simp only [OrderMaintenance.apply, bind, Except.bind, hins]; rfl
    exact Machine.wp_mono (fun m' _ ⟨h', _, _⟩ => fin (ReachW.step hR hv hap) h') hwp
  case delete x =>
    rw [Machine.wp_seq]
    refine wp_assign_g x rfl (fun s1 hl1 hm1 hc1 => ?_)
    obtain ⟨om', hdel, -, -, hwp⟩ := deleteW_ok (h.congr hm1 hc1) hI hv
      (by
        rw [hl1]
        simp [Machine.State.upd])
    have hap : om.apply proofParams (.delete x) = .ok (.deleted, om') := by
      simp only [OrderMaintenance.apply, bind, Except.bind, hdel]; rfl
    exact Machine.wp_mono (fun m' _ ⟨h', _⟩ => fin (ReachW.step hR hv hap) h') hwp
  case order x y =>
    rw [Machine.wp_seq]
    refine wp_assign_g x rfl (fun s1 hl1 hm1 hc1 => ?_)
    rw [Machine.wp_seq]
    refine wp_assign_g y rfl (fun s2 hl2 hm2 hc2 => ?_)
    obtain ⟨ho, hwp⟩ := orderW_okM ((h.congr hm1 hc1).congr hm2 hc2) hI hv.1 hv.2
      (by
        rw [hl2, hl1]
        simp [Machine.State.upd]) (by
          rw [hl2]
          simp [Machine.State.upd])
    have hap : om.apply proofParams (.order x y) = .ok (.bool (OrderMaintenance.Spec.precedes
      Sp.list x y), om) := by
      simp only [OrderMaintenance.apply, bind, Except.bind, ho]; rfl
    exact Machine.wp_mono (fun m' _ ⟨h', _, _⟩ => ⟨om, p, ReachW.step hR hv hap, h'⟩) hwp

/-! ### The run -/

/-- **The threading**: after a valid sequence, the machine state holds a wrapper state reached by
initialization and all the operations so far. -/
theorem run_reachW {KB : Nat} (h4 : 4 ≤ KB) : ∀ (ops : List OrderMaintenance.Spec.Op) {t : Nat}
  {om : OrderMaintenance}
    {Sp : OrderMaintenance.Spec.State} {m : State} {p : Nat}, ReachW KB t om Sp → WEnc om m p →
      OrderMaintenance.Spec.Valid Sp ops →
    ∃ om' p', ReachW KB (t + ops.length) om' (OrderMaintenance.Spec.final Sp ops) ∧ WEnc om'
      (runSt m ops) p'
  | [], _, _, _, _, _, hR, h, _ => ⟨_, _, hR, h⟩
  | op :: ops, t, _, Sp, m, _, hR, h, ⟨hv, hvs⟩ => by
    obtain ⟨-, om', p', hR', h'⟩ := step_reachW h4 hR h hv
    obtain ⟨om'', p'', hR'', h''⟩ := run_reachW h4 ops hR' h' hvs
    refine ⟨om'', p'', ?_, h''⟩
    have e : t + (op :: ops).length = t + 1 + ops.length := by simp; omega
    rw [e]; exact hR''

theorem valid_take : ∀ (ops : List OrderMaintenance.Spec.Op) (Sp : OrderMaintenance.Spec.State)
  (i : Nat), OrderMaintenance.Spec.Valid Sp ops →
    OrderMaintenance.Spec.Valid Sp (ops.take i)
  | [], _, _, _ => by simp [OrderMaintenance.Spec.Valid]
  | _ :: _, _, 0, _ => trivial
  | op :: ops, Sp, i + 1, ⟨hv, hvs⟩ => ⟨hv, valid_take ops _ i hvs⟩

/-- Operation `i` of a valid sequence is valid in the specification state before it. -/
theorem valid_get : ∀ (ops : List OrderMaintenance.Spec.Op) (Sp : OrderMaintenance.Spec.State)
  (i : Nat) (hi : i < ops.length),
    OrderMaintenance.Spec.Valid Sp ops → ops[i].Valid (OrderMaintenance.Spec.final Sp (ops.take i))
  | [], _, _, hi, _ => by simp at hi
  | _ :: _, _, 0, _, ⟨hv, _⟩ => hv
  | op :: ops, Sp, i + 1, hi, ⟨_, hvs⟩ => valid_get ops _ i (by simpa using hi) hvs

/-- **Initialization reaches `ReachW`**, the wrapper state in slot 0. -/
theorem init_reachW {m : State} {KB : Nat} (hkb : m.loc "kb" = KB) (h4 : 4 ≤ KB) :
    ∃ om, ReachW KB 0 om OrderMaintenance.Spec.State.empty ∧ WEnc om (exec initWS m).st 0 := by
  obtain ⟨om, hinit, -, hwp⟩ := initW_ok hkb h4
  exact ⟨om, ReachW.init hinit, hwp.2.1⟩

/-- **The state before each operation**: operation `i` is valid there, and the machine state
before it holds a wrapper state reached by initialization and the first `i` operations. -/
theorem before_reachW {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops) (i : Nat) (hi : i < ops.length) :
    ops[i].Valid (OrderMaintenance.Spec.final OrderMaintenance.Spec.State.empty (ops.take i)) ∧
      ∃ om p,
      ReachW KB i om (OrderMaintenance.Spec.final OrderMaintenance.Spec.State.empty (ops.take i)) ∧
      WEnc om (runSt (exec initWS m₀).st (ops.take i)) p := by
  refine ⟨valid_get ops _ i hi hv, ?_⟩
  obtain ⟨om, hR, h⟩ := init_reachW hkb h4
  obtain ⟨om', p', hR', h'⟩ := run_reachW h4 (ops.take i) hR h (valid_take ops _ i hv)
  refine ⟨om', p', ?_, h'⟩
  have e : 0 + (ops.take i).length = i := by simp; omega
  rw [e] at hR'; exact hR'

/-! ### The final theorem -/

/-- **Theorems A, B and W at Level M.** For `4 ≤ K_B < 2^512` (in local `kb`) and every valid
operation sequence: the machine program returns exactly the specification's answers within the
step bounds of `theoremAB_M`; initialization computes no value at or above `2^1029`; and the
machine code of operation `i`, run from the machine state before it, computes no value at or
above `2^(2·(wKom om + 128) + 5) + 2·(i + 1)`, where `om` is the wrapper state held by that machine
state, reached by initialization and the first `i` operations (`wKom om = 64·L`, `L` the larger
`max(8, ⌊log₂ N⌋ + 1)` of its cores). -/
theorem theoremABW_M {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 : KB <
  2 ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops) :
    ((exec initWS m₀).status = .ok ∧ (exec initWS m₀).cost ≤ initB ∧
      ∃ cs, runM (exec initWS m₀).st ops = some (OrderMaintenance.Spec.run
        OrderMaintenance.Spec.State.empty ops, cs) ∧
        ∀ c ∈ cs, c ≤ opB KB) ∧
    dpk initWS m₀ < 2 ^ 1029 ∧
    ∀ i (hi : i < ops.length), ∃ om p,
      ReachW KB i om (OrderMaintenance.Spec.final OrderMaintenance.Spec.State.empty (ops.take i)) ∧
      WEnc om (runSt (exec initWS m₀).st (ops.take i)) p ∧
      dpk (opS ops[i]) (runSt (exec initWS m₀).st (ops.take i)) < 2 ^ (2 * (wKom om + 128) + 5)
        + 2 * (i + 1) := by
  refine ⟨theoremAB_M hkb h4 ops hv, theoremW_init hkb h512, fun i hi => ?_⟩
  obtain ⟨hvi, om, p, hR, h⟩ := before_reachW hkb h4 ops hv i hi
  exact ⟨om, p, hR, h, theoremW_op h4 h512 hR h hvi⟩

end OrderMaintenance.Impl

/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.InitM


/-!
# M6: Theorems A and B at Level M

The machine program: `initWS` once (with `K_B` in local `kb`), then `opS op` for each operation.
An operation's arguments are put in locals by `opS`; an order query leaves its answer in local `r`.

* `init_reach`: initialization reaches a state holding Level F's initial state with the invariant.
* `step_reach`: from such a state, each valid operation returns the specification's answer and
  reaches such a state again, in at most `opB K_B` machine steps.
* `theoremAB_M`: for every valid operation sequence, the machine returns `Spec.run`'s answers, and
  every operation takes at most `opB K_B` steps. `opB K_B` depends on `K_B` alone: not on `N`, the
  number of live elements, or the history.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-- The machine code of one operation, its arguments as literals. -/
def opS : OrderMaintenance.Spec.Op → Stmt
  | .insertFirst => .seq (.assign "hx" (.lit 0)) insertWS
  | .insertAfter x => .seq (.assign "hx" (.lit 1)) (.seq (.assign "x" (.lit x)) insertWS)
  | .delete x => .seq (.assign "x" (.lit x)) deleteWS
  | .order x y => .seq (.assign "x" (.lit x)) (.seq (.assign "y" (.lit y)) orderWS)

/-- The answer of an operation, read from the machine state after it. -/
def ansOf : OrderMaintenance.Spec.Op → State → OrderMaintenance.Spec.Ans
  | .insertFirst, _ => .inserted
  | .insertAfter _, _ => .inserted
  | .delete _, _ => .deleted
  | .order _ _, m => .bool (decide (m.loc "r" ≠ 0))

/-- **The bound on one operation's machine steps.** -/
def opB (KB : Nat) : Nat := insW KB + delW KB + 200

/-- A machine state holding a wrapper state with the Level M invariant for `Sp`, and `K_B`. -/
def Reach (KB : Nat) (m : State) (Sp : OrderMaintenance.Spec.State) : Prop :=
  ∃ om p, WEnc om m p ∧ MInv om Sp ∧ om.KB = KB

theorem reach_of {KB : Nat} {om : OrderMaintenance} {m : State} {Sp :
  OrderMaintenance.Spec.State} (h : WEnc om m 0 ∨ WEnc om m 1)
    (hI : MInv om Sp) (hK : om.KB = KB) : Reach KB m Sp := by
  rcases h with h | h
  · exact ⟨om, 0, h, hI, hK⟩
  · exact ⟨om, 1, h, hI, hK⟩

/-- **Initialization.** -/
theorem init_reach {m : State} {KB : Nat} (hkb : m.loc "kb" = KB) (h4 : 4 ≤ KB) :
    wp initWS (fun m' k => Reach KB m' OrderMaintenance.Spec.State.empty ∧ k ≤ initB) m := by
  obtain ⟨om, hinit, hI, hwp⟩ := initW_ok hkb h4
  have hK : om.KB = KB := by
    unfold OrderMaintenance.init at hinit
    simp only [bind, Except.bind] at hinit
    split at hinit
    · cases hinit
    · injection hinit with h; rw [← h]
  exact Machine.wp_mono (fun m' k ⟨h, hk⟩ => ⟨⟨om, 0, h, hI, hK⟩, hk⟩) hwp

/-- **One operation**: the specification's answer, the invariant again, at most `opB K_B` steps. -/
theorem step_reach {KB : Nat} {m : State} {Sp : OrderMaintenance.Spec.State} (hR : Reach KB m
  Sp) {op : OrderMaintenance.Spec.Op}
    (hv : op.Valid Sp) :
    wp (opS op) (fun m' k => Reach KB m' (OrderMaintenance.Spec.step Sp op).1 ∧ ansOf op m' =
      (OrderMaintenance.Spec.step Sp op).2 ∧
      k ≤ opB KB) m := by
  obtain ⟨om, p, h, hI, hK⟩ := hR
  cases op <;> unfold opS
  case insertFirst =>
    rw [Machine.wp_seq]
    refine wp_assign_g 0 rfl (fun s1 hl1 hm1 hc1 => ?_)
    obtain ⟨om', -, hI', hK', hwp⟩ := insertW_ok (h.congr hm1 hc1) hI (hx := none) hv
      (by
        rw [hl1]
        simp [Machine.State.upd, b2n]) (fun x e => by cases e)
    refine Machine.wp_mono (fun m' k ⟨h', _, hk⟩ => ⟨reach_of h' hI' (hK'.trans hK), rfl, ?_⟩) hwp
    rw [hK] at hk; unfold opB; simp only [Expr.cost] at hk ⊢; omega
  case insertAfter x =>
    rw [Machine.wp_seq]
    refine wp_assign_g 1 rfl (fun s1 hl1 hm1 hc1 => ?_)
    rw [Machine.wp_seq]
    refine wp_assign_g x rfl (fun s2 hl2 hm2 hc2 => ?_)
    obtain ⟨om', -, hI', hK', hwp⟩ := insertW_ok ((h.congr hm1 hc1).congr hm2 hc2) hI (hx :=
      some x) hv
      (by
        rw [hl2, hl1]
        simp [Machine.State.upd, b2n]) (fun x' e => by
        cases e; rw [hl2]; simp [Machine.State.upd])
    refine Machine.wp_mono (fun m' k ⟨h', _, hk⟩ => ⟨reach_of h' hI' (hK'.trans hK), rfl, ?_⟩) hwp
    rw [hK] at hk; unfold opB; simp only [Expr.cost] at hk ⊢; omega
  case delete x =>
    rw [Machine.wp_seq]
    refine wp_assign_g x rfl (fun s1 hl1 hm1 hc1 => ?_)
    obtain ⟨om', -, hI', hK', hwp⟩ := deleteW_ok (h.congr hm1 hc1) hI hv
      (by
        rw [hl1]
        simp [Machine.State.upd])
    refine Machine.wp_mono (fun m' k ⟨h', hk⟩ => ⟨reach_of h' hI' (hK'.trans hK), rfl, ?_⟩) hwp
    rw [hK] at hk; unfold opB; simp only [Expr.cost] at hk ⊢; omega
  case order x y =>
    rw [Machine.wp_seq]
    refine wp_assign_g x rfl (fun s1 hl1 hm1 hc1 => ?_)
    rw [Machine.wp_seq]
    refine wp_assign_g y rfl (fun s2 hl2 hm2 hc2 => ?_)
    obtain ⟨-, hwp⟩ := orderW_okM ((h.congr hm1 hc1).congr hm2 hc2) hI hv.1 hv.2
      (by
        rw [hl2, hl1]
        simp [Machine.State.upd]) (by
          rw [hl2]
          simp [Machine.State.upd])
    refine Machine.wp_mono (fun m' k ⟨h', hr, hk⟩ => ⟨⟨om, p, h', hI, hK⟩, ?_, ?_⟩) hwp
    · change OrderMaintenance.Spec.Ans.bool (decide (m'.loc "r" ≠ 0)) =
        OrderMaintenance.Spec.Ans.bool (OrderMaintenance.Spec.precedes Sp.list x y)
      rw [hr]; cases OrderMaintenance.Spec.precedes Sp.list x y <;> rfl
    · unfold opB; simp only [Expr.cost] at hk ⊢; omega

/-- The machine run over a sequence of operations: the answers and the cost of each operation
(`none` if an operation fails or reaches an error). -/
def runM : State → List OrderMaintenance.Spec.Op → Option (List OrderMaintenance.Spec.Ans × List
  Nat)
  | _, [] => some ([], [])
  | m, op :: ops =>
    if (exec (opS op) m).status = .ok then
      (runM (exec (opS op) m).st ops).map fun r => (ansOf op (exec (opS op) m).st :: r.1, (exec
        (opS op) m).cost :: r.2)
    else none

theorem run_reach {KB : Nat} : ∀ (ops : List OrderMaintenance.Spec.Op) (Sp :
  OrderMaintenance.Spec.State) (m : State), Reach KB m Sp →
    OrderMaintenance.Spec.Valid Sp ops → ∃ cs, runM m ops = some (OrderMaintenance.Spec.run Sp
      ops, cs) ∧ ∀ c ∈ cs, c ≤ opB KB
  | [], _, _, _, _ => ⟨[], rfl, fun _ h => by cases h⟩
  | op :: ops, Sp, m, hR, ⟨hv, hvs⟩ => by
    obtain ⟨hst, hR', hans, hk⟩ := step_reach hR hv
    obtain ⟨cs, hrun, hcs⟩ := run_reach ops _ _ hR' hvs
    refine ⟨(exec (opS op) m).cost :: cs, ?_, ?_⟩
    · simp only [runM, hst, ite_true, hrun, Option.map_some, hans]; rfl
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hk
      · exact hcs c hc

/-- **Theorems A and B at Level M.** For `K_B ≥ 4` (in local `kb`) and every valid operation
sequence, the machine program returns exactly the specification's answers; initialization takes
at most `initB` steps and each operation at most `opB K_B` steps. -/
theorem theoremAB_M {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid
      OrderMaintenance.Spec.State.empty ops) :
    (exec initWS m₀).status = .ok ∧ (exec initWS m₀).cost ≤ initB ∧
      ∃ cs, runM (exec initWS m₀).st ops = some (OrderMaintenance.Spec.run
        OrderMaintenance.Spec.State.empty ops, cs) ∧
        ∀ c ∈ cs, c ≤ opB KB := by
  obtain ⟨hst, hR, hk⟩ := init_reach hkb h4
  exact ⟨hst, hk, run_reach ops _ _ hR hv⟩

/-! ### The constants -/

theorem insB_eq : insB = 94462311 := by rw [← insBound_proof 0]; rfl

/-- **The constant of Theorem B** for the proof parameters' `K_B = 4`. -/
theorem opB_four : opB 4 = 1133561742 := by
  unfold opB insW delW rebB iterB; rw [insB_eq]

theorem initB_eq : initB = 6648 := by rfl

end OrderMaintenance.Impl

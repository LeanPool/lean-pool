/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.SlotFrame
public import LeanPool.OrderMaintenance.Machine.Logic


/-!
# M6: calling a compiled core procedure from wrapper code

`wp_coreCall`: if machine state `m` holds core `s` in slot `p`, a `call` of the compiled body of a
core procedure ends as `evalF` says: the slot holds the resulting core, the results are copied
back, the cost is the source's plus the call's overhead, and every array outside slot `p` is
unchanged.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same exec_frame wp)

/-- **A call of a compiled core procedure.** -/
theorem wp_coreCall {p : Nat} {κ : Caps} {s : Core} {m : State} (h : Enc p κ s m)
    {nm : String} {ps rs ds : List Reg} {body : Stm} {args : List OrderMaintenance.Machine.Expr}
    {vs : List Nat}
    (hargs : OrderMaintenance.Machine.evalList m args = some vs)
    {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF κ body s (Machine.State.setLocs (fun _ => 0) ps vs) = .ok s' L' n)
    {Q : State → Nat → Prop}
    (hQ : ∀ m', Enc p κ s' m' → (∀ b, ¬ InSlot p b → Same b m m') →
      m'.loc = Machine.State.setLocs m.loc ds (rs.map L') →
      Q m' (1 + OrderMaintenance.Machine.costList args + ds.length + n)) :
    wp (.call nm ps (body.compile p κ) rs args ds) Q m := by
  rw [OrderMaintenance.Machine.wp_call]
  refine ⟨vs, hargs, ?_⟩
  set m0 := (m.bump (OrderMaintenance.Machine.maxvList m args)).enter ps vs
  have h0 : Enc p κ s m0 := (h.bump _).withLoc _
  have hA := sim body h0 rfl
  have hl : m0.loc = Machine.State.setLocs (fun _ => 0) ps vs := rfl
  rw [hl, he] at hA
  obtain ⟨hst, hE, hL, hc⟩ := hA
  unfold wp OrderMaintenance.Machine.Out.Ok
  refine ⟨hst, ?_⟩
  rw [hc]
  refine hQ _ ((hE.withLoc _)) (fun b hb => ?_) (by simp [Machine.State.leave, hL])
  have := compile_frame p κ body m0 hb
  exact ⟨this.1, this.2⟩

end OrderMaintenance.Impl

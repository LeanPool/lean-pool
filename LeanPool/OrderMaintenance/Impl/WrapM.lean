/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.NewCore
public import LeanPool.OrderMaintenance.Proof.Top.Setup


/-!
# M6: the wrapper as machine code

**Layout.** The cores live in slots 0 and 1 (arrays `1000·p + code`); the wrapper's own arrays
are numbered from 2000, outside both slots:
* one cell each: `wa 0` parity (the slot of `cur`), `wa 1` whether `nxt` exists, `wa 2` cursor,
  `wa 3` cursorSet, `wa 4` live, `wa 5` nextHandle, `wa 6` rebuilds, `wa 7` `K_B`;
* the handle maps `wIdx q` (`q` = 0, 1): `curIdx` in `wIdx p`, `nxtIdx` in `wIdx (1 - p)`.

`WEnc om m p` says that machine state `m` holds wrapper state `om` with `cur` in slot `p`.
The wrapper code tests the parity and runs the code specialized to it.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

def wa (k : Nat) : Arr := 2000 + k
def wIdx (q : Nat) : Arr := 2010 + q

theorem wa_notSlot {p k : Nat} (hp : p < 2) : ¬ InSlot p (wa k) := by
  unfold InSlot wa; omega
theorem wIdx_notSlot {p q : Nat} (hp : p < 2) : ¬ InSlot p (wIdx q) := by
  unfold InSlot wIdx; omega

/-- **The encoding of the wrapper state.** -/
structure WEnc (om : OrderMaintenance) (m : State) (p : Nat) : Prop where
  p2 : p < 2
  scap : ∀ k < 8, m.cap (wa k) = 1
  par : m.mem (wa 0) 0 = p
  nxtOn : m.mem (wa 1) 0 = b2n om.nxt.isSome
  cursor : m.mem (wa 2) 0 = om.cursor
  cset : m.mem (wa 3) 0 = b2n om.cursorSet
  live : m.mem (wa 4) 0 = om.live
  next : m.mem (wa 5) 0 = om.nextHandle
  reb : m.mem (wa 6) 0 = om.rebuilds
  kb : m.mem (wa 7) 0 = om.KB
  cur : Enc p (capsOf om.cur.P) om.cur m
  nxt : ∀ n, om.nxt = some n → Enc (1 - p) (capsOf n.P) n m
  idxC : ∀ h < m.cap (wIdx p), m.mem (wIdx p) h = om.curIdx.getX h
  idxN : om.nxt.isSome → ∀ h < m.cap (wIdx (1 - p)), m.mem (wIdx (1 - p)) h = om.nxtIdx.getX h
  roomC : om.nextHandle + (om.cur.P.N - om.cur.count) ≤ m.cap (wIdx p)
  roomN : ∀ n, om.nxt = some n →
    om.nextHandle + (om.cur.P.N - om.cur.count) + (n.P.N - n.count) ≤ m.cap (wIdx (1 - p))

/-- The wrapper state survives anything that keeps slot `p`'s core, the other slot, and the
wrapper's arrays. -/
theorem WEnc.of_slot {om : OrderMaintenance} {m m' : State} {p : Nat} (h : WEnc om m p)
    (hcur : Enc p (capsOf om.cur.P) om.cur m') (hS : ∀ b, ¬ InSlot p b → Same b m m') : WEnc om m' p := by
  have hp := h.p2
  have hw : ∀ k, Same (wa k) m m' := fun k => hS _ (wa_notSlot hp)
  have hi : ∀ q, Same (wIdx q) m m' := fun q => hS _ (wIdx_notSlot hp)
  refine ⟨hp, fun k hk => by rw [(hw k).2]; exact h.scap k hk, by rw [(hw 0).1]; exact h.par,
    by rw [(hw 1).1]; exact h.nxtOn, by rw [(hw 2).1]; exact h.cursor, by rw [(hw 3).1]; exact h.cset,
    by rw [(hw 4).1]; exact h.live, by rw [(hw 5).1]; exact h.next, by rw [(hw 6).1]; exact h.reb,
    by rw [(hw 7).1]; exact h.kb, hcur, fun n hn => ?_, fun x hx => ?_, fun hn x hx => ?_, ?_, fun n hn => ?_⟩
  · exact (h.nxt n hn).of_same fun b hb => hS b (fun hpb => inSlot_disj (by omega) hpb hb)
  · rw [(hi p).2] at hx; rw [(hi p).1]; exact h.idxC x hx
  · rw [(hi (1 - p)).2] at hx; rw [(hi (1 - p)).1]; exact h.idxN hn x hx
  · rw [(hi p).2]; exact h.roomC
  · rw [(hi (1 - p)).2]; exact h.roomN n hn

theorem WEnc.bump {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (v : Nat) : WEnc om (m.bump v) p :=
  h.of_slot (h.cur.bump v) fun _ _ => ⟨rfl, rfl⟩
theorem WEnc.setLoc {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (x : Reg) (v : Nat) :
    WEnc om (m.setLoc x v) p :=
  h.of_slot (h.cur.setLoc x v) fun _ _ => ⟨rfl, rfl⟩

/-- The parity test. -/
def parE : Expr := .bin .eq (.load (wa 0) (.lit 0)) (.lit 0)

/-- Run the code specialized to the parity. -/
def byPar (c : Nat → Stmt) : Stmt := .ite parE (c 0) (c 1)

theorem wp_byPar {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {c : Nat → Stmt} {Q : State → Nat → Prop}
    (hc : wp (c p) (fun s' n => Q s' (1 + parE.cost + n)) (m.bump (parE.maxv m))) : wp (byPar c) Q m := by
  unfold byPar
  rw [OrderMaintenance.Machine.wp_ite]
  have hev : parE.eval m = some (if p = 0 then 1 else 0) := by
    simp [parE, Expr.eval, h.scap 0 (by omega), h.par, BinOp.eval]
  refine ⟨_, hev, ?_⟩
  have := h.p2
  by_cases hp : p = 0
  · subst hp; simpa using hc
  · have : p = 1 := by omega
    subst this; simpa using hc

/-! ### Order queries -/

/-- Order of the handles in locals `x`, `y`; the answer in local `r`. -/
def orderC (p : Nat) : Stmt :=
  .seq (.assign "xi" (.load (wIdx p) (.var "x"))) (.seq (.assign "yi" (.load (wIdx p) (.var "y")))
    (.call "order" ["x", "y"] (orderP.body.compile p κ₀) ["r"] [.var "xi", .var "yi"] ["r"]))

def orderWS : Stmt := byPar orderC

theorem order_run_state {x y : Nat} {s s' : Core} {b : Bool} (h : (OrderMaintenance.Model.order x y).run s = .ok b s') :
    s' = s := by
  unfold OrderMaintenance.Model.order OrderMaintenance.Model.key at h; simp [getE, getG, getC] at h; exact h.2.symm

/-- **An order query** at the machine level. -/
theorem orderW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {x y : Nat}
    (hx : m.loc "x" = x) (hy : m.loc "y" = y) (hxc : x < m.cap (wIdx p)) (hyc : y < m.cap (wIdx p))
    {P : Params} {n R : Nat} {L : List Nat} (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L om.cur)
    (hP : om.cur.P = P) (hxL : om.curIdx.getX x ∈ L) (hyL : om.curIdx.getX y ∈ L)
    (hcntL : om.cur.count = L.length) (hM : Mc (capsOf P) P om.cur) {b : Bool} {s' : Core}
    (hr : (OrderMaintenance.Model.order (om.curIdx.getX x) (om.curIdx.getX y)).run om.cur = .ok b s') :
    wp orderWS (fun m' c => WEnc om m' p ∧ m'.loc "r" = b2n b ∧ c ≤ 100) m := by
  have e := order_run_state hr; subst e
  refine wp_byPar h ?_
  set m0 := m.bump (parE.maxv m)
  have h0 := h.bump (parE.maxv m)
  unfold orderC
  rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
  refine ⟨om.curIdx.getX x, by simp [Expr.eval, m0, hx, hxc, h.idxC x hxc], ?_⟩
  rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
  set m1 := (m0.bump _).setLoc "xi" (om.curIdx.getX x)
  have h1 : WEnc om m1 p := (h0.bump _).setLoc _ _
  refine ⟨om.curIdx.getX y, by simp [Expr.eval, m1, m0, hy, hyc, h.idxC y hyc], ?_⟩
  set m2 := (m1.bump _).setLoc "yi" (om.curIdx.getX y)
  have h2 : WEnc om m2 p := (h1.bump _).setLoc _ _
  have hcur : Enc p (capsOf P) om.cur m2 := by rw [← hP]; exact h2.cur
  obtain ⟨L', c, he, hrr, hc⟩ := orderAgreeM hC hP hxL hyL (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x", "y"]
    [om.curIdx.getX x, om.curIdx.getX y]) (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (capsOf_ok P) hcntL hM hr
  rw [compile_κ₀ p P]
  refine wp_coreCall hcur (by simp [OrderMaintenance.Machine.evalList, Expr.eval, m2, m1]) he (fun m3 hE hS hL => ?_)
  refine ⟨h2.of_slot (by rw [hP]; exact hE) hS, by rw [hL]; simp [OrderMaintenance.Machine.State.setLocs, hrr], ?_⟩
  simp [OrderMaintenance.Machine.costList, Expr.cost, parE] at *; omega

/-! ### Writing the current handle map -/

/-- Writing `v` at handle `x` of the current handle map. -/
theorem WEnc.writeC {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {x v : Nat} (hx : x < m.cap (wIdx p)) :
    WEnc { om with curIdx := om.curIdx.setX x v } (m.write (wIdx p) x v) p := by
  have hp := h.p2
  have hne : ∀ k < 8, wa k ≠ wIdx p := fun k hk e => by
    have : (2000 + k : Nat) = 2010 + p := e
    omega
  have hq : wIdx (1 - p) ≠ wIdx p := fun e => by
    have : (2010 + (1 - p) : Nat) = 2010 + p := e
    omega
  refine ⟨hp, fun k hk => h.scap k hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.cur.of_same fun b hb => ⟨?_, rfl⟩, fun n hn => (h.nxt n hn).of_same fun b hb => ⟨?_, rfl⟩,
    fun i hi => ?_, fun hn i hi => ?_, h.roomC, h.roomN⟩
  all_goals simp only [State.write, OrderMaintenance.Machine.State.upd]
  · rw [ite_eq_right (hne 0 (by decide))]; exact h.par
  · rw [ite_eq_right (hne 1 (by decide))]; exact h.nxtOn
  · rw [ite_eq_right (hne 2 (by decide))]; exact h.cursor
  · rw [ite_eq_right (hne 3 (by decide))]; exact h.cset
  · rw [ite_eq_right (hne 4 (by decide))]; exact h.live
  · rw [ite_eq_right (hne 5 (by decide))]; exact h.next
  · rw [ite_eq_right (hne 6 (by decide))]; exact h.reb
  · rw [ite_eq_right (hne 7 (by decide))]; exact h.kb
  · funext i; rw [ite_eq_right (fun e => wIdx_notSlot hp (e ▸ hb))]
  · funext i; rw [ite_eq_right (fun e => wIdx_notSlot (p := 1 - p) (by omega) (e ▸ hb))]
  · simp only [ite_true, OrderMaintenance.Proof.Top.getX_setX']
    by_cases e : i = x
    · simp [e]
    · simp [e, h.idxC i hi]
  · rw [ite_eq_right hq]; exact h.idxN hn i hi

/-! ### Deletion -/

/-- Delete the element of handle `x` from `cur`. -/
def curDelC (p : Nat) : Stmt :=
  .seq (.assign "xi" (.load (wIdx p) (.var "x")))
  (.seq (.call "markDead" ["x"] (markDeadP.body.compile p κ₀) [] [.var "xi"] [])
    (.store (wIdx p) (.var "x") (.lit 0)))

theorem curDelW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {x : Nat}
    (hx : m.loc "x" = x) (hxc : x < m.cap (wIdx p))
    {P : Params} {n R : Nat} {L : List Nat} (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L om.cur)
    (hP : om.cur.P = P) (hxL : om.curIdx.getX x ∈ L) (hcntL : om.cur.count = L.length)
    (hM : Mc (capsOf P) P om.cur) {c' : Core} (hr : (markDead (om.curIdx.getX x)).run om.cur = .ok () c') :
    wp (curDelC p) (fun m' k => WEnc { om with cur := c', curIdx := om.curIdx.setX x 0 } m' p ∧
      m'.loc = OrderMaintenance.Machine.State.upd m.loc "xi" (om.curIdx.getX x) ∧ k ≤ 40) m := by
  obtain ⟨s', hr', ⟨L', c, he, hc⟩, -, hcnt', hP', -⟩ := markDeadAgreeM hC hP hxL
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x"] [om.curIdx.getX x])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (capsOf_ok P) hcntL hM
  rw [hr] at hr'; obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr'
  unfold curDelC
  rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
  refine ⟨om.curIdx.getX x, by simp [Expr.eval, hx, hxc, h.idxC x hxc], ?_⟩
  set m1 := (m.bump _).setLoc "xi" (om.curIdx.getX x)
  have h1 : WEnc om m1 p := (h.bump _).setLoc _ _
  rw [OrderMaintenance.Machine.wp_seq, compile_κ₀ p P]
  have hcur : Enc p (capsOf P) om.cur m1 := by rw [← hP]; exact h1.cur
  refine wp_coreCall hcur (by simp [OrderMaintenance.Machine.evalList, Expr.eval, m1]) he (fun m2 hE hS hL => ?_)
  have h2 : WEnc { om with cur := c' } m2 p := by
    have hE' : Enc p (capsOf c'.P) c' m2 := by rw [hP', hP]; exact hE
    refine ⟨h1.p2, fun k hk => by rw [(hS _ (wa_notSlot h1.p2)).2]; exact h1.scap k hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hE', fun n hn => (h1.nxt n hn).of_same fun b hb => hS b (fun hpb => inSlot_disj (by have := h1.p2; omega) hpb hb),
      fun i hi => ?_, fun hn i hi => ?_, ?_, fun n hn => ?_⟩
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.par
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.nxtOn
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.cursor
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.cset
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.live
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.next
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.reb
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.kb
    · rw [(hS _ (wIdx_notSlot h1.p2)).2] at hi; rw [(hS _ (wIdx_notSlot h1.p2)).1]; exact h1.idxC i hi
    · rw [(hS _ (wIdx_notSlot h1.p2)).2] at hi; rw [(hS _ (wIdx_notSlot h1.p2)).1]; exact h1.idxN hn i hi
    · rw [(hS _ (wIdx_notSlot h1.p2)).2]; show _ + (c'.P.N - c'.count) ≤ _; rw [hP', hcnt']; exact h1.roomC
    · rw [(hS _ (wIdx_notSlot h1.p2)).2]; show _ + (c'.P.N - c'.count) + _ ≤ _; rw [hP', hcnt']; exact h1.roomN n hn
  rw [OrderMaintenance.Machine.wp_store]
  have hxc2 : x < m2.cap (wIdx p) := by rw [(hS _ (wIdx_notSlot h1.p2)).2]; exact hxc
  refine ⟨x, 0, by simp [Expr.eval, hL, OrderMaintenance.Machine.State.setLocs, m1, hx], rfl, hxc2, ?_⟩
  refine ⟨(h2.bump _ |>.bump _).writeC (by simpa using hxc2), by simp [hL, OrderMaintenance.Machine.State.setLocs, m1], ?_⟩
  simp [OrderMaintenance.Machine.costList, Expr.cost] at *; omega

/-! ### The next core -/

/-- The next core changes (in its slot), with the same parameters and count. -/
theorem WEnc.of_nxt {om : OrderMaintenance} {m m' : State} {p : Nat} (h : WEnc om m p) {n n' : Core} (hn : om.nxt = some n)
    (hE : Enc (1 - p) (capsOf n'.P) n' m') (hS : ∀ b, ¬ InSlot (1 - p) b → Same b m m')
    (hcnt : n'.count = n.count) (hP : n'.P = n.P) : WEnc { om with nxt := some n' } m' p := by
  have hp := h.p2
  have hp' : 1 - p < 2 := by omega
  have hw : ∀ k, Same (wa k) m m' := fun k => hS _ (wa_notSlot hp')
  have hi : ∀ q, Same (wIdx q) m m' := fun q => hS _ (wIdx_notSlot hp')
  refine ⟨hp, fun k hk => by rw [(hw k).2]; exact h.scap k hk, by rw [(hw 0).1]; exact h.par,
    by rw [(hw 1).1, h.nxtOn,
      hn]; rfl, by rw [(hw 2).1]; exact h.cursor, by rw [(hw 3).1]; exact h.cset,
    by rw [(hw 4).1]; exact h.live, by rw [(hw 5).1]; exact h.next, by rw [(hw 6).1]; exact h.reb,
    by rw [(hw 7).1]; exact h.kb, h.cur.of_same fun b hb => hS b (fun hpb => inSlot_disj (by omega) hpb hb),
    fun n2 hn2 => ?_, fun x hx => ?_, fun _ x hx => ?_, ?_, fun n2 hn2 => ?_⟩
  · cases hn2; exact hE
  · rw [(hi p).2] at hx; rw [(hi p).1]; exact h.idxC x hx
  · rw [(hi (1 - p)).2] at hx; rw [(hi (1 - p)).1]; exact h.idxN (by rw [hn]; rfl) x hx
  · rw [(hi p).2]; exact h.roomC
  · cases hn2; rw [(hi (1 - p)).2]; show _ + (n'.P.N - n'.count) ≤ _; rw [hcnt, hP]; exact h.roomN n hn

/-- Writing `v` at handle `x` of the next handle map. -/
theorem WEnc.writeN {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {x v : Nat}
    (hx : x < m.cap (wIdx (1 - p))) :
    WEnc { om with nxtIdx := om.nxtIdx.setX x v } (m.write (wIdx (1 - p)) x v) p := by
  have hp := h.p2
  have hne : ∀ k < 8, wa k ≠ wIdx (1 - p) := fun k hk e => by
    have : (2000 + k : Nat) = 2010 + (1 - p) := e
    omega
  have hq : wIdx p ≠ wIdx (1 - p) := fun e => by
    have : (2010 + p : Nat) = 2010 + (1 - p) := e
    omega
  refine ⟨hp, fun k hk => h.scap k hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.cur.of_same fun b hb => ⟨?_, rfl⟩, fun n hn => (h.nxt n hn).of_same fun b hb => ⟨?_, rfl⟩,
    fun i hi => ?_, fun hn i hi => ?_, h.roomC, h.roomN⟩
  all_goals simp only [State.write, OrderMaintenance.Machine.State.upd]
  · rw [ite_eq_right (hne 0 (by decide))]; exact h.par
  · rw [ite_eq_right (hne 1 (by decide))]; exact h.nxtOn
  · rw [ite_eq_right (hne 2 (by decide))]; exact h.cursor
  · rw [ite_eq_right (hne 3 (by decide))]; exact h.cset
  · rw [ite_eq_right (hne 4 (by decide))]; exact h.live
  · rw [ite_eq_right (hne 5 (by decide))]; exact h.next
  · rw [ite_eq_right (hne 6 (by decide))]; exact h.reb
  · rw [ite_eq_right (hne 7 (by decide))]; exact h.kb
  · funext i; rw [ite_eq_right (fun e => wIdx_notSlot hp (e ▸ hb))]
  · funext i; rw [ite_eq_right (fun e => wIdx_notSlot (p := 1 - p) (by omega) (e ▸ hb))]
  · rw [ite_eq_right hq]; exact h.idxC i hi
  · simp only [ite_true, OrderMaintenance.Proof.Top.getX_setX']
    by_cases e : i = x
    · simp [e]
    · simp [e, h.idxN hn i hi]

/-! ### Mirroring a deletion into `nxt` -/

def mirrorDelC (p : Nat) : Stmt :=
  .ite (.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)) .skip
    (.seq (.assign "xn" (.load (wIdx (1 - p)) (.var "x")))
      (.ite (.bin .eq (.var "xn") (.lit 0)) .skip
        (.seq (.call "markDead" ["x"] (markDeadP.body.compile (1 - p) κ₀) [] [.var "xn"] [])
          (.store (wIdx (1 - p)) (.var "x") (.lit 0)))))

/-- The core facts a deletion from `nxt` needs. -/
def DelOK (n : Core) (xn : Nat) : Prop :=
  ∃ (P : Params) (nn R : Nat) (L : List Nat), CostInv (TIat TopInv P) topMu (topJ P) nn R L n ∧ n.P = P ∧
    xn ∈ L ∧ n.count = L.length ∧ Mc (capsOf P) P n

theorem mirrorDelW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {x : Nat}
    (hx : m.loc "x" = x) (hxc : om.nxt.isSome → x < m.cap (wIdx (1 - p)))
    (hN : ∀ n, om.nxt = some n → om.nxtIdx.getX x ≠ 0 → DelOK n (om.nxtIdx.getX x))
    {om2 : OrderMaintenance} (hr : om.mirrorDelete x = .ok om2) :
    wp (mirrorDelC p) (fun m' k => WEnc om2 m' p ∧ m'.loc "x" = x ∧ k ≤ 50) m := by
  have hp := h.p2
  unfold mirrorDelC
  rw [OrderMaintenance.Machine.wp_ite]
  cases hn : om.nxt with
  | none =>
    have : om2 = om := by unfold OrderMaintenance.mirrorDelete at hr; rw [hn] at hr; cases hr; rfl
    subst this
    refine ⟨1, by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n], ?_⟩
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true, OrderMaintenance.Machine.wp_skip]
    exact ⟨h.bump _, by simp [hx], by simp [Expr.cost]⟩
  | some n =>
    refine ⟨0, by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n], ?_⟩
    simp only [ne_eq, not_true_eq_false, ite_false]
    have hxc' := hxc (by rw [hn]; rfl)
    rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
    refine ⟨om.nxtIdx.getX x, by simp [Expr.eval, hx, hxc', h.idxN (by rw [hn]; rfl) x hxc'], ?_⟩
    set m1 := ((m.bump _).bump _).setLoc "xn" (om.nxtIdx.getX x)
    have h1 : WEnc om m1 p := ((h.bump _).bump _).setLoc _ _
    rw [OrderMaintenance.Machine.wp_ite]
    by_cases h0 : om.nxtIdx.getX x = 0
    · have : om2 = om := by
        unfold OrderMaintenance.mirrorDelete at hr; rw [hn] at hr; simp [h0] at hr
        cases hr; rfl
      subst this
      refine ⟨1, by simp [Expr.eval, m1, h0, BinOp.eval], ?_⟩
      simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true, OrderMaintenance.Machine.wp_skip]
      exact ⟨h1.bump _, by simp [m1, hx], by simp [Expr.cost]⟩
    · refine ⟨0, by simp [Expr.eval, m1, h0, BinOp.eval], ?_⟩
      simp only [ne_eq, not_true_eq_false, ite_false]
      obtain ⟨P, nn, R, L, hC, hP, hxL, hcntL, hM⟩ := hN n hn h0
      obtain ⟨n', hr', ⟨L', c, he, hc⟩, -, hcnt', hP', -⟩ := markDeadAgreeM hC hP hxL
        (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x"] [om.nxtIdx.getX x])
        (by simp [OrderMaintenance.Machine.State.setLocs,
          OrderMaintenance.Machine.State.upd]) (capsOf_ok P) hcntL hM
      have hom2 : om2 = { om with nxt := some n', nxtIdx := om.nxtIdx.setX x 0 } := by
        unfold OrderMaintenance.mirrorDelete at hr; rw [hn] at hr; simp [h0, runCore, hr'] at hr; exact hr.symm
      subst hom2
      rw [OrderMaintenance.Machine.wp_seq, compile_κ₀ (1 - p) P]
      have hb1 := h1.bump (Expr.maxv m1 (.bin .eq (.var "xn") (.lit 0)))
      have hnE : Enc (1 - p) (capsOf P) n (m1.bump (Expr.maxv m1 (.bin .eq (.var "xn") (.lit 0)))) := by
        rw [← hP]; exact hb1.nxt n hn
      refine wp_coreCall hnE (by simp [OrderMaintenance.Machine.evalList, Expr.eval, m1]) he (fun m2 hE hS hL => ?_)
      have h2 : WEnc { om with nxt := some n' } m2 p :=
        hb1.of_nxt hn (by rw [hP', hP]; exact hE) hS hcnt' hP'
      rw [OrderMaintenance.Machine.wp_store]
      have hxc2 : x < m2.cap (wIdx (1 - p)) := by
        rw [(hS _ (wIdx_notSlot (by omega))).2]; exact hxc'
      refine ⟨x, 0, by simp [Expr.eval, hL, OrderMaintenance.Machine.State.setLocs, m1, hx], rfl, hxc2, ?_⟩
      refine ⟨(h2.bump _ |>.bump _).writeN (by simpa using hxc2), by simp [hL, OrderMaintenance.Machine.State.setLocs, m1, hx], ?_⟩
      simp [OrderMaintenance.Machine.costList, Expr.cost] at *; omega

/-! ### Writing the wrapper's scalars -/

theorem wa_ne {i j : Nat} (h : i ≠ j) : wa i ≠ wa j := fun e => by
  have : (2000 + i : Nat) = 2000 + j := e
  omega
theorem wa_ne_idx {k q : Nat} (hk : k < 8) : wa k ≠ wIdx q := fun e => by
  have : (2000 + k : Nat) = 2010 + q := e
  omega

/-- A write to scalar `k`: the other scalars, the cores and the maps are unchanged. -/
theorem WEnc.scalarFrame {om : OrderMaintenance} {m : State} {p k v : Nat} (h : WEnc om m p) (hk : k < 8) :
    Enc p (capsOf om.cur.P) om.cur (m.write (wa k) 0 v) ∧
      (∀ n, om.nxt = some n → Enc (1 - p) (capsOf n.P) n (m.write (wa k) 0 v)) ∧
      (∀ j, j ≠ k → (m.write (wa k) 0 v).mem (wa j) 0 = m.mem (wa j) 0) ∧
      (∀ q, Same (wIdx q) m (m.write (wa k) 0 v)) ∧ (m.write (wa k) 0 v).cap = m.cap ∧
      (m.write (wa k) 0 v).mem (wa k) 0 = v := by
  have hp := h.p2
  refine ⟨h.cur.of_same fun b hb => ⟨?_, rfl⟩, fun n hn => (h.nxt n hn).of_same fun b hb => ⟨?_, rfl⟩,
    fun j hj => ?_, fun q => ⟨?_, rfl⟩, rfl, by simp [State.write, OrderMaintenance.Machine.State.upd]⟩
  · simp only [State.write]; funext i; rw [ite_eq_right (fun e => wa_notSlot hp (e ▸ hb))]
  · simp only [State.write]; funext i; rw [ite_eq_right (fun e => wa_notSlot (p := 1 - p) (by omega) (e ▸ hb))]
  · simp only [State.write]; rw [ite_eq_right (wa_ne hj)]
  · simp only [State.write]; funext i; rw [ite_eq_right (Ne.symm (wa_ne_idx hk))]

theorem WEnc.writeCursor {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (v : Nat) :
    WEnc { om with cursor := v } (m.write (wa 2) 0 v) p := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.scalarFrame (k := 2) (v := v) (by decide)
  exact ⟨h.p2, fun k hk => by rw [a5]; exact h.scap k hk, by rw [a3 0 (by decide)]; exact h.par,
    by rw [a3 1 (by decide)]; exact h.nxtOn, a6, by rw [a3 3 (by decide)]; exact h.cset,
    by rw [a3 4 (by decide)]; exact h.live, by rw [a3 5 (by decide)]; exact h.next,
    by rw [a3 6 (by decide)]; exact h.reb, by rw [a3 7 (by decide)]; exact h.kb, a1, a2,
    fun i hi => by rw [(a4 p).2] at hi; rw [(a4 p).1]; exact h.idxC i hi,
    fun hn i hi => by rw [(a4 _).2] at hi; rw [(a4 _).1]; exact h.idxN hn i hi,
    by rw [(a4 p).2]; exact h.roomC, fun n hn => by rw [(a4 _).2]; exact h.roomN n hn⟩

theorem WEnc.writeCset {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (b : Bool) :
    WEnc { om with cursorSet := b } (m.write (wa 3) 0 (b2n b)) p := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.scalarFrame (k := 3) (v := b2n b) (by decide)
  exact ⟨h.p2, fun k hk => by rw [a5]; exact h.scap k hk, by rw [a3 0 (by decide)]; exact h.par,
    by rw [a3 1 (by decide)]; exact h.nxtOn, by rw [a3 2 (by decide)]; exact h.cursor, a6,
    by rw [a3 4 (by decide)]; exact h.live, by rw [a3 5 (by decide)]; exact h.next,
    by rw [a3 6 (by decide)]; exact h.reb, by rw [a3 7 (by decide)]; exact h.kb, a1, a2,
    fun i hi => by rw [(a4 p).2] at hi; rw [(a4 p).1]; exact h.idxC i hi,
    fun hn i hi => by rw [(a4 _).2] at hi; rw [(a4 _).1]; exact h.idxN hn i hi,
    by rw [(a4 p).2]; exact h.roomC, fun n hn => by rw [(a4 _).2]; exact h.roomN n hn⟩

theorem WEnc.writeLive {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (v : Nat) :
    WEnc { om with live := v } (m.write (wa 4) 0 v) p := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.scalarFrame (k := 4) (v := v) (by decide)
  exact ⟨h.p2, fun k hk => by rw [a5]; exact h.scap k hk, by rw [a3 0 (by decide)]; exact h.par,
    by rw [a3 1 (by decide)]; exact h.nxtOn, by rw [a3 2 (by decide)]; exact h.cursor,
    by rw [a3 3 (by decide)]; exact h.cset, a6, by rw [a3 5 (by decide)]; exact h.next,
    by rw [a3 6 (by decide)]; exact h.reb, by rw [a3 7 (by decide)]; exact h.kb, a1, a2,
    fun i hi => by rw [(a4 p).2] at hi; rw [(a4 p).1]; exact h.idxC i hi,
    fun hn i hi => by rw [(a4 _).2] at hi; rw [(a4 _).1]; exact h.idxN hn i hi,
    by rw [(a4 p).2]; exact h.roomC, fun n hn => by rw [(a4 _).2]; exact h.roomN n hn⟩

theorem WEnc.writeNext {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (v : Nat)
    (hrC : v + (om.cur.P.N - om.cur.count) ≤ m.cap (wIdx p))
    (hrN : ∀ n, om.nxt = some n → v + (om.cur.P.N - om.cur.count) + (n.P.N - n.count) ≤ m.cap (wIdx (1 - p))) :
    WEnc { om with nextHandle := v } (m.write (wa 5) 0 v) p := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.scalarFrame (k := 5) (v := v) (by decide)
  exact ⟨h.p2, fun k hk => by rw [a5]; exact h.scap k hk, by rw [a3 0 (by decide)]; exact h.par,
    by rw [a3 1 (by decide)]; exact h.nxtOn, by rw [a3 2 (by decide)]; exact h.cursor,
    by rw [a3 3 (by decide)]; exact h.cset, by rw [a3 4 (by decide)]; exact h.live, a6,
    by rw [a3 6 (by decide)]; exact h.reb, by rw [a3 7 (by decide)]; exact h.kb, a1, a2,
    fun i hi => by rw [(a4 p).2] at hi; rw [(a4 p).1]; exact h.idxC i hi,
    fun hn i hi => by rw [(a4 _).2] at hi; rw [(a4 _).1]; exact h.idxN hn i hi,
    by rw [(a4 p).2]; exact hrC, fun n hn => by rw [(a4 _).2]; exact hrN n hn⟩

theorem WEnc.writeReb {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (v : Nat) :
    WEnc { om with rebuilds := v } (m.write (wa 6) 0 v) p := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.scalarFrame (k := 6) (v := v) (by decide)
  exact ⟨h.p2, fun k hk => by rw [a5]; exact h.scap k hk, by rw [a3 0 (by decide)]; exact h.par,
    by rw [a3 1 (by decide)]; exact h.nxtOn, by rw [a3 2 (by decide)]; exact h.cursor,
    by rw [a3 3 (by decide)]; exact h.cset, by rw [a3 4 (by decide)]; exact h.live,
    by rw [a3 5 (by decide)]; exact h.next, a6, by rw [a3 7 (by decide)]; exact h.kb, a1, a2,
    fun i hi => by rw [(a4 p).2] at hi; rw [(a4 p).1]; exact h.idxC i hi,
    fun hn i hi => by rw [(a4 _).2] at hi; rw [(a4 _).1]; exact h.idxN hn i hi,
    by rw [(a4 p).2]; exact h.roomC, fun n hn => by rw [(a4 _).2]; exact h.roomN n hn⟩

/-- The current core changes (in its slot). -/
theorem WEnc.of_cur {om : OrderMaintenance} {m m' : State} {p : Nat} (h : WEnc om m p) {c' : Core}
    (hE : Enc p (capsOf c'.P) c' m') (hS : ∀ b, ¬ InSlot p b → Same b m m')
    (hrC : om.nextHandle + (c'.P.N - c'.count) ≤ m.cap (wIdx p))
    (hrN : ∀ n, om.nxt = some n → om.nextHandle + (c'.P.N - c'.count) + (n.P.N - n.count) ≤ m.cap (wIdx (1 - p))) :
    WEnc { om with cur := c' } m' p := by
  have hp := h.p2
  have hw : ∀ k, Same (wa k) m m' := fun k => hS _ (wa_notSlot hp)
  have hi : ∀ q, Same (wIdx q) m m' := fun q => hS _ (wIdx_notSlot hp)
  exact ⟨hp, fun k hk => by rw [(hw k).2]; exact h.scap k hk, by rw [(hw 0).1]; exact h.par,
    by rw [(hw 1).1]; exact h.nxtOn, by rw [(hw 2).1]; exact h.cursor, by rw [(hw 3).1]; exact h.cset,
    by rw [(hw 4).1]; exact h.live, by rw [(hw 5).1]; exact h.next, by rw [(hw 6).1]; exact h.reb,
    by rw [(hw 7).1]; exact h.kb, hE,
    fun n hn => (h.nxt n hn).of_same fun b hb => hS b (fun hpb => inSlot_disj (by omega) hpb hb),
    fun x hx => by rw [(hi p).2] at hx; rw [(hi p).1]; exact h.idxC x hx,
    fun hn x hx => by rw [(hi (1 - p)).2] at hx; rw [(hi (1 - p)).1]; exact h.idxN hn x hx,
    by rw [(hi p).2]; exact hrC, fun n hn => by rw [(hi (1 - p)).2]; exact hrN n hn⟩

/-! ### Insertion into `cur` -/

/-- Insert after the element of handle `x` (local `hx` = 1) or at the front (`hx` = 0); the new
handle is the counter `nextHandle` (local `hy`), and the new element lands in local `y`. -/
def curInsC (p : Nat) : Stmt :=
  .seq (.assign "hy" (.load (wa 5) (.lit 0)))
  (.seq (.ite (.bin .eq (.var "hx") (.lit 0)) (.assign "xi" (.load (arrF p (.s .head)) (.lit 0)))
      (.assign "xi" (.load (wIdx p) (.var "x"))))
  (.seq (.call "insertAfter" ["x", "h"] (insertAfterP.body.compile p κ₀) ["y"] [.var "xi", .var "hy"] ["y"])
  (.seq (.store (wa 5) (.lit 0) (.bin .add (.var "hy") (.lit 1)))
    (.store (wIdx p) (.var "hy") (.var "y")))))

/-- The element a wrapper insertion goes after, in `cur`. -/
def insAnchor (om : OrderMaintenance) (hx : Option Nat) : Nat :=
  match hx with
  | none => om.cur.head
  | some x => om.curIdx.getX x

/-- The wrapper state after the insertion into `cur`. -/
def insOM (om : OrderMaintenance) (c' : Core) (y : Nat) : OrderMaintenance :=
  { om with cur := c', nextHandle := om.nextHandle + 1, curIdx := om.curIdx.setX om.nextHandle y }

theorem curInsW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {hx : Option Nat}
    (hhx : m.loc "hx" = b2n hx.isSome) (hxx : ∀ x, hx = some x → m.loc "x" = x ∧ x < m.cap (wIdx p))
    {P : Params} {n R : Nat} {L : List Nat} (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L om.cur)
    (hP : om.cur.P = P) (hxL : insAnchor om hx ∈ L) (hcntL : om.cur.count = L.length)
    (hcnt : om.cur.count + 1 ≤ P.N) (hM : Mc (capsOf P) P om.cur)
    (hk : 1 ≤ om.cur.P.reservationBudget) (hR : topJ P / om.cur.P.reservationBudget + 1 ≤ R)
      (hn : 1 ≤ n)
    (hsize : 2 + 2 * ((om.cur.count + 1) / (om.cur.P.theta + 1 - cmax om.cur.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((om.cur.count + 1) / (om.cur.P.theta + 1 - cmax om.cur.P)) ≤ capT om.cur.P)
    (hI5 : (om.cur.P.theta : ℝ) + R * (OrderMaintenance.Zeroing.Hn (n - 1) + 1) ≤ om.cur.P.T)
    (hpow : om.cur.P.a = 2 ^ Nat.log2 om.cur.P.a) :
    ∃ c' y, (insertAfter (insAnchor om hx) om.nextHandle).run om.cur = .ok y c' ∧
      CostInv (TIat TopInv P) topMu (topJ P) n R (OrderMaintenance.Spec.insertAfterL (insAnchor om hx) om.cur.E.size L) c' ∧
      c'.count = om.cur.count + 1 ∧ c'.P = om.cur.P ∧ Mc (capsOf P) P c' ∧ y = om.cur.E.size ∧
      wp (curInsC p) (fun m' k => WEnc (insOM om c' y) m' p ∧ m'.loc "hy" = om.nextHandle ∧ m'.loc "y" = y ∧
        m'.loc "hx" = m.loc "hx" ∧ m'.loc "x" = m.loc "x" ∧ k ≤ insBound P + 100) m := by
  have hp := h.p2
  obtain ⟨c', hr, ⟨L', c, he, hy, hc⟩, hC', hcnt', hP', hM'⟩ := insertAgreeM hC hP hxL hk hR hn hsize hcap hI5
    om.nextHandle (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x", "h"] [insAnchor om hx, om.nextHandle])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd])
    hpow (capsOf_ok P) hcntL hcnt hM
  refine ⟨c', _, hr, hC', hcnt', hP', hM', rfl, ?_⟩
  unfold curInsC
  rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
  refine ⟨om.nextHandle, by simp [Expr.eval, h.scap 5 (by decide), h.next], ?_⟩
  set m1 := (m.bump _).setLoc "hy" om.nextHandle
  have h1 : WEnc om m1 p := (h.bump _).setLoc _ _
  rw [OrderMaintenance.Machine.wp_seq]
  have hhx1 : m1.loc "hx" = b2n hx.isSome := by simp [m1, hhx]
  -- the anchor, in local `xi`
  have hanchor : wp (.ite (.bin .eq (.var "hx") (.lit 0)) (.assign "xi" (.load (arrF p (.s .head)) (.lit 0)))
      (.assign "xi" (.load (wIdx p) (.var "x"))))
      (fun s' k => WEnc om s' p ∧ s'.loc "xi" = insAnchor om hx ∧ s'.loc "hy" = om.nextHandle ∧
        s'.loc "hx" = m.loc "hx" ∧ s'.loc "x" = m.loc "x" ∧ k ≤ 10) m1 := by
    rw [OrderMaintenance.Machine.wp_ite]
    refine ⟨if b2n hx.isSome = 0 then 1 else 0, by simp [Expr.eval, BinOp.eval, hhx1], ?_⟩
    have hb := h1.bump (Expr.maxv m1 (.bin .eq (.var "hx") (.lit 0)))
    cases hx with
    | none =>
      simp only [Option.isSome_none, b2n, Bool.false_eq_true, ↓reduceIte, ne_eq, one_ne_zero,
        not_false_eq_true,
        OrderMaintenance.Machine.wp_assign]
      refine ⟨om.cur.head, ?_, (hb.bump _).setLoc _ _, by simp [insAnchor], by simp [m1], by simp [m1],
        by simp [m1], by simp [Expr.cost]⟩
      have hc1 := hb.cur.cap (.s .head)
      have hm1 := hb.cur.mem (.s .head) 0 (by rw [Fld.cap]; omega)
      simp only [Expr.eval, Option.bind_some, hc1, Fld.cap, show (0 : Nat) < 1 from by decide,
        ite_true, hm1]
      rfl
    | some x =>
      obtain ⟨hxl, hxc⟩ := hxx x rfl
      simp only [Option.isSome_some, b2n, ↓reduceIte, one_ne_zero, ne_eq, not_true_eq_false,
        OrderMaintenance.Machine.wp_assign]
      refine ⟨om.curIdx.getX x, ?_, (hb.bump _).setLoc _ _, by simp [insAnchor], by simp [m1], by simp [m1],
        by simp [m1], by simp [Expr.cost]⟩
      have hxc' : x < (m1.bump (Expr.maxv m1 (.bin .eq (.var "hx") (.lit 0)))).cap (wIdx p) := by simpa [m1] using hxc
      simp [Expr.eval, m1, hxl, hxc, h.idxC x hxc]
  refine OrderMaintenance.Machine.wp_mono (fun s2 k2 hR => ?_) hanchor
  obtain ⟨h2, hxi, hhy, hhx2, hx2, hk2⟩ := hR
  have hroom := h2.roomC
  have hcntN : om.cur.count + 1 ≤ om.cur.P.N := by rw [hP]; exact hcnt
  rw [OrderMaintenance.Machine.wp_seq, compile_κ₀ p P]
  have hcur : Enc p (capsOf P) om.cur s2 := by rw [← hP]; exact h2.cur
  refine wp_coreCall hcur (by simp [OrderMaintenance.Machine.evalList, Expr.eval, hxi, hhy]) he (fun m3 hE hS hL => ?_)
  have h3 : WEnc { om with cur := c' } m3 p := by
    refine h2.of_cur (by rw [hP', hP]; exact hE) hS ?_ ?_
    · rw [hP', hcnt']; omega
    · intro n0 hn0; have := h2.roomN n0 hn0; rw [hP', hcnt']; omega
  have hL3 : ∀ x, x ≠ "y" → m3.loc x = s2.loc x := fun x hx => by
    rw [hL]; simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hx]
  have hy3 : m3.loc "y" = om.cur.E.size := by rw [hL]; simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hy]
  rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_store]
  refine ⟨0, om.nextHandle + 1, rfl, by simp [Expr.eval, BinOp.eval, hL3 "hy" (by decide), hhy], by
    rw [h3.scap 5 (by decide)]; decide, ?_⟩
  set m4 := ((m3.bump _).bump _).write (wa 5) 0 (om.nextHandle + 1)
  have h4 : WEnc { om with cur := c', nextHandle := om.nextHandle + 1 } m4 p := by
    refine ((h3.bump _).bump _).writeNext _ ?_ ?_
    · show om.nextHandle + 1 + (c'.P.N - c'.count) ≤ m3.cap (wIdx p)
      rw [(hS _ (wIdx_notSlot hp)).2, hP', hcnt']; omega
    · intro n0 hn0; have := h2.roomN n0 hn0
      show om.nextHandle + 1 + (c'.P.N - c'.count) + _ ≤ m3.cap (wIdx (1 - p))
      rw [(hS _ (wIdx_notSlot hp)).2, hP', hcnt']; omega
  rw [OrderMaintenance.Machine.wp_store]
  have hcap4 : om.nextHandle < m4.cap (wIdx p) := by
    show om.nextHandle < m3.cap (wIdx p)
    rw [(hS _ (wIdx_notSlot hp)).2]; omega
  refine ⟨om.nextHandle, om.cur.E.size, by simp [Expr.eval, m4, hL3 "hy" (by decide), hhy],
    by simp [Expr.eval, m4, hy3], hcap4, ?_⟩
  refine ⟨((h4.bump _).bump _).writeC (by simpa using hcap4), ?_, ?_, ?_, ?_, ?_⟩
  · simp [m4, hL3 "hy" (by decide), hhy]
  · simp [m4, hy3]
  · simp [m4, hL3 "hx" (by decide), hhx2]
  · simp [m4, hL3 "x" (by decide), hx2]
  · have : insBound om.cur.P = insBound P := by rw [hP]
    simp [OrderMaintenance.Machine.costList, Expr.cost] at *
    omega

/-! ### Cores in service -/

/-- **A core in service**, as the wrapper's Level M steps need it: Level F's `CoreOK` for the
proof parameters, room for one more element, and the capacity predicate. -/
structure InService (c : Core) (L : List Nat) : Prop where
  ok : CoreOK proofParams TopInv topMu topJ nfP RfP c L
  room : c.count + 1 ≤ c.P.N
  mc : Mc (capsOf c.P) c.P c

theorem proofParams_a (N : Nat) : (proofParams N).a = 2 ^ Nat.log2 (proofParams N).a := by
  show 8 = 2 ^ Nat.log2 8; decide

/-- The parameter conditions of `insertAgreeM`, for a core in service. -/
theorem InService.params {c : Core} {L : List Nat} (h : InService c L) :
    1 ≤ c.P.reservationBudget ∧ topJ c.P / c.P.reservationBudget + 1 ≤ RfP c.P ∧ 1 ≤ nfP c.P ∧
      2 + 2 * ((c.count + 1) / (c.P.theta + 1 - cmax c.P)) ≤ nfP c.P + 1 ∧
      2 + 2 * ((c.count + 1) / (c.P.theta + 1 - cmax c.P)) ≤ capT c.P ∧
      (c.P.theta : ℝ) + RfP c.P * (OrderMaintenance.Zeroing.Hn (nfP c.P - 1) + 1) ≤ c.P.T ∧
      c.P.a = 2 ^ Nat.log2 c.P.a := by
  have hmk := h.ok.pmk
  have S := costSetup
  have hdiv : (c.count + 1) / (c.P.theta + 1 - cmax c.P) ≤ c.P.N / (c.P.theta + 1 - cmax c.P) :=
    Nat.div_le_div_right h.room
  have h1 := S.kR c.P.N; have h2 := S.R c.P.N; have h3 := S.n1 c.P.N; have h4 := S.size c.P.N
  have h5 := S.capc c.P.N; have h6 := S.I5 c.P.N
  rw [← hmk] at h1 h2 h3 h6
  have hN : (proofParams c.P.N).N = c.P.N := S.PN _
  rw [← hmk] at h4 h5
  refine ⟨h1, h2, h3, by omega, by omega, h6, ?_⟩
  rw [hmk]; exact proofParams_a _

/-- **An insertion into a core in service**, at Level M. -/
theorem InService.insert {c : Core} {L : List Nat} (h : InService c L) {x : Nat} (hx : x ∈ L) (hh : Nat)
    (Lx : Loc) (hLx : Lx "x" = x) (hLh : Lx "h" = hh) :
    ∃ c', (insertAfter x hh).run c = .ok c.E.size c' ∧
      (∃ L' m, evalF (capsOf c.P) insertAfterP.body c Lx = .ok c' L' m ∧ L' "y" = c.E.size ∧ m ≤ insBound c.P) ∧
      CoreOK proofParams TopInv topMu topJ nfP RfP c' (OrderMaintenance.Spec.insertAfterL x c.E.size L) ∧
      c'.count = c.count + 1 ∧ c'.P = c.P ∧ Mc (capsOf c.P) c.P c' := by
  obtain ⟨hk, hR, hn, hsize, hcap, hI5, hpow⟩ := h.params
  obtain ⟨c', hr, he, hC', hcnt', hP', hM'⟩ := insertAgreeM h.ok.cost rfl hx hk hR hn hsize hcap hI5 hh Lx hLx hLh
    hpow (capsOf_ok c.P) h.ok.cnt h.room h.mc
  refine ⟨c', hr, he, ⟨by rw [hP']; exact hC', by rw [hcnt', h.ok.cnt, length_insertAfterL hx],
    by rw [hP']; exact h.ok.pmk⟩, hcnt', hP', hM'⟩

/-! ### Insertion into `nxt` -/

/-- Insert after the element in local `xn` of `nxt`, with handle `hh`; record it in the next
handle map. -/
def nxtInsC (p : Nat) : Stmt :=
  .seq (.call "insertAfter" ["x", "h"] (insertAfterP.body.compile (1 - p) κ₀) ["y"] [.var "xn", .var "hh"] ["y2"])
    (.store (wIdx (1 - p)) (.var "hh") (.var "y2"))

/-- The wrapper state after an insertion into `nxt`. -/
def nxtOM (om : OrderMaintenance) (n' : Core) (hh y : Nat) : OrderMaintenance := { om with nxt := some n', nxtIdx := om.nxtIdx.setX hh y }

theorem nxtInsW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {n : Core} (hn : om.nxt = some n)
    {B : List Nat} (hS : InService n B) {xn hh : Nat} (hxn : xn ∈ B) (hlx : m.loc "xn" = xn)
    (hlh : m.loc "hh" = hh) (hhc : hh < m.cap (wIdx (1 - p))) :
    ∃ n', (insertAfter xn hh).run n = .ok n.E.size n' ∧
      CoreOK proofParams TopInv topMu topJ nfP RfP n' (OrderMaintenance.Spec.insertAfterL xn n.E.size B) ∧
      n'.count = n.count + 1 ∧ n'.P = n.P ∧ Mc (capsOf n.P) n.P n' ∧
      wp (nxtInsC p) (fun m' k => WEnc (nxtOM om n' hh n.E.size) m' p ∧
        (∀ x, x ≠ "y2" → m'.loc x = m.loc x) ∧ k ≤ insBound n.P + 20) m := by
  have hp := h.p2
  obtain ⟨n', hr, ⟨L', c, he, hy, hc⟩, hok, hcnt', hP', hM'⟩ := hS.insert hxn hh
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x", "h"] [xn, hh]) (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
  refine ⟨n', hr, hok, hcnt', hP', hM', ?_⟩
  unfold nxtInsC
  rw [OrderMaintenance.Machine.wp_seq, compile_κ₀ (1 - p) n.P]
  refine wp_coreCall (h.nxt n hn) (by simp [OrderMaintenance.Machine.evalList, Expr.eval, hlx, hlh]) he (fun m2 hE hS2 hL => ?_)
  have h2 : WEnc { om with nxt := some n' } m2 p := by
    have hroomN := h.roomN n hn
    have hrm := hS.room
    refine ⟨hp, fun k hk => by rw [(hS2 _ (wa_notSlot (by omega))).2]; exact h.scap k hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      h.cur.of_same fun b hb => hS2 b (fun hpb => inSlot_disj (by omega) hpb hb),
      fun n2 hn2 => by cases hn2; rw [hP']; exact hE, fun i hi => ?_, fun _ i hi => ?_, ?_, fun n2 hn2 => ?_⟩
    · rw [(hS2 _ (wa_notSlot (by omega))).1]; exact h.par
    · rw [(hS2 _ (wa_notSlot (by omega))).1, h.nxtOn, hn]; rfl
    · rw [(hS2 _ (wa_notSlot (by omega))).1]; exact h.cursor
    · rw [(hS2 _ (wa_notSlot (by omega))).1]; exact h.cset
    · rw [(hS2 _ (wa_notSlot (by omega))).1]; exact h.live
    · rw [(hS2 _ (wa_notSlot (by omega))).1]; exact h.next
    · rw [(hS2 _ (wa_notSlot (by omega))).1]; exact h.reb
    · rw [(hS2 _ (wa_notSlot (by omega))).1]; exact h.kb
    · rw [(hS2 _ (wIdx_notSlot (by omega))).2] at hi; rw [(hS2 _ (wIdx_notSlot (by omega))).1]; exact h.idxC i hi
    · rw [(hS2 _ (wIdx_notSlot (by omega))).2] at hi; rw [(hS2 _ (wIdx_notSlot (by omega))).1]
      exact h.idxN (by rw [hn]; rfl) i hi
    · rw [(hS2 _ (wIdx_notSlot (by omega))).2]; exact h.roomC
    · cases hn2; rw [(hS2 _ (wIdx_notSlot (by omega))).2]
      show om.nextHandle + (om.cur.P.N - om.cur.count) + (n'.P.N - n'.count) ≤ m.cap (wIdx (1 - p))
      rw [hP', hcnt']; omega
  have hL2 : ∀ x, x ≠ "y2" → m2.loc x = m.loc x := fun x hx => by
    rw [hL]; simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hx]
  have hy2 : m2.loc "y2" = n.E.size := by rw [hL]; simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hy]
  rw [OrderMaintenance.Machine.wp_store]
  have hhc2 : hh < m2.cap (wIdx (1 - p)) := by rw [(hS2 _ (wIdx_notSlot (by omega))).2]; exact hhc
  refine ⟨hh, n.E.size, by simp [Expr.eval, hL2 "hh" (by decide), hlh], by simp [Expr.eval, hy2], hhc2, ?_⟩
  refine ⟨((h2.bump _).bump _).writeN (by simpa using hhc2), fun x hx => by simp [hL2 x hx], ?_⟩
  simp [OrderMaintenance.Machine.costList, Expr.cost] at *; omega

/-- An assignment followed by code: the code runs from any state that differs only in the local. -/
theorem wp_assign_seq {x : Reg} {e : Expr} {c : Stmt} {Q : State → Nat → Prop} {s : State} {v : Nat}
    (he : e.eval s = some v)
    (h : ∀ s', s'.loc = OrderMaintenance.Machine.State.upd s.loc x v → s'.mem = s.mem → s'.cap = s.cap →
      wp c (fun s'' n => Q s'' (1 + e.cost + n)) s') : wp (.seq (.assign x e) c) Q s := by
  rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
  exact ⟨v, he, h _ rfl rfl rfl⟩

theorem WEnc.congr {om : OrderMaintenance} {m m' : State} {p : Nat} (h : WEnc om m p) (hm : m'.mem = m.mem) (hc : m'.cap = m.cap) :
    WEnc om m' p :=
  h.of_slot (h.cur.congr hm hc) fun b _ => ⟨by rw [hm], by rw [hc]⟩

/-! ### Mirroring an insertion into `nxt` -/

def mirrorInsC (p : Nat) : Stmt :=
  .ite (.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)) .skip
    (.ite (.bin .eq (.load (wa 3) (.lit 0)) (.lit 0)) .skip
      (.ite (.bin .eq (.var "hx") (.lit 0))
        (.seq (.assign "xn" (.load (arrF (1 - p) (.s .head)) (.lit 0))) (.seq (.assign "hh" (.var "hy")) (nxtInsC p)))
        (.seq (.assign "xn" (.load (wIdx (1 - p)) (.var "x")))
          (.ite (.bin .eq (.var "xn") (.lit 0)) .skip (.seq (.assign "hh" (.var "hy")) (nxtInsC p))))))

/-- The anchor of a mirrored insertion in `nxt`. -/
def mirAnchor (om : OrderMaintenance) (n : Core) (hx : Option Nat) : Nat :=
  match hx with
  | none => n.head
  | some x => om.nxtIdx.getX x

theorem mirrorInsW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {hx : Option Nat} {hy : Nat}
    (hhx : m.loc "hx" = b2n hx.isSome) (hxx : ∀ x, hx = some x → m.loc "x" = x ∧
      (om.nxt.isSome → x < m.cap (wIdx (1 - p)))) (hhy : m.loc "hy" = hy)
    (hhyc : om.nxt.isSome → hy < m.cap (wIdx (1 - p)))
    (hN : ∀ n, om.nxt = some n → om.cursorSet = true → (hx = none ∨ ∃ x, hx = some x ∧ om.nxtIdx.getX x ≠ 0) →
      ∃ B, InService n B ∧ mirAnchor om n hx ∈ B)
    {om2 : OrderMaintenance} (hr : om.mirrorInsert hx hy = .ok om2) :
    wp (mirrorInsC p) (fun m' k => WEnc om2 m' p ∧ (∀ x, x ≠ "xn" → x ≠ "hh" → x ≠ "y2" → m'.loc x = m.loc x) ∧
      k ≤ insBound (om.nxt.map (·.P) |>.getD om.cur.P) + 100) m := by
  have hp := h.p2
  unfold mirrorInsC
  rw [OrderMaintenance.Machine.wp_ite]
  cases hn : om.nxt with
  | none =>
    have : om2 = om := by unfold OrderMaintenance.mirrorInsert at hr; rw [hn] at hr; cases hr; rfl
    subst this
    refine ⟨1, by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n], ?_⟩
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true, OrderMaintenance.Machine.wp_skip]
    exact ⟨h.bump _, fun x _ _ _ => by simp, by simp [Expr.cost]⟩
  | some n =>
    refine ⟨0, by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n], ?_⟩
    simp only [ne_eq, not_true_eq_false, ite_false]
    have hb1 := h.bump (Expr.maxv m (.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)))
    rw [OrderMaintenance.Machine.wp_ite]
    by_cases hcs : om.cursorSet = false
    · have : om2 = om := by
        unfold OrderMaintenance.mirrorInsert at hr; rw [hn] at hr; simp [hcs] at hr; cases hr; rfl
      subst this
      refine ⟨1, by simp [Expr.eval, h.scap 3 (by decide), h.cset, hcs, BinOp.eval, b2n], ?_⟩
      simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true, OrderMaintenance.Machine.wp_skip]
      exact ⟨hb1.bump _, fun x _ _ _ => by simp, by simp [Expr.cost]⟩
    · have hcs' : om.cursorSet = true := by simpa using hcs
      refine ⟨0, by simp [Expr.eval, h.scap 3 (by decide), h.cset, hcs', BinOp.eval, b2n], ?_⟩
      simp only [ne_eq, not_true_eq_false, ite_false]
      set m2 := (m.bump (Expr.maxv m (.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)))).bump
        (Expr.maxv (m.bump (Expr.maxv m (.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)))) (.bin .eq (.load (wa 3) (.lit 0)) (.lit 0)))
      have h2 : WEnc om m2 p := hb1.bump _
      have hhx2 : m2.loc "hx" = b2n hx.isSome := by simp [m2, hhx]
      have hhy2 : m2.loc "hy" = hy := by simp [m2, hhy]
      have hyc := hhyc (by rw [hn]; rfl)
      rw [OrderMaintenance.Machine.wp_ite]
      refine ⟨if b2n hx.isSome = 0 then 1 else 0, by simp [Expr.eval, BinOp.eval, hhx2], ?_⟩
      have hb2 := h2.bump (Expr.maxv m2 (.bin .eq (.var "hx") (.lit 0)))
      cases hx with
      | none =>
        simp only [Option.isSome_none, b2n, Bool.false_eq_true, ↓reduceIte, ne_eq, one_ne_zero,
          not_false_eq_true]
        obtain ⟨B, hS, hxB⟩ := hN n hn hcs' (Or.inl rfl)
        rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
        have hnE := h.nxt n hn
        have hc1 := hnE.cap (.s .head)
        have hm1 := hnE.mem (.s .head) 0 (by rw [Fld.cap]; omega)
        refine ⟨n.head, by simp [m2, Expr.eval, hc1, Fld.cap, hm1, Fld.get, SF.get], ?_⟩
        set m3 := ((m2.bump (Expr.maxv m2 (.bin .eq (.var "hx") (.lit 0)))).bump _).setLoc "xn" n.head
        have h3 : WEnc om m3 p := (hb2.bump _).setLoc _ _
        rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
        refine ⟨hy, by simp [Expr.eval, m3, hhy2], ?_⟩
        set m4 := (m3.bump _).setLoc "hh" hy
        have h4 : WEnc om m4 p := (h3.bump _).setLoc _ _
        obtain ⟨n', hr', -, -, -, -, hwp⟩ := nxtInsW_ok h4 hn hS (xn := n.head) (hh := hy) hxB (by simp [m4, m3])
          (by simp [m4]) (by simpa [m4, m3, m2] using hyc)
        have hom2 : om2 = nxtOM om n' hy n.E.size := by
          unfold OrderMaintenance.mirrorInsert at hr; rw [hn] at hr; simp [hcs', runCore, hr'] at hr
          cases hr; simp only [nxtOM]; rw [hcs']
        subst hom2
        refine OrderMaintenance.Machine.wp_mono (fun m5 k5 ⟨h5, hl5, hk5⟩ => ⟨h5, fun x a b c => ?_, ?_⟩) hwp
        · rw [hl5 x c]; simp [m4, m3, m2, a, b]
        · simp only [Option.map_some, Option.getD_some, Expr.cost] at hk5 ⊢; omega
      | some x =>
        simp only [Option.isSome_some, b2n, ↓reduceIte, one_ne_zero, ne_eq, not_true_eq_false]
        obtain ⟨hxl, hxc⟩ := hxx x rfl
        have hxc' := hxc (by rw [hn]; rfl)
        rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_assign]
        refine ⟨om.nxtIdx.getX x, by simp [Expr.eval, m2, hxl, hxc', h.idxN (by rw [hn]; rfl) x hxc'], ?_⟩
        set m3 := ((m2.bump (Expr.maxv m2 (.bin .eq (.var "hx") (.lit 0)))).bump _).setLoc "xn" (om.nxtIdx.getX x)
        have h3 : WEnc om m3 p := (hb2.bump _).setLoc _ _
        have hl3 : ∀ z, z ≠ "xn" → m3.loc z = m.loc z := fun z hz => by simp [m3, m2, hz]
        have hxn3 : m3.loc "xn" = om.nxtIdx.getX x := by simp [m3]
        rw [OrderMaintenance.Machine.wp_ite]
        by_cases h0 : om.nxtIdx.getX x = 0
        · have : om2 = om := by
            unfold OrderMaintenance.mirrorInsert at hr; rw [hn] at hr; simp [hcs', h0] at hr; cases hr; rfl
          subst this
          refine ⟨1, by simp only [Expr.eval, hxn3, h0, Option.bind_some, BinOp.eval]; rfl, ?_⟩
          simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true,
            OrderMaintenance.Machine.wp_skip]
          refine ⟨h3.bump _, fun y a b c => ?_, by simp [Expr.cost]⟩
          show m3.loc y = m.loc y
          exact hl3 y a
        · refine ⟨0, by simp only [Expr.eval, hxn3, h0, Option.bind_some, BinOp.eval]; rfl, ?_⟩
          simp only [ne_eq, not_true_eq_false, ite_false]
          obtain ⟨B, hS, hxB⟩ := hN n hn hcs' (Or.inr ⟨x, rfl, h0⟩)
          have h3' : WEnc om (m3.bump (Expr.maxv m3 (.bin .eq (.var "xn") (.lit 0)))) p := h3.bump _
          refine wp_assign_seq (v := hy) (by simp only [Expr.eval]; rw [show (m3.bump _).loc "hy" = m3.loc "hy" from rfl,
            hl3 "hy" (by decide), hhy]) (fun m4 hl4 hm4 hc4 => ?_)
          have h4 : WEnc om m4 p := h3'.congr hm4 hc4
          have hl4' : ∀ z, z ≠ "hh" → m4.loc z = m3.loc z := fun z hz => by
            rw [hl4]; simp only [OrderMaintenance.Machine.State.upd, ite_eq_right hz]; rfl
          obtain ⟨n', hr', -, -, -, -, hwp⟩ := nxtInsW_ok h4 hn hS (xn := om.nxtIdx.getX x) (hh := hy) hxB
            (by rw [hl4' "xn" (by decide),
              hxn3]) (by rw [hl4]; simp [OrderMaintenance.Machine.State.upd])
            (by rw [hc4]; show hy < m.cap (wIdx (1 - p)); exact hyc)
          have hom2 : om2 = nxtOM om n' hy n.E.size := by
            unfold OrderMaintenance.mirrorInsert at hr; rw [hn] at hr; simp [hcs', h0, runCore, hr'] at hr
            cases hr; simp only [nxtOM]; rw [hcs']
          subst hom2
          refine OrderMaintenance.Machine.wp_mono (fun m5 k5 ⟨h5, hl5, hk5⟩ => ⟨h5, fun y a b c => ?_, ?_⟩) hwp
          · rw [hl5 y c, hl4' y b, hl3 y a]
          · simp only [Option.map_some, Option.getD_some, Expr.cost] at hk5 ⊢; omega

/-! ### The swap -/

/-- `nxt` replaces `cur`: flip the parity, and `nxt` is gone. -/
def swapC (p : Nat) : Stmt :=
  .seq (.store (wa 0) (.lit 0) (.lit (1 - p))) (.store (wa 1) (.lit 0) (.lit 0))

theorem swapW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {n : Core} (hn : om.nxt = some n)
    {Q : State → Nat → Prop} (hQ : ∀ m' k, WEnc (om.swap n) m' (1 - p) → (∀ x, m'.loc x = m.loc x) → k ≤ 10 → Q m' k) :
    wp (swapC p) Q m := by
  have hp := h.p2
  unfold swapC
  rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_store]
  refine ⟨0, 1 - p, rfl, rfl, by rw [h.scap 0 (by decide)]; decide, ?_⟩
  rw [OrderMaintenance.Machine.wp_store]
  set m1 := ((m.bump (Expr.maxv m (.lit 0))).bump (Expr.maxv m (.lit (1 - p)))).write (wa 0) 0 (1 - p)
  refine ⟨0, 0, rfl, rfl, by simp [m1, State.write, h.scap 0 (by decide), h.scap 1 (by decide)], ?_⟩
  set m2 := ((m1.bump (Expr.maxv m1 (.lit 0))).bump (Expr.maxv m1 (.lit 0))).write (wa 1) 0 0
  apply hQ
  · have hS : ∀ b, b ≠ wa 0 → b ≠ wa 1 → Same b m m2 := fun b h0 h1 =>
      ⟨by simp [m2, m1, State.write, h0, h1], by simp [m2, m1, State.write]⟩
    have hsl : ∀ q, q < 2 → ∀ b, InSlot q b → b ≠ wa 0 ∧ b ≠ wa 1 := fun q hq b hb =>
      ⟨fun e => wa_notSlot hq (e ▸ hb), fun e => wa_notSlot hq (e ▸ hb)⟩
    have hpp : 1 - (1 - p) = p := by omega
    refine ⟨by omega, fun k hk => by simp [m2, m1, State.write, h.scap k hk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, (fun n2 hn2 => by simp [OrderMaintenance.swap] at hn2), (fun i hi => ?_), (fun hn2 => by simp [OrderMaintenance.swap] at hn2), ?_,
      (fun n2 hn2 => by simp [OrderMaintenance.swap] at hn2)⟩
    · simp [m2, m1, State.write, OrderMaintenance.Machine.State.upd,
      wa_ne (show (0 : Nat) ≠ 1 by decide)]
    · simp [m2, m1, State.write, OrderMaintenance.Machine.State.upd, OrderMaintenance.swap, b2n]
    · have := hS (wa 2) (wa_ne (by decide)) (wa_ne (by decide)); rw [this.1]; exact h.cursor
    · have := hS (wa 3) (wa_ne (by decide)) (wa_ne (by decide)); rw [this.1]; exact h.cset
    · have := hS (wa 4) (wa_ne (by decide)) (wa_ne (by decide)); rw [this.1]; exact h.live
    · have := hS (wa 5) (wa_ne (by decide)) (wa_ne (by decide)); rw [this.1]; exact h.next
    · have := hS (wa 6) (wa_ne (by decide)) (wa_ne (by decide)); rw [this.1]; exact h.reb
    · have := hS (wa 7) (wa_ne (by decide)) (wa_ne (by decide)); rw [this.1]; exact h.kb
    · exact (h.nxt n hn).of_same fun b hb => hS b (hsl _ (by omega) b hb).1 (hsl _ (by omega) b hb).2
    · have hne0 := wa_ne_idx (k := 0) (q := 1 - p) (by decide)
      have hne1 := wa_ne_idx (k := 1) (q := 1 - p) (by decide)
      have := hS (wIdx (1 - p)) (Ne.symm hne0) (Ne.symm hne1)
      rw [this.2] at hi; rw [this.1]; exact h.idxN (by rw [hn]; rfl) i hi
    · have hne0 := wa_ne_idx (k := 0) (q := 1 - p) (by decide)
      have hne1 := wa_ne_idx (k := 1) (q := 1 - p) (by decide)
      have := hS (wIdx (1 - p)) (Ne.symm hne0) (Ne.symm hne1)
      rw [this.2]; have := h.roomN n hn; show om.nextHandle + (n.P.N - n.count) ≤ _; omega
  · intro x; simp [m2, m1]
  · simp [Expr.cost]

end OrderMaintenance.Impl

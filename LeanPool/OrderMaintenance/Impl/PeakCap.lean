/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakABW
public import LeanPool.OrderMaintenance.Impl.Memory


/-!
# Theorem W, option (A), stage A4: the capacities along the history

**The capacity of every core is at most `24·t + 64`** after `t` operations (`reachW_cap`). The
first core has `N = 64`. A new core is created only by a rebuild start, with Level F's
`nextCapacity = 4·max(live + (count + L + 2)/(K_B − 1) + 1, 16)`, where `live ≤ t`, and
`count ≤ N/2` (the start comes right after an operation on an idle `cur`, whose count is below
`N/2`), `8·L ≤ N` and `K_B ≥ 4`; so `N' ≤ 4t + 8 + (5N + 16)/6 ≤ 24(t + 1) + 64` when
`N ≤ 24t + 64`. Everything else (preparation, copies, mirrored operations, the swap) keeps the
parameters of both cores.

Hence the word size of the wrapper state before operation `i` is
`wKom om ≤ 64·(⌊log₂(i + 1)⌋ + 8)` (`wKom_le`), and the per-operation bound of `theoremABW_M`
becomes a bound in `i` alone (`Impl/PeakFinal.lean`). Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

/-- The capacity bound after `t` operations. -/
def capB (t : Nat) : Nat := 24 * t + 64

/-- Both cores have capacity at most `X`. -/
def CapB (X : Nat) (om : OrderMaintenance) : Prop := om.cur.P.N ≤ X ∧ ∀ n, om.nxt = some n → n.P.N ≤ X

theorem CapB.mono {X Y : Nat} {om : OrderMaintenance} (h : CapB X om) (hXY : X ≤ Y) : CapB Y om :=
  ⟨le_trans h.1 hXY, fun n hn => le_trans (h.2 n hn) hXY⟩

/-! ### The rebuild keeps the parameters -/

theorem copy_P {om om' : OrderMaintenance} {n n' : Core} (hC : CopyOK om n) (hcp : copyAtCursor om n = .ok (om', n')) :
    om'.cur = om.cur ∧ n'.P = n.P := by
  unfold copyAtCursor at hcp
  cases hl : (om.cur.E.getX om.cursor).live with
  | false =>
    simp only [hl, Bool.false_eq_true, ite_false, pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; subst h2
    exact ⟨rfl, rfl⟩
  | true =>
    obtain ⟨B, hS, htl, -⟩ := hC.2 hl
    obtain ⟨c', hr', -, -, -, hP', -⟩ := hS.insert htl (om.cur.E.getX om.cursor).h
      (fun r => if r = "x" then n.tail else (om.cur.E.getX om.cursor).h) (by simp) (by simp)
    simp only [hl, ite_true, bind, Except.bind, runCore, hr', pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; subst h2
    exact ⟨rfl, hP'⟩

/-- **The rebuild loop keeps the capacities**: `cur` stays, or is replaced by `nxt` (the swap);
`nxt` keeps its parameters. -/
theorem loop_cap {X : Nat} : ∀ f b (om : OrderMaintenance) (n : Core), RLSafe om n f b → om.cur.P.N ≤ X → n.P.N ≤ X →
    ∀ R, rebuildLoop om n f b = .ok R → CapB X R := by
  intro f
  induction f with
  | zero =>
    intro b om n _ hc hn R hR
    cases hR
    exact ⟨hc, fun n' e => by cases e; exact hn⟩
  | succ f ih =>
    intro b om n hF hc hnX R hR
    by_cases hb : b = 0
    · subst hb
      rw [rebuildLoop_zero] at hR; cases hR
      exact ⟨hc, fun n' e => by cases e; exact hnX⟩
    have hF' := hF hb
    unfold rebuildLoop at hR
    rw [ite_eq_right hb] at hR
    cases hcs : om.cursorSet with
    | false =>
      rw [ite_eq_left (by simp [hcs])] at hR
      obtain ⟨hPM, hN1, -, hst⟩ := hF'.1 hcs
      cases hpr : prepareStep.run n with
      | error e s' => simp [runCore, hpr, bind, Except.bind] at hR
      | ok r n' =>
        have hrc : runCore n prepareStep = .ok (r, n') := by simp [runCore, hpr]
        simp only [bind, Except.bind, hrc] at hR
        have hP' : n'.P = n.P := (prepAgreeM hPM hN1 hpr (fun _ => 0)).2.1
        have hn' : n'.P.N ≤ X := by rw [hP']; exact hnX
        obtain ⟨-, hT, hFl⟩ := hst r n' hpr
        cases r with
        | true =>
          simp only [ite_true] at hR
          exact ih _ _ _ (hT rfl) hc hn' R hR
        | false =>
          simp only [Bool.false_eq_true, ite_false] at hR
          exact ih _ _ _ (hFl rfl) hc hn' R hR
    | true =>
      rw [ite_eq_right (by simp [hcs])] at hR
      by_cases hcN : om.cursor = NIL
      · rw [ite_eq_left hcN] at hR
        injection hR with hR; subst hR
        exact ⟨hnX, fun n' e => by cases e⟩
      · rw [ite_eq_right hcN] at hR
        obtain ⟨hCO, hnext⟩ := hF'.2 hcs hcN
        cases hcp : copyAtCursor om n with
        | error e => simp [hcp, bind, Except.bind] at hR
        | ok r =>
          obtain ⟨om', n'⟩ := r
          simp only [bind, Except.bind, hcp] at hR
          obtain ⟨e1, hP'⟩ := copy_P hCO hcp
          have hn' : n'.P.N ≤ X := by rw [hP']; exact hnX
          have hc' : om'.cur.P.N ≤ X := by rw [e1]; exact hc
          by_cases hc'N : om'.cursor = NIL
          · rw [ite_eq_left hc'N] at hR
            injection hR with hR; subst hR
            exact ⟨hn', fun n'' e => by cases e⟩
          · rw [ite_eq_right hc'N] at hR
            exact ih _ _ _ (hnext om' n' hcp hc'N) hc' hn' R hR

/-- **The rebuild step keeps the capacities**, given a bound on the capacity of a new core. -/
theorem rebuild_cap {X : Nat} {om : OrderMaintenance} (hX : MX om)
    (hF : ∀ n, om.nxt = some n → RLSafeP { om with nxt := none } n (om.KB + 1) om.KB)
    (hC : CapB X om) (hst : om.nxt = none → om.nextCapacity ≤ X) {R : OrderMaintenance}
    (hr : om.rebuildStep proofParams = .ok R) : CapB X R := by
  cases hn : om.nxt with
  | none =>
    have hR : R = om ∨ R = startOM om (prepStart (proofParams om.nextCapacity) false) := by
      unfold OrderMaintenance.rebuildStep at hr; rw [hn] at hr
      simp only at hr
      split at hr
      · simp only [newCore_true, bind, Except.bind, pure, Except.pure] at hr
        injection hr with hr; exact Or.inr hr.symm
      · injection hr with hr; exact Or.inl hr.symm
    rcases hR with rfl | rfl
    · exact hC
    · exact ⟨hC.1, fun n' e => by cases e; exact hst hn⟩
  | some n0 =>
    have hr' : rebuildLoop { om with nxt := none } n0 (om.KB + 1) om.KB = .ok R := by
      unfold OrderMaintenance.rebuildStep at hr; rw [hn] at hr; exact hr
    have hS := (loop_M _ _ _ _ (hF n0 hn) (hX.2 n0 hn) hX.1).1
    exact loop_cap _ _ _ _ hS hC.1 (hC.2 n0 hn) R hr'

/-! ### The capacity of a new core -/

theorem nextCap_le {N live cnt KB t : Nat} (h64 : 64 ≤ N) (hN : N ≤ capB t) (hl : live ≤ t + 1)
    (hc : 2 * cnt ≤ N) (hk : 4 ≤ KB) :
    4 * max (live + ((cnt + (pL N + 2)) / (KB - 1) + 1)) 16 ≤ capB (t + 1) := by
  have hL := pL_small h64
  have hdiv : (cnt + (pL N + 2)) / (KB - 1) ≤ (cnt + (pL N + 2)) / 3 :=
    Nat.div_le_div_left (by omega) (by norm_num)
  have h3 := Nat.div_mul_le_self (cnt + (pL N + 2)) 3
  unfold capB at hN ⊢
  have hm : max (live + ((cnt + (pL N + 2)) / (KB - 1) + 1)) 16 ≤ 6 * t + 22 := max_le (by omega) (by omega)
  omega

theorem nextCapacity_le {om : OrderMaintenance} {t : Nat} (h64 : 64 ≤ om.cur.P.N) (hmk : om.cur.P = proofParams om.cur.P.N)
    (hN : om.cur.P.N ≤ capB t) (hl : om.live ≤ t + 1) (hc : 2 * om.cur.count ≤ om.cur.P.N) (hk : 4 ≤ om.KB) :
    om.nextCapacity ≤ capB (t + 1) := by
  have hL : om.cur.P.L = pL om.cur.P.N := by rw [hmk]; rfl
  unfold OrderMaintenance.nextCapacity
  simp only [hL]
  exact nextCap_le h64 hN hl hc hk

/-! ### Mirroring keeps an absent `nxt` absent -/

theorem mirrorInsert_none {om om2 : OrderMaintenance} {hx : Option Nat} {hy : Nat} (hm : om.mirrorInsert hx hy = .ok om2)
    (h2 : om2.nxt = none) : om.nxt = none := by
  cases hn : om.nxt with
  | none => rfl
  | some n =>
    exfalso
    unfold OrderMaintenance.mirrorInsert at hm
    rw [hn] at hm
    simp only [bind, Except.bind, pure, Except.pure] at hm
    repeat' split at hm
    all_goals first | (injection hm with hm; subst hm) | (injection hm)
    all_goals first | (rw [hn] at h2; cases h2) | (simp at h2)

theorem mirrorDelete_none {om om2 : OrderMaintenance} {x : Nat} (hm : om.mirrorDelete x = .ok om2)
    (h2 : om2.nxt = none) : om.nxt = none := by
  cases hn : om.nxt with
  | none => rfl
  | some n =>
    exfalso
    unfold OrderMaintenance.mirrorDelete at hm
    rw [hn] at hm
    simp only [bind, Except.bind, pure, Except.pure] at hm
    repeat' split at hm
    all_goals first | (injection hm with hm; subst hm) | (injection hm)
    all_goals first | (rw [hn] at h2; cases h2) | (simp at h2)

/-! ### The operations -/

/-- **An insertion keeps the capacity bound**, one more operation counted. -/
theorem insert_cap {t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI : MInv om Sp) {hx : Option Nat}
    (hv : (insOp hx).Valid Sp) (hB : WBW t om om.nxt) (hC : CapB (capB t) om) :
    ∃ om', om.insert proofParams hx = .ok (Sp.fresh, om') ∧ CapB (capB (t + 1)) om' := by
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  obtain ⟨om', hins, -⟩ := insert_cost costSetup hW hx hv
  obtain ⟨c', om2, hr1, hm2, hsafe⟩ := insert_safe costSetup hW hx hv
  have hR' : ({ om2 with live := om2.live + 1 } : OrderMaintenance).rebuildStep proofParams = .ok om' := by
    rw [← insert_eq hr1 hm2, hf]; exact hins
  have hxS : ∀ x, hx = some x → x ∈ Sp.list := fun x e => by subst e; exact hv
  have hxL : insAnchor om hx ∈ A.elist := by
    cases hx with
    | none => exact hR.head
    | some x => exact (hIdx x (hxS x rfl)).1
  have hS0 := hI.cur hR.inv
  obtain ⟨c'', hr'', -, -, hcnt, hP'', hM''⟩ := hS0.insert hxL om.nextHandle
    (fun r => if r = "x" then insAnchor om hx else om.nextHandle) (by simp) (by simp)
  have hr1' : (insertAfter (insAnchor om hx) om.nextHandle).run om.cur = .ok om.cur.E.size c' := hr1
  rw [hr1'] at hr''
  injection hr'' with _ hcc; subst hcc
  obtain ⟨e1, e2, hX2⟩ := mirrorInsert_M (om := insOM om c' om.cur.E.size) (hx := hx) (hy := om.nextHandle)
    (fun n hn => hI.2.2 n hn) (fun n hn hs hc => hI.mirror hx n hn hs hc) hm2
  have hX3 : MX ({ om2 with live := om2.live + 1 } : OrderMaintenance) :=
    ⟨by show Mc (capsOf om2.cur.P) om2.cur.P om2.cur; rw [e1]; show Mc (capsOf c'.P) c'.P c'; rw [hP'']; exact hM'',
      fun n hn => hX2 n hn⟩
  refine ⟨om', hins, ?_⟩
  -- the bound after the insertion into `cur`, for `mirror_wbw`
  have hcW := hS0.wb hxL om.nextHandle hB.cur hr1'
  have hcf := hS0.hframe hxL om.nextHandle hr1'
  have hW1 : WBW (t + 1) (insOM om c' om.cur.E.size) (insOM om c' om.cur.E.size).nxt := by
    refine ⟨by show WB (wK c'.P) c'; rw [hP'']; exact hcW, fun c e => ?_, hB.noNxt,
      by show ArrB (wK c'.P) _; rw [hP'']; exact arrB_setX hB.curIdx hS0.Esize_lt _,
      by show om.cursor < 2 ^ wK c'.P; rw [hP'']; exact hB.cursor,
      h_le_of_frame hcf (fun i => le_trans (hB.hcur i) (Nat.le_succ _)) (Nat.le_succ _),
      le_trans hB.live (Nat.le_succ _), by show om.nextHandle + 1 ≤ t + 1; have := hB.hnd; omega,
      le_trans hB.reb (Nat.le_succ _)⟩
    obtain ⟨a1, a2, a3⟩ := hB.nxt c e
    exact ⟨a1, a2, fun i => le_trans (a3 i) (Nat.le_succ _)⟩
  obtain ⟨-, f1, f2, -, f4, f5⟩ := mirror_wbw (om := insOM om c' om.cur.E.size) hW1 (Nat.le_succ _)
    (fun n hn hs hc => hI.mirror hx n hn hs hc) hm2
  have hcur : om2.cur = c' := f1
  have hle : capB t ≤ capB (t + 1) := by unfold capB; omega
  refine rebuild_cap hX3 hsafe ⟨?_, fun n hn => ?_⟩ (fun hn => ?_) hR'
  · show om2.cur.P.N ≤ _; rw [hcur, hP'']; exact le_trans hC.1 hle
  · obtain ⟨n0, hn0, hP0⟩ := f5 n hn
    rw [hP0]; exact le_trans (hC.2 n0 hn0) hle
  · have hn0 : om.nxt = none := mirrorInsert_none (om := insOM om c' om.cur.E.size) hm2 hn
    have hidle := hW.idle hn0
    have hmk := hI.cmk
    refine nextCapacity_le (om := ({ om2 with live := om2.live + 1 } : OrderMaintenance)) ?_ ?_ ?_ ?_ ?_ ?_
    · show 64 ≤ om2.cur.P.N; rw [hcur, hP'']; exact hW.big
    · show om2.cur.P = proofParams om2.cur.P.N; rw [hcur, hP'']; exact hmk
    · show om2.cur.P.N ≤ _; rw [hcur, hP'']; exact hC.1
    · show om2.live + 1 ≤ t + 1; rw [f2]; have := hB.live; show om.live + 1 ≤ t + 1; omega
    · show 2 * om2.cur.count ≤ om2.cur.P.N; rw [hcur, hP'', hcnt]; omega
    · show 4 ≤ om2.KB; rw [f4]; exact hW.kb

/-- **A deletion keeps the capacity bound**, one more operation counted. -/
theorem delete_cap {t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI : MInv om Sp) {x : Nat}
    (hv : x ∈ Sp.list) (hB : WBW t om om.nxt) (hC : CapB (capB t) om) :
    ∃ om', om.delete proofParams x = .ok om' ∧ CapB (capB (t + 1)) om' := by
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  obtain ⟨om', hdel, -⟩ := delete_cost costSetup hW hv
  obtain ⟨c', om2, hr1, hm2, hsafe⟩ := delete_safe costSetup hW hv
  have hR' : ({ om2 with live := om2.live - 1 } : OrderMaintenance).rebuildStep proofParams = .ok om' := by
    rw [← delete_eq hr1 hm2]; exact hdel
  have hxL : om.curIdx.getX x ∈ A.elist := (hIdx x hv).1
  have hS0 := hI.cur hR.inv
  obtain ⟨c'', hr'', -, -, -, hP'', hM''⟩ := markDeadAgreeM hS0.ok.cost rfl hxL (κ := capsOf om.cur.P)
    (fun _ => om.curIdx.getX x) rfl (capsOf_ok _) hS0.ok.cnt hS0.mc
  rw [hr1] at hr''
  injection hr'' with _ hcc; subst hcc
  obtain ⟨e1, e2, -, hX2⟩ := mirrorDelete_M (om := { om with cur := c', curIdx := om.curIdx.setX x 0 }) (x := x)
    (fun n hn => hI.2.2 n hn) (fun n hn hx0 => hI.mirrorDel x n hn hx0) hm2
  have hX3 : MX ({ om2 with live := om2.live - 1 } : OrderMaintenance) :=
    ⟨by show Mc (capsOf om2.cur.P) om2.cur.P om2.cur; rw [e1]; show Mc (capsOf c'.P) c'.P c'; rw [hP'']; exact hM'',
      fun n hn => hX2 n hn⟩
  refine ⟨om', hdel, ?_⟩
  have hc' : c' = { om.cur with E := om.cur.E.modify (om.curIdx.getX x) fun e => { e with live := false } } := by
    rw [markDead_run] at hr1; cases hr1; rfl
  have hcW := markDead_wb hB.cur _ hr1
  have hP1 : c'.P = om.cur.P := by rw [hc']
  have hcnt : c'.count = om.cur.count := by rw [hc']
  have hW1 : WBW (t + 1) ({ om with cur := c', curIdx := om.curIdx.setX x 0 } : OrderMaintenance)
      ({ om with cur := c', curIdx := om.curIdx.setX x 0 } : OrderMaintenance).nxt := by
    refine ⟨by show WB (wK c'.P) c'; rw [hP1]; exact hcW, fun c e => ?_, hB.noNxt,
      by show ArrB (wK c'.P) _; rw [hP1]; exact arrB_setX hB.curIdx (pos _) _,
      by show om.cursor < 2 ^ wK c'.P; rw [hP1]; exact hB.cursor, fun i => ?_,
      le_trans hB.live (Nat.le_succ _), le_trans hB.hnd (Nat.le_succ _), le_trans hB.reb (Nat.le_succ _)⟩
    · exact hB.nxt c e
    · rw [hc']; show ((om.cur.E.modify _ _).getX i).h ≤ _
      rw [Array.getX_modify]; split
      · exact hB.hcur i
      · exact hB.hcur i
  obtain ⟨-, f1, f2, -, f5⟩ := mirrorDel_wbw hW1 hm2
  have hcur : om2.cur = c' := f1
  have hle : capB t ≤ capB (t + 1) := by unfold capB; omega
  refine rebuild_cap hX3 hsafe ⟨?_, fun n hn => ?_⟩ (fun hn => ?_) hR'
  · show om2.cur.P.N ≤ _; rw [hcur, hP1]; exact le_trans hC.1 hle
  · obtain ⟨n0, hn0, hP0⟩ := f5 n hn
    rw [hP0]; exact le_trans (hC.2 n0 hn0) hle
  · have hn0 : om.nxt = none := mirrorDelete_none (om := { om with cur := c', curIdx := om.curIdx.setX x 0 }) hm2 hn
    have hidle := hW.idle hn0
    have hmk := hI.cmk
    refine nextCapacity_le (om := ({ om2 with live := om2.live - 1 } : OrderMaintenance)) ?_ ?_ ?_ ?_ ?_ ?_
    · show 64 ≤ om2.cur.P.N; rw [hcur, hP1]; exact hW.big
    · show om2.cur.P = proofParams om2.cur.P.N; rw [hcur, hP1]; exact hmk
    · show om2.cur.P.N ≤ _; rw [hcur, hP1]; exact hC.1
    · show om2.live - 1 ≤ t + 1; rw [f2]; have := hB.live; show om.live - 1 ≤ t + 1; omega
    · show 2 * om2.cur.count ≤ om2.cur.P.N; rw [hcur, hP1, hcnt]; omega
    · show 4 ≤ om2.KB; rw [e2]; exact hW.kb

/-! ### The reachable states -/

/-- **The capacities along the history**: after `t` operations both cores have capacity at most
`24·t + 64`. -/
theorem reachW_cap {KB : Nat} (h4 : 4 ≤ KB) {t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
    (h : ReachW KB t om Sp) : CapB (capB t) om := by
  induction h with
  | init hi =>
    obtain ⟨n, hnew, hrun⟩ := newCore_run (P := proofParams minimumCapacity) (lazy := false)
    unfold OrderMaintenance.init at hi
    simp only [bind, Except.bind, hnew, pure, Except.pure] at hi
    injection hi with hi; subst hi
    obtain ⟨-, hPn⟩ := initCore_fields hrun
    refine ⟨?_, fun n' e => by cases e⟩
    show n.P.N ≤ capB 0
    rw [hPn]; show minimumCapacity ≤ capB 0; unfold capB minimumCapacity; omega
  | @step t om om' Sp op a hR hv hr ih =>
    obtain ⟨hI, hB, -⟩ := reachW_inv h4 hR
    cases op with
    | insertFirst =>
      obtain ⟨om'', hins, hC⟩ := insert_cap hI (hx := none) hv hB ih
      unfold OrderMaintenance.apply at hr
      simp only [bind, Except.bind, hins, pure, Except.pure] at hr
      injection hr with hr; injection hr with _ h2; subst h2; exact hC
    | insertAfter x =>
      obtain ⟨om'', hins, hC⟩ := insert_cap hI (hx := some x) hv hB ih
      unfold OrderMaintenance.apply at hr
      simp only [bind, Except.bind, hins, pure, Except.pure] at hr
      injection hr with hr; injection hr with _ h2; subst h2; exact hC
    | delete x =>
      obtain ⟨om'', hdel, hC⟩ := delete_cap hI hv hB ih
      unfold OrderMaintenance.apply at hr
      simp only [bind, Except.bind, hdel, pure, Except.pure] at hr
      injection hr with hr; injection hr with _ h2; subst h2; exact hC
    | order x y =>
      unfold OrderMaintenance.apply at hr
      simp only [bind, Except.bind, pure, Except.pure] at hr
      split at hr
      · cases hr
      · injection hr with hr; injection hr with _ h2; subst h2
        exact ih.mono (by unfold capB; omega)

/-! ### The word size along the history -/

theorem log2_capB (t : Nat) : Nat.log2 (capB t) + 1 ≤ Nat.log2 (t + 1) + 7 := by
  have h1 : t + 1 < 2 ^ (Nat.log2 (t + 1) + 1) := Nat.lt_log2_self
  have h2 : capB t < 2 ^ (Nat.log2 (t + 1) + 7) := by
    rw [show Nat.log2 (t + 1) + 7 = (Nat.log2 (t + 1) + 1) + 6 by omega, pow_add]
    unfold capB; norm_num; omega
  have := (Nat.log2_lt (n := capB t) (by unfold capB; omega)).2 h2
  omega

theorem pL_mono {a b : Nat} (h : a ≤ b) : pL a ≤ pL b := by
  unfold pL; exact max_le_max le_rfl (Nat.size_le_size h)

theorem pL_capB (t : Nat) : pL (capB t) ≤ Nat.log2 (t + 1) + 8 := by
  rw [pL_eq (by unfold capB; omega)]
  have := log2_capB t
  apply max_le <;> omega

/-- **The word size before operation `t`**: `wKom om ≤ 64·(⌊log₂(t + 1)⌋ + 8)`. -/
theorem wKom_le {KB : Nat} (h4 : 4 ≤ KB) {t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
    (h : ReachW KB t om Sp) : wKom om ≤ 64 * (Nat.log2 (t + 1) + 8) := by
  obtain ⟨hI, -, -⟩ := reachW_inv h4 h
  have hC := reachW_cap h4 h
  have hw : ∀ P : Params, P = proofParams P.N → P.N ≤ capB t → wK P ≤ 64 * (Nat.log2 (t + 1) + 8) :=
    fun P hP hN => by
      rw [hP]; show 64 * pL P.N ≤ _
      exact Nat.mul_le_mul_left 64 (le_trans (pL_mono hN) (pL_capB t))
  unfold wKom
  apply max_le (hw _ hI.cmk hC.1)
  split
  · next n hn => exact hw _ (hI.nP hn) (hC.2 n hn)
  · exact Nat.zero_le _

end OrderMaintenance.Impl

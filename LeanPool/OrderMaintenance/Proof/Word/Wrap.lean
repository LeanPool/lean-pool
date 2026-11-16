/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.Serve


/-!
# Theorem W, stage B3: the wrapper's stored values

`WBW t om nx`: the wrapper state `om`, with next core `nx`, after `t` operations: each core
bounded at its own word size (`WB (wK c.P) c`), the element index arrays and the cursor bounded at
their core's word size, every handle stored in a core at most `nextHandle`, and the counters
(`live`, `nextHandle`, `rebuilds`) at most `t`. The next core is a separate argument because the
rebuild loop holds it outside the record.

This file proves that the wrapper's operations keep `WBW`, along the Level M invariant `MInv` (whose
`InService`, `CopyOK` and `PrepM` contexts give each core operation its hypotheses):
* `loop_wb`: the rebuild loop (preparation steps, copy steps, the swap), following `RLSafe`;
* `rebuild_wb`: the rebuild step (a fresh core, or the loop);
* `insert_wbw`, `delete_wbw`: an insertion and a deletion (the core operation on `cur`, the
  mirrored one on `nxt`, the rebuild step).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top OrderMaintenance.Impl
/-! ### The predicate -/

/-- **The wrapper's values**, each core at its own word size. -/
structure WBW (t : Nat) (om : OrderMaintenance) (nx : Option Core) : Prop where
  cur : WB (wK om.cur.P) om.cur
  nxt : ∀ c, nx = some c → WB (wK c.P) c ∧ ArrB (wK c.P) om.nxtIdx ∧ ∀ i, (c.E.getX i).h ≤
    om.nextHandle
  noNxt : nx = none → ∀ i, om.nxtIdx.getX i = 0
  curIdx : ArrB (wK om.cur.P) om.curIdx
  cursor : om.cursor < 2 ^ wK om.cur.P
  hcur : ∀ i, (om.cur.E.getX i).h ≤ om.nextHandle
  live : om.live ≤ t
  hnd : om.nextHandle ≤ t
  reb : om.rebuilds ≤ t

theorem WBW.withNxt {t : Nat} {om : OrderMaintenance} {nx : Option Core} (h : WBW t om nx) (y :
  Option Core) :
    WBW t {
      om with
      nxt := y
    } nx :=
  ⟨h.cur, h.nxt, h.noNxt, h.curIdx, h.cursor, h.hcur, h.live, h.hnd, h.reb⟩

/-- **The swap**: `nxt` becomes `cur`, its index array `curIdx`. -/
theorem WBW.swap {t : Nat} {om : OrderMaintenance} {n : Core} (h : WBW t om (some n)) (hc :
  om.cursor = NIL) :
    WBW t (om.swap n) none := by
  obtain ⟨hn, hidx, hh⟩ := h.nxt n rfl
  exact ⟨hn, (fun c e => nomatch e), fun _ i => by simp [OrderMaintenance.swap], hidx, by
    change om.cursor < _; rw [hc]; exact pos _, hh, h.live, h.hnd, h.reb⟩

/-! ### Facts about a core in service -/

/-- The element count of a core in service is far below its word size. -/
theorem _root_.OrderMaintenance.Impl.InService.Esize_lt {c : Core} {L : List Nat} (h : InService
  c L) :
    c.E.size < 2 ^ wK c.P := by
  have hmk : c.P = proofParams c.P.N := h.ok.pmk
  obtain ⟨A, hI, hel⟩ := h.ok.cost.low.inv
  have hE := E_size_le hI
  rw [hel, ← h.ok.cnt] at hE
  have hr := h.room
  have := (room_counts c.P.N hr hE (le_refl (2 + 2 * c.count))).1
  rw [← hmk] at this
  omega

/-- **The handles across an insertion into a core in service**: the new element gets `hh`. -/
theorem _root_.OrderMaintenance.Impl.InService.hframe {c : Core} {L : List Nat} (h : InService c
  L) {x : Nat}
    (hx : x ∈ L) (hh : Nat) {y : Nat} {c' : Core} (hr : (insertAfter x hh).run c = .ok y c') :
    ∀ e, (c'.E.getX e).h = if e = c.E.size then hh else (c.E.getX e).h := by
  obtain ⟨A, hI, hel⟩ := h.ok.cost.low.inv
  have hP : CoreP c.P := by rw [h.ok.pmk]; exact core_proof _
  obtain ⟨s', A', hr', -, -, F⟩ := insertAfter_run hI (hel ▸ hx) hP hh
  rw [hr] at hr'
  obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr'
  exact F.h

theorem h_le_of_frame {c c' : Core} {hh B : Nat} (hf : ∀ e, (c'.E.getX e).h = if e = c.E.size
  then hh else (c.E.getX e).h)
    (hc : ∀ i, (c.E.getX i).h ≤ B) (hb : hh ≤ B) : ∀ i, (c'.E.getX i).h ≤ B := fun i => by
  rw [hf i]; split
  · exact hb
  · exact hc i

/-! ### The rebuild loop -/

/-- **A copy step** keeps the bound: the copied element goes after the tail of `nxt` (a core in
service), with its handle; the index array records its index; the cursor moves on. -/
theorem copy_wbw {t : Nat} {om om' : OrderMaintenance} {n n' : Core} (hC : CopyOK om n) (h : WBW
  t om (some n))
    (hcp : copyAtCursor om n = .ok (om', n')) : WBW t om' (some n') ∧ n'.P = n.P := by
  obtain ⟨hn, hidx, hh⟩ := h.nxt n rfl
  have hnx := h.cur.eNext om.cursor
  unfold copyAtCursor at hcp
  cases hl : (om.cur.E.getX om.cursor).live with
  | false =>
    simp only [hl, Bool.false_eq_true, ite_false, pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; subst h2
    exact ⟨⟨h.cur, fun c e => by cases e; exact ⟨hn, hidx, hh⟩, (fun e => nomatch e), h.curIdx, hnx,
      h.hcur, h.live, h.hnd, h.reb⟩, rfl⟩
  | true =>
    obtain ⟨B, hS, htl, hlt⟩ := hC.2 hl
    obtain ⟨c', hr', -, -, -, hP', -⟩ := hS.insert htl (om.cur.E.getX om.cursor).h
      (fun r => if r = "x" then n.tail else (om.cur.E.getX om.cursor).h) (by simp) (by simp)
    have hf := hS.hframe htl _ hr'
    have hW' := hS.wb htl _ hn hr'
    have hE := hS.Esize_lt
    simp only [hl, ite_true, bind, Except.bind, runCore, hr', pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; subst h2
    refine ⟨⟨h.cur, fun c e => ?_, (fun e => nomatch e), h.curIdx, hnx, h.hcur, h.live, h.hnd,
      h.reb⟩, hP'⟩
    cases e
    rw [hP']
    exact ⟨hW', arrB_setX hidx hE _, h_le_of_frame hf hh (le_of_lt hlt)⟩

/-- **The rebuild loop keeps the bound**, along Level M's loop context `RLSafe`: preparation
steps (`PrepM`), copy steps (`CopyOK`), the swap. The counters do not change. -/
theorem loop_wb {t : Nat} : ∀ f b (om : OrderMaintenance) (n : Core), RLSafe om n f b → n.P =
  proofParams n.P.N →
    WBW t om (some n) → ∀ R, rebuildLoop om n f b = .ok R → WBW t R R.nxt := by
  intro f
  induction f with
  | zero =>
    intro b om n _ _ hW R hR
    cases hR
    exact hW.withNxt _
  | succ f ih =>
    intro b om n hF hmk hW R hR
    by_cases hb : b = 0
    · subst hb
      rw [rebuildLoop_zero] at hR; cases hR
      exact hW.withNxt _
    have hF' := hF hb
    obtain ⟨hn, hidx, hh⟩ := hW.nxt n rfl
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
        have hW' := hPM.wb hmk hn hpr
        have hP' : n'.P = n.P := (prepAgreeM hPM hN1 hpr (fun _ => 0)).2.1
        have hE : ∀ i, (n'.E.getX i).h = (n.E.getX i).h := by
          have := pres_prepareStep n; rw [hpr] at this; exact this.eH
        have hmk' : n'.P = proofParams n'.P.N := by rw [hP']; exact hmk
        have hnx : ∀ c, some n' = some c → WB (wK c.P) c ∧ ArrB (wK c.P) om.nxtIdx ∧
            ∀ i, (c.E.getX i).h ≤ om.nextHandle := fun c e => by
          cases e; rw [hP']; exact ⟨hW', hidx, fun i => by rw [hE]; exact hh i⟩
        obtain ⟨-, hT, hFl⟩ := hst r n' hpr
        cases r with
        | true =>
          simp only [ite_true] at hR
          exact ih _ _ _ (hT rfl) hmk' ⟨hW.cur, hnx, (fun e => nomatch e), hW.curIdx,
            hW.cur.eNext _, hW.hcur,
            hW.live, hW.hnd, hW.reb⟩ R hR
        | false =>
          simp only [Bool.false_eq_true, ite_false] at hR
          exact ih _ _ _ (hFl rfl) hmk' ⟨hW.cur, hnx, (fun e => nomatch e), hW.curIdx,
            hW.cursor, hW.hcur,
            hW.live, hW.hnd, hW.reb⟩ R hR
    | true =>
      rw [ite_eq_right (by simp [hcs])] at hR
      by_cases hc : om.cursor = NIL
      · rw [ite_eq_left hc] at hR
        injection hR with hR; subst hR
        exact hW.swap hc
      · rw [ite_eq_right hc] at hR
        obtain ⟨hCO, hnext⟩ := hF'.2 hcs hc
        cases hcp : copyAtCursor om n with
        | error e => simp [hcp, bind, Except.bind] at hR
        | ok r =>
          obtain ⟨om', n'⟩ := r
          simp only [bind, Except.bind, hcp] at hR
          obtain ⟨hW', hP'⟩ := copy_wbw hCO hW hcp
          by_cases hc' : om'.cursor = NIL
          · rw [ite_eq_left hc'] at hR
            injection hR with hR; subst hR
            exact hW'.swap hc'
          · rw [ite_eq_right hc'] at hR
            exact ih _ _ _ (hnext om' n' hcp hc') (by
              rw [hP']
              exact hmk) hW' R hR

/-! ### The rebuild step -/

/-- The fresh core of a rebuild start has no handles yet. -/
theorem prepStart_h (P : Params) (r : Bool) : ∀ i, ((prepStart P r).E.getX i).h = 0 := by
  intro i
  refine getX_of (p := fun e : Elem => e.h = 0) rfl (fun x hx => ?_) i
  simp only [prepStart, initState, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl <;> rfl

/-- **The rebuild step keeps the bound**: a rebuild start (a fresh core, `wb_prepStart`; one more
rebuild), or the loop (`loop_wb`, with Level M's loop context from `loop_M`). -/
theorem rebuild_wb {t : Nat} {om : OrderMaintenance} (hX : MX om)
    (hF : ∀ n, om.nxt = some n → RLSafeP {
      om with
      nxt := none
    } n (om.KB + 1) om.KB)
    (hmkN : ∀ n, om.nxt = some n → n.P = proofParams n.P.N)
    (hB : WBW t om om.nxt) (hreb : om.rebuilds + 1 ≤ t) {R : OrderMaintenance}
    (hr : om.rebuildStep proofParams = .ok R) : WBW t R R.nxt := by
  cases hn : om.nxt with
  | none =>
    rw [hn] at hB
    have hR : R = om ∨ R = startOM om (prepStart (proofParams om.nextCapacity) false) := by
      unfold OrderMaintenance.rebuildStep at hr; rw [hn] at hr
      simp only at hr
      split at hr
      · simp only [newCore_true, bind, Except.bind, pure, Except.pure] at hr
        injection hr with hr; exact Or.inr hr.symm
      · injection hr with hr; exact Or.inl hr.symm
    rcases hR with rfl | rfl
    · rw [hn]; exact hB
    · obtain ⟨hL, -⟩ := room_wK om.nextCapacity
      refine ⟨hB.cur, fun c e => ?_, (fun e => nomatch e), hB.curIdx, hB.cursor, hB.hcur,
        hB.live, hB.hnd,
        by change om.rebuilds + 1 ≤ t; exact hreb⟩
      cases e
      exact ⟨wb_prepStart (params_wB _) hL false, arrB_empty _, fun i => by
        rw [prepStart_h]
        exact Nat.zero_le _⟩
  | some n0 =>
    have hr' : rebuildLoop {
      om with
      nxt := none
    } n0 (om.KB + 1) om.KB = .ok R := by
      unfold OrderMaintenance.rebuildStep at hr; rw [hn] at hr; exact hr
    have hS := (loop_M _ _ _ _ (hF n0 hn) (hX.2 n0 hn) hX.1).1
    rw [hn] at hB
    exact loop_wb _ _ _ _ hS (hmkN n0 hn) (hB.withNxt none) R hr'

/-! ### Mirroring an insertion -/

/-- **A mirrored insertion keeps the bound**: the insertion into `nxt` (a core in service, at the
mirrored anchor), its index, its handle. -/
theorem mirror_wbw {t : Nat} {om : OrderMaintenance} {hx : Option Nat} {hy : Nat} (hB : WBW t om
  om.nxt)
    (hhy : hy ≤ om.nextHandle)
    (hN : ∀ n, om.nxt = some n → om.cursorSet = true →
      (hx = none ∨ ∃ x, hx = some x ∧ om.nxtIdx.getX x ≠ 0) → ∃ B, InService n B ∧ mirAnchor om
        n hx ∈ B)
    {om2 : OrderMaintenance} (hm : om.mirrorInsert hx hy = .ok om2) :
    WBW t om2 om2.nxt ∧ om2.cur = om.cur ∧ om2.live = om.live ∧ om2.rebuilds = om.rebuilds ∧
      om2.KB = om.KB ∧ ∀ n', om2.nxt = some n' → ∃ n, om.nxt = some n ∧ n'.P = n.P := by
  have hkeep : om2 = om → WBW t om2 om2.nxt ∧ om2.cur = om.cur ∧ om2.live = om.live ∧
      om2.rebuilds = om.rebuilds ∧ om2.KB = om.KB ∧ ∀ n', om2.nxt = some n' → ∃ n, om.nxt = some
        n ∧ n'.P = n.P := by
    rintro rfl
    exact ⟨hB, rfl, rfl, rfl, rfl, fun n' h => ⟨n', h, rfl⟩⟩
  unfold OrderMaintenance.mirrorInsert at hm
  split at hm
  · next hn => injection hm with hm; exact hkeep hm.symm
  · next n hn =>
    rw [hn] at hB
    obtain ⟨hWn, hidx, hh⟩ := hB.nxt n rfl
    have hmir : ∀ xn, om.cursorSet = true → (hx = none ∨ ∃ x, hx = some x ∧ om.nxtIdx.getX x ≠ 0) →
        xn = mirAnchor om n hx →
        (do let r ← runCore n (insertAfter xn hy)
            pure ({
              om with
              nxt := some r.2
              nxtIdx := om.nxtIdx.setX hy r.1
              cursorSet := true
            } : OrderMaintenance)) = .ok om2 →
        WBW t om2 om2.nxt ∧ om2.cur = om.cur ∧ om2.live = om.live ∧ om2.rebuilds = om.rebuilds ∧
          om2.KB = om.KB ∧ ∀ n', om2.nxt = some n' → ∃ n₀, om.nxt = some n₀ ∧ n'.P = n₀.P := by
      intro xn hs hcp hxn hm
      obtain ⟨B, hS, hxB⟩ := hN n hn hs hcp
      rw [← hxn] at hxB
      obtain ⟨c', hr, -, -, -, hP', -⟩ := hS.insert hxB hy
        (fun r => if r = "x" then xn else hy) (by simp) (by simp)
      have hf := hS.hframe hxB hy hr
      have hW' := hS.wb hxB hy hWn hr
      have hE := hS.Esize_lt
      simp only [bind, Except.bind, runCore, hr, pure, Except.pure] at hm
      injection hm with hm; subst hm
      refine ⟨⟨hB.cur, fun c e => ?_, (fun e => nomatch e), hB.curIdx, hB.cursor, hB.hcur,
        hB.live, hB.hnd,
        hB.reb⟩, rfl, rfl, rfl, rfl, fun n' h => ⟨n, hn, by cases h; exact hP'⟩⟩
      cases e
      rw [hP']
      exact ⟨hW', arrB_setX hidx hE _, h_le_of_frame hf hh hhy⟩
    by_cases hs : om.cursorSet = true
    · cases hx with
      | none =>
        simp only [hs, Bool.true_and, ite_true] at hm
        exact hmir n.head hs (Or.inl rfl) rfl hm
      | some x =>
        by_cases hx0 : om.nxtIdx.getX x = 0
        · simp only [hx0, hs, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false,
          pure,
            Except.pure] at hm
          injection hm with hm; exact hkeep hm.symm
        · have : (om.nxtIdx.getX x != 0) = true := by simp [hx0]
          simp only [hs, this, Bool.and_self, ite_true] at hm
          exact hmir (om.nxtIdx.getX x) hs (Or.inr ⟨x, rfl, hx0⟩) rfl hm
    · have hs' : om.cursorSet = false := by simpa using hs
      simp only [hs', Bool.false_and, Bool.false_eq_true, ite_false, pure, Except.pure] at hm
      injection hm with hm; exact hkeep hm.symm

/-! ### Mirroring a deletion -/

theorem mirrorDel_wbw {t : Nat} {om : OrderMaintenance} {x : Nat} (hB : WBW t om om.nxt) {om2 :
  OrderMaintenance}
    (hm : om.mirrorDelete x = .ok om2) :
    WBW t om2 om2.nxt ∧ om2.cur = om.cur ∧ om2.live = om.live ∧ om2.rebuilds = om.rebuilds ∧
      ∀ n', om2.nxt = some n' → ∃ n, om.nxt = some n ∧ n'.P = n.P := by
  unfold OrderMaintenance.mirrorDelete at hm
  split at hm
  · next hn => injection hm with hm; subst hm; exact ⟨hB, rfl, rfl, rfl, fun n' h => ⟨n', h, rfl⟩⟩
  · next n hn =>
    rw [hn] at hB
    obtain ⟨hWn, hidx, hh⟩ := hB.nxt n rfl
    by_cases hx0 : om.nxtIdx.getX x = 0
    · simp only [hx0, bne_self_eq_false, Bool.false_eq_true, ite_false, pure, Except.pure] at hm
      injection hm with hm; subst hm
      exact ⟨by rw [hn]; exact hB, rfl, rfl, rfl, fun n' h => ⟨n', h, rfl⟩⟩
    · have : (om.nxtIdx.getX x != 0) = true := by simp [hx0]
      simp only [this, ite_true, bind, Except.bind, runCore, markDead_run, pure, Except.pure] at hm
      injection hm with hm; subst hm
      have hW' := markDead_wb hWn (om.nxtIdx.getX x) (markDead_run n _)
      refine ⟨⟨hB.cur, fun c e => ?_, (fun e => nomatch e), hB.curIdx, hB.cursor, hB.hcur,
        hB.live, hB.hnd,
        hB.reb⟩, rfl, rfl, rfl, fun n' h => ⟨n, hn, by cases h; rfl⟩⟩
      cases e
      refine ⟨hW', arrB_setX hidx (pos _) _, fun i => ?_⟩
      change ((n.E.modify _ _).getX i).h ≤ _
      rw [Array.getX_modify]; split
      · exact hh i
      · exact hh i

/-! ### The operations -/

theorem _root_.OrderMaintenance.Impl.MInv.nP {om : OrderMaintenance} {Sp :
  OrderMaintenance.Spec.State} (hI : MInv om Sp) {n : Core}
    (hn : om.nxt = some n) : n.P = proofParams n.P.N := by
  obtain ⟨c₀, live₀, I, D, hRW⟩ := hI.1.busy n hn
  rw [hRW.nP]; rfl

theorem WBW.mono {t t' : Nat} {om : OrderMaintenance} {nx : Option Core} (h : WBW t om nx) (ht :
  t ≤ t') : WBW t' om nx :=
  ⟨h.cur, h.nxt, h.noNxt, h.curIdx, h.cursor, h.hcur, le_trans h.live ht, le_trans h.hnd ht,
    le_trans h.reb ht⟩

/-- Inserting into the current core preserves the wrapper's stored-value bounds,
with one additional operation counted. -/
theorem insert_core_wbw {t : Nat} {om : OrderMaintenance} {L : List Nat}
    (hS : InService om.cur L) {hx : Option Nat} {c' : Core} (hxL : insAnchor om hx ∈ L)
    (hB : WBW t om om.nxt) (hP : c'.P = om.cur.P)
    (hr : (insertAfter (insAnchor om hx) om.nextHandle).run om.cur = .ok om.cur.E.size c') :
    WBW (t + 1) (insOM om c' om.cur.E.size) (insOM om c' om.cur.E.size).nxt := by
  have hcW := hS.wb hxL om.nextHandle hB.cur hr
  have hcf := hS.hframe hxL om.nextHandle hr
  refine ⟨by change WB (wK c'.P) c'; rw [hP]; exact hcW, fun c e => ?_, hB.noNxt,
    by change ArrB (wK c'.P) _; rw [hP]; exact arrB_setX hB.curIdx hS.Esize_lt _,
    by change om.cursor < 2 ^ wK c'.P; rw [hP]; exact hB.cursor,
    h_le_of_frame hcf (fun i => le_trans (hB.hcur i) (Nat.le_succ _)) (Nat.le_succ _),
    le_trans hB.live (Nat.le_succ _), by change om.nextHandle + 1 ≤ t + 1; have := hB.hnd; omega,
    le_trans hB.reb (Nat.le_succ _)⟩
  obtain ⟨a1, a2, a3⟩ := hB.nxt c e
  exact ⟨a1, a2, fun i => le_trans (a3 i) (Nat.le_succ _)⟩

/-- Marking a current element dead preserves all stored-value bounds and advances
only the history allowance. -/
theorem markDead_wbw {t : Nat} {om : OrderMaintenance} {c' : Core} {x : Nat}
    (hB : WBW t om om.nxt) (hr : (markDead (om.curIdx.getX x)).run om.cur = .ok () c') :
    WBW (t + 1) { om with cur := c', curIdx := om.curIdx.setX x 0 }
      ({ om with cur := c', curIdx := om.curIdx.setX x 0 } : OrderMaintenance).nxt := by
  have hc' : c' = {
    om.cur with
    E := om.cur.E.modify (om.curIdx.getX x) fun e => {
      e with
      live := false
    }
  } := by
    rw [markDead_run] at hr; cases hr; rfl
  have hcW := markDead_wb hB.cur _ hr
  have hP1 : c'.P = om.cur.P := by rw [hc']
  refine ⟨by change WB (wK c'.P) c'; rw [hP1]; exact hcW, fun c e => ?_, hB.noNxt,
    by change ArrB (wK c'.P) _; rw [hP1]; exact arrB_setX hB.curIdx (pos _) _,
    by change om.cursor < 2 ^ wK c'.P; rw [hP1]; exact hB.cursor, fun i => ?_,
    le_trans hB.live (Nat.le_succ _), le_trans hB.hnd (Nat.le_succ _), le_trans hB.reb
      (Nat.le_succ _)⟩
  · exact hB.nxt c e
  · rw [hc']; change ((om.cur.E.modify _ _).getX i).h ≤ _
    rw [Array.getX_modify]; split
    · exact hB.hcur i
    · exact hB.hcur i

/-- **An insertion keeps the Level M invariant and the bound.** -/
theorem insert_step {t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI :
  MInv om Sp) {hx : Option Nat}
    (hv : (insOp hx).Valid Sp) (hB : WBW t om om.nxt) :
    ∃ om', om.insert proofParams hx = .ok (Sp.fresh, om') ∧ MInv om' (OrderMaintenance.Spec.step
      Sp (insOp hx)).1 ∧
      WBW (t + 1) om' om'.nxt ∧ om'.KB = om.KB := by
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  obtain ⟨om', c', om2, hins, hI', hr1, hm2, hsafe, hR', hP'', hcnt, e1, e2, hX3⟩ :=
    hI.insert_prefix hv
  have hxS : ∀ x, hx = some x → x ∈ Sp.list := fun x e => by subst e; exact hv
  have hxL : insAnchor om hx ∈ A.elist := by
    cases hx with
    | none => exact hR.head
    | some x => exact (hIdx x (hxS x rfl)).1
  have hS0 := hI.cur hR.inv
  have hr1' : (insertAfter (insAnchor om hx) om.nextHandle).run om.cur = .ok om.cur.E.size c' := hr1
  refine ⟨om', hins, hI', ?_, (rebuildStep_KB hR').trans e2⟩
  -- the bound after the insertion into `cur`
  have hW1 := insert_core_wbw hS0 hxL hB hP'' hr1'
  -- the mirrored insertion
  obtain ⟨hW2, f1, f2, f3, -, f5⟩ := mirror_wbw (om := insOM om c' om.cur.E.size) hW1
    (Nat.le_succ _)
    (fun n hn hs hc => hI.mirror hx n hn hs hc) hm2
  have hB3 : WBW (t + 1) ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance) om2.nxt :=
    ⟨hW2.cur, hW2.nxt, hW2.noNxt, hW2.curIdx, hW2.cursor, hW2.hcur,
      by change om2.live + 1 ≤ t + 1; rw [f2]; have := hB.live; change om.live + 1 ≤ t + 1; omega,
        hW2.hnd, hW2.reb⟩
  have hrb : ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance).rebuilds + 1 ≤ t + 1 := by
    change om2.rebuilds + 1 ≤ t + 1
    rw [f3]; have := hB.reb; change om.rebuilds + 1 ≤ t + 1; omega
  refine rebuild_wb hX3 hsafe (fun n hn => ?_) hB3 hrb hR'
  obtain ⟨n0, hn0, hP0⟩ := f5 n hn
  rw [hP0]; exact hI.nP hn0

/-- **A deletion keeps the Level M invariant and the bound.** -/
theorem delete_step {t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI :
  MInv om Sp) {x : Nat}
    (hv : x ∈ Sp.list) (hB : WBW t om om.nxt) :
    ∃ om', om.delete proofParams x = .ok om' ∧ MInv om' (OrderMaintenance.Spec.step Sp (.delete
      x)).1 ∧
      WBW (t + 1) om' om'.nxt ∧ om'.KB = om.KB := by
  obtain ⟨om', c', om2, hdel, hI', hr1, hm2, hsafe, hR', hP'', e1, e2, hX3⟩ :=
    hI.delete_prefix hv
  refine ⟨om', hdel, hI', ?_, (rebuildStep_KB hR').trans e2⟩
  -- the bound after the deletion in `cur`
  have hW1 := markDead_wbw hB hr1
  obtain ⟨hW2, f1, f2, f3, f5⟩ := mirrorDel_wbw hW1 hm2
  have hB3 : WBW (t + 1) ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance) om2.nxt :=
    ⟨hW2.cur, hW2.nxt, hW2.noNxt, hW2.curIdx, hW2.cursor, hW2.hcur,
      by change om2.live - 1 ≤ t + 1; have := hW2.live; omega, hW2.hnd, hW2.reb⟩
  have hrb : ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance).rebuilds + 1 ≤ t + 1 := by
    change om2.rebuilds + 1 ≤ t + 1
    rw [f3]; have := hB.reb; change om.rebuilds + 1 ≤ t + 1; omega
  refine rebuild_wb hX3 hsafe (fun n hn => ?_) hB3 hrb hR'
  obtain ⟨n0, hn0, hP0⟩ := f5 n hn
  rw [hP0]; exact hI.nP hn0

/-! ### Initialization -/

theorem initState_h (P : Params) : ∀ i, ((initState P).E.getX i).h = 0 := by
  intro i
  refine getX_of (p := fun e : Elem => e.h = 0) rfl (fun x hx => ?_) i
  simp only [initState, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> rfl

/-- **Initialization**: the Level M invariant and the bound after no operation. -/
theorem init_step {KB : Nat} (h4 : 4 ≤ KB) :
    ∃ om, OrderMaintenance.init proofParams KB = .ok om ∧ MInv om
      OrderMaintenance.Spec.State.empty ∧ WBW 0 om om.nxt := by
  obtain ⟨om, hinit, hW⟩ := init_cost costSetup h4
  obtain ⟨n, hnew, hrun⟩ := newCore_run (P := proofParams minimumCapacity) (lazy := false)
  have hom : om = {
    cur := n
    KB := KB
  } := by
    unfold OrderMaintenance.init at hinit
    simp only [bind, Except.bind, hnew] at hinit
    injection hinit with h; exact h.symm
  subst hom
  obtain ⟨-, hPn⟩ := initCore_fields hrun
  have hPn' : n.P = proofParams minimumCapacity := hPn
  have hM : Mc (capsOf n.P) n.P n := by
    rw [hPn']
    exact eager_M (s := {
      P := proofParams minimumCapacity
    }) (pp_topPP _) (by decide) hrun
  refine ⟨_, hinit, ⟨hW, hM, fun n' h => by cases h⟩, ?_⟩
  have hWn : WB (wK n.P) n := by rw [hPn']; exact newCore_wK hnew
  have hh : ∀ i, (n.E.getX i).h = 0 := by
    have hr : (initTop false).run (initState (proofParams minimumCapacity)) = .ok () n := by
      unfold initCore at hrun
      simp only [run_getP_bind] at hrun
      rw [run_bind, run_set] at hrun
      exact hrun
    have := pres_initTop false (initState (proofParams minimumCapacity))
    rw [hr] at this
    intro i; rw [this.eH i]; exact initState_h _ i
  exact ⟨hWn, (fun c e => nomatch e), (fun _ i => by simp [Array.getX]), arrB_empty _, pos _,
    fun i => le_of_eq (hh i), le_refl _, le_refl _, le_refl _⟩

/-! ### An operation -/

/-- **An operation keeps the Level M invariant and the bound**, one more operation counted. -/
theorem apply_step {t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI :
  MInv om Sp) {op : OrderMaintenance.Spec.Op}
    (hv : op.Valid Sp) (hB : WBW t om om.nxt) {a : OrderMaintenance.Spec.Ans} {om' :
      OrderMaintenance}
    (hr : om.apply proofParams op = .ok (a, om')) :
    MInv om' (OrderMaintenance.Spec.step Sp op).1 ∧ WBW (t + 1) om' om'.nxt ∧ om'.KB = om.KB := by
  cases op with
  | insertFirst =>
    obtain ⟨om'', hins, hI', hB', hK⟩ := insert_step hI (hx := none) hv hB
    unfold OrderMaintenance.apply at hr
    simp only [bind, Except.bind, hins, pure, Except.pure] at hr
    injection hr with hr; injection hr with h1 h2; subst h2
    exact ⟨hI', hB', hK⟩
  | insertAfter x =>
    obtain ⟨om'', hins, hI', hB', hK⟩ := insert_step hI (hx := some x) hv hB
    unfold OrderMaintenance.apply at hr
    simp only [bind, Except.bind, hins, pure, Except.pure] at hr
    injection hr with hr; injection hr with h1 h2; subst h2
    exact ⟨hI', hB', hK⟩
  | delete x =>
    obtain ⟨om'', hdel, hI', hB', hK⟩ := delete_step hI hv hB
    unfold OrderMaintenance.apply at hr
    simp only [bind, Except.bind, hdel, pure, Except.pure] at hr
    injection hr with hr; injection hr with h1 h2; subst h2
    exact ⟨hI', hB', hK⟩
  | order x y =>
    unfold OrderMaintenance.apply at hr
    simp only [bind, Except.bind, pure, Except.pure] at hr
    split at hr
    · cases hr
    · injection hr with hr; injection hr with h1 h2; subst h2
      exact ⟨hI, hB.mono (Nat.le_succ t), rfl⟩

/-! ### Reachable wrapper states -/

/-- **The wrapper states reached by initialization and valid operations**, with the number of
operations and the specification state. -/
inductive ReachW (KB : Nat) : Nat → OrderMaintenance → OrderMaintenance.Spec.State → Prop
  | init {om : OrderMaintenance} : OrderMaintenance.init proofParams KB = .ok om → ReachW KB 0
    om OrderMaintenance.Spec.State.empty
  | step {t : Nat} {om om' : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} {op :
    OrderMaintenance.Spec.Op} {a : OrderMaintenance.Spec.Ans} :
      ReachW KB t om Sp → op.Valid Sp → om.apply proofParams op = .ok (a, om') →
      ReachW KB (t + 1) om' (OrderMaintenance.Spec.step Sp op).1

theorem reachW_inv {KB : Nat} (h4 : 4 ≤ KB) {t : Nat} {om : OrderMaintenance} {Sp :
  OrderMaintenance.Spec.State}
    (h : ReachW KB t om Sp) : MInv om Sp ∧ WBW t om om.nxt ∧ om.KB = KB := by
  induction h with
  | init hi =>
    obtain ⟨om', hi', hI, hB⟩ := init_step h4
    rw [hi] at hi'; cases hi'
    refine ⟨hI, hB, ?_⟩
    unfold OrderMaintenance.init at hi
    simp only [bind, Except.bind] at hi
    split at hi
    · cases hi
    · injection hi with h; rw [← h]
  | step _ hv hr ih =>
    obtain ⟨hI, hB, hK⟩ := ih
    obtain ⟨hI', hB', hK'⟩ := apply_step hI hv hB hr
    exact ⟨hI', hB', hK'.trans hK⟩

/-! ### Theorem W, option B -/

/-- **The word size of a wrapper state**: `64·L` for the larger `L` of its two cores. -/
def wKom (om : OrderMaintenance) : Nat :=
  max (wK om.cur.P) (match om.nxt with | some c => wK c.P | none => 0)

theorem wK_ge (N : Nat) : 512 ≤ wK (proofParams N) := by
  have := pL_ge N; change 512 ≤ 64 * pL N; omega

/-- **Theorem W (stored values, Level F).** On every wrapper state reached by initialization and
`t` valid operations, every value stored in either core is below `2^K`, `K = 64·L` for the larger
`L = pL N` of the two cores (`wKom`), handles excepted; the element index arrays and the cursor are
below `2^K`; every handle stored in a core, the live count, the handle counter and the rebuild
counter are at most `t`. (`K_B < 2^512` puts the constant `K_B` below `2^K` too.) -/
theorem theoremW_stored {KB t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
  (h4 : 4 ≤ KB) (hKB : KB < 2 ^ 512)
    (h : ReachW KB t om Sp) : OMB (wKom om) t om := by
  obtain ⟨hI, hB, hK⟩ := reachW_inv h4 h
  have h1 : wK om.cur.P ≤ wKom om := le_max_left _ _
  have h2 : ∀ c, om.nxt = some c → wK c.P ≤ wKom om := fun c hc => by
    unfold wKom; rw [hc]; exact le_max_right _ _
  have h512 : 512 ≤ wKom om := by
    obtain ⟨A, hR, -⟩ := hI.1.w.core
    have hmk := (hI.1.cur A hR.inv).pmk
    have := wK_ge om.cur.P.N
    rw [← hmk] at this
    omega
  refine ⟨hB.cur.mono h1, fun c hc => ((hB.nxt c hc).1).mono (h2 c hc), hB.curIdx.mono h1, ?_,
    fun i => le_trans (hB.hcur i) hB.hnd, fun c hc i => le_trans ((hB.nxt c hc).2.2 i) hB.hnd,
    lt_mono h1 hB.cursor, by rw [hK]; exact lt_pow_mono hKB h512, ⟨hB.live, hB.hnd, hB.reb⟩⟩
  cases hn : om.nxt with
  | none => intro i; rw [hB.noNxt hn i]; exact pos _
  | some c => exact ((hB.nxt c hn).2.1).mono (h2 c hn)

end OrderMaintenance.Proof.Word

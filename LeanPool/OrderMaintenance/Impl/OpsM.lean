/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.RebuildM
public import LeanPool.OrderMaintenance.Proof.Cost.WrapSafe


/-!
# M6: the wrapper's operations as machine code

The Level M side conditions of the cores (`Mc`, `PrepM`) are not part of Level F's invariant; they
are carried alongside it (`MX`). Level F's run supplies the rest of what the core calls need
(`RLSafeF`, `insert_safe`, `delete_safe`).
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-- Level F's safety facts at the proof parameters. -/
abbrev RLSafeP := RLSafeF proofParams TopInv topMu topJ nfP RfP

/-- The Level M side condition of `nxt`: in preparation, or in service with the capacities. -/
def NxtM (om : OrderMaintenance) (n : Core) : Prop :=
  (om.cursorSet = false → PrepM n) ∧ (om.cursorSet = true → Mc (capsOf n.P) n.P n)

/-- **The Level M side conditions of the wrapper state.** -/
def MX (om : OrderMaintenance) : Prop := Mc (capsOf om.cur.P) om.cur.P om.cur ∧ ∀ n, om.nxt =
  some n → NxtM om n

/-- A copy step keeps the capacities of `nxt`. -/
theorem copy_M {om : OrderMaintenance} {n : Core} (hC : CopyOK om n) (hM : Mc (capsOf n.P) n.P
  n) {om' : OrderMaintenance} {n' : Core}
    (hcp : copyAtCursor om n = .ok (om', n')) :
    om'.cursorSet = om.cursorSet ∧ om'.cur = om.cur ∧ Mc (capsOf n'.P) n'.P n' := by
  unfold copyAtCursor at hcp
  cases hl : (om.cur.E.getX om.cursor).live with
  | false =>
    simp only [hl, Bool.false_eq_true, ite_false, pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; subst h2
    exact ⟨rfl, rfl, hM⟩
  | true =>
    obtain ⟨L, hS, htail, -⟩ := hC.2 hl
    obtain ⟨c', hr, -, -, -, hP', hM'⟩ := hS.insert htail (om.cur.E.getX om.cursor).h
      (fun r => if r = "x" then n.tail else (om.cur.E.getX om.cursor).h) (by simp) (by simp)
    simp only [hl, ite_true, bind, Except.bind, runCore, hr] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; subst h2
    exact ⟨rfl, rfl, by rw [hP']; exact hM'⟩

/-- **Along the rebuild loop**: Level F's safety facts and the side conditions give what the machine
iterations need, and the side conditions hold at the end. -/
theorem loop_M : ∀ f b (om : OrderMaintenance) (n : Core), RLSafeP om n f b → NxtM om n →
    Mc (capsOf om.cur.P) om.cur.P om.cur → RLSafe om n f b ∧ ∀ R, rebuildLoop om n f b = .ok R →
      MX R := by
  intro f
  induction f with
  | zero =>
    intro b om n _ hN hMc
    refine ⟨trivial, fun R hR => ?_⟩
    cases hR
    exact ⟨hMc, fun n' hn' => by cases hn'; exact hN⟩
  | succ f ih =>
    intro b om n hF hN hMc
    by_cases hb : b = 0
    · subst hb
      refine ⟨rlSafe_zero om n _, fun R hR => ?_⟩
      rw [rebuildLoop_zero] at hR; cases hR
      exact ⟨hMc, fun n' hn' => by cases hn'; exact hN⟩
    have hF' := hF hb
    -- the prepare step
    have hprep : om.cursorSet = false → PrepM n ∧ 1 ≤ n.P.N ∧ om.cur.head < om.cur.E.size ∧
        ∀ r n', prepareStep.run n = .ok r n' → n'.count = n.count ∧
          (r = true → RLSafe {
            om with
            cursor := (om.cur.E.getX om.cur.head).next
            cursorSet := true
          } n' f b ∧
            ∀ R, rebuildLoop {
              om with
              cursor := (om.cur.E.getX om.cur.head).next
              cursorSet := true
            } n' f b = .ok R →
              MX R) ∧
          (r = false → RLSafe om n' f (b - 1) ∧ ∀ R, rebuildLoop om n' f (b - 1) = .ok R → MX R)
            := by
      intro hcs
      obtain ⟨hN1, hhd, hst⟩ := hF'.1 hcs
      refine ⟨hN.1 hcs, hN1, hhd, fun r n' hr => ?_⟩
      obtain ⟨hcnt, hT, hFl⟩ := hst r n' hr
      obtain ⟨-, hP', hF2, hT2⟩ := prepAgreeM (hN.1 hcs) hN1 hr (fun _ => 0)
      refine ⟨hcnt, fun hrt => ih _ _ _ (hT hrt) ⟨(fun h => by simp at h), fun _ => by
        rw [hP']; exact (hT2 hrt).1⟩ hMc, fun hrf => ih _ _ _ (hFl hrf) ⟨fun _ => hF2 hrf, fun h
          => by
        rw [hcs] at h; cases h⟩ hMc⟩
    -- the copy step
    have hcopy : om.cursorSet = true → om.cursor ≠ NIL → CopyOK om n ∧
        ∀ om' n', copyAtCursor om n = .ok (om', n') → Mc (capsOf n'.P) n'.P n' ∧ (om'.cursor ≠ NIL →
          RLSafe om' n' f (b - 1) ∧ ∀ R, rebuildLoop om' n' f (b - 1) = .ok R → MX R) := by
      intro hcs hc
      obtain ⟨hlt, hlive, hnext⟩ := hF'.2 hcs hc
      have hCO : CopyOK om n := ⟨hlt, fun hl => by
        obtain ⟨L, hok, hroom, htail, hh⟩ := hlive hl
        exact ⟨L, ⟨hok, hroom, hN.2 hcs⟩, htail, hh⟩⟩
      refine ⟨hCO, fun om' n' hcp => ?_⟩
      obtain ⟨e1, e2, hM'⟩ := copy_M hCO (hN.2 hcs) hcp
      refine ⟨hM', fun hc' => ih _ _ _ (hnext om' n' hcp hc') ⟨(fun h => by
        rw [e1, hcs] at h
        cases h),
        fun _ => hM'⟩ (by
          rw [e2]
          exact hMc)⟩
    refine ⟨fun _ => ⟨fun hcs => ?_, fun hcs hc => ?_⟩, fun R hR => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hprep hcs
      exact ⟨h1, h2, h3, fun r n' hr => ⟨(h4 r n' hr).1, fun hrt => ((h4 r n' hr).2.1 hrt).1,
        fun hrf => ((h4 r n' hr).2.2 hrf).1⟩⟩
    · obtain ⟨h1, h2⟩ := hcopy hcs hc
      exact ⟨h1, fun om' n' hcp hc' => ((h2 om' n' hcp).2 hc').1⟩
    · unfold rebuildLoop at hR
      rw [ite_eq_right hb] at hR
      cases hcs : om.cursorSet with
      | false =>
        rw [ite_eq_left (by simp [hcs])] at hR
        obtain ⟨-, -, -, h4⟩ := hprep hcs
        cases hpr : prepareStep.run n with
        | error e s' => simp [runCore, hpr, bind, Except.bind] at hR
        | ok r n' =>
          have hrc : runCore n prepareStep = .ok (r, n') := by simp [runCore, hpr]
          simp only [bind, Except.bind, hrc] at hR
          cases r with
          | true => simp only [ite_true] at hR; exact ((h4 true n' hpr).2.1 rfl).2 R hR
          | false => simp only [Bool.false_eq_true, ite_false] at hR; exact ((h4 false n'
            hpr).2.2 rfl).2 R hR
      | true =>
        rw [ite_eq_right (by simp [hcs])] at hR
        by_cases hc : om.cursor = NIL
        · rw [ite_eq_left hc] at hR
          injection hR with hR; subst hR
          exact ⟨hN.2 hcs, fun n' hn' => by cases hn'⟩
        · rw [ite_eq_right hc] at hR
          obtain ⟨-, h2⟩ := hcopy hcs hc
          cases hcp : copyAtCursor om n with
          | error e => simp [hcp, bind, Except.bind] at hR
          | ok r =>
            obtain ⟨om', n'⟩ := r
            simp only [bind, Except.bind, hcp] at hR
            by_cases hc' : om'.cursor = NIL
            · rw [ite_eq_left hc'] at hR
              injection hR with hR; subst hR
              exact ⟨(h2 om' n' hcp).1, fun n'' hn'' => by cases hn''⟩
            · rw [ite_eq_right hc'] at hR
              exact ((h2 om' n' hcp).2 hc').2 R hR

/-! ### The rebuild step -/

/-- The rebuild's share of an operation: start a rebuild, or run the loop. -/
def rebuildC (p : Nat) : Stmt :=
  .ite (.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)) (startC p) (loopC p)

/-- The cost bound of the rebuild step. -/
def rebB (KB : Nat) : Nat := 3600 + (KB + 1) * (1 + iterB)

/-- The locals the rebuild step may change. -/
def RbLoc (x : Reg) : Prop := StLoc x ∧ ItLoc x ∧ x ≠ "it"

theorem pp_topPP (N : Nat) : topPP (proofParams N) := pp_proof N

/-- **The rebuild step keeps the side conditions.** -/
theorem rebuild_MX {om : OrderMaintenance} (hX : MX om)
    (hF : ∀ n, om.nxt = some n → RLSafeP {
      om with
      nxt := none
    } n (om.KB + 1) om.KB)
    {R : OrderMaintenance} (hr : om.rebuildStep proofParams = .ok R) : MX R := by
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
    · exact hX
    · exact ⟨hX.1, fun n hn' => by
        cases hn'
        exact ⟨fun _ => prepM_start _ (pp_topPP _), fun h => by simp [startOM] at h⟩⟩
  | some n0 =>
    have hr' : rebuildLoop {
      om with
      nxt := none
    } n0 (om.KB + 1) om.KB = .ok R := by
      unfold OrderMaintenance.rebuildStep at hr; rw [hn] at hr; exact hr
    exact (loop_M _ _ _ _ (hF n0 hn) (hX.2 n0 hn) hX.1).2 R hr'

/-- **The rebuild step**: the machine ends holding Level F's result (in one slot or the other),
which satisfies the side conditions. -/
theorem rebuildW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hX : MX om)
  (hkb : 1 ≤ om.KB)
    (hF : ∀ n, om.nxt = some n → RLSafeP {
      om with
      nxt := none
    } n (om.KB + 1) om.KB)
    {R : OrderMaintenance} (hr : om.rebuildStep proofParams = .ok R) :
    MX R ∧ wp (rebuildC p) (fun m' k => (WEnc R m' p ∨ WEnc R m' (1 - p)) ∧
      (∀ x, RbLoc x → m'.loc x = m.loc x) ∧ k ≤ rebB om.KB) m := by
  cases hn : om.nxt with
  | none =>
    refine ⟨rebuild_MX hX hF hr, ?_⟩
    · unfold rebuildC
      refine wp_ite_g 1 (by simp [Expr.eval, BinOp.eval, h.scap 1 (by decide), h.nxtOn, hn, b2n])
        (fun s1 hl1 hm1 hc1 => ?_)
      simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
      refine Machine.wp_mono (fun s2 k2 ⟨h2, hl2, hk2⟩ => ⟨Or.inl h2, fun x hx => ?_, ?_⟩)
        (startW_ok (h.congr hm1 hc1) hn hkb hr)
      · rw [hl2 x hx.1, hl1]
      · unfold rebB; simp only [Expr.cost] at hk2 ⊢; omega
  | some n0 =>
    have hr' : rebuildLoop {
      om with
      nxt := none
    } n0 (om.KB + 1) om.KB = .ok R := by
      unfold OrderMaintenance.rebuildStep at hr; rw [hn] at hr; exact hr
    obtain ⟨hS, hXR⟩ := loop_M _ _ _ _ (hF n0 hn) (hX.2 n0 hn) hX.1
    refine ⟨hXR R hr', ?_⟩
    have hom : ({
      ({
        om with
        nxt := none
      } : OrderMaintenance) with
      nxt := some n0
    } :
      OrderMaintenance) = om := by
      cases om; simp only at hn; subst hn; rfl
    unfold rebuildC
    refine wp_ite_g 0 (by simp [Expr.eval, BinOp.eval, h.scap 1 (by decide), h.nxtOn, hn, b2n])
      (fun s1 hl1 hm1 hc1 => ?_)
    simp only [ne_eq, not_true_eq_false, ite_false]
    have h1 : WEnc ({
      ({
        om with
        nxt := none
      } : OrderMaintenance) with
      nxt := some n0
    } :
      OrderMaintenance) s1 p := by
      rw [hom]; exact h.congr hm1 hc1
    refine Machine.wp_mono (fun s2 k2 ⟨h2, hl2, hk2⟩ => ⟨h2, fun x hx => ?_, ?_⟩) (loopW_ok h1
      hr' hS)
    · rw [hl2 x hx.2.1 hx.2.2, hl1]
    · unfold rebB; simp only [Expr.cost] at hk2 ⊢; omega

/-! ### `K_B` never changes -/

theorem copy_KB {om : OrderMaintenance} {n : Core} {om' : OrderMaintenance} {n' : Core} (hcp :
  copyAtCursor om n = .ok (om', n')) :
    om'.KB = om.KB := by
  unfold copyAtCursor at hcp
  cases hl : (om.cur.E.getX om.cursor).live with
  | false =>
    simp only [hl, Bool.false_eq_true, ite_false, pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; rfl
  | true =>
    simp only [hl, ite_true, bind, Except.bind] at hcp
    split at hcp
    · cases hcp
    · injection hcp with hcp; injection hcp with h1 h2; subst h1; rfl

theorem rebuildLoop_KB : ∀ f b (om : OrderMaintenance) (n : Core) (R : OrderMaintenance),
  rebuildLoop om n f b = .ok R → R.KB = om.KB := by
  intro f
  induction f with
  | zero => intro b om n R h; cases h; rfl
  | succ f ih =>
    intro b om n R h
    unfold rebuildLoop at h
    split at h
    · cases h; rfl
    split at h
    · simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i v hv
        split at h
        · have := ih _ _ _ _ h; exact this
        · have := ih _ _ _ _ h; exact this
    split at h
    · cases h; rfl
    · simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i v hv
        obtain ⟨om', n'⟩ := v
        have := copy_KB hv
        split at h
        · cases h; exact this
        · rw [ih _ _ _ _ h]; exact this

theorem rebuildStep_KB {om R : OrderMaintenance} (h : om.rebuildStep proofParams = .ok R) : R.KB
  = om.KB := by
  unfold OrderMaintenance.rebuildStep at h
  split at h
  · simp only at h
    split at h
    · simp only [newCore_true, bind, Except.bind, pure, Except.pure] at h; cases h; rfl
    · cases h; rfl
  · have := rebuildLoop_KB _ _ _ _ _ h; exact this

/-! ### The wrapper invariant at Level M -/

/-- Level F's cost invariant at the proof parameters. -/
abbrev WCP (om : OrderMaintenance) (Sp : OrderMaintenance.Spec.State) : Prop := WC proofParams
  TopInv topPI topMu topNu topJ nfP RfP om Sp

/-- **The wrapper invariant at Level M**: Level F's, with the side conditions. -/
def MInv (om : OrderMaintenance) (Sp : OrderMaintenance.Spec.State) : Prop := WCP om Sp ∧ MX om

/-- `cur` is in service. -/
theorem MInv.cur {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI : MInv om Sp) {A
  : Abs} (hA : INV om.cur A) :
    InService om.cur A.elist :=
  ⟨hI.1.cur A hA, hI.1.cur_room costSetup, hI.2.1⟩

/-- What mirroring an insertion needs. -/
theorem MInv.mirror {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI : MInv om Sp)
  (hx : Option Nat) :
    ∀ n, om.nxt = some n → om.cursorSet = true →
      (hx = none ∨ ∃ x, hx = some x ∧ om.nxtIdx.getX x ≠ 0) → ∃ B, InService n B ∧ mirAnchor om
        n hx ∈ B := by
  intro n hn hs hc
  obtain ⟨-, -, A, -, -, -, hN⟩ := hI.1.w
  unfold NxtR at hN; rw [hn] at hN
  obtain ⟨B, hRB, hIB, hzB, -⟩ := hN
  obtain ⟨c₀, live₀, I, D, hRW⟩ := hI.1.busy n hn
  refine ⟨B.elist, ⟨((hRW.serve hs).1 B hRB.inv).1, hI.1.nxt_room costSetup hn hs, (hI.2.2 n
    hn).2 hs⟩, ?_⟩
  rcases hc with rfl | ⟨x, rfl, hx0⟩
  · exact hRB.head
  · exact (hIB x (hzB x hx0)).1

/-- Mirroring an insertion keeps the side conditions of `nxt`. -/
theorem mirrorInsert_M {om : OrderMaintenance} {hx : Option Nat} {hy : Nat}
    (hX : ∀ n, om.nxt = some n → NxtM om n)
    (hN : ∀ n, om.nxt = some n → om.cursorSet = true →
      (hx = none ∨ ∃ x, hx = some x ∧ om.nxtIdx.getX x ≠ 0) → ∃ B, InService n B ∧ mirAnchor om
        n hx ∈ B)
    {om2 : OrderMaintenance} (hm : om.mirrorInsert hx hy = .ok om2) :
    om2.cur = om.cur ∧ om2.KB = om.KB ∧ ∀ n, om2.nxt = some n → NxtM om2 n := by
  unfold OrderMaintenance.mirrorInsert at hm
  cases hn : om.nxt with
  | none => rw [hn] at hm; injection hm with hm; subst hm; exact ⟨rfl, rfl, fun n h => by
    rw [hn] at h; cases h⟩
  | some n =>
    rw [hn] at hm
    simp only at hm
    have hkeep : om2 = om → om2.cur = om.cur ∧ om2.KB = om.KB ∧ ∀ n, om2.nxt = some n → NxtM om2
      n := by
      rintro rfl; exact ⟨rfl, rfl, fun n2 h2 => hX n2 h2⟩
    have hmir : ∀ xn, om.cursorSet = true → (hx = none ∨ ∃ x, hx = some x ∧ om.nxtIdx.getX x ≠ 0) →
        xn = mirAnchor om n hx →
        (do let r ← runCore n (insertAfter xn hy)
            pure ({
              om with
              nxt := some r.2
              nxtIdx := om.nxtIdx.setX hy r.1
              cursorSet := true
            } : OrderMaintenance)) = .ok om2 →
        om2.cur = om.cur ∧ om2.KB = om.KB ∧ ∀ n, om2.nxt = some n → NxtM om2 n := by
      intro xn hs hcp hxn hm
      obtain ⟨B, hS, hB⟩ := hN n hn hs hcp
      rw [← hxn] at hB
      obtain ⟨c', hr, -, -, -, hP', hM'⟩ := hS.insert hB hy
        (fun r => if r = "x" then xn else hy) (by simp) (by simp)
      simp only [bind, Except.bind, runCore, hr, pure, Except.pure] at hm
      injection hm with hm; subst hm
      refine ⟨rfl, rfl, fun n2 h2 => ?_⟩
      cases h2
      exact ⟨fun h => by simp [] at h, fun _ => by rw [hP']; exact hM'⟩
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

/-- **Level F's insertion, step by step**: the insertion into `cur`, its mirroring, and the
rebuild step. -/
theorem insert_eq {mk : Nat → Params} {om : OrderMaintenance} {hx : Option Nat} {c' : Core} {om2
  : OrderMaintenance}
    (hr : (insertAfter (insXi om hx) om.nextHandle).run om.cur = .ok om.cur.E.size c')
    (hm : ({
      om with
      cur := c'
      nextHandle := om.nextHandle + 1
      curIdx := om.curIdx.setX om.nextHandle om.cur.E.size
    } : OrderMaintenance).mirrorInsert hx om.nextHandle = .ok om2)
    (R : OrderMaintenance) : om.insert mk hx = .ok (om.nextHandle, R) ↔
      ({
        om2 with
        live := om2.live + 1
      } : OrderMaintenance).rebuildStep mk = .ok R := by
  have e : om.insert mk hx = (({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance).rebuildStep
    mk).bind
      fun R => .ok (om.nextHandle, R) := by
    unfold OrderMaintenance.insert
    cases hx <;>
    · simp only [insXi] at hr
      dsimp only
      rw [onCur_ok hr]
      simp only [bind, Except.bind]
      rw [hm]
      rfl
  rw [e]
  cases ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance).rebuildStep mk with
  | error e => simp [Except.bind]
  | ok a => simp [Except.bind]

/-! ### Insertion -/

/-- Increment the wrapper's live-handle counter. -/
def liveIncC : Stmt := .store (wa 4) (.lit 0) (.bin .add (.load (wa 4) (.lit 0)) (.lit 1))

theorem liveIncW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) :
    wp liveIncC (fun m' k => WEnc {
      om with
      live := om.live + 1
    } m' p ∧ m'.loc = m.loc ∧ k ≤
      10) m :=
  wp_store_g 0 (om.live + 1) rfl (by simp [Expr.eval, BinOp.eval, h.scap 4 (by decide), h.live])
    (by rw [h.scap 4 (by decide)]; decide)
    (fun s' hl hm hc => ⟨(h.writeLive _).congr hm hc, hl, by simp [Expr.cost]⟩)

/-- The insertion code of parity `p`. -/
def insC (p : Nat) : Stmt := .seq (curInsC p) (.seq (mirrorInsC p) (.seq liveIncC (rebuildC p)))

/-- **The wrapper's insertion**: the handle of the anchor in local `x` (if `hx` = 1). -/
def insertWS : Stmt := byPar insC

/-- The cost bound of an insertion. -/
def insW (KB : Nat) : Nat := 2 * insB + 400 + rebB KB

theorem insBound_of {P : Params} (h : P = proofParams P.N) : insBound P = insB := by
  rw [h]; exact insBound_proof _

theorem wp_par_or {om : OrderMaintenance} {m : State} {p : Nat} (hp : p < 2) (h : WEnc om m p ∨
  WEnc om m (1 - p)) :
    WEnc om m 0 ∨ WEnc om m 1 := by
  have : p = 0 ∨ p = 1 := by omega
  rcases h with h | h
  · rcases this with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  · rcases this with rfl | rfl
    · exact Or.inr h
    · exact Or.inl h

/-- The shared functional prefix of insertion: the core update, mirroring, and safe
rebuild preserve parameters and the Level M invariant. Machine and word bounds reuse it. -/
theorem MInv.insert_prefix {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
    (hI : MInv om Sp) {hx : Option Nat} (hv : (insOp hx).Valid Sp) :
    ∃ (om' : OrderMaintenance) (c' : Core) (om2 : OrderMaintenance),
      om.insert proofParams hx = .ok (Sp.fresh, om') ∧
      MInv om' (OrderMaintenance.Spec.step Sp (insOp hx)).1 ∧
      (insertAfter (insXi om hx) om.nextHandle).run om.cur = .ok om.cur.E.size c' ∧
      (insOM om c' om.cur.E.size).mirrorInsert hx om.nextHandle = .ok om2 ∧
      (∀ n, om2.nxt = some n →
        RLSafeP { om2 with live := om2.live + 1, nxt := none } n (om2.KB + 1) om2.KB) ∧
      ({ om2 with live := om2.live + 1 } : OrderMaintenance).rebuildStep proofParams = .ok om' ∧
      c'.P = om.cur.P ∧ c'.count = om.cur.count + 1 ∧ om2.cur = c' ∧ om2.KB = om.KB ∧
      MX { om2 with live := om2.live + 1 } := by
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  obtain ⟨om', hins, hW'⟩ := insert_cost costSetup hW hx hv
  obtain ⟨c', om2, hr1, hm2, hsafe⟩ := insert_safe costSetup hW hx hv
  have hR' : ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance).rebuildStep proofParams =
    .ok om' := by
    rw [← insert_eq hr1 hm2, hf]; exact hins
  -- the anchor, and `cur` in service
  have hxS : ∀ x, hx = some x → x ∈ Sp.list := fun x e => by subst e; exact hv
  have hxL : insAnchor om hx ∈ A.elist := by
    cases hx with
    | none => exact hR.head
    | some x => exact (hIdx x (hxS x rfl)).1
  have hS0 := hI.cur hR.inv
  -- the side conditions after the mirroring and the rebuild step
  obtain ⟨c'', hr'', -, -, hcnt, hP'', hM''⟩ := hS0.insert hxL om.nextHandle
    (fun r => if r = "x" then insAnchor om hx else om.nextHandle) (by simp) (by simp)
  have hr1' : (insertAfter (insAnchor om hx) om.nextHandle).run om.cur = .ok om.cur.E.size c' := hr1
  rw [hr1'] at hr''
  injection hr'' with _ hcc; subst hcc
  obtain ⟨e1, e2, hX2⟩ := mirrorInsert_M (om := insOM om c' om.cur.E.size) (hx := hx) (hy :=
    om.nextHandle)
    (fun n hn => hI.2.2 n hn) (fun n hn hs hc => hI.mirror hx n hn hs hc) hm2
  have hX3 : MX ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance) :=
    ⟨by change Mc (capsOf om2.cur.P) om2.cur.P om2.cur; rw [e1]; change Mc (capsOf c'.P) c'.P c'; rw
      [hP'']; exact hM'',
      fun n hn => hX2 n hn⟩
  exact ⟨om', c', om2, hins, ⟨hW', rebuild_MX hX3 hsafe hR'⟩, hr1, hm2, hsafe,
    hR', hP'', hcnt, e1, e2, hX3⟩

/-- **An insertion at Level M**: it answers Level F's handle, keeps the invariant, and the machine
code runs in at most `insW K_B` steps. -/
theorem insertW_ok {om : OrderMaintenance} {m : State} {p : Nat} {Sp :
  OrderMaintenance.Spec.State} (h : WEnc om m p) (hI : MInv om Sp)
    {hx : Option Nat} (hv : (insOp hx).Valid Sp) (hhx : m.loc "hx" = b2n hx.isSome)
    (hxl : ∀ x, hx = some x → m.loc "x" = x) :
    ∃ om', om.insert proofParams hx = .ok (Sp.fresh, om') ∧ MInv om' (OrderMaintenance.Spec.step
      Sp (insOp hx)).1 ∧
      om'.KB = om.KB ∧ wp insertWS (fun m' k => (WEnc om' m' 0 ∨ WEnc om' m' 1) ∧ m'.loc "hy" =
        Sp.fresh ∧
        k ≤ insW om.KB) m := by
  have hp := h.p2
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
  obtain ⟨hk, hRf, hn1, hsize, hcap, hI5, hpow⟩ := hS0.params
  refine ⟨om', hins, hI', (rebuildStep_KB hR').trans e2, ?_⟩
  -- the machine
  refine wp_byPar h ?_
  have h0 := h.bump (parE.maxv m)
  unfold insC
  rw [Machine.wp_seq]
  have hxc : ∀ x, hx = some x → x < om.nextHandle := fun x e => by
    have := hS.2 x (hxS x e); rw [hf]; exact this
  obtain ⟨c3, y, hr3, -, -, -, -, hy, hwp1⟩ := curInsW_ok h0 (by simpa using hhx)
    (fun x e => ⟨by simpa using hxl x e, by have := h0.roomC; have := hxc x e; omega⟩)
    hS0.ok.cost rfl hxL hS0.ok.cnt hS0.room hS0.mc hk hRf hn1 hsize hcap hI5 hpow
  rw [hr1'] at hr3
  injection hr3 with hyy hcc; subst hcc; subst hyy
  refine Machine.wp_mono (fun m1 k1 ⟨h1, hy1, hyy1, hhx1, hx1, hk1⟩ => ?_) hwp1
  rw [Machine.wp_seq]
  have hib : insBound ((insOM om c' om.cur.E.size).nxt.map (·.P) |>.getD (insOM om c'
    om.cur.E.size).cur.P) = insB := by
    cases hn : om.nxt with
    | none => simp only [insOM, hn, Option.map_none, Option.getD_none]; rw [hP'']; exact hS0.insB
    | some n =>
      simp only [insOM, hn, Option.map_some, Option.getD_some]
      obtain ⟨c₀, live₀, I, D, hRW⟩ := hW.busy n hn
      rw [hRW.nP]; exact insBound_proof _
  have hmir := mirrorInsW_ok (om := insOM om c' om.cur.E.size) h1 (hx := hx) (hy := om.nextHandle)
    (by
      rw [hhx1]
      simpa using hhx)
    (fun x e => ⟨by rw [hx1]; simpa using hxl x e, fun hs => by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
      have h5 := h1.roomN n hn; have h6 := hxc x e
      simp only [insOM] at h5; omega⟩)
    hy1
    (fun hs => by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
      have h5 := h1.roomN n hn
      simp only [insOM] at h5; omega)
    (fun n hn hs hc => hI.mirror hx n hn hs hc) hm2
  refine Machine.wp_mono (fun m2 k2 ⟨h2, hl2, hk2⟩ => ?_) hmir
  rw [Machine.wp_seq]
  refine Machine.wp_mono (fun m3 k3 ⟨h3, hl3, hk3⟩ => ?_) (liveIncW_ok h2)
  have hkb : 1 ≤ ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance).KB := by
    change 1 ≤ om2.KB; rw [e2]; have := hW.kb; change 1 ≤ om.KB; omega
  obtain ⟨-, hwp4⟩ := rebuildW_ok h3 hX3 hkb hsafe hR'
  refine Machine.wp_mono (fun m4 k4 ⟨h4, hl4, hk4⟩ => ⟨wp_par_or hp h4, ?_, ?_⟩) hwp4
  · rw [hl4 "hy" (by simp [RbLoc, StLoc, ItLoc, pLocs]), hl3,
    hl2 "hy" (by decide) (by decide) (by decide), hy1, hf]
  · have hKB : ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance).KB = om.KB := e2
    rw [hKB] at hk4
    rw [hib] at hk2
    have := hS0.insB
    unfold insW
    simp only [Expr.cost, parE] at hk1 hk2 hk3 hk4 ⊢
    omega

/-! ### Deletion -/

/-- What mirroring a deletion needs: an element copied into `nxt` is in service there. -/
theorem MInv.mirrorDel {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI : MInv om
  Sp) (x : Nat) :
    ∀ n, om.nxt = some n → om.nxtIdx.getX x ≠ 0 → om.cursorSet = true ∧ DelOK n (om.nxtIdx.getX
      x) := by
  intro n hn hx0
  obtain ⟨-, -, A, -, -, -, hN⟩ := hI.1.w
  unfold NxtR at hN; rw [hn] at hN
  obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN
  have hxB := hzB x hx0
  cases hs : om.cursorSet with
  | false =>
    rw [hs] at hcs; simp only [Bool.false_eq_true, ite_false] at hcs; subst hcs
    rw [liveH_initAbs hRB] at hxB; cases hxB
  | true =>
    obtain ⟨c₀, live₀, I, D, hRW⟩ := hI.1.busy n hn
    have hok := ((hRW.serve hs).1 B hRB.inv).1
    exact ⟨rfl, n.P, _, _, B.elist, hok.cost, rfl, (hIB x hxB).1, hok.cnt, (hI.2.2 n hn).2 hs⟩

/-- Mirroring a deletion keeps the side conditions of `nxt`. -/
theorem mirrorDelete_M {om : OrderMaintenance} {x : Nat} (hX : ∀ n, om.nxt = some n → NxtM om n)
    (hN : ∀ n, om.nxt = some n → om.nxtIdx.getX x ≠ 0 → om.cursorSet = true ∧ DelOK n
      (om.nxtIdx.getX x))
    {om2 : OrderMaintenance} (hm : om.mirrorDelete x = .ok om2) :
    om2.cur = om.cur ∧ om2.KB = om.KB ∧ om2.live = om.live ∧ ∀ n, om2.nxt = some n → NxtM om2 n
      := by
  unfold OrderMaintenance.mirrorDelete at hm
  cases hn : om.nxt with
  | none =>
    rw [hn] at hm; injection hm with hm; subst hm
    exact ⟨rfl, rfl, rfl, fun n h => by rw [hn] at h; cases h⟩
  | some n =>
    rw [hn] at hm
    simp only at hm
    by_cases hx0 : om.nxtIdx.getX x = 0
    · simp only [hx0, bne_self_eq_false, Bool.false_eq_true, ite_false, pure, Except.pure] at hm
      injection hm with hm; subst hm
      exact ⟨rfl, rfl, rfl, fun n2 h2 => by rw [hn] at h2; cases h2; exact hX n hn⟩
    · have : (om.nxtIdx.getX x != 0) = true := by simp [hx0]
      simp only [this, ite_true] at hm
      obtain ⟨hs, P, nn, R, L, hC, hP, hxL, hcnt, hM⟩ := hN n hn hx0
      obtain ⟨n', hr, -, -, -, hP', hM'⟩ := markDeadAgreeM hC hP hxL (κ := capsOf P)
        (fun _ => om.nxtIdx.getX x) rfl (capsOf_ok P) hcnt hM
      simp only [bind, Except.bind, runCore, hr, pure, Except.pure] at hm
      injection hm with hm; subst hm
      refine ⟨rfl, rfl, rfl, fun n2 h2 => ?_⟩
      cases h2
      exact ⟨fun h => by simp [hs] at h, fun _ => by rw [hP', hP]; exact hM'⟩

/-- **Level F's deletion, step by step.** -/
theorem delete_eq {mk : Nat → Params} {om : OrderMaintenance} {x : Nat} {c' : Core} {om2 :
  OrderMaintenance}
    (hr : (markDead (om.curIdx.getX x)).run om.cur = .ok () c')
    (hm : ({
      om with
      cur := c'
      curIdx := om.curIdx.setX x 0
    } : OrderMaintenance).mirrorDelete
      x = .ok om2)
    (R : OrderMaintenance) : om.delete mk x = .ok R ↔ ({
      om2 with
      live := om2.live - 1
    } :
      OrderMaintenance).rebuildStep mk = .ok R := by
  have e : om.delete mk x = ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance).rebuildStep
    mk := by
    unfold OrderMaintenance.delete
    rw [onCur_ok hr]
    simp only [bind, Except.bind]
    rw [hm]
  rw [e]

/-- Decrement the wrapper's live-handle counter with truncated subtraction. -/
def liveDecC : Stmt := .store (wa 4) (.lit 0) (tsubE (.load (wa 4) (.lit 0)) (.lit 1))

theorem liveDecW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) :
    wp liveDecC (fun m' k => WEnc {
      om with
      live := om.live - 1
    } m' p ∧ m'.loc = m.loc ∧ k ≤
      20) m :=
  wp_store_g 0 (om.live - 1) rfl
    (tsubE_eval (eval_load_lit (by rw [h.scap 4 (by decide)]; decide) h.live) rfl)
    (by rw [h.scap 4 (by decide)]; decide)
    (fun s' hl hm hc => ⟨(h.writeLive _).congr hm hc, hl, by simp [Expr.cost, tsubE]⟩)

/-- The deletion code of parity `p`. -/
def delC (p : Nat) : Stmt := .seq (curDelC p) (.seq (mirrorDelC p) (.seq liveDecC (rebuildC p)))

/-- **The wrapper's deletion** of the handle in local `x`. -/
def deleteWS : Stmt := byPar delC

/-- The cost bound of a deletion. -/
def delW (KB : Nat) : Nat := 200 + rebB KB

/-- The shared functional prefix of deletion: marking, mirroring, and the safe rebuild
retain the core parameters and intermediate Level M invariant. -/
theorem MInv.delete_prefix {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
    (hI : MInv om Sp) {x : Nat} (hv : x ∈ Sp.list) :
    ∃ (om' : OrderMaintenance) (c' : Core) (om2 : OrderMaintenance),
      om.delete proofParams x = .ok om' ∧
      MInv om' (OrderMaintenance.Spec.step Sp (.delete x)).1 ∧
      (markDead (om.curIdx.getX x)).run om.cur = .ok () c' ∧
      ({ om with cur := c', curIdx := om.curIdx.setX x 0 } : OrderMaintenance).mirrorDelete x =
        .ok om2 ∧
      (∀ n, om2.nxt = some n →
        RLSafeP { om2 with live := om2.live - 1, nxt := none } n (om2.KB + 1) om2.KB) ∧
      ({ om2 with live := om2.live - 1 } : OrderMaintenance).rebuildStep proofParams = .ok om' ∧
      c'.P = om.cur.P ∧ om2.cur = c' ∧ om2.KB = om.KB ∧
      MX { om2 with live := om2.live - 1 } := by
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  obtain ⟨om', hdel, hW'⟩ := delete_cost costSetup hW hv
  obtain ⟨c', om2, hr1, hm2, hsafe⟩ := delete_safe costSetup hW hv
  have hR' : ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance).rebuildStep proofParams =
    .ok om' := by
    rw [← delete_eq hr1 hm2]; exact hdel
  have hxL : om.curIdx.getX x ∈ A.elist := (hIdx x hv).1
  have hS0 := hI.cur hR.inv
  obtain ⟨c'', hr'', -, -, -, hP'', hM''⟩ := markDeadAgreeM hS0.ok.cost rfl hxL (κ := capsOf
    om.cur.P)
    (fun _ => om.curIdx.getX x) rfl (capsOf_ok _) hS0.ok.cnt hS0.mc
  rw [hr1] at hr''
  injection hr'' with _ hcc; subst hcc
  obtain ⟨e1, e2, -, hX2⟩ := mirrorDelete_M (om := {
    om with
    cur := c'
    curIdx := om.curIdx.setX x 0
  }) (x := x)
    (fun n hn => hI.2.2 n hn) (fun n hn hx0 => hI.mirrorDel x n hn hx0) hm2
  have hX3 : MX ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance) :=
    ⟨by change Mc (capsOf om2.cur.P) om2.cur.P om2.cur; rw [e1]; change Mc (capsOf c'.P) c'.P c'; rw
      [hP'']; exact hM'',
      fun n hn => hX2 n hn⟩
  exact ⟨om', c', om2, hdel, ⟨hW', rebuild_MX hX3 hsafe hR'⟩, hr1, hm2, hsafe,
    hR', hP'', e1, e2, hX3⟩

/-- **A deletion at Level M**: it keeps the invariant, and the machine code runs in at most
`delW K_B` steps. -/
theorem deleteW_ok {om : OrderMaintenance} {m : State} {p : Nat} {Sp :
  OrderMaintenance.Spec.State} (h : WEnc om m p) (hI : MInv om Sp)
    {x : Nat} (hv : x ∈ Sp.list) (hxl : m.loc "x" = x) :
    ∃ om', om.delete proofParams x = .ok om' ∧ MInv om' (OrderMaintenance.Spec.step Sp (.delete
      x)).1 ∧
      om'.KB = om.KB ∧ wp deleteWS (fun m' k => (WEnc om' m' 0 ∨ WEnc om' m' 1) ∧ k ≤ delW
        om.KB) m := by
  have hp := h.p2
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  obtain ⟨om', c', om2, hdel, hI', hr1, hm2, hsafe, hR', hP'', e1, e2, hX3⟩ :=
    hI.delete_prefix hv
  have hxL : om.curIdx.getX x ∈ A.elist := (hIdx x hv).1
  have hS0 := hI.cur hR.inv
  refine ⟨om', hdel, hI', (rebuildStep_KB hR').trans e2, ?_⟩
  refine wp_byPar h ?_
  have h0 := h.bump (parE.maxv m)
  have hxc : x < om.nextHandle := by have := hS.2 x hv; rw [hf]; exact this
  unfold delC
  rw [Machine.wp_seq]
  refine Machine.wp_mono (fun m1 k1 ⟨h1, hl1, hk1⟩ => ?_)
    (curDelW_ok h0 (by simpa using hxl) (by
      have := h0.roomC
      omega) hS0.ok.cost rfl hxL hS0.ok.cnt hS0.mc hr1)
  rw [Machine.wp_seq]
  have hx1 : m1.loc "x" = x := by rw [hl1]; simp [Machine.State.upd, hxl]
  refine Machine.wp_mono (fun m2 k2 ⟨h2, hl2, hk2⟩ => ?_)
    (mirrorDelW_ok h1 hx1 (fun hs => by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
      have h5 := h1.roomN n hn; simp only at h5; omega) (fun n hn hx0 => (hI.mirrorDel x n hn
        hx0).2) hm2)
  rw [Machine.wp_seq]
  refine Machine.wp_mono (fun m3 k3 ⟨h3, hl3, hk3⟩ => ?_) (liveDecW_ok h2)
  have hkb : 1 ≤ ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance).KB := by
    change 1 ≤ om2.KB; rw [e2]; have := hW.kb; change 1 ≤ om.KB; omega
  obtain ⟨-, hwp4⟩ := rebuildW_ok h3 hX3 hkb hsafe hR'
  refine Machine.wp_mono (fun m4 k4 ⟨h4, hl4, hk4⟩ => ⟨wp_par_or hp h4, ?_⟩) hwp4
  have hKB : ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance).KB = om.KB := e2
  rw [hKB] at hk4
  unfold delW
  simp only [Expr.cost, parE] at hk1 hk2 hk3 hk4 ⊢
  omega

/-! ### Order queries -/

/-- **An order query at Level M**: the specification's answer in local `r`, the state unchanged,
at most 100 steps. -/
theorem orderW_okM {om : OrderMaintenance} {m : State} {p : Nat} {Sp :
  OrderMaintenance.Spec.State} (h : WEnc om m p) (hI : MInv om Sp)
    {x y : Nat} (hxv : x ∈ Sp.list) (hyv : y ∈ Sp.list) (hxl : m.loc "x" = x) (hyl : m.loc "y" =
      y) :
    om.order x y = .ok (OrderMaintenance.Spec.precedes Sp.list x y) ∧
      wp orderWS (fun m' k => WEnc om m' p ∧ m'.loc "r" = b2n (OrderMaintenance.Spec.precedes
        Sp.list x y) ∧ k ≤ 100) m := by
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  have ho := order_ok hW.w hxv hyv
  refine ⟨ho, ?_⟩
  obtain ⟨hx1, -, -⟩ := hIdx x hxv
  obtain ⟨hy1, -, -⟩ := hIdx y hyv
  have hrun := order_correct hR.inv hx1 hy1
  have hb : OrderMaintenance.Spec.precedes A.elist (om.curIdx.getX x) (om.curIdx.getX y) =
    OrderMaintenance.Spec.precedes Sp.list x y := by
    unfold OrderMaintenance.order at ho; rw [runCore_ok hrun] at ho; injection ho
  rw [hb] at hrun
  have hS0 := hI.cur hR.inv
  have hxc : x < om.nextHandle := by have := hS.2 x hxv; rw [hf]; exact this
  have hyc : y < om.nextHandle := by have := hS.2 y hyv; rw [hf]; exact this
  exact orderW_ok h hxl hyl (by
    have := h.roomC
    omega) (by
    have := h.roomC
    omega) hS0.ok.cost rfl hx1 hy1
    hS0.ok.cnt hS0.mc hrun

end OrderMaintenance.Impl

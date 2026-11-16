/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakWrapM


/-!
# Theorem W, option (A), stage A3: the peak of the rebuild

The machine code of `RebuildM.lean` with the budget `BW K KH`:
* the pieces of an iteration: `prepC_pk` (`prepareStep_peak`), `copyC_pk` (a copy step, the
  insertion through `nxtInsC_pk`), `endC_pk` (the swap), `spendC_pk`;
* `iterC_pk`: one iteration, from the loop invariant `LoopB` (Level M's `LoopI` with the value
  bounds `WK` of the state of Level F's run; the bounds are carried along the run as option (B)'s
  `loop_wb` carries them: `PrepM.wb`, `copy_wbw`); `loopC_pk`: the loop (`wpB_loop`, the iteration
  cost from `iterW_ok`);
* `startC_pk`: a rebuild start (the trigger, the new capacity, `newCore_pk`, the new handle map);
* `rebuildC_pk`: the rebuild step.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

variable {K KH T : Nat}

/-! ### The pieces of an iteration -/

theorem prepC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K KH T om) {n : Core}
    (hn : om.nxt = some n) (hM : PrepM n) (hN1 : 1 ≤ n.P.N) {r : Bool} {n' : Core}
    (hr : prepareStep.run n = .ok r n') : wpB (BW K KH) (prepC p) TT m := by
  obtain ⟨⟨L', c, he, -, -⟩, -⟩ := prepAgreeM hM hN1 hr (State.setLocs (fun _ => 0) [] [])
  have hnK := hW.nxtK hn
  unfold prepC
  rw [compile_κ₀ (1 - p) n.P]
  exact wpB_coreCall (h.nxt n hn) (vs := []) rfl he (by simp)
    (pk_BW (prepareStep_peak hnK.caps (by have := hnK.k8; omega) (h.nxt n hn) hnK.wb hnK.hh hnK.room hM
      (by simp) he)) (fun _ _ _ _ => trivial)

theorem endC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K KH T om) :
    wpB (BW K KH) (endC p) TT m := by
  obtain ⟨hb1, hb2, -⟩ := hW.pack
  have hp := h.p2
  unfold endC swapC
  refine wpB_seq_T (Qc := TT) ?_ (fun _ _ _ => wpB_T (OrderMaintenance.Machine.wpB_assign_g (Q := TT) 0 rfl (by simp)
    (fun _ _ _ _ => trivial)))
  refine wpB_store_seq 0 (1 - p) rfl rfl (by rw [h.scap 0 (by decide)]; decide) (by simp) (by simp; bw_omega K KH)
    (fun s' _ _ hc => ?_)
  exact wpB_T (OrderMaintenance.Machine.wpB_store_g (Q := TT) 0 0 rfl rfl (by rw [hc, h.scap 1 (by decide)]; decide) (by simp)
    (by simp) (fun _ _ _ _ => trivial))

theorem spendC_pk {s : State} {b : Nat} (hb : s.loc "bud" = b) (hb0 : b ≠ 0) (hbK : b < 2 ^ K) :
    wpB (BW K KH) spendC TT s :=
  wpB_T (OrderMaintenance.Machine.wpB_assign_g (Q := TT) (b - 1) (by simp [Expr.eval, BinOp.eval, hb]; omega)
    (by simp [Expr.eval, BinOp.eval,
      hb]; have := pow_BW K; have := Nat.two_pow_pos KH; unfold BW; split <;> simp <;> omega)
    (fun _ _ _ _ => trivial))

theorem _root_.OrderMaintenance.Proof.Word.WBW.ofWith {t : Nat} {om : OrderMaintenance} {y nx : Option Core} (h : WBW t { om with nxt := y } nx) : WBW t om nx :=
  ⟨h.cur, h.nxt, h.noNxt, h.curIdx, h.cursor, h.hcur, h.live, h.hnd, h.reb⟩

theorem copy_cur {om om' : OrderMaintenance} {n n' : Core} (hcp : copyAtCursor om n = .ok (om', n')) :
    om'.cur = om.cur ∧ om'.KB = om.KB := by
  unfold copyAtCursor at hcp
  cases hl : (om.cur.E.getX om.cursor).live with
  | false =>
    simp only [hl, Bool.false_eq_true, ite_false, pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; exact ⟨rfl, rfl⟩
  | true =>
    simp only [hl, ite_true, bind, Except.bind] at hcp
    split at hcp
    · cases hcp
    · injection hcp with hcp; injection hcp with h1 h2; subst h1; exact ⟨rfl, rfl⟩

theorem copyC_pk {om : OrderMaintenance} {n : Core} {m : State} {p : Nat} (h : WEnc { om with nxt := some n } m p)
    (hW : WK K KH T { om with nxt := some n }) (hC : CopyOK om n) : wpB (BW K KH) (copyC p) TT m := by
  obtain ⟨hb1, hb2, -⟩ := hW.pack
  have hnh : om.nextHandle ≤ T := hW.wbw.hnd
  have hcur : om.cursor < 2 ^ K := hW.cursor
  have hp := h.p2
  have hcK := hW.curK
  obtain ⟨hcE, hlive⟩ := hC
  set e := om.cur.E.getX om.cursor with he
  have hcapE : om.cursor < (capsOf om.cur.P).tbl .E := Nat.lt_of_lt_of_le hcE (h.cur.sle .E)
  unfold copyC
  refine wpB_assign_seq om.cursor (eval_load_lit (by rw [h.scap 2 (by decide)]; decide) h.cursor)
    (by simp [Expr.eval, h.scap 2 (by decide), h.cursor]; bw_omega K KH) (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  have hc1' : s1.loc "c" = om.cursor := by rw [hl1]; simp [State.upd]
  have hdead : (Expr.load (arrF p (.e .dead)) (.var "c")).eval s1 = some (b2n !e.live) :=
    eval_load_var hc1' (by rw [h1.cur.cap]; exact hcapE) (by rw [h1.cur.mem _ _ hcapE]; rfl)
  -- the state after the conditional copy: some wrapper state with the same `cur`, and `c`
  refine wpB_seq_T (Qc := fun s' _ => (∃ W : OrderMaintenance, WEnc W s' p ∧ W.cur = om.cur) ∧ s'.loc "c" = om.cursor) ?_
    (fun s' _ ⟨⟨W, hW', hWc⟩, hcl⟩ => ?_)
  · refine wpB_ite_Q _ hdead (by rw [OrderMaintenance.Machine.Expr.maxv, hdead]; simp [hc1']; unfold b2n BW; split <;> omega)
      (fun s2 hl2 hm2 hc2 => ?_)
    have h2 := h1.congr hm2 hc2
    cases hl : e.live with
    | false =>
      simp only [hl, Bool.not_false, b2n, ne_eq, one_ne_zero, not_false_eq_true, ite_true,
        ↓reduceIte]
      exact OrderMaintenance.Machine.wpB_skip ⟨⟨_, h2, rfl⟩, by rw [hl2, hc1']⟩
    | true =>
      obtain ⟨B, hS, htail, hhc⟩ := hlive hl
      simp only [hl, Bool.not_true, b2n, Bool.false_eq_true, ne_eq, not_true_eq_false, ite_false,
        ↓reduceIte,
        not_false_eq_true]
      have hhT : e.h ≤ T := le_trans (hW.wbw.hcur om.cursor) hnh
      have hc2' : s2.loc "c" = om.cursor := by rw [hl2, hc1']
      have hev2 : (Expr.load (arrF p (.e .h)) (.var "c")).eval s2 = some e.h :=
        eval_load_var hc2' (by rw [h2.cur.cap]; exact hcapE) (by rw [h2.cur.mem _ _ hcapE]; try rfl)
      refine wpB_seq_ofQ (Qc := fun s3 _ => s3.loc = State.upd s2.loc "hh" e.h ∧ s3.mem = s2.mem ∧ s3.cap = s2.cap)
        (wp_assign_g e.h hev2 (fun s3 a b c => ⟨a, b, c⟩))
        (wpB_T (OrderMaintenance.Machine.wpB_assign_g (Q := TT) e.h hev2
          (by rw [OrderMaintenance.Machine.Expr.maxv,
            hev2]; simp [hc2']; bw_omega K KH) (fun _ _ _ _ => trivial)))
        (fun s3 _ ⟨hl3, hm3, hc3⟩ => ?_)
      have h3 := h2.congr hm3 hc3
      have hnE := h3.nxt n rfl
      have hnK := hW.nxtK (n := n) rfl
      have htl := hnK.wb.scalars.2.2.1
      have hmt : (Expr.load (arrF (1 - p) (.s .tail)) (.lit 0)).maxv s3 ≤ BW K KH := by
        simp [Expr.eval, hnE.cap, Fld.cap, hnE.mem (.s .tail) 0 (by simp [Fld.cap]), Fld.get,
          SF.get]
        unfold BW; omega
      have hhc4 : e.h < s3.cap (wIdx (1 - p)) := by
        have := h.roomN n rfl
        rw [hc3, hc2, hc1]
        simp only at this
        omega
      refine wpB_seq_ofQ (Qc := fun s4 _ => s4.loc = State.upd s3.loc "xn" n.tail ∧ s4.mem = s3.mem ∧
          s4.cap = s3.cap)
        (wp_assign_g n.tail (eval_load_lit (by rw [hnE.cap]; simp [Fld.cap])
          (by rw [hnE.mem _ _ (by simp [Fld.cap])]; rfl)) (fun s4 a b c => ⟨a, b, c⟩))
        (wpB_T (OrderMaintenance.Machine.wpB_assign_g (Q := TT) n.tail (eval_load_lit (by rw [hnE.cap]; simp [Fld.cap])
          (by rw [hnE.mem _ _ (by simp [Fld.cap])]; rfl)) hmt (fun _ _ _ _ => trivial)))
        (fun s4 _ ⟨hl4, hm4, hc4⟩ => ?_)
      have h4 := h3.congr hm4 hc4
      obtain ⟨n2, -, -, -, -, -, hwp⟩ := nxtInsW_ok (xn := n.tail) (hh := e.h) h4 rfl hS htail
        (by simp [hl4, State.upd]) (by simp [hl4, hl3, State.upd]) (by rw [hc4]; exact hhc4)
      refine OrderMaintenance.Machine.wpB_mono le_rfl (fun s5 k5 ⟨h5, hl5, _⟩ => ⟨⟨_, h5, rfl⟩, ?_⟩)
        (wpB_and hwp (nxtInsC_pk (xn := n.tail) (hh := e.h) h4 hW rfl hS htail (by simp [hl4, State.upd])
          (by simp [hl4, hl3, State.upd]) (by rw [hc4]; exact hhc4) hhT))
      rw [hl5 "c" (by decide), hl4, hl3, hl2]; simp [State.upd, hc1']
  -- the cursor moves on
  have hcap : om.cursor < s'.cap (arrF p (.e .next)) := by
    rw [hW'.cur.cap, hWc]; exact hcapE
  have hv : s'.mem (arrF p (.e .next)) om.cursor = (om.cur.E.getX om.cursor).next := by
    rw [hW'.cur.mem _ _ (by rw [hWc]; exact hcapE), hWc]; rfl
  have hnx : (om.cur.E.getX om.cursor).next < 2 ^ K := hcK.wb.eNext om.cursor
  exact wpB_T (OrderMaintenance.Machine.wpB_store_g (Q := TT) 0 _ rfl (eval_load_var hcl hcap hv)
    (by rw [hW'.scap 2 (by decide)]; decide) (by simp)
    (by rw [OrderMaintenance.Machine.Expr.maxv,
      eval_load_var hcl hcap hv]; simp [hcl]; bw_omega K KH)
    (fun _ _ _ _ => trivial))

/-! ### The value bounds along the loop -/

/-- A preparation step keeps the value bounds. -/
theorem WK.prep {om : OrderMaintenance} {n : Core} (hW : WK K KH T { om with nxt := some n }) (hM : PrepM n)
    (hN1 : 1 ≤ n.P.N) {r : Bool} {n' : Core} (hpr : prepareStep.run n = .ok r n') :
    WK K KH T { om with nxt := some n' } := by
  obtain ⟨hn, hidx, hh⟩ := hW.wbw.nxt n rfl
  have hmk := hW.npmk n rfl
  have hW' := hM.wb hmk hn hpr
  have hP' : n'.P = n.P := (prepAgreeM hM hN1 hpr (fun _ => 0)).2.1
  have hE : ∀ i, (n'.E.getX i).h = (n.E.getX i).h := by
    have := pres_prepareStep n; rw [hpr] at this; exact this.eH
  refine ⟨⟨hW.wbw.cur, fun c e => ?_, (fun e => nomatch e), hW.wbw.curIdx, hW.wbw.cursor, hW.wbw.hcur,
    hW.wbw.live, hW.wbw.hnd, hW.wbw.reb⟩, hW.cpmk, hW.cwk, fun c e => ?_, fun c e => ?_, hW.kb, hW.hT⟩
  · cases e; rw [hP']; exact ⟨hW', hidx, fun i => by rw [hE]; exact hh i⟩
  · cases e; rw [hP']; exact hmk
  · cases e; rw [hP']; exact hW.nwk n rfl

/-- Moving the cursor to the successor of `head` keeps the value bounds. -/
theorem WK.toCopy {om : OrderMaintenance} {n : Core} (hW : WK K KH T { om with nxt := some n }) :
    WK K KH T { ({ om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } : OrderMaintenance) with
      nxt := some n } :=
  ⟨⟨hW.wbw.cur, hW.wbw.nxt, hW.wbw.noNxt, hW.wbw.curIdx, hW.wbw.cur.eNext _, hW.wbw.hcur, hW.wbw.live,
    hW.wbw.hnd, hW.wbw.reb⟩, hW.cpmk, hW.cwk, hW.npmk, hW.nwk, hW.kb, hW.hT⟩

/-- A copy step keeps the value bounds. -/
theorem WK.copy {om : OrderMaintenance} {n : Core} (hW : WK K KH T { om with nxt := some n }) (hC : CopyOK om n)
    {om' : OrderMaintenance} {n' : Core} (hcp : copyAtCursor om n = .ok (om', n')) : WK K KH T { om' with nxt := some n' } := by
  obtain ⟨hB, hP'⟩ := copy_wbw hC hW.wbw.ofWith hcp
  obtain ⟨hc, hk⟩ := copy_cur hcp
  have hcP : om'.cur.P = om.cur.P := by rw [hc]
  refine ⟨hB.withNxt _, ?_, ?_, fun c e => ?_, fun c e => ?_, ?_, hW.hT⟩
  · show om'.cur.P = proofParams om'.cur.P.N; rw [hcP]; exact hW.cpmk
  · show wK om'.cur.P ≤ K; rw [hcP]; exact hW.cwk
  · cases e; rw [hP']; exact hW.npmk n rfl
  · cases e; rw [hP']; exact hW.nwk n rfl
  · show om'.KB < 2 ^ K; rw [hk]; exact hW.kb

/-- **The loop invariant with the value bounds**: Level M's `LoopI`, the state of Level F's run
bounded (`WK`), its budget at most `K_B`. -/
def LoopB (K KH T : Nat) (R : OrderMaintenance) (p f : Nat) (s : State) : Prop :=
  (∃ om n b, WEnc { om with nxt := some n } s p ∧ s.loc "bud" = b ∧ rebuildLoop om n f b = .ok R ∧
    RLSafe om n f b ∧ WK K KH T { om with nxt := some n } ∧ b ≤ om.KB) ∨ (s.loc "bud" = 0 ∧ WEnc R s (1 - p))

theorem LoopB.loopI {R : OrderMaintenance} {p f : Nat} {s : State} (h : LoopB K KH T R p f s) : LoopI R p f s := by
  rcases h with ⟨om, n, b, h1, h2, h3, h4, -, -⟩ | h
  · exact Or.inl ⟨om, n, b, h1, h2, h3, h4⟩
  · exact Or.inr h

theorem LoopB.congr {R : OrderMaintenance} {p f : Nat} {s s' : State} (h : LoopB K KH T R p f s)
    (hl : s'.loc "bud" = s.loc "bud") (hm : s'.mem = s.mem) (hc : s'.cap = s.cap) : LoopB K KH T R p f s' := by
  rcases h with ⟨om, n, b, h, hb, hr, hS, hW, hbK⟩ | ⟨hb, hW⟩
  · exact Or.inl ⟨om, n, b, h.congr hm hc, by rw [hl, hb], hr, hS, hW, hbK⟩
  · exact Or.inr ⟨by rw [hl, hb], hW.congr hm hc⟩

/-! ### One iteration -/

theorem bud_maxv {s : State} {b : Nat} (hb : s.loc "bud" = b) (hbK : b < 2 ^ K) :
    (Expr.bin .eq (.var "bud") (.lit 0)).maxv s ≤ BW K KH := by
  simp [Expr.eval, BinOp.eval,
    hb]; have := pow_BW K; have := Nat.two_pow_pos KH; unfold BW; split <;> omega

theorem flag_maxv {om : OrderMaintenance} {s : State} {p k : Nat} (h : WEnc om s p) (hk : k < 8) (hv : s.mem (wa k) 0 ≤ 1) :
    (Expr.bin .eq (.load (wa k) (.lit 0)) (.lit 0)).maxv s ≤ BW K KH := by
  simp [Expr.eval, BinOp.eval, h.scap k hk]; split <;> bw_omega K KH

theorem b2n_le (b : Bool) : b2n b ≤ 1 := by unfold b2n; split <;> omega

/-- **One iteration of the rebuild loop.** -/
theorem iterC_pk {R : OrderMaintenance} {p f : Nat} {s : State} (hp : p < 2) (hI : LoopB K KH T R p (f + 1) s) :
    wpB (BW K KH) (iterC p) (fun s' _ => LoopB K KH T R p f s') s := by
  unfold iterC
  rcases hI with ⟨om, n, b, h, hb, hr, hS, hW, hbK⟩ | ⟨hb, hW⟩
  swap
  · refine wpB_ite_Q 1 (by simp [Expr.eval, BinOp.eval, hb])
      (by simp [Expr.eval, BinOp.eval, hb]; bw_omega K KH) (fun s1 hl1 hm1 hc1 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    exact OrderMaintenance.Machine.wpB_skip (Or.inr ⟨by rw [hl1, hb], hW.congr hm1 hc1⟩)
  have hkb : om.KB < 2 ^ K := hW.kb
  have hbK' : b < 2 ^ K := by omega
  by_cases hb0 : b = 0
  · subst hb0
    rw [rebuildLoop_zero] at hr; cases hr
    refine wpB_ite_Q 1 (by simp [Expr.eval, BinOp.eval, hb]) (bud_maxv hb hbK') (fun s1 hl1 hm1 hc1 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    exact OrderMaintenance.Machine.wpB_skip (Or.inl ⟨om, n, 0, h.congr hm1 hc1, by rw [hl1, hb], rebuildLoop_zero om n f,
      rlSafe_zero om n f, hW, Nat.zero_le _⟩)
  refine wpB_ite_Q 0 (by simp [Expr.eval, BinOp.eval, hb, hb0]) (bud_maxv hb hbK') (fun s1 hl1 hm1 hc1 => ?_)
  simp only [ne_eq, not_true_eq_false, ite_false]
  have h1 := h.congr hm1 hc1
  have hS' := hS hb0
  unfold rebuildLoop at hr
  rw [ite_eq_right hb0] at hr
  cases hcs : om.cursorSet with
  | false =>
    obtain ⟨hM, hN1, hhd, hnext⟩ := hS'.1 hcs
    rw [ite_eq_left (by simp [hcs])] at hr
    refine wpB_ite_Q 1 (by simp [Expr.eval, BinOp.eval, h1.scap 3 (by decide), h1.cset, hcs, b2n])
      (flag_maxv h1 (by decide) (by rw [h1.cset]; exact b2n_le _)) (fun s2 hl2 hm2 hc2 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    have h2 := h1.congr hm2 hc2
    cases hpr : prepareStep.run n with
    | error e s' => simp [runCore, hpr, bind, Except.bind] at hr
    | ok r n' =>
      have hrc : runCore n prepareStep = .ok (r, n') := by simp [runCore, hpr]
      simp only [bind, Except.bind, hrc] at hr
      obtain ⟨hcnt, hT, hF⟩ := hnext r n' hpr
      have hW' := hW.prep hM hN1 hpr
      refine wpB_seq_ofQ (prepW_ok h2 rfl hM hN1 hpr hcnt) (prepC_pk h2 hW rfl hM hN1 hpr)
        (fun s3 k3 ⟨h3, hr3, hl3, hk3⟩ => ?_)
      cases r with
      | true =>
        simp only [ite_true] at hr
        refine wpB_ite_Q 1 (by simp [Expr.eval, hr3,
          b2n]) (by simp [Expr.eval, hr3, b2n]; try bw_omega K KH)
          (fun s4 hl4 hm4 hc4 => ?_)
        simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
        have h4 := h3.congr hm4 hc4
        have hcK := hW.curK
        have hhdK : om.cur.head < 2 ^ K := hcK.wb.scalars.2.1
        have hnxK : (om.cur.E.getX om.cur.head).next < 2 ^ K := hcK.wb.eNext _
        have hcapE : om.cur.head < (capsOf om.cur.P).tbl .E := Nat.lt_of_lt_of_le hhd (h4.cur.sle .E)
        have hhd' : (Expr.load (arrF p (.s .head)) (.lit 0)).eval s4 = some om.cur.head :=
          eval_load_lit (by rw [h4.cur.cap]; simp [Fld.cap]) (by rw [h4.cur.mem _ _ (by simp [Fld.cap])]; rfl)
        have hev : (Expr.load (arrF p (.e .next)) (.load (arrF p (.s .head)) (.lit 0))).eval s4 =
            some (om.cur.E.getX om.cur.head).next :=
          eval_load hhd' (by rw [h4.cur.cap]; exact hcapE) (by rw [h4.cur.mem (.e .next) om.cur.head hcapE]; rfl)
        refine OrderMaintenance.Machine.wpB_seq (OrderMaintenance.Machine.wpB_store_g 0 (om.cur.E.getX om.cur.head).next rfl hev
          (by rw [h4.scap 2 (by decide)]; decide) (by simp)
          (by rw [OrderMaintenance.Machine.Expr.maxv, hev, OrderMaintenance.Machine.Expr.maxv,
            hhd']; simp; bw_omega K KH)
          (fun s5 hl5 hm5 hc5 => ?_))
        have h5 := (h4.writeCursor _).congr hm5 hc5
        refine OrderMaintenance.Machine.wpB_store_g 0 1 rfl rfl (by rw [hc5, h4.scap 3 (by decide)]; decide) (by simp)
          (by simp; have := Nat.two_pow_pos KH; bw_omega K KH) (fun s6 hl6 hm6 hc6 => ?_)
        have h6 := (h5.writeCset true).congr hm6 hc6
        exact Or.inl ⟨_, n', b, h6, by rw [hl6, hl5, hl4, hl3 "bud" (by decide), hl2, hl1, hb], hr,
          hT rfl, hW'.toCopy, hbK⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hr
        refine wpB_ite_Q 0 (by simp [Expr.eval, hr3,
          b2n]) (by simp [Expr.eval, hr3, b2n]; try bw_omega K KH)
          (fun s4 hl4 hm4 hc4 => ?_)
        simp only [ne_eq, not_true_eq_false, ite_false]
        have h4 := h3.congr hm4 hc4
        have hb4 : s4.loc "bud" = b := by rw [hl4, hl3 "bud" (by decide), hl2, hl1, hb]
        refine OrderMaintenance.Machine.wpB_mono le_rfl (fun s5 k5 ⟨⟨hb5, hl5, hm5, hc5, hk5⟩, _⟩ => ?_)
          (wpB_and2 (spendW_ok hb4 hb0) (spendC_pk (KH := KH) hb4 hb0 hbK'))
        exact Or.inl ⟨om, n', b - 1, h4.congr hm5 hc5, hb5, hr, hF rfl, hW', by omega⟩
  | true =>
    rw [ite_eq_right (by simp [hcs])] at hr
    refine wpB_ite_Q 0 (by simp [Expr.eval, BinOp.eval, h1.scap 3 (by decide), h1.cset, hcs, b2n])
      (flag_maxv h1 (by decide) (by rw [h1.cset]; exact b2n_le _)) (fun s2 hl2 hm2 hc2 => ?_)
    simp only [ne_eq, not_true_eq_false, ite_false]
    have h2 := h1.congr hm2 hc2
    have hcm : (Expr.bin .eq (.load (wa 2) (.lit 0)) (.lit 0)).maxv s2 ≤ BW K KH := by
      have : om.cursor < 2 ^ K := hW.cursor
      simp [Expr.eval, BinOp.eval, h2.scap 2 (by decide), h2.cursor]
      split <;> bw_omega K KH
    by_cases hc : om.cursor = NIL
    · rw [ite_eq_left hc] at hr; cases hr
      refine wpB_ite_Q 1 (by simp [Expr.eval, BinOp.eval, h2.scap 2 (by decide), h2.cursor, hc]) hcm
        (fun s3 hl3 hm3 hc3 => ?_)
      simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
      refine OrderMaintenance.Machine.wpB_mono le_rfl (fun s4 k4 ⟨⟨hb4, h4, _⟩, _⟩ => Or.inr ⟨hb4, h4⟩)
        (wpB_and2 (endW_ok (h2.congr hm3 hc3)) (endC_pk (h2.congr hm3 hc3) hW))
    · rw [ite_eq_right hc] at hr
      obtain ⟨hC, hnext⟩ := hS'.2 hcs hc
      refine wpB_ite_Q 0 (by simp [Expr.eval, BinOp.eval, h2.scap 2 (by decide), h2.cursor, hc]) hcm
        (fun s3 hl3 hm3 hc3 => ?_)
      simp only [ne_eq, not_true_eq_false, ite_false]
      have h3 := h2.congr hm3 hc3
      cases hcp : copyAtCursor om n with
      | error e => simp [hcp, bind, Except.bind] at hr
      | ok r =>
        obtain ⟨om', n'⟩ := r
        simp only [bind, Except.bind, hcp] at hr
        have hW' := hW.copy hC hcp
        have hk' := (copy_cur hcp).2
        refine wpB_seq_ofQ (copyW_ok h3 hC hcp) (copyC_pk h3 hW hC) (fun s4 k4 ⟨h4, hl4, hk4⟩ => ?_)
        have hb4 : s4.loc "bud" = b := by
          rw [hl4 _ (by decide) (by decide) (by decide) (by decide), hl3, hl2, hl1, hb]
        have hcm4 : (Expr.bin .eq (.load (wa 2) (.lit 0)) (.lit 0)).maxv s4 ≤ BW K KH := by
          have : om'.cursor < 2 ^ K := hW'.cursor
          simp [Expr.eval, BinOp.eval, h4.scap 2 (by decide), h4.cursor]
          split <;> bw_omega K KH
        by_cases hc' : om'.cursor = NIL
        · rw [ite_eq_left hc'] at hr; cases hr
          refine wpB_ite_Q 1 (by simp [Expr.eval, BinOp.eval, h4.scap 2 (by decide), h4.cursor, hc']) hcm4
            (fun s5 hl5 hm5 hc5 => ?_)
          simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
          refine OrderMaintenance.Machine.wpB_mono le_rfl (fun s6 k6 ⟨⟨hb6, h6, _⟩, _⟩ => Or.inr ⟨hb6, h6⟩)
            (wpB_and2 (endW_ok (h4.congr hm5 hc5)) (endC_pk (h4.congr hm5 hc5) hW'))
        · rw [ite_eq_right hc'] at hr
          refine wpB_ite_Q 0 (by simp [Expr.eval, BinOp.eval, h4.scap 2 (by decide), h4.cursor, hc']) hcm4
            (fun s5 hl5 hm5 hc5 => ?_)
          simp only [ne_eq, not_true_eq_false, ite_false]
          have hb5 : s5.loc "bud" = b := by rw [hl5, hb4]
          refine OrderMaintenance.Machine.wpB_mono le_rfl (fun s6 k6 ⟨⟨hb6, hl6, hm6, hc6, _⟩, _⟩ =>
            Or.inl ⟨om', n', b - 1, (h4.congr hm5 hc5).congr hm6 hc6, hb6, hr, hnext om' n' hcp hc', hW', by omega⟩)
            (wpB_and2 (spendW_ok hb5 hb0) (spendC_pk (KH := KH) hb5 hb0 hbK'))

/-! ### The loop -/

/-- **The rebuild loop.** -/
theorem loopC_pk {om : OrderMaintenance} {n : Core} {m : State} {p : Nat} (h : WEnc { om with nxt := some n } m p)
    (hW : WK K KH T { om with nxt := some n }) {R : OrderMaintenance}
    (hr : rebuildLoop om n (om.KB + 1) om.KB = .ok R) (hS : RLSafe om n (om.KB + 1) om.KB) :
    wpB (BW K KH) (loopC p) TT m := by
  have hp := h.p2
  have hkb : om.KB < 2 ^ K := hW.kb
  unfold loopC
  have hk0 : m.mem (wa 7) 0 = om.KB := h.kb
  refine wpB_assign_seq om.KB (eval_load_lit (by rw [h.scap 7 (by decide)]; decide) h.kb)
    (by simp [Expr.eval, h.scap 7 (by decide), hk0]; bw_omega K KH) (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  have hk1 : s1.mem (wa 7) 0 = om.KB := h1.kb
  refine OrderMaintenance.Machine.wpB_loop (om.KB + 1) (fun k s => LoopB K KH T R p (om.KB + 1 - k) s) iterB
    (by simp [Expr.eval, BinOp.eval, h1.scap 7 (by decide), hk1])
    (by simp [Expr.eval, h1.scap 7 (by decide), hk1,
      BinOp.eval]; bw_omega K KH) ?_ ?_ (fun _ _ _ _ => trivial)
  · refine Or.inl ⟨om, n, om.KB, h1.bump _, ?_, by simpa using hr, by simpa using hS, hW, le_rfl⟩
    simp [hl1, State.upd, State.bump]
  · intro k hk s hI
    have hI' : LoopB K KH T R p (om.KB - k + 1) (s.setLoc "it" k) := by
      have e : om.KB + 1 - k = om.KB - k + 1 := by omega
      rw [e] at hI
      exact hI.congr (by simp [State.setLoc, State.upd]) rfl rfl
    refine OrderMaintenance.Machine.wpB_mono le_rfl (fun s' k' ⟨⟨_, _, hk2⟩, hI2⟩ => ⟨?_, hk2⟩)
      (wpB_and2 (iterW_ok hp hI'.loopI) (iterC_pk hp hI'))
    have e : om.KB + 1 - (k + 1) = om.KB - k := by omega
    rw [e]; exact hI2

/-! ### Starting a rebuild -/

theorem size_le4 {N N' : Nat} (h : N' ≤ 4 * N) : Nat.size N' ≤ Nat.size N + 2 := by
  apply Nat.size_le.mpr
  have h1 := Nat.lt_size_self N
  rw [pow_add]
  omega

/-- **A capacity at most four times larger** has `L` at most 2 larger: `wK` at most 128 larger. -/
theorem wK_mono4 {N N' : Nat} (h : N' ≤ 4 * N) : wK (proofParams N') ≤ wK (proofParams N) + 128 := by
  have := size_le4 h
  show 64 * pL N' ≤ 64 * pL N + 128
  unfold pL
  omega
/-- **A rebuild start**: the trigger, the new capacity, the new core (`newCore_pk`), the new handle
map. The new core's word size is at most `K` (`hRK`, about the result of Level F's step). -/
theorem startC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K KH T om) (hn : om.nxt = none)
    (hkb : 1 ≤ om.KB) {R : OrderMaintenance} (hr : om.rebuildStep proofParams = .ok R) (hK0 : wK om.cur.P + 128 ≤ K)
    (hR4 : ∀ c, R.nxt = some c → c.P.N ≤ 4 * R.cur.P.N) : wpB (BW K KH) (startC p) TT m := by
  have hp := h.p2
  have hp' : 1 - p < 2 := by omega
  have hcK := hW.curK
  obtain ⟨hb1, hb2, -, hlvT, hnhT, hrbT, hkbK, -⟩ := hW.pack
  have hcntK : om.cur.count < 2 ^ K := hcK.wb.scalars.1
  have hNK : om.cur.P.N < 2 ^ K := hcK.wb.P.1
  have hLK : om.cur.P.L < 2 ^ K := hcK.wb.P.2.1
  have h64 : 64 ≤ 2 ^ K := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 6 ≤ K by
    have := hcK.k8; omega))
  unfold startC
  -- the three reads
  refine wpB_assign_seq om.cur.count (eval_load_lit (by rw [h.cur.cap]; simp [Fld.cap])
    (by rw [h.cur.mem _ _ (by simp [Fld.cap])]; rfl))
    (by simp [Expr.eval, h.cur.cap, Fld.cap, h.cur.mem (.s .count) 0 (by simp [Fld.cap]), Fld.get,
      SF.get]; bw_omega K KH)
    (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  have hmN : (Expr.load (arrP p) (.lit 0)).maxv s1 ≤ BW K KH := by
    have e : s1.mem (arrP p) 0 = om.cur.P.N := h1.cur.pmem .N
    simp [Expr.eval, h1.cur.pcap, e]; bw_omega K KH
  refine wpB_assign_seq om.cur.P.N (eval_load_lit (by rw [h1.cur.pcap]; decide) (h1.cur.pmem .N)) hmN
    (fun s2 hl2 hm2 hc2 => ?_)
  have h2 := h1.congr hm2 hc2
  refine wpB_assign_seq om.live (eval_load_lit (by rw [h2.scap 4 (by decide)]; decide) h2.live)
    (by simp [Expr.eval, h2.scap 4 (by decide), h2.live]; bw_omega K KH) (fun s3 hl3 hm3 hc3 => ?_)
  have h3 := h2.congr hm3 hc3
  have hcnt3 : s3.loc "cnt" = om.cur.count := by rw [hl3, hl2, hl1]; simp [State.upd]
  have hnC3 : s3.loc "nC" = om.cur.P.N := by rw [hl3, hl2]; simp [State.upd]
  have hlv3 : s3.loc "lv" = om.live := by rw [hl3]; simp [State.upd]
  have hcond : condE.maxv s3 ≤ BW K KH := by
    simp [condE, Expr.eval, BinOp.eval, hcnt3, hnC3, hlv3]
    have : om.cur.P.N / 2 ≤ om.cur.P.N := Nat.div_le_self _ _
    have : om.cur.P.N / 8 ≤ om.cur.P.N := Nat.div_le_self _ _
    split_ifs <;> bw_omega K KH
  by_cases hc : (decide (om.cur.count ≥ om.cur.P.N / 2) || (decide (om.cur.P.N > minimumCapacity) &&
      decide (om.live < om.cur.P.N / 8))) = true
  · have hR : R = startOM om (prepStart (proofParams om.nextCapacity) false) := by
      have e : om.rebuildStep proofParams = .ok (startOM om (prepStart (proofParams om.nextCapacity) false)) := by
        unfold OrderMaintenance.rebuildStep; rw [hn]
        simp only [hc, ite_true, newCore_true, bind, Except.bind, pure, Except.pure]; rfl
      rw [e] at hr; injection hr with hr; exact hr.symm
    subst hR
    have hNc : wK (proofParams om.nextCapacity) ≤ K := by
      have h4 : om.nextCapacity ≤ 4 * om.cur.P.N := hR4 _ rfl
      have := wK_mono4 h4
      rw [← hW.cpmk] at this
      omega
    have hNc' : om.nextCapacity < 2 ^ K :=
      lt_of_lt_of_le (OrderMaintenance.Proof.Word.N_lt _) (Nat.pow_le_pow_right (by norm_num)
        (show pL om.nextCapacity ≤ K by have : 64 * pL om.nextCapacity ≤ K := hNc; omega))
    have hc' : om.cur.P.N / 2 ≤ om.cur.count ∨ (64 < om.cur.P.N ∧ om.live < om.cur.P.N / 8) := by
      simpa [minimumCapacity] using hc
    refine wpB_ite_T 1 (by
      simp only [condE, Expr.eval, hcnt3, hnC3, hlv3, Option.bind_some, BinOp.eval]
      rcases hc' with h' | ⟨h1', h2'⟩
      · simp [h']
      · simp [h1', h2']) hcond (fun s4 hl4 hm4 hc4 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    have h4 := h3.congr hm4 hc4
    -- the scalar writes
    refine wpB_store_seq 0 0 rfl rfl (by rw [h4.scap 3 (by decide)]; decide) (by simp) (by simp)
      (fun s5 hl5 hm5 hc5 => ?_)
    have h5 := (h4.writeCset false).congr hm5 hc5
    refine wpB_store_seq 0 (om.rebuilds + 1) rfl
      (by simp [Expr.eval, BinOp.eval, h5.scap 6 (by decide),
        h5.reb]) (by rw [h5.scap 6 (by decide)]; decide)
      (by simp) (by simp [Expr.eval, BinOp.eval, h5.scap 6 (by decide), h5.reb]; bw_omega K KH)
      (fun s6 hl6 hm6 hc6 => ?_)
    have h6 := (h5.writeReb (om.rebuilds + 1)).congr hm6 hc6
    have hl6' : s6.loc = s3.loc := by rw [hl6, hl5, hl4]
    -- the next capacity
    set na := om.live + ((om.cur.count + (om.cur.P.L + 2)) / (om.KB - 1) + 1)
    have hcapv : 4 * (na + (16 - na)) = om.nextCapacity := by
      show 4 * (na + (16 - na)) = 4 * max na 16
      rw [Nat.max_def]; split <;> omega
    have hnaK : na < 2 ^ K := by omega
    have hdiv : (om.cur.count + (om.cur.P.L + 2)) / (om.KB - 1) ≤ om.cur.count + (om.cur.P.L + 2) :=
      Nat.div_le_self _ _
    have hL6 : s6.mem (arrP p) 1 = om.cur.P.L := h6.cur.pmem .L
    have hK6 : s6.mem (wa 7) 0 = om.KB := h6.kb
    refine wpB_assign_seq na (by
      simp [naE, Expr.eval, hL6, hK6, BinOp.eval, hl6', hcnt3, hlv3, h6.cur.pcap,
        h6.scap 7 (by decide : 7 < 8), hkb]
      omega) (by
      simp [naE, Expr.eval, hL6, hK6, BinOp.eval, hl6', hcnt3, hlv3, h6.cur.pcap,
        h6.scap 7 (by decide : 7 < 8), hkb]
      bw_omega K KH) (fun s7 hl7 hm7 hc7 => ?_)
    have hna7 : s7.loc "na" = na := by rw [hl7]; simp [State.upd]
    refine wpB_seq_ofQ (Qc := fun s8 _ => s8.loc = State.upd s7.loc "nN" om.nextCapacity ∧ s8.mem = s7.mem ∧
        s8.cap = s7.cap)
      (wp_assign_g om.nextCapacity (by
        have : (tsubE (.lit 16) (.var "na")).eval s7 = some (16 - na) := tsubE_eval rfl (by simp [Expr.eval, hna7])
        simp only [nNE, Expr.eval, this, Option.bind_some, BinOp.eval, hna7]
        rw [hcapv]) (fun s8 a b c => ⟨a, b, c⟩))
      (wpB_T (OrderMaintenance.Machine.wpB_assign_g (Q := TT) om.nextCapacity (by
        have : (tsubE (.lit 16) (.var "na")).eval s7 = some (16 - na) := tsubE_eval rfl (by simp [Expr.eval, hna7])
        simp only [nNE, Expr.eval, this, Option.bind_some, BinOp.eval, hna7]
        rw [hcapv]) (by
        simp only [nNE, tsubE, Expr.maxv, Expr.eval, hna7, Option.bind_some, BinOp.eval,
          Option.getD_some]
        split_ifs <;> (try simp only [Option.getD_some, Option.bind_some, Nat.sub_zero,
          Nat.add_zero]) <;> bw_omega K KH) (fun _ _ _ _ => trivial)))
      (fun s8 _ ⟨hl8, hm8, hc8⟩ => ?_)
    have h8 := (h6.congr hm7 hc7).congr hm8 hc8
    have hN8 : s8.loc "nN" = om.nextCapacity := by rw [hl8]; simp [State.upd]
    have hpos : 0 < om.nextCapacity := by rw [← hcapv]; omega
    -- the new core
    refine wpB_seq_ofQ (OrderMaintenance.Impl.newCore_ok (1 - p) hN8 hpos) (newCore_pk (1 - p) hN8 hpos hNc)
      (fun s9 k9 ⟨hE9, hS9, hN9, hl9, hk9⟩ => ?_)
    have hw9 : ∀ k, Same (wa k) s8 s9 := fun k => hS9 _ (wa_notSlot hp')
    have hsl9 : ∀ b, InSlot p b → Same b s8 s9 := fun b hb => hS9 b (fun hb' => inSlot_disj (by omega) hb hb')
    have hcur9 : Enc p (capsOf om.cur.P) om.cur s9 := h8.cur.of_same hsl9
    -- the handle map
    have hcntv : (Expr.load (arrF p (.s .count)) (.lit 0)).eval s9 = some om.cur.count :=
      eval_load_lit (by rw [hcur9.cap]; simp [Fld.cap]) (by rw [hcur9.mem _ _ (by simp [Fld.cap])]; rfl)
    have hNv : (Expr.load (arrP p) (.lit 0)).eval s9 = some om.cur.P.N :=
      eval_load_lit (by rw [hcur9.pcap]; decide) (hcur9.pmem .N)
    have hhv : (Expr.load (wa 5) (.lit 0)).eval s9 = some om.nextHandle :=
      eval_load_lit (by rw [(hw9 5).2, h8.scap 5 (by decide)]; decide) (by rw [(hw9 5).1]; exact h8.next)
    have hev : (idxCapE p).eval s9 = some (om.nextHandle + (om.cur.P.N - om.cur.count) + om.nextCapacity) := by
      have ht := tsubE_eval hNv hcntv
      unfold idxCapE
      rw [eval_bin (eval_bin hhv ht) (show (Expr.var "nN").eval s9 = some om.nextCapacity by simp [Expr.eval, hN9])]
      rfl
    have hmx : (idxCapE p).maxv s9 ≤ BW K KH := by
      have e1 : s9.mem (wa 5) 0 = om.nextHandle := by rw [(hw9 5).1]; exact h8.next
      have e2 : s9.mem (arrP p) 0 = om.cur.P.N := hcur9.pmem .N
      have e3 : s9.mem (arrF p (.s .count)) 0 = om.cur.count := by rw [hcur9.mem _ _ (by simp [Fld.cap])]; rfl
      have c1 : s9.cap (wa 5) = 1 := by rw [(hw9 5).2, h8.scap 5 (by decide)]
      have c2 : s9.cap (arrP p) = 16 := hcur9.pcap
      have c3 : s9.cap (arrF p (.s .count)) = 1 := by rw [hcur9.cap]; simp [Fld.cap]
      simp [idxCapE, tsubE, Expr.eval, BinOp.eval, e1, e2, e3, c1, c2, c3, hN9]
      split_ifs <;> (try simp only [Option.getD_some, Option.bind_some, Nat.sub_zero,
        Nat.add_zero]) <;> bw_omega K KH
    refine wpB_seq_T (OrderMaintenance.Machine.wpB_alloc_g (Q := fun s10 _ => s10.cap (wa 1) = 1) _ hev hmx
      (fun s10 _ _ hc10 => by
        rw [hc10]; simp [State.alloc, State.upd, wa_ne_idx (show 1 < 8 by decide)]
        rw [(hw9 1).2, h8.scap 1 (by decide)])) (fun s10 _ hc10 => ?_)
    exact wpB_T (OrderMaintenance.Machine.wpB_store_g (Q := TT) 0 1 rfl rfl (by rw [hc10]; decide) (by simp)
      (by simp; bw_omega K KH) (fun _ _ _ _ => trivial))
  · have hc' : ¬ (om.cur.P.N / 2 ≤ om.cur.count ∨ (64 < om.cur.P.N ∧ om.live < om.cur.P.N / 8)) := by
      simpa [minimumCapacity] using hc
    push Not at hc'
    refine wpB_ite_T 0 (by
      simp only [condE, Expr.eval, hcnt3, hnC3, hlv3, Option.bind_some, BinOp.eval]
      by_cases h64 : 64 < om.cur.P.N
      · simp [hc'.1, Nat.not_lt.mpr (hc'.2 h64)]
      · simp [hc'.1, h64]) hcond (fun _ _ _ _ => ?_)
    simpa using wpB_skip_T

/-! ### The rebuild step -/

/-- **The rebuild step**: a rebuild start, or the loop. -/
theorem rebuildC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K KH T om) (hX : MX om)
    (hkb : 1 ≤ om.KB) (hF : ∀ n, om.nxt = some n → RLSafeP { om with nxt := none } n (om.KB + 1) om.KB)
    {R : OrderMaintenance} (hr : om.rebuildStep proofParams = .ok R) (hK0 : wK om.cur.P + 128 ≤ K)
    (hR4 : ∀ c, R.nxt = some c → c.P.N ≤ 4 * R.cur.P.N) : wpB (BW K KH) (rebuildC p) TT m := by
  have hmx : (Expr.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)).maxv m ≤ BW K KH :=
    flag_maxv h (by decide) (by rw [h.nxtOn]; exact b2n_le _)
  unfold rebuildC
  cases hn : om.nxt with
  | none =>
    refine wpB_ite_T 1 (by simp [Expr.eval, BinOp.eval, h.scap 1 (by decide), h.nxtOn, hn, b2n]) hmx
      (fun s1 hl1 hm1 hc1 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    exact startC_pk (h.congr hm1 hc1) hW hn hkb hr hK0 hR4
  | some n0 =>
    have hr' : rebuildLoop { om with nxt := none } n0 (om.KB + 1) om.KB = .ok R := by
      unfold OrderMaintenance.rebuildStep at hr; rw [hn] at hr; exact hr
    obtain ⟨hS, -⟩ := loop_M _ _ _ _ (hF n0 hn) (hX.2 n0 hn) hX.1
    have hom : ({ ({ om with nxt := none } : OrderMaintenance) with nxt := some n0 } : OrderMaintenance) = om := by
      cases om; simp only at hn; subst hn; rfl
    refine wpB_ite_T 0 (by simp [Expr.eval, BinOp.eval, h.scap 1 (by decide), h.nxtOn, hn, b2n]) hmx
      (fun s1 hl1 hm1 hc1 => ?_)
    simp only [ne_eq, not_true_eq_false, ite_false]
    have h1 : WEnc ({ ({ om with nxt := none } : OrderMaintenance) with nxt := some n0 } : OrderMaintenance) s1 p := by
      rw [hom]; exact h.congr hm1 hc1
    have hW1 : WK K KH T ({ ({ om with nxt := none } : OrderMaintenance) with nxt := some n0 } : OrderMaintenance) := by rw [hom]; exact hW
    exact loopC_pk h1 hW1 hr' hS

end OrderMaintenance.Impl

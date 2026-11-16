/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.WrapM


/-!
# M6: the rebuild loop as machine code

`loopC p` runs Level F's `rebuildLoop om nxt (K_B + 1) K_B`, with `cur` in slot `p` and `nxt` in
slot `1 - p`. It is a `for` loop of `K_B + 1` iterations; the local `bud` holds the budget, and an
iteration with no budget left does nothing. The swap sets the budget to 0, so the iterations after
it do nothing either (the parity has changed, but they only read `bud`).

What each iteration needs from the run (the preconditions of the core calls) is collected along
Level F's run by `RLSafe`.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-! ### Rules that forget the intermediate state -/

theorem wp_ite_g {c : Expr} {t f : Stmt} {Q : State → Nat → Prop} {s : State} (v : Nat)
    (hc : c.eval s = some v)
    (h : ∀ s', s'.loc = s.loc → s'.mem = s.mem → s'.cap = s.cap →
      wp (if v ≠ 0 then t else f) (fun s'' n => Q s'' (1 + c.cost + n)) s') : wp (.ite c t f) Q s := by
  rw [OrderMaintenance.Machine.wp_ite]; exact ⟨v, hc, h _ rfl rfl rfl⟩

theorem wp_assign_g {x : Reg} {e : Expr} {Q : State → Nat → Prop} {s : State} (v : Nat)
    (he : e.eval s = some v)
    (h : ∀ s', s'.loc = OrderMaintenance.Machine.State.upd s.loc x v → s'.mem = s.mem → s'.cap = s.cap → Q s' (1 + e.cost)) :
    wp (.assign x e) Q s := by
  rw [OrderMaintenance.Machine.wp_assign]; exact ⟨v, he, h _ rfl rfl rfl⟩

theorem wp_store_g {a : Arr} {i e : Expr} {Q : State → Nat → Prop} {s : State} (j v : Nat)
    (hi : i.eval s = some j) (he : e.eval s = some v) (hj : j < s.cap a)
    (h : ∀ s', s'.loc = s.loc → s'.mem = (s.write a j v).mem → s'.cap = s.cap → Q s' (1 + i.cost + e.cost)) :
    wp (.store a i e) Q s := by
  rw [OrderMaintenance.Machine.wp_store]; exact ⟨j, v, hi, he, hj, h _ rfl rfl rfl⟩

theorem wp_skip_g {Q : State → Nat → Prop} {s : State} (h : Q s 1) : wp .skip Q s :=
  OrderMaintenance.Machine.wp_skip.mpr h

/-! ### The code -/

/-- A preparation step of `nxt`; `r` = whether it is ready. -/
def prepC (p : Nat) : Stmt :=
  .call "prepareStep" [] (prepP.body.compile (1 - p) κ₀) ["r"] [] ["r"]

/-- Copy the element at the cursor into `nxt` if it is live, and advance the cursor. -/
def copyC (p : Nat) : Stmt :=
  .seq (.assign "c" (.load (wa 2) (.lit 0)))
    (.seq (.ite (.load (arrF p (.e .dead)) (.var "c")) .skip
        (.seq (.assign "hh" (.load (arrF p (.e .h)) (.var "c")))
          (.seq (.assign "xn" (.load (arrF (1 - p) (.s .tail)) (.lit 0))) (nxtInsC p))))
      (.store (wa 2) (.lit 0) (.load (arrF p (.e .next)) (.var "c"))))

/-- The end of the rebuild: the swap, and no budget left. -/
def endC (p : Nat) : Stmt := .seq (swapC p) (.assign "bud" (.lit 0))

/-- Spend one unit of budget. -/
def spendC : Stmt := .assign "bud" (.bin .sub (.var "bud") (.lit 1))

/-- One iteration of the rebuild loop. -/
def iterC (p : Nat) : Stmt :=
  .ite (.bin .eq (.var "bud") (.lit 0)) .skip
    (.ite (.bin .eq (.load (wa 3) (.lit 0)) (.lit 0))
      (.seq (prepC p)
        (.ite (.var "r")
          (.seq (.store (wa 2) (.lit 0) (.load (arrF p (.e .next)) (.load (arrF p (.s .head)) (.lit 0))))
            (.store (wa 3) (.lit 0) (.lit 1)))
          spendC))
      (.ite (.bin .eq (.load (wa 2) (.lit 0)) (.lit 0))
        (endC p)
        (.seq (copyC p)
          (.ite (.bin .eq (.load (wa 2) (.lit 0)) (.lit 0)) (endC p) spendC))))

/-- The rebuild loop: `K_B + 1` iterations with budget `K_B`. -/
def loopC (p : Nat) : Stmt :=
  .seq (.assign "bud" (.load (wa 7) (.lit 0)))
    (.loop "it" (.bin .add (.load (wa 7) (.lit 0)) (.lit 1)) (iterC p))

/-! ### What the iterations need -/

/-- What a copy step needs: the cursor is an element of `cur`, and if it is live, `nxt` is in
service with the anchor `tail`, and the handle is below the counter. -/
def CopyOK (om : OrderMaintenance) (n : Core) : Prop :=
  om.cursor < om.cur.E.size ∧ ((om.cur.E.getX om.cursor).live = true →
    ∃ B, InService n B ∧ n.tail ∈ B ∧ (om.cur.E.getX om.cursor).h < om.nextHandle)

/-- **What the iterations of Level F's run need**, along the run. -/
def RLSafe (om : OrderMaintenance) (n : Core) : Nat → Nat → Prop
  | 0, _ => True
  | f + 1, b => b ≠ 0 →
    (om.cursorSet = false → PrepM n ∧ 1 ≤ n.P.N ∧ om.cur.head < om.cur.E.size ∧
      ∀ r n', prepareStep.run n = .ok r n' → n'.count = n.count ∧
        (r = true → RLSafe { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } n' f b) ∧
        (r = false → RLSafe om n' f (b - 1))) ∧
    (om.cursorSet = true → om.cursor ≠ NIL → CopyOK om n ∧
      ∀ om' n', copyAtCursor om n = .ok (om', n') → om'.cursor ≠ NIL → RLSafe om' n' f (b - 1))

theorem rlSafe_zero (om : OrderMaintenance) (n : Core) : ∀ f, RLSafe om n f 0
  | 0 => trivial
  | _ + 1 => fun h => absurd rfl h

theorem rebuildLoop_zero (om : OrderMaintenance) (n : Core) : ∀ f, rebuildLoop om n f 0 = .ok { om with nxt := some n }
  | 0 => rfl
  | _ + 1 => rfl

/-! ### A preparation step -/

theorem prepW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {n : Core} (hn : om.nxt = some n)
    (hM : PrepM n) (hN1 : 1 ≤ n.P.N) {r : Bool} {n' : Core} (hr : prepareStep.run n = .ok r n')
    (hcnt : n'.count = n.count) :
    wp (prepC p) (fun m' k => WEnc { om with nxt := some n' } m' p ∧ m'.loc "r" = b2n r ∧
      (∀ x, x ≠ "r" → m'.loc x = m.loc x) ∧ k ≤ 450) m := by
  obtain ⟨⟨L', c, he, hr', hc⟩, hP, -, -⟩ := prepAgreeM hM hN1 hr (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] [])
  unfold prepC
  rw [compile_κ₀ (1 - p) n.P]
  refine wp_coreCall (h.nxt n hn) (vs := []) rfl he (fun m2 hE hS hL => ?_)
  refine ⟨h.of_nxt hn (by rw [hP]; exact hE) hS hcnt hP, ?_, fun x hx => ?_, ?_⟩
  · rw [hL]; simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hr']
  · rw [hL]; simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hx]
  · simp [OrderMaintenance.Machine.costList]; omega

/-! ### A copy step -/

theorem eval_load_var {s : State} {a : Arr} {x : Reg} {j v : Nat} (hx : s.loc x = j) (hj : j < s.cap a)
    (hv : s.mem a j = v) : (Expr.load a (.var x)).eval s = some v := by
  simp [Expr.eval, hx, hj, hv]

theorem eval_load_lit {s : State} {a : Arr} {j v : Nat} (hj : j < s.cap a)
    (hv : s.mem a j = v) : (Expr.load a (.lit j)).eval s = some v := by
  simp [Expr.eval, hj, hv]

/-- The insertion bound of a core of the proof parameters (it depends only on the `K`s). -/
def insB : Nat := insBound (proofParams 0)

theorem insBound_proof (N : Nat) : insBound (proofParams N) = insB := rfl

theorem InService.insB {c : Core} {L : List Nat} (h : InService c L) : insBound c.P = insB := by
  rw [h.ok.pmk]; rfl

attribute [irreducible] insB

theorem eval_bin {s : State} {op : BinOp} {a b : Expr} {x y : Nat} (ha : a.eval s = some x)
    (hb : b.eval s = some y) : (Expr.bin op a b).eval s = op.eval x y := by
  simp [Expr.eval, ha, hb]

theorem eval_load {s : State} {a : Arr} {i : Expr} {j v : Nat} (hi : i.eval s = some j) (hj : j < s.cap a)
    (hv : s.mem a j = v) : (Expr.load a i).eval s = some v := by
  simp [Expr.eval, hi, hj, hv]

/-- The last part of a copy step: the cursor moves to the successor. -/
theorem copyEnd {W : OrderMaintenance} {s : State} {p : Nat} (h : WEnc W s p) {c : Nat} (hc : s.loc "c" = c)
    (hcE : c < W.cur.E.size) {Q : State → Nat → Prop}
    (hQ : ∀ s', WEnc { W with cursor := (W.cur.E.getX c).next } s' p → s'.loc = s.loc →
      Q s' (1 + (Expr.lit 0).cost + (Expr.load (arrF p (.e .next)) (.var "c")).cost)) :
    wp (.store (wa 2) (.lit 0) (.load (arrF p (.e .next)) (.var "c"))) Q s := by
  have hcap : c < s.cap (arrF p (.e .next)) := by
    rw [h.cur.cap]; exact Nat.lt_of_lt_of_le hcE (h.cur.sle .E)
  refine wp_store_g 0 (W.cur.E.getX c).next rfl
    (eval_load_var hc hcap (by rw [h.cur.mem _ _ (by rw [← h.cur.cap]; exact hcap)]; rfl))
    (by rw [h.scap 2 (by decide)]; decide) (fun s' hl hm hcp => ?_)
  exact hQ s' ((h.writeCursor _).congr hm hcp) hl

theorem copyW_ok {om : OrderMaintenance} {n : Core} {m : State} {p : Nat} (h : WEnc { om with nxt := some n } m p)
    (hC : CopyOK om n) {om' : OrderMaintenance} {n' : Core} (hcp : copyAtCursor om n = .ok (om', n')) :
    wp (copyC p) (fun m' k => WEnc { om' with nxt := some n' } m' p ∧
      (∀ x, x ≠ "c" → x ≠ "hh" → x ≠ "xn" → x ≠ "y2" → m'.loc x = m.loc x) ∧ k ≤ insB + 100) m := by
  have hp := h.p2
  obtain ⟨hcE, hlive⟩ := hC
  set e := om.cur.E.getX om.cursor with he
  have hcapE : om.cursor < (capsOf om.cur.P).tbl .E := Nat.lt_of_lt_of_le hcE (h.cur.sle .E)
  unfold copyC
  rw [OrderMaintenance.Machine.wp_seq]
  refine wp_assign_g om.cursor (eval_load_lit (by rw [h.scap 2 (by decide)]; decide) h.cursor)
    (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  have hc1' : s1.loc "c" = om.cursor := by rw [hl1]; simp [OrderMaintenance.Machine.State.upd]
  have hl1' : ∀ x, x ≠ "c" → s1.loc x = m.loc x := fun x hx => by rw [hl1]; simp [OrderMaintenance.Machine.State.upd, hx]
  rw [OrderMaintenance.Machine.wp_seq]
  have hdead : (Expr.load (arrF p (.e .dead)) (.var "c")).eval s1 = some (b2n !e.live) :=
    eval_load_var hc1' (by rw [h1.cur.cap]; exact hcapE) (by rw [h1.cur.mem _ _ hcapE]; rfl)
  refine wp_ite_g _ hdead (fun s2 hl2 hm2 hc2 => ?_)
  have h2 := h1.congr hm2 hc2
  cases hl : e.live with
  | false =>
    have hom : om' = { om with cursor := e.next } ∧ n' = n := by
      unfold copyAtCursor at hcp; simp only [← he, hl] at hcp; cases hcp; exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hom
    simp only [hl, Bool.not_false, b2n, ne_eq, one_ne_zero, not_false_eq_true, ite_true, ↓reduceIte]
    refine wp_skip_g ?_
    refine copyEnd h2 (by rw [hl2, hc1']) hcE (fun s3 h3 hl3 => ⟨h3, fun x a b c d => ?_, ?_⟩)
    · rw [hl3, hl2, hl1' x a]
    · simp [Expr.cost]
  | true =>
    obtain ⟨B, hS, htail, hhc⟩ := hlive hl
    simp only [hl, Bool.not_true, b2n, Bool.false_eq_true, ne_eq, not_true_eq_false, ite_false,
      ↓reduceIte,
      not_false_eq_true]
    rw [OrderMaintenance.Machine.wp_seq]
    refine wp_assign_g e.h (eval_load_var (by rw [hl2, hc1']) (by rw [h2.cur.cap]; exact hcapE)
      (by rw [h2.cur.mem _ _ hcapE]; rfl)) (fun s3 hl3 hm3 hc3 => ?_)
    have h3 := h2.congr hm3 hc3
    rw [OrderMaintenance.Machine.wp_seq]
    have hnE := h3.nxt n rfl
    refine wp_assign_g n.tail (eval_load_lit (by rw [hnE.cap]; simp [Fld.cap])
      (by rw [hnE.mem _ _ (by simp [Fld.cap])]; rfl)) (fun s4 hl4 hm4 hc4 => ?_)
    have h4 := h3.congr hm4 hc4
    have hhc4 : e.h < s4.cap (wIdx (1 - p)) := by
      have := h.roomN n rfl
      rw [hc4, hc3, hc2, hc1]
      simp only at this
      omega
    obtain ⟨n2, hr2, -, -, -, -, hwp⟩ := nxtInsW_ok h4 rfl hS htail
      (by rw [hl4]; simp [OrderMaintenance.Machine.State.upd]) (by rw [hl4, hl3]; simp [OrderMaintenance.Machine.State.upd]) hhc4
    have hom : om' = { om with nxtIdx := om.nxtIdx.setX e.h n.E.size, cursor := e.next } ∧ n' = n2 := by
      unfold copyAtCursor at hcp; simp only [← he, hl, ite_true, runCore, hr2] at hcp; cases hcp
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hom
    refine OrderMaintenance.Machine.wp_mono (fun s5 k5 ⟨h5, hl5, hk5⟩ => ?_) hwp
    have hc5 : s5.loc "c" = om.cursor := by
      rw [hl5 "c" (by decide), hl4, hl3, hl2]; simp [OrderMaintenance.Machine.State.upd, hc1']
    refine copyEnd h5 hc5 hcE (fun s6 h6 hl6 => ⟨?_, fun x a b c d => ?_, ?_⟩)
    · exact h6
    · rw [hl6, hl5 x d, hl4, hl3, hl2]; simp [OrderMaintenance.Machine.State.upd, b, c, hl1' x a]
    · rw [hS.insB] at hk5; simp [Expr.cost]; omega

/-! ### One iteration -/

/-- The loop's invariant, `f` iterations from the end of a run with result `R`: the machine holds
a state of the run (with its budget in `bud`), or the run has ended in the swap (no budget). -/
def LoopI (R : OrderMaintenance) (p f : Nat) (s : State) : Prop :=
  (∃ om n b, WEnc { om with nxt := some n } s p ∧ s.loc "bud" = b ∧ rebuildLoop om n f b = .ok R ∧
    RLSafe om n f b) ∨ (s.loc "bud" = 0 ∧ WEnc R s (1 - p))

/-- The locals an iteration may change. -/
def ItLoc (x : Reg) : Prop := x ≠ "bud" ∧ x ≠ "r" ∧ x ≠ "c" ∧ x ≠ "hh" ∧ x ≠ "xn" ∧ x ≠ "y2"

/-- The cost bound of an iteration. -/
def iterB : Nat := insB + 600

theorem swap_with (om : OrderMaintenance) (n : Core) : ({ om with nxt := some n } : OrderMaintenance).swap n = om.swap n := rfl

theorem endW_ok {om : OrderMaintenance} {n : Core} {s : State} {p : Nat} (h : WEnc { om with nxt := some n } s p) :
    wp (endC p) (fun s' k => s'.loc "bud" = 0 ∧ WEnc (om.swap n) s' (1 - p) ∧
      (∀ x, x ≠ "bud" → s'.loc x = s.loc x) ∧ k ≤ 20) s := by
  unfold endC
  rw [OrderMaintenance.Machine.wp_seq]
  refine swapW_ok h rfl (fun m1 k1 h1 hl1 hk1 => ?_)
  refine wp_assign_g 0 rfl (fun s2 hl2 hm2 hc2 => ⟨?_, h1.congr hm2 hc2, fun x hx => ?_, ?_⟩)
  · rw [hl2]; simp [OrderMaintenance.Machine.State.upd]
  · rw [hl2]; simp [OrderMaintenance.Machine.State.upd, hx, hl1]
  · simp [Expr.cost]; omega

theorem spendW_ok {s : State} {b : Nat} (hb : s.loc "bud" = b) (hb0 : b ≠ 0) :
    wp spendC (fun s' k => s'.loc "bud" = b - 1 ∧ (∀ x, x ≠ "bud" → s'.loc x = s.loc x) ∧
      s'.mem = s.mem ∧ s'.cap = s.cap ∧ k ≤ 5) s := by
  refine wp_assign_g (b - 1) (by simp [Expr.eval, BinOp.eval, hb]; omega)
    (fun s2 hl2 hm2 hc2 => ⟨?_, fun x hx => ?_, hm2, hc2, by simp [Expr.cost]⟩)
  · rw [hl2]; simp [OrderMaintenance.Machine.State.upd]
  · rw [hl2]; simp [OrderMaintenance.Machine.State.upd, hx]

theorem iterW_ok {R : OrderMaintenance} {p f : Nat} {s : State} (hp : p < 2) (hI : LoopI R p (f + 1) s) :
    wp (iterC p) (fun s' k => LoopI R p f s' ∧ (∀ x, ItLoc x → s'.loc x = s.loc x) ∧ k ≤ iterB) s := by
  unfold iterC
  rcases hI with ⟨om, n, b, h, hb, hr, hS⟩ | ⟨hb, hW⟩
  swap
  · refine wp_ite_g 1 (by simp [Expr.eval, BinOp.eval, hb]) (fun s1 hl1 hm1 hc1 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    exact wp_skip_g ⟨Or.inr ⟨by rw [hl1, hb], hW.congr hm1 hc1⟩, fun x _ => by rw [hl1],
      by unfold iterB; simp only [Expr.cost]; omega⟩
  by_cases hb0 : b = 0
  · subst hb0
    rw [rebuildLoop_zero] at hr; cases hr
    refine wp_ite_g 1 (by simp [Expr.eval, BinOp.eval, hb]) (fun s1 hl1 hm1 hc1 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    exact wp_skip_g ⟨Or.inl ⟨om, n, 0, h.congr hm1 hc1, by rw [hl1, hb], rebuildLoop_zero om n f,
      rlSafe_zero om n f⟩, fun x _ => by rw [hl1], by unfold iterB; simp only [Expr.cost]; omega⟩
  refine wp_ite_g 0 (by simp [Expr.eval, BinOp.eval, hb, hb0]) (fun s1 hl1 hm1 hc1 => ?_)
  simp only [ne_eq, not_true_eq_false, ite_false]
  have h1 := h.congr hm1 hc1
  have hS' := hS hb0
  unfold rebuildLoop at hr
  rw [ite_eq_right hb0] at hr
  cases hcs : om.cursorSet with
  | false =>
    obtain ⟨hM, hN1, hhd, hnext⟩ := hS'.1 hcs
    rw [ite_eq_left (by simp [hcs])] at hr
    refine wp_ite_g 1 (by simp [Expr.eval, BinOp.eval, h1.scap 3 (by decide), h1.cset, hcs, b2n])
      (fun s2 hl2 hm2 hc2 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    have h2 := h1.congr hm2 hc2
    cases hpr : prepareStep.run n with
    | error e s' => simp [runCore, hpr, bind, Except.bind] at hr
    | ok r n' =>
      have hrc : runCore n prepareStep = .ok (r, n') := by simp [runCore, hpr]
      simp only [bind, Except.bind, hrc] at hr
      obtain ⟨hcnt, hT, hF⟩ := hnext r n' hpr
      rw [OrderMaintenance.Machine.wp_seq]
      refine OrderMaintenance.Machine.wp_mono (fun s3 k3 ⟨h3, hr3, hl3, hk3⟩ => ?_) (prepW_ok h2 rfl hM hN1 hpr hcnt)
      cases r with
      | true =>
        simp only [ite_true] at hr
        refine wp_ite_g 1 (by simp [Expr.eval, hr3, b2n]) (fun s4 hl4 hm4 hc4 => ?_)
        simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
        have h4 := h3.congr hm4 hc4
        have hcapE : om.cur.head < (capsOf om.cur.P).tbl .E := Nat.lt_of_lt_of_le hhd (h4.cur.sle .E)
        rw [OrderMaintenance.Machine.wp_seq]
        refine wp_store_g 0 (om.cur.E.getX om.cur.head).next rfl ?_ (by rw [h4.scap 2 (by decide)]; decide)
          (fun s5 hl5 hm5 hc5 => ?_)
        · have hhd' : (Expr.load (arrF p (.s .head)) (.lit 0)).eval s4 = some om.cur.head :=
            eval_load_lit (by rw [h4.cur.cap]; simp [Fld.cap]) (by rw [h4.cur.mem _ _ (by simp [Fld.cap])]; rfl)
          exact eval_load hhd' (by rw [h4.cur.cap]; exact hcapE)
            (by rw [h4.cur.mem (.e .next) om.cur.head (by exact hcapE)]; rfl)
        have h5 := (h4.writeCursor _).congr hm5 hc5
        refine wp_store_g 0 1 rfl rfl (by rw [hc5, h4.scap 3 (by decide)]; decide) (fun s6 hl6 hm6 hc6 => ?_)
        have h6 := (h5.writeCset true).congr hm6 hc6
        refine ⟨Or.inl ⟨_, n', b, h6, by rw [hl6, hl5, hl4, hl3 "bud" (by decide), hl2, hl1, hb], hr,
          hT rfl⟩, fun x hx => ?_, ?_⟩
        · rw [hl6, hl5, hl4, hl3 x hx.2.1, hl2, hl1]
        · unfold iterB; simp only [Expr.cost] at hk3 ⊢; omega
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hr
        refine wp_ite_g 0 (by simp [Expr.eval, hr3, b2n]) (fun s4 hl4 hm4 hc4 => ?_)
        simp only [ne_eq, not_true_eq_false, ite_false]
        have h4 := h3.congr hm4 hc4
        have hb4 : s4.loc "bud" = b := by rw [hl4, hl3 "bud" (by decide), hl2, hl1, hb]
        refine OrderMaintenance.Machine.wp_mono (fun s5 k5 ⟨hb5, hl5, hm5, hc5, hk5⟩ => ?_) (spendW_ok hb4 hb0)
        refine ⟨Or.inl ⟨om, n', b - 1, h4.congr hm5 hc5, hb5, hr, hF rfl⟩, fun x hx => ?_, ?_⟩
        · rw [hl5 x hx.1, hl4, hl3 x hx.2.1, hl2, hl1]
        · unfold iterB; simp only [Expr.cost] at hk3 ⊢; omega
  | true =>
    rw [ite_eq_right (by simp [hcs])] at hr
    refine wp_ite_g 0 (by simp [Expr.eval, BinOp.eval, h1.scap 3 (by decide), h1.cset, hcs, b2n])
      (fun s2 hl2 hm2 hc2 => ?_)
    simp only [ne_eq, not_true_eq_false, ite_false]
    have h2 := h1.congr hm2 hc2
    by_cases hc : om.cursor = NIL
    · rw [ite_eq_left hc] at hr; cases hr
      refine wp_ite_g 1 (by simp [Expr.eval, BinOp.eval, h2.scap 2 (by decide), h2.cursor, hc])
        (fun s3 hl3 hm3 hc3 => ?_)
      simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
      refine OrderMaintenance.Machine.wp_mono (fun s4 k4 ⟨hb4, h4, hl4, hk4⟩ => ?_) (endW_ok (h2.congr hm3 hc3))
      refine ⟨Or.inr ⟨hb4, h4⟩, fun x hx => ?_, ?_⟩
      · rw [hl4 x hx.1, hl3, hl2, hl1]
      · unfold iterB; simp only [Expr.cost] at hk4 ⊢; omega
    · rw [ite_eq_right hc] at hr
      obtain ⟨hC, hnext⟩ := hS'.2 hcs hc
      refine wp_ite_g 0 (by simp [Expr.eval, BinOp.eval, h2.scap 2 (by decide), h2.cursor, hc])
        (fun s3 hl3 hm3 hc3 => ?_)
      simp only [ne_eq, not_true_eq_false, ite_false]
      have h3 := h2.congr hm3 hc3
      cases hcp : copyAtCursor om n with
      | error e => simp [hcp, bind, Except.bind] at hr
      | ok r =>
        obtain ⟨om', n'⟩ := r
        simp only [bind, Except.bind, hcp] at hr
        rw [OrderMaintenance.Machine.wp_seq]
        refine OrderMaintenance.Machine.wp_mono (fun s4 k4 ⟨h4, hl4, hk4⟩ => ?_) (copyW_ok h3 hC hcp)
        have hb4 : s4.loc "bud" = b := by
          rw [hl4 _ (by decide) (by decide) (by decide) (by decide), hl3, hl2, hl1, hb]
        by_cases hc' : om'.cursor = NIL
        · rw [ite_eq_left hc'] at hr; cases hr
          refine wp_ite_g 1 (by simp [Expr.eval, BinOp.eval, h4.scap 2 (by decide), h4.cursor, hc'])
            (fun s5 hl5 hm5 hc5 => ?_)
          simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
          refine OrderMaintenance.Machine.wp_mono (fun s6 k6 ⟨hb6, h6, hl6, hk6⟩ => ?_) (endW_ok (h4.congr hm5 hc5))
          refine ⟨Or.inr ⟨hb6, h6⟩, fun x hx => ?_, ?_⟩
          · rw [hl6 x hx.1, hl5, hl4 x hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2, hl3, hl2, hl1]
          · unfold iterB; simp only [Expr.cost] at hk4 hk6 ⊢; omega
        · rw [ite_eq_right hc'] at hr
          refine wp_ite_g 0 (by simp [Expr.eval, BinOp.eval, h4.scap 2 (by decide), h4.cursor, hc'])
            (fun s5 hl5 hm5 hc5 => ?_)
          simp only [ne_eq, not_true_eq_false, ite_false]
          have hb5 : s5.loc "bud" = b := by rw [hl5, hb4]
          refine OrderMaintenance.Machine.wp_mono (fun s6 k6 ⟨hb6, hl6, hm6, hc6, hk6⟩ => ?_) (spendW_ok hb5 hb0)
          refine ⟨Or.inl ⟨om', n', b - 1, (h4.congr hm5 hc5).congr hm6 hc6, hb6, hr, hnext om' n' hcp hc'⟩,
            fun x hx => ?_, ?_⟩
          · rw [hl6 x hx.1, hl5, hl4 x hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2, hl3, hl2, hl1]
          · unfold iterB; simp only [Expr.cost] at hk4 hk6 ⊢; omega

/-! ### The loop -/

theorem LoopI.congr {R : OrderMaintenance} {p f : Nat} {s s' : State} (h : LoopI R p f s) (hl : s'.loc "bud" = s.loc "bud")
    (hm : s'.mem = s.mem) (hc : s'.cap = s.cap) : LoopI R p f s' := by
  rcases h with ⟨om, n, b, h, hb, hr, hS⟩ | ⟨hb, hW⟩
  · exact Or.inl ⟨om, n, b, h.congr hm hc, by rw [hl, hb], hr, hS⟩
  · exact Or.inr ⟨by rw [hl, hb], hW.congr hm hc⟩

/-- **The rebuild loop**: the machine ends holding Level F's result, in one slot or the other. -/
theorem loopW_ok {om : OrderMaintenance} {n : Core} {m : State} {p : Nat} (h : WEnc { om with nxt := some n } m p) {R : OrderMaintenance}
    (hr : rebuildLoop om n (om.KB + 1) om.KB = .ok R) (hS : RLSafe om n (om.KB + 1) om.KB) :
    wp (loopC p) (fun m' k => (WEnc R m' p ∨ WEnc R m' (1 - p)) ∧
      (∀ x, ItLoc x → x ≠ "it" → m'.loc x = m.loc x) ∧ k ≤ 20 + (om.KB + 1) * (1 + iterB)) m := by
  have hp := h.p2
  unfold loopC
  rw [OrderMaintenance.Machine.wp_seq]
  refine wp_assign_g om.KB (eval_load_lit (by rw [h.scap 7 (by decide)]; decide) h.kb) (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  refine OrderMaintenance.Machine.wp_loop (om.KB + 1)
    (fun k s => LoopI R p (om.KB + 1 - k) s ∧ ∀ x, ItLoc x → x ≠ "it" → s.loc x = m.loc x) iterB
    (by simp [Expr.eval, BinOp.eval, h1.scap 7 (by decide), h1.kb]) ⟨?_, fun x hx _ => ?_⟩ ?_ ?_
  · refine Or.inl ⟨om, n, om.KB, h1.bump _, ?_, by simpa using hr, by simpa using hS⟩
    simp [hl1, OrderMaintenance.Machine.State.upd]
  · simp [hl1, OrderMaintenance.Machine.State.upd, hx.1]
  · intro k hk s ⟨hI, hfr⟩
    have hI' : LoopI R p (om.KB - k + 1) (s.setLoc "it" k) := by
      have e : om.KB + 1 - k = om.KB - k + 1 := by omega
      rw [e] at hI
      exact hI.congr (by simp [OrderMaintenance.Machine.State.upd]) rfl rfl
    refine OrderMaintenance.Machine.wp_mono (fun s' k' ⟨hI2, hl2, hk2⟩ => ⟨⟨?_, fun x hx hit => ?_⟩, hk2⟩) (iterW_ok hp hI')
    · have e : om.KB + 1 - (k + 1) = om.KB - k := by omega
      rw [e]; exact hI2
    · rw [hl2 x hx]; simp [OrderMaintenance.Machine.State.upd, hit, hfr x hx hit]
  · intro s' c ⟨hI, hfr⟩ hc
    refine ⟨?_, hfr, ?_⟩
    · simp only [Nat.sub_self] at hI
      rcases hI with ⟨om', n', b, h', -, hr', -⟩ | ⟨-, hW⟩
      · left; cases hr'; exact h'
      · right; exact hW
    · simp only [Expr.cost] at hc ⊢; omega

/-! ### Starting a rebuild -/

/-- **A new `nxt`** in slot `1 - p`, with a zero handle map of room enough. -/
theorem WEnc.start {om : OrderMaintenance} {m m' : State} {p : Nat} (h : WEnc om m p) (hn : om.nxt = none) {n : Core}
    (hE : Enc (1 - p) (capsOf n.P) n m') (hS : ∀ b, ¬ InSlot (1 - p) b → b ≠ wIdx (1 - p) → Same b m m')
    (hcap : om.nextHandle + (om.cur.P.N - om.cur.count) + n.P.N ≤ m'.cap (wIdx (1 - p)))
    (hz : ∀ i, m'.mem (wIdx (1 - p)) i = 0) :
    WEnc { om with nxt := some n, nxtIdx := #[] } (m'.write (wa 1) 0 1) p := by
  have hp := h.p2
  have hp' : 1 - p < 2 := by omega
  have hw : ∀ k, k < 8 → Same (wa k) m m' := fun k hk => hS _ (wa_notSlot hp') (wa_ne_idx hk)
  have hip : Same (wIdx p) m m' := hS _ (wIdx_notSlot hp') (fun e => by
    have : (2010 + p : Nat) = 2010 + (1 - p) := e
    omega)
  have hW : ∀ b, b ≠ wa 1 → Same b m' (m'.write (wa 1) 0 1) := fun b hb =>
    ⟨by simp [State.write, hb], rfl⟩
  have hk : ∀ k, k < 8 → k ≠ 1 → (m'.write (wa 1) 0 1).mem (wa k) 0 = m.mem (wa k) 0 := fun k hk h1 => by
    rw [(hW _ (wa_ne h1)).1, (hw k hk).1]
  refine ⟨hp, fun k hk' => ?_, by rw [hk 0 (by decide) (by decide)]; exact h.par, ?_,
    by rw [hk 2 (by decide) (by decide)]; exact h.cursor, by rw [hk 3 (by decide) (by decide)]; exact h.cset,
    by rw [hk 4 (by decide) (by decide)]; exact h.live, by rw [hk 5 (by decide) (by decide)]; exact h.next,
    by rw [hk 6 (by decide) (by decide)]; exact h.reb, by rw [hk 7 (by decide) (by decide)]; exact h.kb,
    h.cur.of_same fun b hb => ?_, fun n2 hn2 => ?_, fun i hi => ?_, fun _ i hi => ?_, ?_, fun n2 hn2 => ?_⟩
  · show m'.cap (wa k) = 1
    rw [(hw k hk').2]; exact h.scap k hk'
  · simp [State.write, OrderMaintenance.Machine.State.upd, b2n]
  · have hb1 : b ≠ wa 1 := fun e => wa_notSlot hp (e ▸ hb)
    have hb2 : ¬ InSlot (1 - p) b := fun hb' => inSlot_disj (by omega) hb hb'
    have hb3 : b ≠ wIdx (1 - p) := fun e => wIdx_notSlot hp (e ▸ hb)
    exact (hS b hb2 hb3).trans (hW b hb1)
  · cases hn2
    exact hE.of_same fun b hb => hW b (fun e => wa_notSlot hp' (e ▸ hb))
  · have hi' : i < m.cap (wIdx p) := by rw [← hip.2]; exact hi
    rw [(hW _ (Ne.symm (wa_ne_idx (by decide)))).1, hip.1]; exact h.idxC i hi'
  · rw [(hW _ (Ne.symm (wa_ne_idx (by decide)))).1, hz]; simp [Array.getX]
  · show om.nextHandle + (om.cur.P.N - om.cur.count) ≤ m'.cap (wIdx p)
    rw [hip.2]; exact h.roomC
  · cases hn2
    show om.nextHandle + (om.cur.P.N - om.cur.count) + (n.P.N - n.count) ≤ m'.cap (wIdx (1 - p))
    omega

/-- The trigger: `count ≥ N/2`, or `N > minimumCapacity` and `live < N/8` (locals `cnt`, `nC`,
  `lv`). -/
def condE : Expr :=
  .bin .or (.bin .le (.bin .div (.var "nC") (.lit 2)) (.var "cnt"))
    (.bin .and (.bin .lt (.lit 64) (.var "nC")) (.bin .lt (.var "lv") (.bin .div (.var "nC") (.lit 8))))

/-- `live + mirrored` of the next capacity. -/
def naE (p : Nat) : Expr :=
  .bin .add (.var "lv") (.bin .add (.bin .div (.bin .add (.var "cnt") (.bin .add (.load (arrP p) (.lit 1)) (.lit 2)))
    (.bin .sub (.load (wa 7) (.lit 0)) (.lit 1))) (.lit 1))

/-- The next capacity, `4 · max na 16`. -/
def nNE : Expr := .bin .mul (.lit 4) (.bin .add (.var "na") (tsubE (.lit 16) (.var "na")))

/-- The capacity of the new handle map: `nextHandle + (N − count) + N'`. -/
def idxCapE (p : Nat) : Expr :=
  .bin .add (.bin .add (.load (wa 5) (.lit 0)) (tsubE (.load (arrP p) (.lit 0)) (.load (arrF p (.s .count)) (.lit 0))))
    (.var "nN")

/-- Start a rebuild if `cur` is half full or too few of its elements are live. -/
def startC (p : Nat) : Stmt :=
  .seq (.assign "cnt" (.load (arrF p (.s .count)) (.lit 0)))
  (.seq (.assign "nC" (.load (arrP p) (.lit 0)))
  (.seq (.assign "lv" (.load (wa 4) (.lit 0)))
  (.ite condE
    (.seq (.store (wa 3) (.lit 0) (.lit 0))
    (.seq (.store (wa 6) (.lit 0) (.bin .add (.load (wa 6) (.lit 0)) (.lit 1)))
    (.seq (.assign "na" (naE p))
    (.seq (.assign "nN" nNE)
    (.seq (newCoreS (1 - p))
    (.seq (.alloc (wIdx (1 - p)) (idxCapE p))
      (.store (wa 1) (.lit 0) (.lit 1))))))))
    .skip)))

/-- The locals a rebuild start may change. -/
def StLoc (x : Reg) : Prop := x ∉ pLocs ∧ x ≠ "cnt" ∧ x ≠ "nC" ∧ x ≠ "lv" ∧ x ≠ "na" ∧ x ≠ "nN"

/-- The state after a rebuild start. -/
def startOM (om : OrderMaintenance) (n : Core) : OrderMaintenance := { om with nxt := some n, nxtIdx := #[], cursorSet := false, rebuilds := om.rebuilds + 1 }

theorem newCore_true (P : Params) : newCore P true = .ok (prepStart P false) := by
  unfold newCore runCore; rw [initCore_lazy_eq]; rfl

theorem startW_ok {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hn : om.nxt = none) (hkb : 1 ≤ om.KB)
    {R : OrderMaintenance} (hr : om.rebuildStep proofParams = .ok R) :
    wp (startC p) (fun m' k => WEnc R m' p ∧ (∀ x, StLoc x → m'.loc x = m.loc x) ∧ k ≤ 3500) m := by
  have hp := h.p2
  have hp' : 1 - p < 2 := by omega
  unfold startC
  -- the three reads
  rw [OrderMaintenance.Machine.wp_seq]
  refine wp_assign_g om.cur.count (eval_load_lit (by rw [h.cur.cap]; simp [Fld.cap])
    (by rw [h.cur.mem _ _ (by simp [Fld.cap])]; rfl)) (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  rw [OrderMaintenance.Machine.wp_seq]
  refine wp_assign_g om.cur.P.N (eval_load_lit (by rw [h1.cur.pcap]; decide) (h1.cur.pmem .N))
    (fun s2 hl2 hm2 hc2 => ?_)
  have h2 := h1.congr hm2 hc2
  rw [OrderMaintenance.Machine.wp_seq]
  refine wp_assign_g om.live (eval_load_lit (by rw [h2.scap 4 (by decide)]; decide) h2.live)
    (fun s3 hl3 hm3 hc3 => ?_)
  have h3 := h2.congr hm3 hc3
  have hcnt3 : s3.loc "cnt" = om.cur.count := by rw [hl3, hl2, hl1]; simp [OrderMaintenance.Machine.State.upd]
  have hnC3 : s3.loc "nC" = om.cur.P.N := by rw [hl3, hl2]; simp [OrderMaintenance.Machine.State.upd]
  have hlv3 : s3.loc "lv" = om.live := by rw [hl3]; simp [OrderMaintenance.Machine.State.upd]
  have hl3' : ∀ x, x ≠ "cnt" → x ≠ "nC" → x ≠ "lv" → s3.loc x = m.loc x := fun x a b c => by
    rw [hl3, hl2, hl1]; simp [OrderMaintenance.Machine.State.upd, a, b, c]
  -- the trigger
  by_cases hc : (decide (om.cur.count ≥ om.cur.P.N / 2) || (decide (om.cur.P.N > minimumCapacity) && decide (om.live < om.cur.P.N / 8))) = true
  · have hR : R = startOM om (prepStart (proofParams om.nextCapacity) false) := by
      have e : om.rebuildStep proofParams = .ok (startOM om (prepStart (proofParams om.nextCapacity) false)) := by
        unfold OrderMaintenance.rebuildStep; rw [hn]
        simp only [hc, ite_true, newCore_true, bind, Except.bind, pure, Except.pure]; rfl
      rw [e] at hr; injection hr with hr; exact hr.symm
    subst hR
    have hc' : om.cur.P.N / 2 ≤ om.cur.count ∨ (64 < om.cur.P.N ∧ om.live < om.cur.P.N / 8) := by
      simpa [minimumCapacity] using hc
    refine wp_ite_g 1 (by
      simp only [condE, Expr.eval, hcnt3, hnC3, hlv3, Option.bind_some, BinOp.eval]
      rcases hc' with h' | ⟨h1', h2'⟩
      · simp [h']
      · simp [h1', h2']) (fun s4 hl4 hm4 hc4 => ?_)
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ite_true]
    have h4 := h3.congr hm4 hc4
    -- the scalar writes
    rw [OrderMaintenance.Machine.wp_seq]
    refine wp_store_g 0 0 rfl rfl (by rw [h4.scap 3 (by decide)]; decide) (fun s5 hl5 hm5 hc5 => ?_)
    have h5 := (h4.writeCset false).congr hm5 hc5
    rw [OrderMaintenance.Machine.wp_seq]
    refine wp_store_g 0 (om.rebuilds + 1) rfl
      (by simp [Expr.eval, BinOp.eval, h5.scap 6 (by decide),
        h5.reb]) (by rw [h5.scap 6 (by decide)]; decide)
      (fun s6 hl6 hm6 hc6 => ?_)
    have h6 := (h5.writeReb (om.rebuilds + 1)).congr hm6 hc6
    have hl6' : s6.loc = s3.loc := by rw [hl6, hl5, hl4]
    -- the next capacity
    rw [OrderMaintenance.Machine.wp_seq]
    set na := om.live + ((om.cur.count + (om.cur.P.L + 2)) / (om.KB - 1) + 1)
    refine wp_assign_g na (by
      have hL : s6.mem (arrP p) 1 = om.cur.P.L := h6.cur.pmem .L
      have hK : s6.mem (wa 7) 0 = om.KB := h6.kb
      simp [naE, Expr.eval, hL, hK, BinOp.eval, hl6', hcnt3, hlv3, h6.cur.pcap,
        h6.scap 7 (by decide : 7 < 8), hkb]
      omega) (fun s7 hl7 hm7 hc7 => ?_)
    rw [OrderMaintenance.Machine.wp_seq]
    have hcapv : 4 * (na + (16 - na)) = om.nextCapacity := by
      show 4 * (na + (16 - na)) = 4 * max na 16
      rw [Nat.max_def]; split <;> omega
    refine wp_assign_g om.nextCapacity (by
      have : (tsubE (.lit 16) (.var "na")).eval s7 = some (16 - na) :=
        tsubE_eval rfl (by simp [Expr.eval, hl7, OrderMaintenance.Machine.State.upd])
      simp only [nNE, Expr.eval, this, Option.bind_some, BinOp.eval, hl7,
        OrderMaintenance.Machine.State.upd, ite_true]
      rw [hcapv]) (fun s8 hl8 hm8 hc8 => ?_)
    have h8 := (h6.congr hm7 hc7).congr hm8 hc8
    have hN8 : s8.loc "nN" = om.nextCapacity := by rw [hl8]; simp [OrderMaintenance.Machine.State.upd]
    have hpos : 0 < om.nextCapacity := by rw [← hcapv]; omega
    -- the new core
    rw [OrderMaintenance.Machine.wp_seq]
    refine OrderMaintenance.Machine.wp_mono (fun s9 k9 ⟨hE9, hS9, hN9, hl9, hk9⟩ => ?_) (OrderMaintenance.Impl.newCore_ok (1 - p) hN8 hpos)
    set P' := proofParams om.nextCapacity
    have hw9 : ∀ k, Same (wa k) s8 s9 := fun k => hS9 _ (wa_notSlot hp')
    have hsl9 : ∀ b, InSlot p b → Same b s8 s9 := fun b hb => hS9 b (fun hb' => inSlot_disj (by omega) hb hb')
    have hcur9 : Enc p (capsOf om.cur.P) om.cur s9 := h8.cur.of_same hsl9
    -- the handle map
    rw [OrderMaintenance.Machine.wp_seq, OrderMaintenance.Machine.wp_alloc]
    have hcntv : (Expr.load (arrF p (.s .count)) (.lit 0)).eval s9 = some om.cur.count :=
      eval_load_lit (by rw [hcur9.cap]; simp [Fld.cap]) (by rw [hcur9.mem _ _ (by simp [Fld.cap])]; rfl)
    have hNv : (Expr.load (arrP p) (.lit 0)).eval s9 = some om.cur.P.N :=
      eval_load_lit (by rw [hcur9.pcap]; decide) (hcur9.pmem .N)
    have hhv : (Expr.load (wa 5) (.lit 0)).eval s9 = some om.nextHandle :=
      eval_load_lit (by rw [(hw9 5).2, h8.scap 5 (by decide)]; decide) (by rw [(hw9 5).1]; exact h8.next)
    refine ⟨om.nextHandle + (om.cur.P.N - om.cur.count) + om.nextCapacity, by
      have ht := tsubE_eval hNv hcntv
      unfold idxCapE
      rw [eval_bin (eval_bin hhv ht) (show (Expr.var "nN").eval s9 = some om.nextCapacity by simp [Expr.eval, hN9])]
      rfl, ?_⟩
    set s10 := (s9.bump ((idxCapE p).maxv s9)).alloc (wIdx (1 - p)) (om.nextHandle + (om.cur.P.N - om.cur.count) + om.nextCapacity)
    have hne : ∀ b, b ≠ wIdx (1 - p) → Same b s9 s10 := fun b hb => ⟨by simp [s10, State.alloc, hb],
      by simp [s10, State.alloc, OrderMaintenance.Machine.State.upd, hb]⟩
    refine wp_store_g 0 1 rfl rfl (by
      rw [(hne _ (wa_ne_idx (by decide))).2, (hw9 1).2,
        h8.scap 1 (by decide)]; decide) (fun s11 hl11 hm11 hc11 => ?_)
    have hW := WEnc.start (n := prepStart P' false) h8 (by simpa using hn)
      (m' := s10) (hE9.of_same fun b hb => hne b (fun e => wIdx_notSlot hp' (e ▸ hb)))
      (fun b hb1 hb2 => (hS9 b hb1).trans (hne b hb2))
      (by simp [s10, State.alloc,
        OrderMaintenance.Machine.State.upd]; rfl) (fun i => by simp [s10, State.alloc])
    refine ⟨hW.congr hm11 (by rw [hc11]; rfl), fun x hx => ?_, ?_⟩
    · obtain ⟨x0, x1, x2, x3, x4, x5⟩ := hx
      rw [hl11]; show s9.loc x = m.loc x
      rw [hl9 x x0, hl8,
        hl7]; simp only [OrderMaintenance.Machine.State.upd, ite_eq_right x5, ite_eq_right x4]
      rw [hl6', hl3' x x1 x2 x3]
    · simp only [Expr.cost, idxCapE, naE, nNE, condE, tsubE] at hk9 ⊢; omega
  · have hR : R = om := by
      have e : om.rebuildStep proofParams = .ok om := by
        unfold OrderMaintenance.rebuildStep; rw [hn]
        simp only [hc, Bool.false_eq_true, ite_false, pure, Except.pure]
      rw [e] at hr; injection hr with hr; exact hr.symm
    subst R
    have hc' : ¬ (om.cur.P.N / 2 ≤ om.cur.count ∨ (64 < om.cur.P.N ∧ om.live < om.cur.P.N / 8)) := by
      simpa [minimumCapacity] using hc
    push Not at hc'
    refine wp_ite_g 0 (by
      simp only [condE, Expr.eval, hcnt3, hnC3, hlv3, Option.bind_some, BinOp.eval]
      by_cases h64 : 64 < om.cur.P.N
      · simp [hc'.1, Nat.not_lt.mpr (hc'.2 h64)]
      · simp [hc'.1, h64]) (fun s4 hl4 hm4 hc4 => ?_)
    simp only [ne_eq, not_true_eq_false, ite_false]
    refine wp_skip_g ⟨h3.congr hm4 hc4, fun x hx => by rw [hl4, hl3' x hx.2.1 hx.2.2.1 hx.2.2.2.1], ?_⟩
    simp only [Expr.cost, condE]; omega

end OrderMaintenance.Impl

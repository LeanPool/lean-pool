/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakParams


/-!
# Theorem W, option (A), stage A3: the peak of the wrapper's machine code

The machine code of `WrapM.lean` (order queries, deletion and insertion into `cur` and `nxt`,
the live counter), re-run with the budget `BW K KH = 2^(2K+4) + 2^KH`. The statements of
`WrapM.lean` are unchanged; each peak theorem here takes the hypotheses of its `wp` theorem plus
the value bounds of the wrapper state:

`WK K KH T om`: option (B)'s `WBW T om om.nxt` (each core bounded at its own word size, the index
arrays, the cursor, every handle and counter at most `T`), both cores of the proof parameters with
`wK ≤ K`, `K_B < 2^K`, and `T < 2^KH`. It gives `CoreK` for both cores (`WK.curK`, `WK.nxtK`), the
hypotheses of the A2 wrappers at every core call (`order_peak`, `markDead_peak`,
`insertAfter_peak`).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

variable {K KH T : Nat}

/-! ### The value bounds of a wrapper state -/

/-- **The value bounds of a wrapper state** at word size `K`, handle width `KH`, counter bound
`T`. -/
structure WK (K KH T : Nat) (om : OrderMaintenance) : Prop where
  wbw : WBW T om om.nxt
  cpmk : om.cur.P = proofParams om.cur.P.N
  cwk : wK om.cur.P ≤ K
  npmk : ∀ n, om.nxt = some n → n.P = proofParams n.P.N
  nwk : ∀ n, om.nxt = some n → wK n.P ≤ K
  kb : om.KB < 2 ^ K
  hT : T < 2 ^ KH

theorem WK.curK {om : OrderMaintenance} (h : WK K KH T om) : CoreK K KH om.cur :=
  ⟨h.cpmk, h.cwk, h.wbw.cur.mono h.cwk, fun i => lt_of_le_of_lt (le_trans (h.wbw.hcur i)
    h.wbw.hnd) h.hT⟩

theorem WK.nxtK {om : OrderMaintenance} (h : WK K KH T om) {n : Core} (hn : om.nxt = some n) :
  CoreK K KH n :=
  ⟨h.npmk n hn, h.nwk n hn, (h.wbw.nxt n hn).1.mono (h.nwk n hn),
    fun i => lt_of_le_of_lt (le_trans ((h.wbw.nxt n hn).2.2 i) h.wbw.hnd) h.hT⟩

theorem WK.k512 {om : OrderMaintenance} (h : WK K KH T om) : 512 ≤ K := h.curK.k8

theorem WK.curIdx {om : OrderMaintenance} (h : WK K KH T om) (i : Nat) : om.curIdx.getX i < 2 ^ K :=
  lt_mono h.cwk (h.wbw.curIdx i)

theorem WK.nxtIdx {om : OrderMaintenance} (h : WK K KH T om) {n : Core} (hn : om.nxt = some n)
  (i : Nat) :
    om.nxtIdx.getX i < 2 ^ K :=
  lt_mono (h.nwk n hn) ((h.wbw.nxt n hn).2.1 i)

theorem WK.cursor {om : OrderMaintenance} (h : WK K KH T om) : om.cursor < 2 ^ K := lt_mono
  h.cwk h.wbw.cursor

/-- The facts the budget side conditions use (`unfold BW; omega`). -/
theorem WK.pack {om : OrderMaintenance} (h : WK K KH T om) :
    16 * 2 ^ K ≤ 2 ^ (2 * K + 4) ∧ T < 2 ^ KH ∧ 512 ≤ K ∧ om.live ≤ T ∧ om.nextHandle ≤ T ∧
      om.rebuilds ≤ T ∧ om.KB < 2 ^ K ∧ om.cursor < 2 ^ K :=
  ⟨pow_BW K, h.hT, h.k512, h.wbw.live, h.wbw.hnd, h.wbw.reb, h.kb, h.cursor⟩

/-- A core field read through the encoding is within the budget. -/
theorem CoreK.fld_lt {c : Core} (hc : CoreK K KH c) (f : Fld) (j : Nat) :
    f.get c j < 2 ^ K + 2 ^ KH := by
  have := fld_of_WB (KH := KH) hc.wb (by
    have := hc.k8
    omega) hc.hh f j
  have := Nat.two_pow_pos K
  have := Nat.two_pow_pos KH
  cases f with
  | e k => cases k <;> simp only [Fld.wd] at this <;> omega
  | _ => simp only [Fld.wd] at this; omega

/-! ### The parity test -/

theorem parE_maxv {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) : parE.maxv m
  ≤ 1 := by
  have := h.p2
  simp [parE, Expr.eval, h.scap 0 (by omega), h.par, BinOp.eval]
  split <;> omega

theorem byPar_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) {c : Nat →
  Stmt} {B : Nat} (hB : 1 ≤ B)
    (hc : wpB B (c p) TT (m.bump (parE.maxv m))) : wpB B (byPar c) TT m := by
  unfold byPar
  have hev : parE.eval m = some (if p = 0 then 1 else 0) := by
    simp [parE, Expr.eval, h.scap 0 (by
      have := h.p2
      omega), h.par, BinOp.eval]
  refine Machine.wpB_ite _ hev (le_trans (parE_maxv h) hB) ?_
  have := h.p2
  by_cases hp : p = 0
  · subst hp; simpa using wpB_T hc
  · have : p = 1 := by omega
    subst this; simpa using wpB_T hc

/-! ### Order queries -/

theorem orderC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K KH
  T om) {x y : Nat}
    (hx : m.loc "x" = x) (hy : m.loc "y" = y) (hxT : x ≤ T) (hyT : y ≤ T)
    (hxc : x < m.cap (wIdx p)) (hyc : y < m.cap (wIdx p)) {L : List Nat} (hS : InService om.cur L)
    (hxL : om.curIdx.getX x ∈ L) (hyL : om.curIdx.getX y ∈ L) {b : Bool} {s' : Core}
    (hr : (OrderMaintenance.Model.order (om.curIdx.getX x) (om.curIdx.getX y)).run om.cur = .ok
      b s') :
    wpB (BW K KH) (orderC p) TT m := by
  obtain ⟨hb1, hb2, -⟩ := hW.pack
  have hcK := hW.curK
  have hix := hW.curIdx x
  have hiy := hW.curIdx y
  obtain ⟨L', c, he, -, -⟩ := orderAgreeM hS.ok.cost  hxL hyL (State.setLocs (fun _ => 0)
    ["x", "y"]
    [om.curIdx.getX x, om.curIdx.getX y]) (by simp [State.setLocs, State.upd])
    (by simp [State.setLocs, State.upd]) (capsOf_ok _) hS.ok.cnt hS.mc hr
  unfold orderC
  refine wpB_assign_seq (om.curIdx.getX x) (by simp [Expr.eval, hx, hxc, h.idxC x hxc])
    (by
      simp only [Expr.maxv, hx, Expr.eval, Option.bind_some, hxc, ↓reduceIte, h.idxC x hxc,
          Option.getD_some, sup_le_iff]
      proveBudget K KH) (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  have hy1 : s1.loc "y" = y := by rw [hl1]; simp [State.upd, hy]
  have hyc1 : y < s1.cap (wIdx p) := by rw [hc1]; exact hyc
  refine wpB_assign_seq (om.curIdx.getX y) (by simp [Expr.eval, hy1, hyc1, h1.idxC y hyc1])
    (by
      simp only [Expr.maxv, hy1, Expr.eval, Option.bind_some, hyc1, ↓reduceIte, h1.idxC y hyc1,
          Option.getD_some, sup_le_iff]
      proveBudget K KH) (fun s2 hl2 hm2 hc2 => ?_)
  have h2 := h1.congr hm2 hc2
  rw [compile_κ₀ p om.cur.P]
  have hev : Machine.evalList s2 [.var "xi", .var "yi"] = some [om.curIdx.getX x, om.curIdx.getX
    y] := by
    simp [Machine.evalList, Expr.eval, hl2, hl1, State.upd]
  refine wpB_coreCall h2.cur hev he ?_ (pk_BW (order_peak hcK.caps (by
    have := hcK.k8
    omega) h2.cur hcK.wb
    hcK.hh hcK.room (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hix, hiy⟩) he)) (fun _ _ _ _ => trivial)
  simp only [Machine.maxvList, List.map_cons, Expr.maxv, hl2, State.upd, String.reduceEq,
      ↓reduceIte, hl1, List.map_nil, List.foldr_cons, List.foldr_nil, zero_le, sup_of_le_left,
      sup_le_iff]; proveBudget K KH

/-! ### Deletion -/

theorem curDelC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K KH
  T om) {x : Nat}
    (hx : m.loc "x" = x) (hxT : x ≤ T) (hxc : x < m.cap (wIdx p)) {L : List Nat} (hS : InService
      om.cur L)
    (hxL : om.curIdx.getX x ∈ L) : wpB (BW K KH) (curDelC p) TT m := by
  obtain ⟨hb1, hb2, -⟩ := hW.pack
  have hcK := hW.curK
  have hix := hW.curIdx x
  obtain ⟨s', -, ⟨L', c, he, -⟩, -⟩ := markDeadAgreeM hS.ok.cost rfl hxL
    (State.setLocs (fun _ => 0) ["x"] [om.curIdx.getX x]) (by simp [State.setLocs, State.upd])
      (capsOf_ok _)
    hS.ok.cnt hS.mc
  unfold curDelC
  refine wpB_assign_seq (om.curIdx.getX x) (by simp [Expr.eval, hx, hxc, h.idxC x hxc])
    (by
      simp only [Expr.maxv, hx, Expr.eval, Option.bind_some, hxc, ↓reduceIte, h.idxC x hxc,
          Option.getD_some, sup_le_iff]
      proveBudget K KH) (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  rw [compile_κ₀ p om.cur.P]
  have hev : Machine.evalList s1 [.var "xi"] = some [om.curIdx.getX x] := by
    simp [Machine.evalList, Expr.eval, hl1, State.upd]
  refine wpB_seq_T (wpB_coreCall (Q := fun m2 _ => m2.loc "x" = x ∧ m2.cap (wIdx p) = m.cap
    (wIdx p))
    h1.cur hev he ?_ (pk_BW (markDead_peak hcK.caps (by
      have := hcK.k8
      omega) h1.cur hcK.wb hcK.hh hcK.room
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      exact hix) he)) (fun m2 _ hS2 hL2 => ⟨?_, ?_⟩)) (fun m2 _ ⟨hx2, hc2⟩ => ?_)
  · simp only [Machine.maxvList, List.map_cons, Expr.maxv, hl1, State.upd, ↓reduceIte,
      List.map_nil, List.foldr_cons, List.foldr_nil, zero_le, sup_of_le_left]; proveBudget K KH
  · rw [hL2]; simp [State.setLocs, hl1, State.upd, hx]
  · rw [(hS2 _ (wIdx_notSlot h.p2)).2, hc1]
  · exact wpB_T (Machine.wpB_store_g (Q := TT) x 0 (by simp [Expr.eval, hx2]) rfl (by
    rw [hc2]
    exact hxc)
      (by
        simp only [Expr.maxv, hx2]
        proveBudget K KH) (by simp) (fun _ _ _ _ => trivial))

theorem mirrorDelC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K
  KH T om) {x : Nat}
    (hx : m.loc "x" = x) (hxT : x ≤ T) (hxc : om.nxt.isSome → x < m.cap (wIdx (1 - p)))
    (hN : ∀ n, om.nxt = some n → om.nxtIdx.getX x ≠ 0 → DelOK n (om.nxtIdx.getX x)) :
    wpB (BW K KH) (mirrorDelC p) TT m := by
  obtain ⟨hb1, hb2, -⟩ := hW.pack
  have hp := h.p2
  unfold mirrorDelC
  have hm1 : (Expr.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)).maxv m ≤ BW K KH := by
    have := h.nxtOn
    simp only [Expr.maxv, Expr.eval, h.scap 1 (by decide), Order.lt_one_iff, Option.bind_some,
        ↓reduceIte, this, Option.getD_some, zero_le, sup_of_le_right, sup_of_le_left,
        BinOp.eval, sup_le_iff]
    unfold b2n BW; split <;> split <;> omega
  cases hn : om.nxt with
  | none =>
    refine wpB_ite_T 1 (by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n]) hm1
      (fun _ _ _ _ => by simpa using wpB_skip_T)
  | some n =>
    refine wpB_ite_T 0 (by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n]) hm1
      (fun s1 hl1 hm1' hc1 => ?_)
    simp only [ne_eq, not_true_eq_false, ite_false]
    have h1 := h.congr hm1' hc1
    have hxc' := hxc (by
      rw [hn]
      rfl)
    have hxc1 : x < s1.cap (wIdx (1 - p)) := by rw [hc1]; exact hxc'
    have hx1 : s1.loc "x" = x := by rw [hl1, hx]
    have hix := hW.nxtIdx hn x
    have hnK := hW.nxtK hn
    refine wpB_assign_seq (om.nxtIdx.getX x) (by simp [Expr.eval, hx1, hxc1, h1.idxN (by
      rw [hn]
      rfl) x hxc1])
      (by simp only [Expr.maxv, hx1, Expr.eval, Option.bind_some, hxc1, ↓reduceIte,
          h1.idxN (by rw [hn]; rfl) x hxc1, Option.getD_some, sup_le_iff]; proveBudget K KH)
      (fun s2 hl2 hm2 hc2 => ?_)
    have h2 := h1.congr hm2 hc2
    have hxn2 : s2.loc "xn" = om.nxtIdx.getX x := by rw [hl2]; simp [State.upd]
    have hmx : (Expr.bin .eq (.var "xn") (.lit 0)).maxv s2 ≤ BW K KH := by
      simp only [Expr.maxv, hxn2, zero_le, sup_of_le_left, Expr.eval, BinOp.eval,
          Option.bind_some, Option.getD_some, sup_le_iff]; unfold BW; split <;> omega
    by_cases h0 : om.nxtIdx.getX x = 0
    · refine wpB_ite_T 1 (by simp [Expr.eval, hxn2, h0, BinOp.eval]) hmx (fun _ _ _ _ => by
        simpa using wpB_skip_T)
    · refine wpB_ite_T 0 (by simp [Expr.eval, hxn2, h0, BinOp.eval]) hmx (fun s3 hl3 hm3 hc3 => ?_)
      simp only [ne_eq, not_true_eq_false, ite_false]
      have h3 := h2.congr hm3 hc3
      obtain ⟨P, nn, R, L, hC, hP, hxL, hcntL, hM⟩ := hN n hn h0
      obtain ⟨n', -, ⟨L', c, he, -⟩, -⟩ := markDeadAgreeM hC hP hxL
        (State.setLocs (fun _ => 0) ["x"] [om.nxtIdx.getX x]) (by
          simp [State.setLocs, State.upd]) (capsOf_ok P)
        hcntL hM
      subst hP
      rw [compile_κ₀ (1 - p) n.P]
      have hev : Machine.evalList s3 [.var "xn"] = some [om.nxtIdx.getX x] := by
        simp [Machine.evalList, Expr.eval, hl3, hxn2]
      have hnE := h3.nxt n hn
      refine wpB_seq_T (wpB_coreCall (Q := fun m2 _ => m2.loc "x" = x ∧ m2.cap (wIdx (1 - p)) =
        m.cap (wIdx (1 - p)))
        hnE hev he ?_ (pk_BW (markDead_peak hnK.caps (by
          have := hnK.k8
          omega) hnE hnK.wb hnK.hh hnK.room
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
          exact hix) he)) (fun m2 _ hS2 hL2 => ⟨?_, ?_⟩)) (fun m2 _ ⟨hx2, hc2'⟩ => ?_)
      · simp only [Machine.maxvList, List.map_cons, Expr.maxv, hl3, hxn2, List.map_nil,
          List.foldr_cons, List.foldr_nil, zero_le, sup_of_le_left]; proveBudget K KH
      · rw [hL2]; simp [State.setLocs, hl3, hl2, State.upd, hx1]
      · rw [(hS2 _ (wIdx_notSlot (by omega))).2, hc3, hc2, hc1]
      · exact wpB_T (Machine.wpB_store_g (Q := TT) x 0 (by simp [Expr.eval, hx2]) rfl
          (by
            rw [hc2']
            exact hxc') (by
            simp only [Expr.maxv, hx2]
            proveBudget K KH) (by simp)
          (fun _ _ _ _ => trivial))

/-! ### The live counter -/

theorem liveDecC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K
  KH T om) :
    wpB (BW K KH) liveDecC TT m := by
  obtain ⟨hb1, hb2, -, hlv, -⟩ := hW.pack
  refine wpB_T (Machine.wpB_store_g (Q := TT) 0 (om.live - 1) rfl
    (tsubE_eval (eval_load_lit (by rw [h.scap 4 (by decide)]; decide) h.live) rfl)
    (by rw [h.scap 4 (by decide)]; decide) (by simp) ?_ (fun _ _ _ _ => trivial))
  simp only [tsubE, Expr.maxv.eq_4, Expr.maxv, Expr.eval, h.scap 4 (by decide), Order.lt_one_iff,
      Option.bind_some, ↓reduceIte, h.live, Option.getD_some, zero_le, sup_of_le_right,
      BinOp.eval, Nat.max_assoc, le_max_iff, Std.le_refl, true_or, or_true, mul_ite, mul_one,
      mul_zero, sup_of_le_left, sup_le_iff]
  unfold BW; split <;> simp <;> omega

theorem liveIncC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K
  KH T om)
    (hlv : om.live + 1 ≤ 2 ^ KH) : wpB (BW K KH) liveIncC TT m := by
  obtain ⟨hb1, hb2, -⟩ := hW.pack
  refine wpB_T (Machine.wpB_store_g (Q := TT) 0 (om.live + 1) rfl
    (by simp [Expr.eval, BinOp.eval, h.scap 4 (by decide),
      h.live]) (by rw [h.scap 4 (by decide)]; decide)
    (by simp) ?_ (fun _ _ _ _ => trivial))
  simp only [Expr.maxv, Expr.eval, h.scap 4 (by decide), Order.lt_one_iff, Option.bind_some,
      ↓reduceIte, h.live, Option.getD_some, zero_le, sup_of_le_right, BinOp.eval, sup_le_iff,
      le_add_iff_nonneg_right, le_add_iff_nonneg_left, and_self, Order.add_one_le_iff]
  unfold BW; omega

/-! ### Insertion into `cur` -/

theorem curInsC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K KH
  T om) {hx : Option Nat}
    (hhx : m.loc "hx" = b2n hx.isSome) (hxx : ∀ x, hx = some x → m.loc "x" = x ∧ x < m.cap (wIdx
      p) ∧ x ≤ T)
    {L : List Nat} (hS : InService om.cur L) (hxL : insAnchor om hx ∈ L) : wpB (BW K KH)
      (curInsC p) TT m := by
  obtain ⟨hb1, hb2, -, -, hnh, -⟩ := hW.pack
  have hp := h.p2
  have hcK := hW.curK
  have hEs : om.cur.E.size < 2 ^ K := lt_mono hW.cwk hS.Esize_lt
  obtain ⟨c', -, ⟨L', c, he, hyL', -⟩, -⟩ := hS.insert hxL om.nextHandle
    (State.setLocs (fun _ => 0) ["x", "h"] [insAnchor om hx, om.nextHandle])
    (by simp [State.setLocs, State.upd]) (by simp [State.setLocs, State.upd])
  have hroom := h.roomC
  have hrm := hS.room
  unfold curInsC
  refine wpB_assign_seq om.nextHandle (by simp [Expr.eval, h.scap 5 (by decide), h.next])
    (by
      simp only [Expr.maxv, Expr.eval, h.scap 5 (by decide), Order.lt_one_iff,
        Option.bind_some, ↓reduceIte, h.next, Option.getD_some, zero_le, sup_of_le_right]
      proveBudget K KH) (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  have hhx1 : s1.loc "hx" = b2n hx.isSome := by rw [hl1]; simp [State.upd, hhx]
  have hhy1 : s1.loc "hy" = om.nextHandle := by rw [hl1]; simp [State.upd]
  have hmx : (Expr.bin .eq (.var "hx") (.lit 0)).maxv s1 ≤ BW K KH := by
    simp only [Expr.maxv, hhx1, zero_le, sup_of_le_left, Expr.eval, BinOp.eval, Option.bind_some,
        Option.getD_some, sup_le_iff]; unfold b2n BW; split <;> split <;> omega
  refine wpB_seq_T (Qc := fun s2 _ => s2.loc "xi" = insAnchor om hx ∧ s2.loc "hy" = om.nextHandle ∧
    s2.mem = s1.mem ∧ s2.cap = s1.cap) ?_ (fun s2 _ ⟨hxi, hhy, hm2, hc2⟩ => ?_)
  · rw [Machine.wpB]
    refine Machine.wpB_ite (if b2n hx.isSome = 0 then 1 else 0) (by
      simp [Expr.eval, BinOp.eval, hhx1]) hmx ?_
    cases hx with
    | none =>
      have hc0 := h1.cur.cap (.s .head)
      have hm0 := h1.cur.mem (.s .head) 0 (by
        rw [Fld.cap]
        omega)
      have hv := hcK.wb.scalars.2.1
      simp only [Option.isSome_none, b2n, Bool.false_eq_true, ↓reduceIte, ne_eq, one_ne_zero,
        not_false_eq_true]
      refine Machine.wpB_assign_g om.cur.head (by
        simp [Expr.eval, hc0, Fld.cap, hm0]
        rfl)
        (by
          simp only [Expr.maxv, Expr.eval, State.bump, zero_le, sup_of_le_left, BinOp.eval,
              Option.bind_some, Option.getD_some, hc0, Fld.cap, Order.lt_one_iff,
              ↓reduceIte, hm0, Fld.get, SF.get, sup_of_le_right]
          proveBudget K KH)
        (fun s' hl hm hc => ⟨by rw [hl]; simp [State.upd, insAnchor], by rw [hl]; simp
          [State.upd, hhy1],
          by rw [hm]; rfl, by rw [hc]; rfl⟩)
    | some x =>
      obtain ⟨hxl, hxc, hxT⟩ := hxx x rfl
      have hx1 : s1.loc "x" = x := by rw [hl1]; simp [State.upd, hxl]
      have hxc1 : x < s1.cap (wIdx p) := by rw [hc1]; exact hxc
      have hix := hW.curIdx x
      simp only [Option.isSome_some, b2n, ↓reduceIte, one_ne_zero, ne_eq, not_true_eq_false]
      refine Machine.wpB_assign_g (om.curIdx.getX x) (by
        simp [Expr.eval, hx1, hxc1, h1.idxC x hxc1])
        (by
          simp only [Expr.maxv, State.bump, zero_le, sup_of_le_left, Expr.eval, BinOp.eval,
              Option.bind_some, Option.getD_some, hx1, hxc1, ↓reduceIte,
              h1.idxC x hxc1, sup_le_iff]
          proveBudget K KH)
        (fun s' hl hm hc => ⟨by rw [hl]; simp [State.upd, insAnchor], by rw [hl]; simp
          [State.upd, hhy1],
          by rw [hm]; rfl, by rw [hc]; rfl⟩)
  have h2 := h1.congr hm2 hc2
  have hev : Machine.evalList s2 [.var "xi", .var "hy"] = some [insAnchor om hx, om.nextHandle]
    := by
    simp [Machine.evalList, Expr.eval, hxi, hhy]
  have hxi' : insAnchor om hx < 2 ^ K := by
    obtain ⟨A, hI, hel⟩ := hS.ok.cost.low.inv
    have := ((hI.eAlloc _).mp (hel ▸ hxL)).2
    omega
  rw [compile_κ₀ p om.cur.P]
  refine wpB_seq_T (wpB_coreCall (Q := fun m3 _ => m3.loc "hy" = om.nextHandle ∧ m3.loc "y" =
    om.cur.E.size ∧
      m3.cap (wa 5) = 1 ∧ m3.cap (wIdx p) = m.cap (wIdx p)) h2.cur hev he ?_
    (pk_BW (insertAfter_peak hcK.caps (by
      have := hcK.k8
      omega) h2.cur hcK.wb hcK.hh hcK.room hS hxL hcK.wk
      (by omega) he)) (fun m3 _ hS3 hL3 => ⟨?_, ?_, ?_, ?_⟩)) (fun m3 _ ⟨hy3, hyy3, hc5, hci⟩ => ?_)
  · simp only [Machine.maxvList, List.map_cons, Expr.maxv, hxi, hhy, List.map_nil,
      List.foldr_cons, List.foldr_nil, zero_le, sup_of_le_left, sup_le_iff]; proveBudget K KH
  · rw [hL3]; simp [State.setLocs, State.upd, hhy]
  · rw [hL3]; simp [State.setLocs, State.upd, hyL']
  · rw [(hS3 _ (wa_notSlot hp)).2, hc2, hc1]; exact h.scap 5 (by decide)
  · rw [(hS3 _ (wIdx_notSlot hp)).2, hc2, hc1]
  have hhc : om.nextHandle < m.cap (wIdx p) := by omega
  refine wpB_store_seq 0 (om.nextHandle + 1) rfl (by simp [Expr.eval, BinOp.eval, hy3]) (by
    rw [hc5]
    decide)
    (by simp) (by
      simp only [Expr.maxv, hy3, Expr.eval, BinOp.eval, Option.bind_some, Option.getD_some,
          sup_le_iff, le_add_iff_nonneg_right, zero_le, le_add_iff_nonneg_left, and_self,
          sup_of_le_right, Order.add_one_le_iff]
      proveBudget K KH) (fun s4 hl4 hm4 hc4 => ?_)
  exact wpB_T (Machine.wpB_store_g (Q := TT) om.nextHandle om.cur.E.size (by
    simp [Expr.eval, hl4, hy3])
    (by
      simp [Expr.eval, hl4, hyy3]) (by
        rw [hc4, hci]
        exact hhc) (by
        simp only [Expr.maxv, hl4, hy3]
        proveBudget K KH)
    (by
      simp only [Expr.maxv, hl4, hyy3]
      proveBudget K KH) (fun _ _ _ _ => trivial))

/-! ### Insertion into `nxt` -/

theorem nxtInsC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K KH
  T om) {n : Core}
    (hn : om.nxt = some n) {B : List Nat} (hS : InService n B) {xn hh : Nat} (hxn : xn ∈ B)
    (hlx : m.loc "xn" = xn) (hlh : m.loc "hh" = hh) (hhc : hh < m.cap (wIdx (1 - p))) (hhT : hh
      ≤ T) :
    wpB (BW K KH) (nxtInsC p) TT m := by
  obtain ⟨hb1, hb2, -⟩ := hW.pack
  have hp := h.p2
  have hnK := hW.nxtK hn
  have hEs : n.E.size < 2 ^ K := lt_mono hnK.wk hS.Esize_lt
  have hxn' : xn < 2 ^ K := by
    obtain ⟨A, hI, hel⟩ := hS.ok.cost.low.inv
    have := ((hI.eAlloc _).mp (hel ▸ hxn)).2
    omega
  obtain ⟨n', -, ⟨L', c, he, hy, -⟩, -⟩ := hS.insert hxn hh
    (State.setLocs (fun _ => 0) ["x", "h"] [xn, hh]) (by simp [State.setLocs, State.upd])
    (by simp [State.setLocs, State.upd])
  unfold nxtInsC
  rw [compile_κ₀ (1 - p) n.P]
  have hnE := h.nxt n hn
  have hev : Machine.evalList m [.var "xn", .var "hh"] = some [xn, hh] := by
    simp [Machine.evalList, Expr.eval, hlx, hlh]
  refine wpB_seq_T (wpB_coreCall (Q := fun m2 _ => m2.loc "hh" = hh ∧ m2.loc "y2" = n.E.size ∧
      m2.cap (wIdx (1 - p)) = m.cap (wIdx (1 - p))) hnE hev he ?_
    (pk_BW (insertAfter_peak hnK.caps (by
      have := hnK.k8
      omega) hnE hnK.wb hnK.hh hnK.room hS hxn hnK.wk
      (by omega) he)) (fun m2 _ hS2 hL2 => ⟨?_, ?_, ?_⟩)) (fun m2 _ ⟨hh2, hy2, hc2⟩ => ?_)
  · simp only [Machine.maxvList, List.map_cons, Expr.maxv, hlx, hlh, List.map_nil,
      List.foldr_cons, List.foldr_nil, zero_le, sup_of_le_left, sup_le_iff]; proveBudget K KH
  · rw [hL2]; simp [State.setLocs, State.upd, hlh]
  · rw [hL2]; simp [State.setLocs, State.upd, hy]
  · rw [(hS2 _ (wIdx_notSlot (by omega))).2]
  exact wpB_T (Machine.wpB_store_g (Q := TT) hh n.E.size (by simp [Expr.eval, hh2])
    (by simp [Expr.eval, hy2]) (by
      rw [hc2]
      exact hhc) (by
      simp only [Expr.maxv, hh2]
      proveBudget K KH)
    (by
      simp only [Expr.maxv, hy2]
      proveBudget K KH) (fun _ _ _ _ => trivial))

theorem mirrorInsC_pk {om : OrderMaintenance} {m : State} {p : Nat} (h : WEnc om m p) (hW : WK K
  KH T om) {hx : Option Nat}
    {hy : Nat} (hhx : m.loc "hx" = b2n hx.isSome)
    (hxx : ∀ x, hx = some x → m.loc "x" = x ∧ (om.nxt.isSome → x < m.cap (wIdx (1 - p))) ∧ x ≤ T)
    (hhy : m.loc "hy" = hy) (hhyc : om.nxt.isSome → hy < m.cap (wIdx (1 - p))) (hyT : hy ≤ T)
    (hN : ∀ n, om.nxt = some n → om.cursorSet = true → (hx = none ∨ ∃ x, hx = some x ∧
      om.nxtIdx.getX x ≠ 0) →
      ∃ B, InService n B ∧ mirAnchor om n hx ∈ B) :
    wpB (BW K KH) (mirrorInsC p) TT m := by
  obtain ⟨hb1, hb2, -⟩ := hW.pack
  have hp := h.p2
  unfold mirrorInsC
  have hm1 : (Expr.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)).maxv m ≤ BW K KH := by
    have := h.nxtOn
    simp only [Expr.maxv, Expr.eval, h.scap 1 (by decide), Order.lt_one_iff, Option.bind_some,
        ↓reduceIte, this, Option.getD_some, zero_le, sup_of_le_right, sup_of_le_left,
        BinOp.eval, sup_le_iff]
    unfold b2n BW; split <;> split <;> omega
  cases hn : om.nxt with
  | none =>
    exact wpB_ite_T 1 (by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n]) hm1
      (fun _ _ _ _ => by simpa using wpB_skip_T)
  | some n =>
    refine wpB_ite_T 0 (by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n]) hm1
      (fun s1 hl1 hm1' hc1 => ?_)
    simp only [ne_eq, not_true_eq_false, ite_false]
    have h1 := h.congr hm1' hc1
    have hm3 : (Expr.bin .eq (.load (wa 3) (.lit 0)) (.lit 0)).maxv s1 ≤ BW K KH := by
      have := h1.cset
      simp only [Expr.maxv, Expr.eval, h1.scap 3 (by decide), Order.lt_one_iff, Option.bind_some,
          ↓reduceIte, this, Option.getD_some, zero_le, sup_of_le_right, sup_of_le_left,
          BinOp.eval, sup_le_iff]
      unfold b2n BW; split <;> split <;> omega
    by_cases hcs : om.cursorSet = false
    · exact wpB_ite_T 1 (by simp [Expr.eval, h1.scap 3 (by decide), h1.cset, hcs, BinOp.eval,
        b2n]) hm3
        (fun _ _ _ _ => by simpa using wpB_skip_T)
    have hcs' : om.cursorSet = true := by simpa using hcs
    refine wpB_ite_T 0 (by simp [Expr.eval, h1.scap 3 (by decide), h1.cset, hcs', BinOp.eval,
      b2n]) hm3
      (fun s2 hl2 hm2 hc2 => ?_)
    simp only [ne_eq, not_true_eq_false, ite_false]
    have h2 := h1.congr hm2 hc2
    have hhx2 : s2.loc "hx" = b2n hx.isSome := by rw [hl2, hl1, hhx]
    have hhy2 : s2.loc "hy" = hy := by rw [hl2, hl1, hhy]
    have hyc := hhyc (by
      rw [hn]
      rfl)
    have hmx : (Expr.bin .eq (.var "hx") (.lit 0)).maxv s2 ≤ BW K KH := by
      simp only [Expr.maxv, hhx2, zero_le, sup_of_le_left, Expr.eval, BinOp.eval,
          Option.bind_some, Option.getD_some, sup_le_iff]; unfold b2n BW; split <;> split <;> omega
    refine wpB_ite_T (if b2n hx.isSome = 0 then 1 else 0) (by
      simp [Expr.eval, BinOp.eval, hhx2]) hmx
      (fun s3 hl3 hm3' hc3 => ?_)
    have h3 := h2.congr hm3' hc3
    have hnK := hW.nxtK hn
    have hnE := h3.nxt n hn
    cases hx with
    | none =>
      simp only [Option.isSome_none, b2n, Bool.false_eq_true, ↓reduceIte, ne_eq, one_ne_zero,
        not_false_eq_true]
      obtain ⟨B, hS, hxB⟩ := hN n hn hcs' (Or.inl rfl)
      have hc0 := hnE.cap (.s .head)
      have hm0 := hnE.mem (.s .head) 0 (by
        rw [Fld.cap]
        omega)
      have hv := hnK.wb.scalars.2.1
      refine wpB_assign_seq n.head (by
        simp [Expr.eval, hc0, Fld.cap, hm0]
        rfl)
        (by
          simp only [Expr.maxv, Expr.eval, hc0, Fld.cap, Order.lt_one_iff, Option.bind_some,
              ↓reduceIte, hm0, Fld.get, SF.get, Option.getD_some, zero_le,
              sup_of_le_right]
          proveBudget K KH) (fun s4 hl4 hm4 hc4 => ?_)
      refine wpB_assign_seq hy (by simp [Expr.eval, hl4, State.upd, hl3, hhy2])
        (by
          simp only [Expr.maxv, hl4, State.upd, String.reduceEq, ↓reduceIte, hl3, hhy2]
          proveBudget K KH) (fun s5 hl5 hm5 hc5 => ?_)
      exact nxtInsC_pk ((h3.congr hm4 hc4).congr hm5 hc5) hW hn hS hxB (by
        rw [hl5]
        simp [State.upd, hl4, mirAnchor])
        (by
          rw [hl5]
          simp [State.upd]) (by
          rw [hc5, hc4, hc3, hc2, hc1]
          exact hyc) hyT
    | some x =>
      simp only [Option.isSome_some, b2n, ↓reduceIte, one_ne_zero, ne_eq, not_true_eq_false]
      obtain ⟨hxl, hxc, hxT⟩ := hxx x rfl
      have hxc' := hxc (by
        rw [hn]
        rfl)
      have hx3 : s3.loc "x" = x := by rw [hl3, hl2, hl1, hxl]
      have hxc3 : x < s3.cap (wIdx (1 - p)) := by rw [hc3, hc2, hc1]; exact hxc'
      have hix := hW.nxtIdx hn x
      refine wpB_assign_seq (om.nxtIdx.getX x) (by simp [Expr.eval, hx3, hxc3, h3.idxN (by
        rw [hn]
        rfl) x hxc3])
        (by simp only [Expr.maxv, hx3, Expr.eval, Option.bind_some, hxc3, ↓reduceIte,
            h3.idxN (by rw [hn]; rfl) x hxc3, Option.getD_some, sup_le_iff]; proveBudget K KH)
        (fun s4 hl4 hm4 hc4 => ?_)
      have h4 := h3.congr hm4 hc4
      have hxn4 : s4.loc "xn" = om.nxtIdx.getX x := by rw [hl4]; simp [State.upd]
      have hmx4 : (Expr.bin .eq (.var "xn") (.lit 0)).maxv s4 ≤ BW K KH := by
        simp only [Expr.maxv, hxn4, zero_le, sup_of_le_left, Expr.eval, BinOp.eval,
            Option.bind_some, Option.getD_some, sup_le_iff]; unfold BW; split <;> omega
      by_cases h0 : om.nxtIdx.getX x = 0
      · exact wpB_ite_T 1 (by simp [Expr.eval, hxn4, h0, BinOp.eval]) hmx4 (fun _ _ _ _ => by
          simpa using wpB_skip_T)
      refine wpB_ite_T 0 (by simp [Expr.eval, hxn4, h0, BinOp.eval]) hmx4 (fun s5 hl5 hm5 hc5 => ?_)
      simp only [ne_eq, not_true_eq_false, ite_false]
      obtain ⟨B, hS, hxB⟩ := hN n hn hcs' (Or.inr ⟨x, rfl, h0⟩)
      refine wpB_assign_seq hy (by simp [Expr.eval, hl5, hl4, State.upd, hl3, hhy2])
        (by
          simp only [Expr.maxv, hl5, hl4, State.upd, String.reduceEq, ↓reduceIte, hl3, hhy2]
          proveBudget K KH) (fun s6 hl6 hm6 hc6 => ?_)
      exact nxtInsC_pk ((h4.congr hm5 hc5).congr hm6 hc6) hW hn hS hxB (by
        rw [hl6]
        simp [State.upd, hl5, hxn4, mirAnchor])
        (by
          rw [hl6]
          simp [State.upd]) (by
          rw [hc6, hc5, hc4, hc3, hc2, hc1]
          exact hyc) hyT

end OrderMaintenance.Impl

/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakRebuildM


/-!
# Theorem W, option (A), stage A3: the peak of one operation, and of the initialization

The wrapper's operations (`OpsM.lean`) with the budget `BW K KH`, along the proofs of
`insertW_ok`, `deleteW_ok`, `orderW_okM` (their statements unchanged): the value bounds `WK` of
each intermediate wrapper state come from option (B)'s steps (`insert_step`, `delete_step`:
the insertion or deletion in `cur`, `mirror_wbw`, `mirrorDel_wbw`, the live counter), with
`T = t + 1`. A core created by the operation has `N' ≤ 4N` (`MInv.nxtN`, from the invariant of the
state after the operation), hence `wK' ≤ wK + 128` (`wK_mono4`).

* `opS_pk`: the machine code of one operation, from a machine state holding a wrapper state
  reached by `t` operations, stays within `BW (wKom om + 128) KH` whenever `t + 1 < 2^KH`.
* `theoremW_op`: **`dpk (opS op) m < 2^(2·(wKom om + 128) + 5) + 2·(t + 1)`**.
* `theoremW_init`: **`dpk initWS m < 2^1029`** for `K_B < 2^512`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

variable {K KH : Nat}

/-! ### The capacity of a new core -/

/-- **The next core is at most four times larger** (as in `reach_mem`). -/
theorem MInv.nxtN {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI : MInv om Sp)
  {n : Core} (hn : om.nxt = some n) :
    n.P.N ≤ 4 * om.cur.P.N := by
  have hW := hI.1
  obtain ⟨-, -, A, hRA, -, -, -⟩ := hW.w
  have hmk : om.cur.P = proofParams om.cur.P.N := (hW.cur A hRA.inv).pmk
  obtain ⟨c₀, live₀, I, D, hRW⟩ := hW.busy n hn
  have hnP := hRW.nP
  have hNn : n.P.N = 4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16 := by
    rw [hnP]; rfl
  have hsm := costSetup.small _ hW.big
  rw [← hmk] at hsm
  have hc0 := hRW.c0
  have hl0 := hRW.l0
  have hkb := hW.kb
  have hdiv : (c₀ + (om.cur.P.L + 2)) / (om.KB - 1) ≤ (c₀ + (om.cur.P.L + 2)) / 3 :=
    Nat.div_le_div_left (by omega) (by norm_num)
  rw [hNn]
  have hbig := hW.big
  apply Nat.mul_le_mul_left 4
  apply max_le <;> omega

/-! ### The value bounds at the start of an operation -/

theorem wK_cur_le {om : OrderMaintenance} : wK om.cur.P ≤ wKom om := le_max_left _ _
theorem wK_nxt_le {om : OrderMaintenance} {n : Core} (hn : om.nxt = some n) : wK n.P ≤ wKom om := by
  unfold wKom; rw [hn]; exact le_max_right _ _

theorem MInv.cmk {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (hI : MInv om Sp) :
  om.cur.P = proofParams om.cur.P.N := by
  obtain ⟨-, -, A, hRA, -, -, -⟩ := hI.1.w
  exact (hI.1.cur A hRA.inv).pmk

/-- The value bounds of a wrapper state of the run. -/
theorem WK.of_inv {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} {t T : Nat} (hI :
  MInv om Sp) (hB : WBW t om om.nxt)
    (ht : t ≤ T) (hK : wKom om ≤ K) (hKB : om.KB < 2 ^ K) (hT : T < 2 ^ KH) : WK K KH T om :=
  ⟨hB.mono ht, hI.cmk, le_trans wK_cur_le hK, fun _ hn => hI.nP hn, fun _ hn => le_trans
    (wK_nxt_le hn) hK,
    hKB, hT⟩

/-! ### Insertion -/

/-- **An insertion**: its peak. -/
theorem insertW_pk {om : OrderMaintenance} {m : State} {p : Nat} {Sp :
  OrderMaintenance.Spec.State} {t : Nat} (h : WEnc om m p)
    (hI : MInv om Sp) (hB : WBW t om om.nxt) {hx : Option Nat} (hv : (insOp hx).Valid Sp)
    (hhx : m.loc "hx" = b2n hx.isSome) (hxl : ∀ x, hx = some x → m.loc "x" = x)
    (hK : wKom om + 128 ≤ K) (hKB : om.KB < 2 ^ K) (hKH : t + 1 < 2 ^ KH) :
    wpB (BW K KH) insertWS TT m := by
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
  -- the value bounds along the operation (`insert_step`)
  have hKw : wKom om ≤ K := by omega
  have hW0 : WK K KH (t + 1) om := WK.of_inv hI hB (Nat.le_succ t) hKw hKB hKH
  have hB1 := insert_core_wbw hS0 hxL hB hP'' hr1'
  have hW1 : WK K KH (t + 1) (insOM om c' om.cur.E.size) :=
    ⟨hB1, by change c'.P = proofParams c'.P.N; rw [hP'']; exact hW0.cpmk,
      by change wK c'.P ≤ K; rw [hP'']; exact hW0.cwk, hW0.npmk, hW0.nwk, hW0.kb, hKH⟩
  obtain ⟨hB2, f1, f2, f3, f4, f5⟩ := mirror_wbw (om := insOM om c' om.cur.E.size) hB1
    (Nat.le_succ _)
    (fun n hn hs hc => hI.mirror hx n hn hs hc) hm2
  have hc2P : om2.cur.P = om.cur.P := by rw [f1]; exact hP''
  have hW2 : WK K KH (t + 1) om2 :=
    ⟨hB2, by rw [hc2P]; exact hW0.cpmk, by rw [hc2P]; exact hW0.cwk,
      fun n hn => by obtain ⟨n0, hn0, hP0⟩ := f5 n hn; rw [hP0]; exact hW1.npmk n0 hn0,
      fun n hn => by obtain ⟨n0, hn0, hP0⟩ := f5 n hn; rw [hP0]; exact hW1.nwk n0 hn0,
      by rw [f4]; exact hW1.kb, hKH⟩
  have hlv2 : om2.live = om.live := f2
  have hW3 : WK K KH (t + 1) ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance) :=
    ⟨⟨hB2.cur, hB2.nxt, hB2.noNxt, hB2.curIdx, hB2.cursor, hB2.hcur,
      by change om2.live + 1 ≤ t + 1; rw [hlv2]; have := hB.live; omega, hB2.hnd, hB2.reb⟩,
      hW2.cpmk, hW2.cwk, hW2.npmk, hW2.nwk, hW2.kb, hKH⟩
  -- the machine
  refine byPar_pk h (by proveBudget K KH) ?_
  have h0 := h.bump (parE.maxv m)
  unfold insC
  have hxc : ∀ x, hx = some x → x < om.nextHandle := fun x e => by
    have := hS.2 x (hxS x e); rw [hf]; exact this
  have hnhT : om.nextHandle ≤ t := hB.hnd
  obtain ⟨c3, y, hr3, -, -, -, -, hy, hwp1⟩ := curInsW_ok h0 (by simpa using hhx)
    (fun x e => ⟨by simpa using hxl x e, by have := h0.roomC; have := hxc x e; omega⟩)
    hS0.ok.cost rfl hxL hS0.ok.cnt hS0.room hS0.mc hk hRf hn1 hsize hcap hI5 hpow
  rw [hr1'] at hr3
  injection hr3 with hyy hcc; subst hcc; subst hyy
  refine wpB_seq_ofQ hwp1 (curInsC_pk h0 hW0 (by simpa using hhx)
    (fun x e => ⟨by simpa using hxl x e, by have := h0.roomC; have := hxc x e; omega,
      by have := hxc x e; omega⟩) hS0 hxL) (fun m1 k1 ⟨h1, hy1, hyy1, hhx1, hx1, hk1⟩ => ?_)
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
  refine wpB_seq_ofQ hmir (mirrorInsC_pk h1 hW1 (hx := hx) (hy := om.nextHandle) (by
    rw [hhx1]
    simpa using hhx)
    (fun x e => ⟨by rw [hx1]; simpa using hxl x e, fun hs => by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
      have h5 := h1.roomN n hn; have h6 := hxc x e
      simp only [insOM] at h5; omega, by have := hxc x e; omega⟩)
    hy1
    (fun hs => by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
      have h5 := h1.roomN n hn
      simp only [insOM] at h5; omega) (by omega)
    (fun n hn hs hc => hI.mirror hx n hn hs hc)) (fun m2 k2 ⟨h2, hl2, hk2⟩ => ?_)
  refine wpB_seq_ofQ (liveIncW_ok h2) (liveIncC_pk h2 hW2 (by
    rw [hlv2]
    have := hB.live
    omega))
    (fun m3 k3 ⟨h3, hl3, hk3⟩ => ?_)
  have hkb : 1 ≤ ({
    om2 with
    live := om2.live + 1
  } : OrderMaintenance).KB := by
    change 1 ≤ om2.KB; rw [e2]; have := hW.kb; change 1 ≤ om.KB; omega
  refine wpB_T (rebuildC_pk h3 hW3 hX3 hkb hsafe hR' ?_ (fun c hc => hI'.nxtN hc))
  change wK om2.cur.P + 128 ≤ K
  rw [hc2P]; have := wK_cur_le (om := om); omega

/-! ### Deletion -/

/-- **A deletion**: its peak. -/
theorem deleteW_pk {om : OrderMaintenance} {m : State} {p : Nat} {Sp :
  OrderMaintenance.Spec.State} {t : Nat} (h : WEnc om m p)
    (hI : MInv om Sp) (hB : WBW t om om.nxt) {x : Nat} (hv : x ∈ Sp.list) (hxl : m.loc "x" = x)
    (hK : wKom om + 128 ≤ K) (hKB : om.KB < 2 ^ K) (hKH : t + 1 < 2 ^ KH) :
    wpB (BW K KH) deleteWS TT m := by
  have hp := h.p2
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  obtain ⟨om', c', om2, hdel, hI', hr1, hm2, hsafe, hR', hP'', e1, e2, hX3⟩ :=
    hI.delete_prefix hv
  have hxL : om.curIdx.getX x ∈ A.elist := (hIdx x hv).1
  have hS0 := hI.cur hR.inv
  -- the value bounds along the operation (`delete_step`)
  have hKw : wKom om ≤ K := by omega
  have hW0 : WK K KH (t + 1) om := WK.of_inv hI hB (Nat.le_succ t) hKw hKB hKH
  have hP1 : c'.P = om.cur.P := hP''
  have hB1 := markDead_wbw hB hr1
  have hW1 : WK K KH (t + 1) ({
    om with
    cur := c'
    curIdx := om.curIdx.setX x 0
  } :
    OrderMaintenance) :=
    ⟨hB1, by change c'.P = proofParams c'.P.N; rw [hP1]; exact hW0.cpmk,
      by change wK c'.P ≤ K; rw [hP1]; exact hW0.cwk, hW0.npmk, hW0.nwk, hW0.kb, hKH⟩
  obtain ⟨hB2, f1, f2, f3, f5⟩ := mirrorDel_wbw hB1 hm2
  have hc2P : om2.cur.P = om.cur.P := by rw [f1]; exact hP1
  have hW2 : WK K KH (t + 1) om2 :=
    ⟨hB2, by rw [hc2P]; exact hW0.cpmk, by rw [hc2P]; exact hW0.cwk,
      fun n hn => by obtain ⟨n0, hn0, hP0⟩ := f5 n hn; rw [hP0]; exact hW1.npmk n0 hn0,
      fun n hn => by obtain ⟨n0, hn0, hP0⟩ := f5 n hn; rw [hP0]; exact hW1.nwk n0 hn0,
      by rw [e2]; exact hW1.kb, hKH⟩
  have hW3 : WK K KH (t + 1) ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance) :=
    ⟨⟨hB2.cur, hB2.nxt, hB2.noNxt, hB2.curIdx, hB2.cursor, hB2.hcur,
      by change om2.live - 1 ≤ t + 1; have := hB2.live; omega, hB2.hnd, hB2.reb⟩,
      hW2.cpmk, hW2.cwk, hW2.npmk, hW2.nwk, hW2.kb, hKH⟩
  -- the machine
  refine byPar_pk h (by proveBudget K KH) ?_
  have h0 := h.bump (parE.maxv m)
  have hxc : x < om.nextHandle := by have := hS.2 x hv; rw [hf]; exact this
  have hnhT : om.nextHandle ≤ t := hB.hnd
  unfold delC
  refine wpB_seq_ofQ (curDelW_ok h0 (by simpa using hxl) (by
    have := h0.roomC
    omega) hS0.ok.cost rfl hxL
    hS0.ok.cnt hS0.mc hr1) (curDelC_pk h0 hW0 (by simpa using hxl) (by omega) (by
      have := h0.roomC
      omega) hS0 hxL)
    (fun m1 k1 ⟨h1, hl1, hk1⟩ => ?_)
  have hx1 : m1.loc "x" = x := by rw [hl1]; simp [State.upd, hxl]
  have hxc1 : ({
    om with
    cur := c'
    curIdx := om.curIdx.setX x 0
  } :
    OrderMaintenance).nxt.isSome → x < m1.cap (wIdx (1 - p)) :=
    fun hs => by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
      have h5 := h1.roomN n hn; simp only at h5; omega
  refine wpB_seq_ofQ (mirrorDelW_ok h1 hx1 hxc1 (fun n hn hx0 => (hI.mirrorDel x n hn hx0).2) hm2)
    (mirrorDelC_pk h1 hW1 hx1 (by omega) hxc1 (fun n hn hx0 => (hI.mirrorDel x n hn hx0).2))
    (fun m2 k2 ⟨h2, hl2, hk2⟩ => ?_)
  refine wpB_seq_ofQ (liveDecW_ok h2) (liveDecC_pk h2 hW2) (fun m3 k3 ⟨h3, hl3, hk3⟩ => ?_)
  have hkb : 1 ≤ ({
    om2 with
    live := om2.live - 1
  } : OrderMaintenance).KB := by
    change 1 ≤ om2.KB; rw [e2]; have := hW.kb; change 1 ≤ om.KB; omega
  refine wpB_T (rebuildC_pk h3 hW3 hX3 hkb hsafe hR' ?_ (fun c hc => hI'.nxtN hc))
  change wK om2.cur.P + 128 ≤ K
  rw [hc2P]; have := wK_cur_le (om := om); omega

/-! ### Order queries -/

/-- **An order query**: its peak. -/
theorem orderW_pk {om : OrderMaintenance} {m : State} {p : Nat} {Sp :
  OrderMaintenance.Spec.State} {t : Nat} (h : WEnc om m p)
    (hI : MInv om Sp) (hB : WBW t om om.nxt) {x y : Nat} (hxv : x ∈ Sp.list) (hyv : y ∈ Sp.list)
    (hxl : m.loc "x" = x) (hyl : m.loc "y" = y)
    (hK : wKom om ≤ K) (hKB : om.KB < 2 ^ K) (hKH : t + 1 < 2 ^ KH) :
    wpB (BW K KH) orderWS TT m := by
  have hW := hI.1
  obtain ⟨hS, hf, A, hR, hL, hIdx, hN⟩ := hW.w
  obtain ⟨hx1, -, -⟩ := hIdx x hxv
  obtain ⟨hy1, -, -⟩ := hIdx y hyv
  have hrun := order_correct hR.inv hx1 hy1
  have hS0 := hI.cur hR.inv
  have hW0 : WK K KH (t + 1) om := WK.of_inv hI hB (Nat.le_succ t) hK hKB hKH
  have hxc : x < om.nextHandle := by have := hS.2 x hxv; rw [hf]; exact this
  have hyc : y < om.nextHandle := by have := hS.2 y hyv; rw [hf]; exact this
  have hnhT : om.nextHandle ≤ t := hB.hnd
  refine byPar_pk h (by proveBudget K KH) ?_
  have h0 := h.bump (parE.maxv m)
  exact orderC_pk h0 hW0 (by simpa using hxl) (by simpa using hyl) (by omega) (by omega)
    (by
      have := h0.roomC
      omega) (by
      have := h0.roomC
      omega) hS0 hx1 hy1 hrun

end OrderMaintenance.Impl

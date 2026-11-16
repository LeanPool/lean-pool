/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Fresh


/-!
# M6: computing a new core's parameters

`paramsS q` computes `proofParams N` from `N` (local `nN`) in a constant number of steps,
stores it in slot `q`'s parameter array, and leaves the capacities of `capsOf (proofParams N)`
in the locals `kE … kW` (`CapLocs`). `msb` gives `⌊log₂ N⌋`; the truncating subtractions of
`proofParams` become branch-free products with comparisons.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-- `a - b`, truncated at 0, without a failing subtraction: `a·[b ≤ a] - b·[b ≤ a]`. -/
def tsubE (a b : Expr) : Expr := .bin .sub (.bin .mul a (.bin .le b a)) (.bin .mul b (.bin .le b a))

theorem tsubE_eval {s : State} {a b : Expr} {x y : Nat} (ha : a.eval s = some x) (hb : b.eval s = some y) :
    (tsubE a b).eval s = some (x - y) := by
  simp only [tsubE, Expr.eval, ha, hb, Option.bind_some, BinOp.eval]
  by_cases h : y ≤ x
  · simp [h]
  · simp [h]; omega

/-! ### The parameters as expressions in `L` and `N` -/

section exprs
open Expr in
def eL : Expr := .var "L"
def eN : Expr := .var "nN"
def eG : Expr := .bin .mul (.lit 2) eL
def eT : Expr := .bin .mul (.bin .mul (.lit 3) eL) eL
def ekg : Expr := .bin .add (.bin .div eG (.lit 3)) (.lit 1)
def egm : Expr := .bin .div (.bin .sub eG (.lit 2)) (.lit 2)
def eUG : Expr := .bin .add (.bin .add eG ekg) (tsubE ekg egm)
def euT : Expr := .bin .add (.bin .div eT egm) (.lit 1)
def ekc : Expr := .bin .add (.bin .div euT (.lit 3)) (.lit 1)
def eMu : Expr := .bin .add euT ekc
def eIC : Expr := .bin .add eT (.bin .mul (.lit 2) ekc)
def ecsB : Expr := .bin .div eIC egm
def ersB : Expr := .bin .add (.bin .mul (.lit 3) eMu) (.lit 1)
def eHC : Expr := .bin .mul (.lit 2) (.bin .add ecsB ersB)
def ePC : Expr := .bin .add (.bin .add (.bin .mul (.lit 3) eMu) ersB) ecsB
def eth : Expr := .bin .mul (.bin .mul (.lit 2) eL) eL
def eH : Expr := .bin .add (.bin .div eL (.lit 3)) (.lit 1)
def eBe : Expr := .bin .add eUG (.bin .add (.un .msb (.bin .add eG ekg)) (.lit 2))
def eBg : Expr := .bin .add eHC (.bin .add (.un .msb ePC) (.lit 2))
def ecm : Expr := .bin .div (.bin .add (.bin .add (.bin .add eT ekc) (.bin .add eG ekg)) (.lit 1)) (.lit 2)
def ecb : Expr := .bin .add (.lit 2) (.bin .mul (.lit 2) (.bin .div eN (.bin .sub (.bin .add eth (.lit 1)) ecm)))
def enb : Expr := .bin .add (.bin .add eH (.lit 2))
  (.bin .mul (.bin .add (.bin .add eH (.lit 1)) (.bin .add (.bin .mul eH (.lit 12)) (.lit 1))) ecb)
end exprs

/-! ### Their values -/

section vals
variable (N L : Nat)
def vG : Nat := 2 * L
def vT : Nat := 3 * L * L
def vkg : Nat := vG L / 3 + 1
def vgm : Nat := (vG L - 2) / 2
def vUG : Nat := vG L + vkg L + (vkg L - vgm L)
def vuT : Nat := vT L / vgm L + 1
def vkc : Nat := vuT L / 3 + 1
def vMu : Nat := vuT L + vkc L
def vIC : Nat := vT L + 2 * vkc L
def vcsB : Nat := vIC L / vgm L
def vrsB : Nat := 3 * vMu L + 1
def vHC : Nat := 2 * (vcsB L + vrsB L)
def vPC : Nat := 3 * vMu L + vrsB L + vcsB L
def vth : Nat := 2 * L * L
def vH : Nat := L / 3 + 1
def vBe : Nat := vUG L + (Nat.log2 (vG L + vkg L) + 2)
def vBg : Nat := vHC L + (Nat.log2 (vPC L) + 2)
def vcm : Nat := (vT L + vkc L + (vG L + vkg L) + 1) / 2
def vcb : Nat := 2 + 2 * (N / (vth L + 1 - vcm L))
def vnb : Nat := (vH L + 2) + ((vH L + 1) + (vH L * 12 + 1)) * vcb N L
end vals

section evals
variable {s : State} {N L : Nat} (hL : s.loc "L" = L) (hN : s.loc "nN" = N)
include hL

theorem eG_ev : eG.eval s = some (vG L) := by simp [eG, eL, Expr.eval, BinOp.eval, hL, vG]
theorem eT_ev : eT.eval s = some (vT L) := by simp [eT, eL, Expr.eval, BinOp.eval, hL, vT]
theorem ekg_ev : ekg.eval s = some (vkg L) := by
  simp [ekg, Expr.eval, BinOp.eval, eG_ev hL, vkg]
theorem egm_ev (h8 : 8 ≤ L) : egm.eval s = some (vgm L) := by
  have h2 : 2 ≤ vG L := by unfold vG; omega
  simp [egm, Expr.eval, BinOp.eval, eG_ev hL, vgm, h2]
theorem eUG_ev (h8 : 8 ≤ L) : eUG.eval s = some (vUG L) := by
  simp [eUG, Expr.eval, BinOp.eval, eG_ev hL, ekg_ev hL, tsubE_eval (ekg_ev hL) (egm_ev hL h8), vUG]
theorem euT_ev (h8 : 8 ≤ L) : euT.eval s = some (vuT L) := by
  simp [euT, Expr.eval, BinOp.eval, eT_ev hL, egm_ev hL h8, vuT]
theorem ekc_ev (h8 : 8 ≤ L) : ekc.eval s = some (vkc L) := by
  simp [ekc, Expr.eval, BinOp.eval, euT_ev hL h8, vkc]
theorem eMu_ev (h8 : 8 ≤ L) : eMu.eval s = some (vMu L) := by
  simp [eMu, Expr.eval, BinOp.eval, euT_ev hL h8, ekc_ev hL h8, vMu]
theorem eIC_ev (h8 : 8 ≤ L) : eIC.eval s = some (vIC L) := by
  simp [eIC, Expr.eval, BinOp.eval, eT_ev hL, ekc_ev hL h8, vIC]
theorem ecsB_ev (h8 : 8 ≤ L) : ecsB.eval s = some (vcsB L) := by
  simp [ecsB, Expr.eval, BinOp.eval, eIC_ev hL h8, egm_ev hL h8, vcsB]
theorem ersB_ev (h8 : 8 ≤ L) : ersB.eval s = some (vrsB L) := by
  simp [ersB, Expr.eval, BinOp.eval, eMu_ev hL h8, vrsB]
theorem eHC_ev (h8 : 8 ≤ L) : eHC.eval s = some (vHC L) := by
  simp [eHC, Expr.eval, BinOp.eval, ecsB_ev hL h8, ersB_ev hL h8, vHC]
theorem ePC_ev (h8 : 8 ≤ L) : ePC.eval s = some (vPC L) := by
  simp [ePC, Expr.eval, BinOp.eval, eMu_ev hL h8, ersB_ev hL h8, ecsB_ev hL h8, vPC]
theorem eth_ev : eth.eval s = some (vth L) := by simp [eth, eL, Expr.eval, BinOp.eval, hL, vth]
theorem eH_ev : eH.eval s = some (vH L) := by simp [eH, eL, Expr.eval, BinOp.eval, hL, vH]
theorem eBe_ev (h8 : 8 ≤ L) : eBe.eval s = some (vBe L) := by
  simp [eBe, Expr.eval, BinOp.eval, UnOp.eval, eUG_ev hL h8, eG_ev hL, ekg_ev hL, vBe]
theorem eBg_ev (h8 : 8 ≤ L) : eBg.eval s = some (vBg L) := by
  simp [eBg, Expr.eval, BinOp.eval, UnOp.eval, eHC_ev hL h8, ePC_ev hL h8, vBg]
theorem ecm_ev (h8 : 8 ≤ L) : ecm.eval s = some (vcm L) := by
  simp [ecm, Expr.eval, BinOp.eval, eT_ev hL, ekc_ev hL h8, eG_ev hL, ekg_ev hL, vcm]
include hN in
theorem ecb_ev (h8 : 8 ≤ L) (hc : vcm L ≤ vth L + 1) : ecb.eval s = some (vcb N L) := by
  simp [ecb, Expr.eval, BinOp.eval, eth_ev hL, ecm_ev hL h8, eN, hN, hc, vcb]
include hN in
theorem enb_ev (h8 : 8 ≤ L) (hc : vcm L ≤ vth L + 1) : enb.eval s = some (vnb N L) := by
  simp [enb, Expr.eval, BinOp.eval, eH_ev hL, ecb_ev hL hN h8 hc, vnb]
end evals

/-! ### They are `proofParams` and its capacities -/

theorem proofParams_eq (N : Nat) : proofParams N =
    { N := N, L := pL N, G := vG (pL N), T := vT (pL N), theta := vth (pL N), elementBits :=
      vBe (pL N),
      groupBits := vBg (pL N), elementSpacing := 2 ^ vUG (pL N), groupSpacing := 2 ^ vHC (pL N), groupBudget := 4, chunkBudget := 4, reservationBudget := 8, a := 8,
      s := 11, beta := 64, H := vH (pL N) } := rfl

theorem cb_proof (N : Nat) : cb (proofParams N) = vcb N (pL N) := rfl

theorem nbMax_proof (N : Nat) : nbMax (proofParams N) = vnb N (pL N) := by
  simp only [nbMax, nb0, OrderMaintenance.Proof.Top.topJ, OrderMaintenance.Proof.Top.walkLeft,
    cb_proof]
  simp [proofParams_eq, vnb]

theorem vcm_le (N : Nat) : vcm (pL N) ≤ vth (pL N) + 1 := by
  have := (cparams_proof N).I4
  have e : cmax (proofParams N) = vcm (pL N) := rfl
  rw [e] at this
  exact Nat.le_succ_of_le this

theorem pL_eq {N : Nat} (h : 0 < N) : pL N = max 8 (Nat.log2 N + 1) := by
  unfold pL
  congr 1
  apply le_antisymm
  · exact Nat.size_le.mpr (Nat.lt_log2_self)
  · exact Nat.lt_size.mpr (Nat.log2_self_le (by omega))

/-- A list of statements in sequence. -/
def seqAll : List Stmt → Stmt
  | [] => .skip
  | c :: cs => .seq c (seqAll cs)

/-- A sequence preserves every local preserved by each of its statements. -/
theorem seqAll_preservesLocal (commands : List Stmt) (x : Reg)
    (h : ∀ c ∈ commands, OrderMaintenance.Machine.PreservesLocal c x) :
    OrderMaintenance.Machine.PreservesLocal (seqAll commands) x := by
  induction commands with
  | nil => exact OrderMaintenance.Machine.preservesLocal_skip x
  | cons c cs ih =>
    exact (h c (by simp)).seq (ih (fun d hd => h d (by simp [hd])))

/-- The parameter computation: `L`, then the parameter array, then the capacity locals. -/
def partA : Stmt :=
  .seq (.assign "L" (.bin .add (.un .msb eN) (.lit 1))) (.ite (.bin .lt eL (.lit 8)) (.assign "L" (.lit 8)) .skip)

/-- The parameters, as (index, expression) pairs. -/
def pList : List (Nat × Expr) := [
  (PF.N.idx, eN), (PF.L.idx, eL), (PF.G.idx, eG), (PF.T.idx, eT), (PF.theta.idx, eth), (PF.Be.idx, eBe),
  (PF.Bg.idx, eBg), (PF.De.idx, .bin .shl (.lit 1) eUG), (PF.Dg.idx, .bin .shl (.lit 1) eHC), (PF.KG.idx, .lit 4),
  (PF.KC.idx, .lit 4), (PF.KR.idx, .lit 8), (PF.a.idx, .lit 8), (PF.s.idx, .lit 11), (PF.beta.idx, .lit 64),
  (PF.H.idx, eH)]

def partB (q : Nat) : Stmt := .seq (.alloc (arr q .prm) (.lit 16)) (OrderMaintenance.Machine.storeAll (arr q .prm) pList)

def partC : Stmt := seqAll [
  .assign "kE" (.bin .add eN (.lit 2)),
  .assign "kG" (.bin .add (.bin .mul (.lit 2) eN) (.lit 4)),
  .assign "kC" (.bin .add ecb (.lit 2)),
  .assign "kN" (.bin .add (.bin .add enb ecb) (.lit 2)),
  .assign "kB" (.bin .add eN (.lit 3)),
  .assign "kCc" (.bin .add ecb (.lit 2)),
  .assign "kL" (.bin .add (.bin .add enb ecb) (.lit 2)),
  .assign "kR" (.bin .add enb (.lit 2)),
  .assign "kRc" (.bin .add (.bin .add enb ecb) (.lit 2)),
  .assign "kf" (.bin .add (.bin .mul (.lit 2) eN) (.lit 4)),
  .assign "kW" (.bin .add eH (.lit 1))]

def paramsS (q : Nat) : Stmt := .seq partA (.seq (partB q) partC)

/-! ### What the parts do -/
theorem partC_ok {s : State} {N L : Nat} (hL : s.loc "L" = L) (hN : s.loc "nN" = N) (h8 : 8 ≤ L)
    (hc : vcm L ≤ vth L + 1) :
    (exec partC s).status = .ok ∧ (exec partC s).st.mem = s.mem ∧ (exec partC s).st.cap = s.cap ∧
      (exec partC s).st.loc "kE" = N + 2 ∧ (exec partC s).st.loc "kG" = 2 * N + 4 ∧
      (exec partC s).st.loc "kC" = vcb N L + 2 ∧ (exec partC s).st.loc "kN" = vnb N L + vcb N L + 2 ∧
      (exec partC s).st.loc "kB" = N + 3 ∧ (exec partC s).st.loc "kCc" = vcb N L + 2 ∧
      (exec partC s).st.loc "kL" = vnb N L + vcb N L + 2 ∧ (exec partC s).st.loc "kR" = vnb N L + 2 ∧
      (exec partC s).st.loc "kRc" = vnb N L + vcb N L + 2 ∧ (exec partC s).st.loc "kf" = 2 * N + 4 ∧
      (exec partC s).st.loc "kW" = vH L + 1 := by
  have hNe : ∀ s' : State, s'.loc "nN" = N → eN.eval s' = some N := fun s' h => by simp [eN, Expr.eval, h]
  generalize hout : exec partC s = result
  simp? [partC, seqAll, exec, Out.bind, State.setLoc, State.upd, Expr.eval,
    BinOp.eval, eH_ev, ecb_ev, enb_ev, hNe, hL, hN, h8, hc] at hout
  cases hout
  simp [State.setLoc, State.upd]


/-- The parameter values, in terms of `N` and `L`. -/
def pvals (N L : Nat) : PF → Nat
  | .N => N | .L => L | .G => vG L | .T => vT L | .theta => vth L | .Be => vBe L | .Bg => vBg L
  | .De => 2 ^ vUG L | .Dg => 2 ^ vHC L | .KG => 4 | .KC => 4 | .KR => 8 | .a => 8 | .s => 11 | .beta => 64
  | .H => vH L

theorem pvals_proof (N : Nat) (k : PF) : pvals N (pL N) k = k.get (proofParams N) := by
  cases k <;> rfl

theorem partB_ok (q : Nat) {s : State} {N L : Nat} (hL : s.loc "L" = L) (hN : s.loc "nN" = N) (h8 : 8 ≤ L) :
    (exec (partB q) s).status = .ok ∧ (exec (partB q) s).st.cap (arr q .prm) = 16 ∧
      (∀ k : PF, (exec (partB q) s).st.mem (arr q .prm) k.idx = pvals N L k) ∧
      (exec (partB q) s).st.loc = s.loc ∧
      (∀ b, b ≠ arr q .prm → Same b s (exec (partB q) s).st) := by
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = (s.bump (Expr.maxv s (.lit 16))).alloc (arr q .prm) 16 := ⟨_, rfl⟩
  have hl1 : s1.loc "L" = L := by rw [hs1]; exact hL
  have hn1 : s1.loc "nN" = N := by rw [hs1]; exact hN
  have hc1 : s1.cap (arr q .prm) = 16 := by rw [hs1]; simp [State.alloc, State.upd]
  have hev : ∀ ie ∈ pList, ie.2.noLoad ∧ (ie.2.eval s1).isSome ∧ ie.1 < s1.cap (arr q .prm) := by
    intro ie hie
    rw [hc1]
    simp only [pList, List.mem_cons, List.not_mem_nil, or_false] at hie
    rcases hie with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [eN, eL, Expr.eval, hl1, hn1, eG_ev hl1, eT_ev hl1, eth_ev hl1, eBe_ev hl1 h8,
      eBg_ev hl1 h8,
      eUG_ev hl1 h8, eHC_ev hl1 h8, eH_ev hl1, PF.idx, BinOp.eval] <;> rfl
  obtain ⟨r1, r2, r3, r4, r5⟩ := OrderMaintenance.Machine.exec_storeAll (arr q .prm) pList s1 hev
  have he : exec (partB q) s = Out.bind ⟨s1, 1 + (Expr.lit 16).cost, .ok⟩
      (exec (OrderMaintenance.Machine.storeAll (arr q .prm) pList)) := by
    simp only [partB, exec, Expr.eval]; rw [hs1]
  rw [he]
  simp only [OrderMaintenance.Machine.Out.bind, r1]
  refine ⟨trivial, by rw [r3, hc1], fun k => ?_, by rw [r2, hs1]; rfl, fun b hb => ?_⟩
  · rw [r4]
    have hm1 : s1.mem (arr q .prm) = fun _ => 0 := by rw [hs1]; simp [State.alloc]
    rw [hm1]
    cases k <;> simp [OrderMaintenance.Machine.storeFold, pList, State.upd, PF.idx, pvals, eN, eL, Expr.eval, hl1, hn1,
      eG_ev hl1, eT_ev hl1, eth_ev hl1, eBe_ev hl1 h8, eBg_ev hl1 h8, eUG_ev hl1 h8, eHC_ev hl1 h8, eH_ev hl1,
      BinOp.eval]
  · refine ⟨by rw [r5 b hb, hs1]; simp [State.alloc, State.bump, hb], by rw [r3, hs1]; simp [State.alloc,
      State.bump, State.upd, hb]⟩

theorem partA_ok {s : State} {N : Nat} (hN : s.loc "nN" = N) :
    (exec partA s).status = .ok ∧ (exec partA s).st.loc "L" = max 8 (Nat.log2 N + 1) ∧
      (∀ x, x ≠ "L" → (exec partA s).st.loc x = s.loc x) ∧ (exec partA s).st.mem = s.mem ∧
      (exec partA s).st.cap = s.cap ∧ (exec partA s).cost ≤ 20 := by
  by_cases h : Nat.log2 N + 1 < 8
  · simp [partA, exec, Out.bind, Expr.eval, BinOp.eval, UnOp.eval, eN, eL, hN, State.setLoc,
    State.upd, h,
      Expr.cost]
    refine ⟨by omega, fun x hx => by simp [hx]⟩
  · simp [partA, exec, Out.bind, Expr.eval, BinOp.eval, UnOp.eval, eN, eL, hN, State.setLoc,
    State.upd, h,
      Expr.cost]
    refine ⟨by omega, fun x hx => by simp [hx]⟩
theorem partC_frame {s : State} (x : Reg) (h1 : x ≠ "kE") (h2 : x ≠ "kG") (h3 : x ≠ "kC") (h4 : x ≠ "kN")
    (h5 : x ≠ "kB") (h6 : x ≠ "kCc") (h7 : x ≠ "kL") (h8' : x ≠ "kR") (h9 : x ≠ "kRc") (h10 : x ≠ "kf")
    (h11 : x ≠ "kW") : (exec partC s).st.loc x = s.loc x := by
  have hframe : OrderMaintenance.Machine.PreservesLocal partC x := by
    apply seqAll_preservesLocal
    intro c hc
    simp only [List.mem_cons, List.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact OrderMaintenance.Machine.preservesLocal_assign h1 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h2 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h3 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h4 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h5 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h6 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h7 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h8' _
    · exact OrderMaintenance.Machine.preservesLocal_assign h9 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h10 _
    · exact OrderMaintenance.Machine.preservesLocal_assign h11 _
  exact hframe s

theorem partB_cost (q : Nat) : (partB q).slCost = some 469 := by
  simp [partB, OrderMaintenance.Machine.storeAll, pList, OrderMaintenance.Machine.Stmt.slCost,
    Expr.cost, eN, eL, eG, eT, eth, eBe, eBg, eUG,
    eHC, eH, ekg, egm, tsubE, ecsB, ersB, eIC, ekc, euT, eMu, ePC]

theorem partC_cost : partC.slCost = some 649 := by
  simp [partC, seqAll, OrderMaintenance.Machine.Stmt.slCost, Expr.cost, eN, eL, eT, eth, eH, ekg,
    egm, ekc, euT, ecb, enb, ecm,
    eG]

theorem pp_N (N : Nat) : (proofParams N).N = N := rfl
theorem pp_H (N : Nat) : (proofParams N).H = vH (pL N) := rfl

theorem bind_st {o : Out} {g : State → Out} (h : o.status = .ok) : (o.bind g).st = (g o.st).st := by
  unfold OrderMaintenance.Machine.Out.bind; rw [h]
theorem bind_cost {o : Out} {g : State → Out} (h : o.status = .ok) : (o.bind g).cost = o.cost + (g o.st).cost := by
  unfold OrderMaintenance.Machine.Out.bind; rw [h]
theorem bind_status {o : Out} {g : State → Out} (h : o.status = .ok) : (o.bind g).status = (g o.st).status := by
  unfold OrderMaintenance.Machine.Out.bind; rw [h]

/-- **The parameters of a new core**, computed in a constant number of steps. -/
theorem paramsS_ok (q : Nat) {m : State} {N : Nat} (hN : m.loc "nN" = N) (hpos : 0 < N) :
    (exec (paramsS q) m).status = .ok ∧ (exec (paramsS q) m).cost ≤ 1500 ∧
      (exec (paramsS q) m).st.cap (arr q .prm) = 16 ∧
      (∀ k : PF, (exec (paramsS q) m).st.mem (arr q .prm) k.idx = k.get (proofParams N)) ∧
      CapLocs (proofParams N) (exec (paramsS q) m).st.loc ∧
      (∀ b, b ≠ arr q .prm → Same b m (exec (paramsS q) m).st) ∧
      (∀ x, x ≠ "L" → x ≠ "kE" → x ≠ "kG" → x ≠ "kC" → x ≠ "kN" → x ≠ "kB" → x ≠ "kCc" → x ≠ "kL" →
        x ≠ "kR" → x ≠ "kRc" → x ≠ "kf" → x ≠ "kW" → (exec (paramsS q) m).st.loc x = m.loc x) := by
  have he : exec (paramsS q) m = (exec partA m).bind fun s => (exec (partB q) s).bind (exec partC) := rfl
  rw [he]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := partA_ok hN
  have hLA : (exec partA m).st.loc "L" = pL N := by rw [a2, pL_eq hpos]
  have hNA : (exec partA m).st.loc "nN" = N := by rw [a3 "nN" (by decide), hN]
  have h8 := pL_ge N
  obtain ⟨b1, b2, b3, b4, b5⟩ := partB_ok q hLA hNA h8
  have hcB := OrderMaintenance.Machine.cost_of_ok _ _ _ (partB_cost q) b1
  have hLB : (exec (partB q) (exec partA m).st).st.loc "L" = pL N := by rw [b4, hLA]
  have hNB : (exec (partB q) (exec partA m).st).st.loc "nN" = N := by rw [b4, hNA]
  have hc := vcm_le N
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := partC_ok hLB hNB h8 hc
  have hfr := partC_frame (s := (exec (partB q) (exec partA m).st).st)
  have hcC := OrderMaintenance.Machine.cost_of_ok _ _ _ partC_cost c1
  simp only [bind_st a1, bind_cost a1, bind_status a1, bind_st b1, bind_cost b1, bind_status b1]
  refine ⟨c1, by rw [hcC, hcB]; omega, by rw [c3]; exact b2, fun k => by rw [c2, b3, pvals_proof], ?_,
    fun b hb => ?_, ?_⟩
  · exact ⟨by rw [c4, pp_N], by rw [c5, pp_N], by rw [c6, cb_proof], by rw [c7, nbMax_proof, cb_proof],
      by rw [c8,
        pp_N], by rw [c9, cb_proof], by rw [c10, nbMax_proof, cb_proof], by rw [c11, nbMax_proof],
      by rw [c12, nbMax_proof, cb_proof], by rw [c13, pp_N], by rw [c14, pp_H]⟩
  · have := b5 b hb
    exact ⟨by rw [c2, this.1, a4], by rw [c3, this.2, a5]⟩
  · intro x h0 h1 h2 h3 h4 h5 h6 h7 h8' h9 h10 h11
    rw [hfr x h1 h2 h3 h4 h5 h6 h7 h8' h9 h10 h11, b4, a3 x h0]

end OrderMaintenance.Impl

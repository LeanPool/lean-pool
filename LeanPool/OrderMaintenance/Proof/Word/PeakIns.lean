/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakBg
public import LeanPool.OrderMaintenance.Proof.Word.Serve


/-!
# Theorem W, option (A), stage A2: the peak of `insertAfter`

* `insertAfter_peakG`: in the context of `insertAgree` (Theorem A) and `insertAfter_wb` (option
  (B)): the element insertion (`insertElem_pkok`, its sizes bounded by the end state through
  `fin_insertElem`), then the background work (`background_peak`), each in its `catch … bug`.
* `insertAfter_peakM`: at the cost proof's top invariant (`TIat TopInv P`, the context of
  `insertAgreeM`), with the capacity predicate `Mc`.
* `InService.peak`: for a core in service (the wrapper's Level M invariant, `InService`), at any
  word size `K ≥ wK c.P` (`64·L`).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top OrderMaintenance.Impl OrderMaintenance.Zeroing
open OrderMaintenance.Machine (Reg State)
variable {K KH W : Nat}

/-- **An insertion** (the context of `insertAgree` and `insertAfter_wb`): its peak. -/
theorem insertAfter_peakG {TI : Core → Prop} {μ : Core → Nat} {J n R NB0 : Nat} {cap : Params → Nat}
    {L : List Nat} {s : Core} {x : Nat} (hTC : TopContract TI μ J cap) (hT : TopWB K TI μ)
    (hTI : ∀ t, TI t → OrderMaintenance.Proof.Top.TopInv t) (hC : CostInv TI μ J n R L s)
    (hx : x ∈ L) (hk : 1 ≤ s.P.reservationBudget) (hR : J / s.P.reservationBudget + 1 ≤ R) (hn
      : 1 ≤ n)
    (hsize : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (OrderMaintenance.Zeroing.Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat)
    {κ : Caps} (Lx : Loc) (hLx : Lx "x" = x) (hLh : Lx "h" = hh) (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    (KI : InsCaps κ s) (Mc : Core → Prop)
    (hM4 : ∀ t, OrderMaintenance.Proof.Top.ts t = OrderMaintenance.Proof.Top.ts s → t.resJob = s.resJob → t.prep = s.prep →
      t.C.size = s.C.size → t.count = s.count + 1 → t.Gs.size ≤ s.Gs.size + 2 → PQCaps κ t → Mc t)
    (hMc : ∀ t, Mc t → TopCaps κ t ∧ PQCaps κ t ∧ t.prep = none ∧
      ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j = 0)
    (hMpop : ∀ t c t1, Mc t → pqPopMax.run t = .ok c t1 → Mc t1)
    (hMjob : ∀ L s j t job r t1, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t →
      t.resJob = some job →
      (jobStep job).run t = .ok r t1 → ResInv TI s.P.reservationBudget J n R μ L s (j + 1) { t1 with resJob := r } →
      Mc { t1 with resJob := r })
    (hMsplit : ∀ L s j t c t1 t2, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t → t.resJob = none → pqPopMax.run t = .ok c t1 →
      (splitChunkStart c).run t1 = .ok () t2 → ResInv TI s.P.reservationBudget J n R μ L s (j +
        1) t2 → Mc t2)
    (hW : WB K s) (hL : LabRoom K s.P) (hE : 4 * s.E.size + 8 ≤ 2 ^ K)
    (hG : s.Gs.size + 2 ≤ 2 ^ K) (hcnt : 2 * s.count + 4 ≤ 2 ^ K)
    (hNB : s.nodes.size + μ s ≤ NB0 + J * s.C.size)
    (hNK : NB0 + J * (2 + 2 * (s.count + 1)) + 2 ≤ 2 ^ K)
    (hCw : CapsW K κ) (hK : 8 ≤ K) (hWK : 2 * K + 4 ≤ W) (hKH : KH ≤ W)
    (hcapC : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512) (hRm : TopRoom K s.P)
    (hGd : Gd K KH κ (ΓH K KH) s Lx) :
    PKok K KH κ (ΓH K KH) W insertAfterP.body s Lx := by
  obtain ⟨y, i, a, ip, js, hGm, hRO⟩ := hC.game
  have hdiv : s.count / (s.P.theta + 1 - cmax s.P) ≤ (s.count + 1) / (s.P.theta + 1 - cmax s.P) :=
    Nat.div_le_div_right (Nat.le_succ s.count)
  have hcnt0 : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1 := by omega
  obtain ⟨s1, s2, hrun1, hrun2, hPost, heG, hgC, hE12, hP1⟩ := insert_step hTC hC.low hC.ti hGm hRO hx
    hk hR hn hcnt0 hI5 hh
  have hyL : s.E.size ∈ OrderMaintenance.Spec.insertAfterL x s.E.size L :=
    (OrderMaintenance.Spec.mem_insertAfterL hx).mpr (Or.inl rfl)
  -- the state after the element insertion
  obtain ⟨A, hI, hel⟩ := hC.low.inv
  obtain ⟨gh, hG0⟩ := hC.low.ginv
  obtain ⟨s₀, -, -, -, hGP⟩ := hC.low.cinv
  subst hel
  have hlen := hI.len_lt
  have hxE : x < s.E.size := ((hI.eAlloc x).mp hx).2
  have hgL : LiveG s (eG s x) := hI.mem_glist_iff.mp (hI.eG_mem hx)
  have hgsz : gSz s (eG s x) ≤ A.elist.length := by rw [hG0.sz _ hgL]; exact runOf_len_le _ _ _
  obtain ⟨lab, hrunE, -⟩ := ins_elem_ok hI hG0 hGP hx hh
  rw [hrunE] at hrun1; injection hrun1 with _ e1; subst e1
  obtain ⟨-, hW1, -⟩ := insertElem_wb hW hL hrunE (by omega) (by omega)
    (show gSz s (eG s x) + 1 < 2 ^ K by omega) (by omega)
  obtain ⟨fG, fC, fF, fE, fPQ, fN, fPa, fPr, fP⟩ := linkElem_frame s x s.E.size lab hh
  set s1 := linkElem s x s.E.size lab hh
  rw [heG, hgC] at hrun2
  have hS12 : Same s1 s2 := by have := pres_chunkSize (gC s (eG s x)) true s1; rw [hrun2] at this; exact this
  obtain ⟨s₀', hCI, -⟩ := hC.low.cinv
  have hcL : LiveC s (gC s (eG s x)) := (hCI.gchk _ hgL).1
  have hcsz : cSz s (gC s (eG s x)) ≤ A.elist.length := by
    rw [hCI.csz _ hcL]; exact celts_len_le _ _ _
  obtain ⟨s2', hrun2', hPQ2, -⟩ := chunkSize_ok (lab := lab) (hh := hh) hC.low.pq hcL
  rw [hrun2] at hrun2'; injection hrun2' with _ e2; subst e2
  obtain ⟨-, -, hC2, -, r2⟩ := hPQ2
  obtain ⟨-, -, -, -, -, -, -, hpr2, hjb2, -, hN2, hPa2, hci2, hlp2⟩ := r2
  have hsC : (sizeState s1 (gC s (eG s x))).C.size = s1.C.size := by simp [sizeState]
  have hsN : (sizeState s1 (gC s (eG s x))).nodes = s1.nodes := rfl
  have hsPa : (sizeState s1 (gC s (eG s x))).path = s1.path := rfl
  have hsPr : (sizeState s1 (gC s (eG s x))).prep = s1.prep := rfl
  -- option (B)'s bounds after the chunk size
  have hW2 : WB K s2 := by
    have := wb_chunkSize hW1 (c := gC s (eG s x)) (inc := true) (hW.gChk _)
      (fun _ => show cSz s (gC s (eG s x)) + 1 < 2 ^ K by omega)
    rw [hrun2] at this; exact this
  have hGs2 : s2.Gs.size = s.Gs.size := by rw [hS12.1.Gsize]; exact fG
  obtain ⟨A2, hI2, hel2⟩ := hPost.inv
  have hlen2 := hI2.len_lt
  rw [hel2] at hlen2
  have hEs2 : s2.E.size = s.E.size + 1 := by rw [hE12]; exact fE
  have hTS : TopSame s s2 := (ts_linkElem s x s.E.size lab hh).trans (by
    have := ts_chunkSize (gC s (eG s x)) true (linkElem s x s.E.size lab hh)
    rw [hrun2] at this; exact this)
  -- the background's peak
  have hBG := background_peak (KH := KH) (W := W) hTC hT hTI hPost hyL heG hgC hrun2 hE12 hP1 rfl hn
    (by rw [hPost.count]; exact hsize) (by rw [hPost.count]; exact hcap) hI5
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["y"] [s.E.size]) (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    hpow (KI.pq.of_same fPQ) (by have := hcL.2; have := KI.cC; omega)
    (by rw [fC]; have := KI.cB (gC s (eG s x)) hcL; omega)
    ⟨by rw [fG]; have := KI.G; omega, by rw [fE]; have := KI.E; omega, by rw [fC]; exact KI.C, KI.fl, KI.f0⟩
    (by rw [fG]; exact KI.G) KI.f0 (by rw [fF]; have := hI.freeG_len; have := KI.G; have := KI.fl; omega)
    (by have := KI.E; omega) Mc
    (fun t hD hq hGt => hM4 t (by
        have hPt : t.P = s.P := by rw [hD.P, hPost.P]
        have hNt : t.nodes = s.nodes := by rw [hD.top.1, hN2, hsN, fN]
        have hPat : t.path = s.path := by rw [hD.top.2.1, hPa2, hsPa, fPa]
        have hct : t.cin = s.cin := by rw [hD.top.2.2.1, hci2]; rfl
        have hlt : t.lpar = s.lpar := by rw [hD.top.2.2.2.1, hlp2]; rfl
        have htag : ∀ c, (t.C.getX c).tag = (s.C.getX c).tag := fun c => by
          have := (hD.links c).2.2
          show cT t c = cT s c
          rw [this]; show (s2.C.getX c).tag = _
          rw [hC2]; simp only [sizeState, Array.getX_modify]; rw [fC]; split <;> rfl
        unfold OrderMaintenance.Proof.Top.ts; rw [hPt, hNt, hPat, hct, hlt]; simp only [htag])
      (by rw [hD.top.2.2.2.2.1, hjb2]; rfl)
      (by rw [hD.top.2.2.2.2.2.1, hpr2, hsPr, fPr]) (by rw [hD.Csize, hC2, hsC, fC])
      (by rw [hD.count, hPost.count]) (by rw [fG] at hGt; exact hGt) hq)
    hMc hMpop (hMjob _) (hMsplit _)
    hW2 (by rw [← hP1, fP]; exact hL) (by omega) (by omega) (by rw [hPost.count]; omega)
    (by rw [hTS.top.1, hTS.Csize, hTC.mframe _ _ hTS]; exact hNB) (by rw [hPost.count]; exact hNK)
    hCw hK hWK hcapC hcapT (by rw [← hP1, fP]; exact hRm)
    (by rw [fC]; have h1 : (s.C.getX (gC s (eG s x))).size = cSz s (gC s (eG s x)) := rfl; omega)
  -- the element insertion
  have hFin := fin_insertElem (κ := κ) (KH := KH) (by omega) hrunE hxE hgL.2.1
    (by rcases hI.eN_mem hx with h | h
        · left; exact h
        · right; exact (hI.size_pos h).2)
    (by have := KI.E; omega) (by have := KI.G; omega) hW hL (by omega) (by omega)
    (show gSz s (eG s x) + 1 < 2 ^ K by omega) (by omega)
  obtain ⟨Li, ni, ei, hyi, -⟩ := insertElem_agree κ s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x", "h"] [x, hh])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) hxE hgL.2.1
    (by rcases hI.eN_mem hx with h | h
        · left; exact h
        · right; exact (hI.size_pos h).2)
    (by have := KI.E; omega) (by have := KI.G; omega) hrunE
  have hev : evList κ s Lx [.var "x", .var "h"] = some [x, hh] := by simp [evList, Exp.ev, hLx, hLh]
  have e1 := evalF_call_ok (q := insertElemP) (args := [.var "x", .var "h"]) (ds := ["y"]) (L := Lx) hev ei
  set L1 := OrderMaintenance.Machine.State.setLocs Lx ["y"] (insertElemP.rets.map Li)
  have h1y : L1 "y" = s.E.size := by
    simp [L1, insertElemP, OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd, hyi]
  have hxK : x < 2 ^ K := by have := hGd.loc "x"; simpa [ΓH, hLx] using this
  have hhK : hh < 2 ^ KH := by have := hGd.loc "h"; simpa [ΓH, hLh] using this
  simp only [insertAfterP]
  refine PKok.seq (PKok.catch_bug (PKok.call (Γc := ΓH K KH) hGd hev ?_ ?_ (by simp [insertElemP, ΓH]) (by simp [ΓH])))
    (fun s3 L3 n3 h3 hG3 => ?_)
  · simp only [pkList, List.map, List.foldr, Exp.pk, hLx, hLh]
    exact max_lt (pow_mono_lt hxK (by omega)) (max_lt (pow_mono_lt hhK hKH) (Nat.two_pow_pos _))
  · refine insertElem_pkok hCw hK hWK hKH ⟨hGd.enc, hGd.vb, fun r => ?_⟩ hFin
    simp only [insertElemP, OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]
    by_cases h1 : r = "h"
    · subst h1; simp [ΓH]; exact hhK
    · by_cases h2 : r = "x"
      · subst h2; simp [ΓH]; exact hxK
      · simp [h1, h2]; split <;> exact Nat.two_pow_pos _
  have c1 : evalF κ (.catch (insertElemP.call [.var "x", .var "h"] ["y"]) .bug) s Lx =
      .ok s1 L1 (1 + (1 + costList [.var "x", .var "h"] + 1 + ni)) := by
    simp only [evalF, e1]; rfl
  rw [c1] at h3
  injection h3 with e3 e4; subst e3 e4
  refine PKok.catch_bug (PKok.callS hCw hK hWK (Γc := ΓK K) (Γe := ΓK K) hG3 (by jsafe) (fun _ => le_refl K)
    (fun vs hvs hG0 => ?_) (by simp [bgP]) (by simp))
  simp [evList, Exp.ev, h1y] at hvs
  subst hvs
  exact hBG hG0

/-- **An insertion at the cost proof's top invariant** (the context of `insertAgreeM` and
`insertAfter_wb_top`): its peak. -/
theorem insertAfter_peakM {P : Params} {n R : Nat} {L : List Nat} {s : Core} {x : Nat}
    (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L s) (hsP : s.P = P)
    (hx : x ∈ L) (hk : 1 ≤ s.P.reservationBudget) (hR : topJ P / s.P.reservationBudget + 1 ≤ R)
      (hn : 1 ≤ n)
    (hsize : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ capT s.P)
    (hI5 : (s.P.theta : ℝ) + R * (OrderMaintenance.Zeroing.Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat)
    {κ : Caps} (Lx : Loc) (hLx : Lx "x" = x) (hLh : Lx "h" = hh) (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    (Kc : CapsOK κ P) (hcntL : s.count = L.length) (hcnt : s.count + 1 ≤ P.N) (hM0 : Mc κ P s)
    (hW : WB K s) (hL : LabRoom K s.P) (hTR : TopRoom K P) (hE : 4 * s.E.size + 8 ≤ 2 ^ K)
    (hG : s.Gs.size + 2 ≤ 2 ^ K) (hcnt' : 2 * s.count + 4 ≤ 2 ^ K)
    (hNK : nb0 P + topJ P * (2 + 2 * (s.count + 1)) + 2 ≤ 2 ^ K)
    (hCw : CapsW K κ) (hK8 : 8 ≤ K) (hWK : 2 * K + 4 ≤ W) (hKH : KH ≤ W)
    (hcapC : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512)
    (hGd : Gd K KH κ (ΓH K KH) s Lx) :
    PKok K KH κ (ΓH K KH) W insertAfterP.body s Lx := by
  have hTC : TopContract (TIat TopInv P) topMu (topJ P) capT := topContract'.at P
  have KI : InsCaps κ s := by
    subst hsP; exact insCaps_of Kc hM0 hC.low hcntL hcnt
  have hNB : s.nodes.size + topMu s ≤ nb0 P + topJ P * s.C.size := by
    have := hM0.2.1; unfold OrderMaintenance.Impl.NodeB at this; rw [hsP] at this; exact this
  refine insertAfter_peakG hTC (topWB hTR hL.K1) (fun t h => h.1) hC hx hk hR hn hsize hcap hI5 hh Lx hLx hLh hpow
    KI (Mc κ P) (fun t hts hjob hprt hCs hct hGt hq => ?_) (fun t h => h.caps Kc) (fun t c t1 h hp => mc_pop h hp)
    (fun L' s' j t job r t1 hI hM hjob hr _ => mc_job hI.2.1.1 hM hjob hr)
    (fun L' s' j t c t1 t2 hI hM hnone hp hs hI' => ?_) hW hL hE hG hcnt' hNB hNK hCw hK8 hWK hKH hcapC hcapT
    (by rw [hsP]; exact hTR) hGd
  · -- the start of the reservation
    obtain ⟨-, hNB, -, -, hpr, hPZ, -, hgs⟩ := hM0
    have hPt : t.P = P := by
      have : (OrderMaintenance.Proof.Top.ts t).P = (OrderMaintenance.Proof.Top.ts s).P := by rw [hts]
      exact this.trans hsP
    have hNt : t.nodes = s.nodes := by
      have : (OrderMaintenance.Proof.Top.ts t).nodes = (OrderMaintenance.Proof.Top.ts s).nodes := by rw [hts]
      exact this
    have hmu : topMu t = topMu s := by unfold topMu; rw [hjob, hts]
    have hcbs : s.C.size ≤ cb s.P := cb_of hC.low (by rw [hsP]; omega)
    refine ⟨hPt, ?_, by rw [hCs, ← hsP]; exact hcbs, hq, by rw [hprt]; exact hpr, ?_, by rw [hct]; omega,
      by rw [hct]; omega⟩
    · unfold OrderMaintenance.Impl.NodeB at hNB ⊢; rw [hNt, hmu, hCs, hPt, ← hsP]; exact hNB
    · intro c hc j
      have : (OrderMaintenance.Proof.Top.ts t).path = (OrderMaintenance.Proof.Top.ts s).path := by rw [hts]
      have hpa : t.path = s.path := this
      rw [hpa]; exact hPZ c (by rw [← hCs]; exact hc) j
  · -- a split start
    obtain ⟨hL', hT', hc', hP', y', i', a', ip', js', hG', hR'⟩ := hI'
    obtain ⟨-, -, hc0, hP0, -⟩ := hI
    have hPt : t.P = P := hM.1
    have hP2 : t2.P = P := by rw [hP', ← hP0, hPt]
    have hc2 : t2.count ≤ P.N := by rw [hc', ← hc0]; exact hM.2.2.2.2.2.2.1
    refine mc_split hM hnone hp hs hP2 ?_ (by have := cb_of hL' (by rw [hP2]; exact hc2); rwa [hP2] at this) hc2
      (by rw [hc', hc0])
    rcases hj : t2.resJob with _ | j'
    · have : topMu t2 = 0 := by unfold topMu; rw [hj]
      omega
    · unfold RoundAt at hR'; rw [hj] at hR'
      have := hR'.2.1; omega

/-- The numeric room of a core in service at a word size `K ≥ wK c.P`. -/
theorem _root_.OrderMaintenance.Impl.InService.room_at {c : Core} {L : List Nat} (h : InService c L) (hKw : wK c.P ≤ K) :
    LabRoom K c.P ∧ TopRoom K c.P ∧ 4 * c.E.size + 8 ≤ 2 ^ K ∧ c.Gs.size + 2 ≤ 2 ^ K ∧
      2 * c.count + 4 ≤ 2 ^ K ∧ nb0 c.P + topJ c.P * (2 + 2 * (c.count + 1)) + 2 ≤ 2 ^ K := by
  have hmk : c.P = proofParams c.P.N := h.ok.pmk
  obtain ⟨hLR, hTR, -⟩ := room_wK c.P.N
  rw [← hmk] at hLR hTR
  obtain ⟨A, hI, hel⟩ := h.ok.cost.low.inv
  have hE := E_size_le hI
  rw [hel, ← h.ok.cnt] at hE
  obtain ⟨-, -, -, -, -, -, -, hGs⟩ := h.mc
  obtain ⟨r1, r2, r3, r4⟩ := room_counts c.P.N h.room hE hGs
  rw [← hmk] at r1 r2 r3 r4
  have hp : 2 ^ wK c.P ≤ 2 ^ K := pow_le_pow' hKw
  exact ⟨⟨by have := hLR.K1; omega, le_trans hLR.Be hKw, le_trans hLR.Bg hKw⟩,
    ⟨le_trans hTR.beta hKw, le_trans hTR.tag hKw⟩, le_trans r1 hp, le_trans r2 hp, le_trans r3 hp, le_trans r4 hp⟩

/-- **An insertion into a core in service**: its peak, at any word size `K ≥ wK c.P` at which
the core's stored values are small. -/
theorem _root_.OrderMaintenance.Impl.InService.peak {c : Core} {L : List Nat} (h : InService c L) {x : Nat} (hx : x ∈ L)
    (hh : Nat) (Lx : Loc) (hLx : Lx "x" = x) (hLh : Lx "h" = hh) (hKw : wK c.P ≤ K) (hW : WB K c)
    (hCw : CapsW K (capsOf c.P)) (hK8 : 8 ≤ K) (hWK : 2 * K + 4 ≤ W) (hKH : KH ≤ W)
    (hGd : Gd K KH (capsOf c.P) (ΓH K KH) c Lx) :
    PKok K KH (capsOf c.P) (ΓH K KH) W insertAfterP.body c Lx := by
  obtain ⟨hk, hR, hn, hsize, hcap, hI5, hpow⟩ := h.params
  obtain ⟨hLR, hTR, r1, r2, r3, r4⟩ := h.room_at hKw
  exact insertAfter_peakM h.ok.cost rfl hx hk hR hn hsize hcap hI5 hh Lx hLx hLh hpow (capsOf_ok c.P)
    h.ok.cnt h.room h.mc hW hLR hTR r1 r2 r3 r4 hCw hK8 hWK hKH (by simp [capsOf]) (by simp [capsOf]) hGd

end OrderMaintenance.Proof.Word

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Word OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg)

variable {K KH : Nat}

/-- `PRoom` is monotone in the word size (for `proom_wK` at a larger `K`). -/
theorem PRoom.mono {K K' : Nat} {P : Params} (h : PRoom K P) (hK : K ≤ K') : PRoom K' P :=
  ⟨le_trans h.Be hK, le_trans h.Bg hK, le_trans h.beta hK, le_trans h.beta9 hK, le_trans h.Hb hK, h.Be1, h.Bg1,
    h.beta1, le_trans h.aH hK⟩

/-- **`insertAfter`**, into a core in service (`InService`, the wrapper's Level M invariant for
every core insertion), at a word size `K ≥ wK s.P`, after an element `x` of its list, with a
handle `hb < 2^KH`: the peak bound of the other wrappers (`PeakTop.lean`), `2^(max (2K+4) KH)`. -/
theorem insertAfter_peak {p : Nat} {m : OrderMaintenance.Machine.State} {s : Core} {L : List Nat} {x hb : Nat}
    (hC : CapsW K (capsOf s.P)) (hK : 8 ≤ K) (hE : Enc p (capsOf s.P) s m) (hWB : WB K s)
    (hh : ∀ i, (s.E.getX i).h < 2 ^ KH) (hR : PRoom K s.P)
    (hS : InService s L) (hx : x ∈ L) (hKw : wK s.P ≤ K) (hbK : hb < 2 ^ KH)
    {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF (capsOf s.P) insertAfterP.body s
      (OrderMaintenance.Machine.State.setLocs (fun _ => 0) insertAfterP.params [x, hb]) = .ok s' L' n) :
    pkF (capsOf s.P) insertAfterP.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) insertAfterP.params [x, hb]) <
      2 ^ wPk K KH := by
  -- the element `x` is below `2^K`
  obtain ⟨-, -, r1, -⟩ := hS.room_at hKw
  obtain ⟨A, hI, hel⟩ := hS.ok.cost.low.inv
  have hxE : x < s.E.size := ((hI.eAlloc x).mp (hel ▸ hx)).2
  have hxK : x < 2 ^ K := by omega
  have hL0 : ∀ r, OrderMaintenance.Machine.State.setLocs (fun _ => 0) insertAfterP.params [x, hb] r < 2 ^ ΓH K KH r := by
    intro r
    simp only [insertAfterP, OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]
    by_cases h1 : r = "h"
    · subst h1; simp [ΓH]; exact hbK
    · by_cases h2 : r = "x"
      · subst h2; simp [ΓH]; exact hxK
      · simp [h1, h2]; split <;> exact Nat.two_pow_pos _
  exact pk_of_PKok (hS.peak hx hb _ (by simp [insertAfterP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [insertAfterP, OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) hKw hWB hC hK (wPk_ge K KH)
    (wPk_geH K KH) (gd_of_WB hE hWB (by omega) hh hR hL0)) he

end OrderMaintenance.Impl

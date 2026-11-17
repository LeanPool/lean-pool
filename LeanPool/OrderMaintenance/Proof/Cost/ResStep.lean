/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Pop


/-!
# The reservation, one iteration at a time

The lower invariants (`LowInv`: INV-S, Lemmas G and C1–C3, the queue, the chunk count) survive the
top structure's steps, which change only top-structure fields and chunk tags.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The invariants below the top structure, with no undriven insertion. -/
structure LowInv (s : Core) (L : List Nat) : Prop where
  inv : ∃ A, INV s A ∧ A.elist = L
  ginv : ∃ gh, GInv s L gh (fun _ => 0)
  cinv : ∃ s₀, CInv s L (fun _ => 0) (fun _ => 0) s₀ ∧ LX s₀ (fun _ => 0) (fun _ => 0) s
  pq : PQC s
  cnt : ∃ e pops, CountInv s e pops
  cp : CParams s.P

theorem TopRel.gsame {s s' : Core} (h : TopRel s s') : GSame s s' := by
  have hG : ∀ g, s'.Gs.getX g = s.Gs.getX g := fun g => by rw [h.Gs]
  have hE : ∀ e, s'.E.getX e = s.E.getX e := fun e => by rw [h.E]
  refine ⟨by rw [h.Gs], fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_,
    fun g => ?_, fun g => ?_, fun g => ?_, fun e => ?_, fun e => ?_, h.rest.2.2.1, h.rest.1⟩ <;>
    simp only [gSz, gSt, gSrc, gLl, gRr, gN, gC, gA, eG, eL, hG, hE]

theorem TopRel.csame {s s' : Core} (h : TopRel s s') : CSame s s' := by
  refine ⟨h.Csize, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_,
    h.rest.1⟩ <;> simp only [cSz, cSt, cSrc, cLl, cRr, cN] <;> rw [h.C c]

theorem TopRel.qsame {s s' : Core} (h : TopRel s s') : QSame s s' := by
  refine ⟨h.Csize, h.rest.1, fun c _ => ?_, fun c _ _ => ?_⟩
  · simp only [cSt]; rw [h.C c]
  · simp only [cSz]; rw [h.C c]

theorem TopRel.pqsame {s s' : Core} (h : TopRel s s') : PQSame s s' := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := h.pq
  exact ⟨p4, p2, p3, p1, p5, p6, p8, p7, by rw [h.rest.1]⟩

/-- The fields below the top structure, but for chunk tags and the queue. -/
structure LowSame (s s' : Core) : Prop where
  E : s'.E = s.E
  Gs : s'.Gs = s.Gs
  Csize : s'.C.size = s.C.size
  C : ∀ c, s'.C.getX c = { s.C.getX c with tag := (s'.C.getX c).tag }
  P : s'.P = s.P
  count : s'.count = s.count
  head : s'.head = s.head

theorem LowSame.topRel {s s' : Core} (h : LowSame s s') (hpq : s'.pqHead = s.pqHead ∧
    s'.pqNext = s.pqNext ∧ s'.pqPrev = s.pqPrev ∧ s'.pqWhere = s.pqWhere ∧ s'.nbNext = s.nbNext ∧
    s'.nbPrev = s.nbPrev ∧ s'.pqHi = s.pqHi ∧ s'.pqLo = s.pqLo)
    (hr : s'.tail = s.tail ∧ s'.firstGroup = s.firstGroup ∧ s'.firstChunk = s.firstChunk ∧
      s'.freeG = s.freeG ∧ s'.fallbacks = s.fallbacks ∧ s'.ready = s.ready) : TopRel s s' :=
  ⟨h.E, h.Gs, h.Csize, h.C, hpq, ⟨h.P, h.count, h.head, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2⟩⟩

theorem TopRel.lowSame {s s' : Core} (h : TopRel s s') : LowSame s s' :=
  ⟨h.E, h.Gs, h.Csize, h.C, h.rest.1, h.rest.2.1, h.rest.2.2.1⟩

theorem LowSame.gsame {s s' : Core} (h : LowSame s s') : GSame s s' := by
  have hG : ∀ g, s'.Gs.getX g = s.Gs.getX g := fun g => by rw [h.Gs]
  have hE : ∀ e, s'.E.getX e = s.E.getX e := fun e => by rw [h.E]
  refine ⟨by rw [h.Gs], fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_,
    fun g => ?_, fun g => ?_, fun g => ?_, fun e => ?_, fun e => ?_, h.head, h.P⟩ <;>
    simp only [gSz, gSt, gSrc, gLl, gRr, gN, gC, gA, eG, eL, hG, hE]

theorem LowSame.csame {s s' : Core} (h : LowSame s s') : CSame s s' := by
  refine ⟨h.Csize, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_,
    h.P⟩ <;> simp only [cSz, cSt, cSrc, cLl, cRr, cN] <;> rw [h.C c]

theorem LowSame.qsame {s s' : Core} (h : LowSame s s') : QSame s s' := by
  refine ⟨h.Csize, h.P, fun c _ => ?_, fun c _ _ => ?_⟩
  · simp only [cSt]; rw [h.C c]
  · simp only [cSz]; rw [h.C c]

theorem LowSame.lsame {s s' : Core} (h : LowSame s s') : LSame s s' := by
  refine ⟨h.Gs, h.P, h.Csize, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_,
    fun c => ?_⟩ <;> simp only [cSz, cSt, cSrc, cLl, cRr, cLs] <;> rw [h.C c]

/-- **The lower invariants across a step below the top structure that changes only tags and the
queue**, given the queue invariant after it. -/
theorem LowInv.transfer {s s' : Core} {L : List Nat} (h : LowInv s L) (hS : LowSame s s')
    (hI : ∃ A, INV s' A ∧ A.elist = L) (hpq : PQC s') : LowInv s' L := by
  obtain ⟨gh, hG⟩ := h.ginv
  obtain ⟨s₀, hC, ⟨lg, hL⟩, hLP, hP⟩ := h.cinv
  obtain ⟨e, pops, hN⟩ := h.cnt
  have hPe := hS.P
  have hGS := hS.gsame
  refine ⟨hI, ⟨gh, hG.of_gsame hGS⟩, ⟨s₀, ?_, ⟨lg, hL.transfer hS.lsame⟩, by rw [hPe]; exact hLP,
    by rw [hPe]; exact hP⟩, hpq, ⟨e, pops, hN.frame hS.qsame hS.count⟩, by rw [hPe]; exact h.cp⟩
  refine hC.transfer hS.csame (fun c => ?_) (fun c => ?_) hC.δu (fun g hg => ?_)
  · unfold celts; congr 1; funext x; rw [hGS.chk, hGS.eG]
  · rw [units_of_Gs hS.Gs]
  · have hg' : LiveG s g := (liveG_of_Gs hS.Gs g).mp hg
    rw [hGS.chk]; exact hC.gchk g hg'

/-- **The lower invariants across a top-structure step.** -/
theorem LowInv.top {s s' : Core} {L : List Nat} (h : LowInv s L) (hT : TopRel s s')
    (hI : ∃ A, INV s' A ∧ A.elist = L) : LowInv s' L :=
  h.transfer hT.lowSame hI (h.pq.qsame hT.pqsame hT.qsame)

/-- With an empty queue, every game value is 0. -/
theorem gval_zero_of_empty {s : Core} (h : PQC s) (h0 : s.pqHi = 0) (c : Nat) : gval s c = 0 := by
  obtain ⟨bl, nb, hQ⟩ := h
  have := (hQ.empty_iff.mp h0) c
  unfold inQC at this; unfold gval
  simp only [decide_eq_false_iff_not, not_and, not_lt] at this
  split
  · next hc => have := this hc.1 hc.2; omega
  · rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem PQOnly.sameLinks {s s' : Core} (h : PQOnly s s') : SameLinks s s' := by
  obtain ⟨hE, hG, hC, hP, r1, -, r3, r4, r5, r6, -⟩ := h
  refine ⟨by rw [hE], ?_, ?_, ?_, ?_, ?_, ?_, by rw [hG], ?_, ?_, ?_, ?_, ?_, ?_, ?_, r1, r3, r4,
    r5, r6, by rw [hC], ?_, ?_, ?_, ?_, hP⟩ <;> intro i <;>
    simp only [eN, eP, eG, eL, gN, gP, gF, gLs, gC, gL, gA, cN, cP, cF, cLs, hE, hG, hC]

theorem PQOnly.topSame {s s' : Core} (h : PQOnly s s') : TopSame s s' := by
  obtain ⟨hE, hG, hC, hP, -, -, -, -, -, r6, r7, r8, r9, -, n1, n2, n3, n4⟩ := h
  refine ⟨⟨n1, n2, n3, n4, r9, r8, r7, r6⟩, by rw [hC], fun c => ?_, hP⟩
  simp only [cN, cP, cT, hC, and_self]

theorem PQOnly.lowSame {s s' : Core} (h : PQOnly s s') : LowSame s s' :=
  ⟨h.E, h.Gs, by rw [h.C], fun c => by rw [h.C], h.P, h.rest.2.1, h.rest.2.2.1⟩

/-- The fields a chunk split start keeps. -/
theorem split_rest {s s2 : Core} {x : Nat} {job : Job}
    (hT : TopRel (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s2) :
    (markState s2 x s.C.size (s.C.size + 1) job).E = s.E ∧
      (markState s2 x s.C.size (s.C.size + 1) job).count = s.count ∧
      (markState s2 x s.C.size (s.C.size + 1) job).head = s.head ∧
      (markState s2 x s.C.size (s.C.size + 1) job).P = s.P := by
  obtain ⟨hE, -, -, -, -, ⟨hP, hc, hh, -⟩⟩ := hT
  exact ⟨hE, hc, hh, hP⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem GSame.of_eq {s s' : Core} (hG : s'.Gs = s.Gs) (hE : s'.E = s.E) (hh : s'.head = s.head)
    (hP : s'.P = s.P) : GSame s s' := by
  have hG' : ∀ g, s'.Gs.getX g = s.Gs.getX g := fun g => by rw [hG]
  have hE' : ∀ e, s'.E.getX e = s.E.getX e := fun e => by rw [hE]
  exact ⟨by rw [hG], fun g => by simp only [gSz, hG'], fun g => by simp only [gSt, hG'],
    fun g => by simp only [gSrc, hG'], fun g => by simp only [gLl, hG'], fun g => by simp only
      [gRr, hG'],
    fun g => by simp only [gN, hG'], fun g => by simp only [gC, hG'], fun g => by simp only [gA,
      hG'],
    fun e => by change (s'.E.getX e).grp = (s.E.getX e).grp; rw [hE'],
    fun e => by change (s'.E.getX e).lab = (s.E.getX e).lab; rw [hE'], hh, hP⟩

/-- **The lower invariants after a pop and the split start.** -/
theorem lowinv_pop {t s2 : Core} {L : List Nat} {c : Nat} {job : Job} (h : LowInv t L)
    (hGP : GParams t.P) (hc : inQC t c = true) (hT5 : cSz t c ≤ t.P.T)
    (hs2 : TopRel (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size
      ((delSt t c).C.size + 1)) s2)
    (hrun : (splitChunkStart c).run (delSt t c) =
      .ok () (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job)) :
    LowInv (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job) L := by
  have hD := delSt_only t c
  have hDS := hD.lowSame
  obtain ⟨A, hI, hel⟩ := h.inv
  obtain ⟨gh, hG⟩ := h.ginv
  obtain ⟨s₀, hC, ⟨lg, hL⟩, hLP, hPP⟩ := h.cinv
  obtain ⟨e, pops, hN⟩ := h.cnt
  obtain ⟨bl, nb, hQ⟩ := h.pq
  have hcq' := hc
  unfold inQC at hcq'; simp only [decide_eq_true_eq] at hcq'
  obtain ⟨hcL, hcq, hθ⟩ := hcq'
  -- the invariants at the state after the deletion from the queue
  have hI1 : INV (delSt t c) A := hI.of_sameLinks hD.sameLinks (fun d => by simp only [cT, hD.C])
  have hG1 : GInv (delSt t c) L gh (fun _ => 0) := hG.of_gsame hDS.gsame
  have hC1 : CInv (delSt t c) A.elist (fun _ => 0) (fun _ => 0) s₀ := by
    rw [hel]
    refine hC.transfer hDS.csame (fun d => ?_) (fun d => ?_) hC.δu (fun g hg => ?_)
    · unfold celts; congr 1; funext x; rw [hDS.gsame.chk, hDS.gsame.eG]
    · rw [units_of_Gs hDS.Gs]
    · rw [hDS.gsame.chk]; exact hC.gchk g ((liveG_of_Gs hDS.Gs g).mp hg)
  have hL1 : LInv (delSt t c) lg s₀ (fun _ => 0) (fun _ => 0) := hL.transfer hDS.lsame
  have hN1 : CountInv (delSt t c) e pops := hN.frame hDS.qsame hDS.count
  have hQS := hDS.qsame
  have hcL1 : LiveC (delSt t c) c := by simp only [LiveC, hQS.Csize]; exact hcL
  have hcq1 : cSt (delSt t c) c = .quiet := (hQS.q c hcL).mpr hcq
  have hsz1 : cSz (delSt t c) c = cSz t c := hQS.sz c hcL hcq
  have hP1 : (delSt t c).P = t.P := hD.P
  have hcA : c ∈ A.chunks := (hI1.cAlloc c).mpr hcL1
  have R := resSpec_run (job := job) hI1 hcA hs2
  obtain ⟨rE, rcnt, rhead, rP⟩ := split_rest (job := job) hs2
  -- INV-S after the split start
  have hgood := good_splitChunkStart c (delSt t c) A hI1
  rw [hrun] at hgood
  obtain ⟨-, A', hI2, hel2⟩ := hgood
  have hun1 : units (delSt t c) c ≤ unitsOf (delSt t c).P (cSz (delSt t c) c) :=
    units_le_unitsOf hI1 (hel ▸ hG1) hC1 (by rw [hP1]; exact hGP) hcL1
  refine ⟨⟨A', hI2, hel2.trans hel⟩, ⟨gh, hG1.of_gsame (GSame.of_eq R.Gs rE rhead rP)⟩,
    ⟨Function.update s₀ c (cSz (delSt t c) c), ?_,
      ⟨lg.fresh (delSt t c).C.size ((delSt t c).C.size + 1), ?_⟩, by rw [rP, hP1]; exact hLP,
      by rw [rP, hP1]; exact hPP⟩, ?_, ⟨e, pops + 1, ?_⟩, by rw [rP, hP1]; exact h.cp⟩
  · rw [← hel]
    exact cinv_pop hI1 R rE hC1 hcL1 hcq1 (by rw [hsz1, hP1]; exact hT5) hun1
  · exact linv_pop (A := A) R hC1 hL1 hcL1 hcq1 hun1
  · exact pqc_pop hQ hc R (pqsame_split hs2)
  · exact hN1.pop R hcL1 hcq1 (by rw [hsz1, hP1]; exact hθ) rcnt

end OrderMaintenance.Proof

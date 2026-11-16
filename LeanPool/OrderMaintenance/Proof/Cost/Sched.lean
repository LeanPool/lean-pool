/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.LHooks


/-!
# Scheduling: the priority queue and the zeroing game

The queue holds exactly the quiet chunks above `θ`, keyed by their sizes (`PQC`). So `pqPopMax`
returns a chunk of largest game value, and `pqEmpty` says that every value is 0. Every step but
the insertion's size update and the pop leaves the queue, and the quiet sizes it reads, alone.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The chunks the queue must hold: live, quiet, above `θ`. -/
def inQC (s : Core) (c : Nat) : Bool := decide (LiveC s c ∧ cSt s c = .quiet ∧ s.P.theta < cSz s c)

/-- **The queue invariant.** -/
def PQC (s : Core) : Prop := QInv s (cSz s) (inQC s)

/-- The queue's own fields. -/
structure PQSame (s s' : Core) : Prop where
  where_ : s'.pqWhere = s.pqWhere
  next : s'.pqNext = s.pqNext
  prev : s'.pqPrev = s.pqPrev
  head : s'.pqHead = s.pqHead
  nbn : s'.nbNext = s.nbNext
  nbp : s'.nbPrev = s.nbPrev
  lo : s'.pqLo = s.pqLo
  hi : s'.pqHi = s.pqHi
  theta : s'.P.theta = s.P.theta

theorem QRep.congr {s s' : Core} {k k' : Nat → Nat} {inQ inQ' : Nat → Bool} {bl : Nat → List Nat}
    {nb : List Nat} (hQ : QRep s k inQ bl nb) (S : PQSame s s') (hin : ∀ c, inQ' c = inQ c)
    (hk : ∀ c, inQ c = true → k' c = k c) : QRep s' k' inQ' bl nb where
  where_ c := by
    rw [S.where_, hQ.where_, hin]
    by_cases h : inQ c = true
    · rw [ite_eq_left h, ite_eq_left h, hk c h]
    · rw [ite_eq_right h, ite_eq_right h]
  pos c h := by rw [hin] at h; rw [S.theta, hk c h]; exact hQ.pos c h
  bucket b := by rw [S.next, S.prev, S.head]; exact hQ.bucket b
  bmem b c := by
    rw [hQ.bmem, hin]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [hk c h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← hk c h1]; exact h2⟩
  nbl := by rw [S.nbn, S.nbp, S.lo]; exact hQ.nbl
  nbmem := hQ.nbmem
  sorted := hQ.sorted
  hi := by rw [S.hi]; exact hQ.hi

theorem QInv.congr {s s' : Core} {k k' : Nat → Nat} {inQ inQ' : Nat → Bool}
    (hQ : QInv s k inQ) (S : PQSame s s') (hin : ∀ c, inQ' c = inQ c)
    (hk : ∀ c, inQ c = true → k' c = k c) : QInv s' k' inQ' := by
  obtain ⟨bl, nb, h⟩ := hQ; exact ⟨bl, nb, h.congr S hin hk⟩

theorem PQSame.refl (s : Core) : PQSame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PQSame.trans {a b c : Core} (h1 : PQSame a b) (h2 : PQSame b c) : PQSame a c :=
  ⟨h2.where_.trans h1.where_, h2.next.trans h1.next, h2.prev.trans h1.prev, h2.head.trans h1.head,
    h2.nbn.trans h1.nbn, h2.nbp.trans h1.nbp, h2.lo.trans h1.lo, h2.hi.trans h1.hi,
    h2.theta.trans h1.theta⟩

/-- **A frame for the queue invariant**: the queue's fields are unchanged, and so are the queued
chunks and their sizes. -/
theorem PQC.frame {s s' : Core} (h : PQC s) (S : PQSame s s')
    (hin : ∀ c, inQC s' c = inQC s c) (hk : ∀ c, inQC s c = true → cSz s' c = cSz s c) :
    PQC s' := QInv.congr h S hin hk

/-- What `PQC` and the game read of the chunks. -/
structure QSame (s s' : Core) : Prop where
  Csize : s'.C.size = s.C.size
  P : s'.P = s.P
  q : ∀ c, LiveC s c → (cSt s' c = .quiet ↔ cSt s c = .quiet)
  sz : ∀ c, LiveC s c → cSt s c = .quiet → cSz s' c = cSz s c

theorem QSame.inQC {s s' : Core} (h : QSame s s') (c : Nat) : inQC s' c = inQC s c := by
  unfold OrderMaintenance.Proof.inQC
  have hL : LiveC s' c ↔ LiveC s c := by simp only [LiveC, h.Csize]
  by_cases hc : LiveC s c
  · by_cases hq : cSt s c = .quiet
    · rw [h.sz c hc hq, h.P]; simp [hc, hq, hL.mpr hc, (h.q c hc).mpr hq]
    · have : ¬ cSt s' c = .quiet := fun e => hq ((h.q c hc).mp e)
      simp [hq, this]
  · have : ¬ LiveC s' c := fun e => hc (hL.mp e)
    simp [hc, this]

theorem PQC.qsame {s s' : Core} (h : PQC s) (S : PQSame s s') (Q : QSame s s') : PQC s' :=
  h.frame S Q.inQC (fun c hc => by
    unfold OrderMaintenance.Proof.inQC at hc; simp only [decide_eq_true_eq] at hc
    exact Q.sz c hc.1 hc.2.1)

/-- The game values agree when the quiet sizes do. -/
theorem QSame.gval {s s' : Core} (h : QSame s s') (c : Nat) : gval s' c = gval s c := by
  unfold OrderMaintenance.Proof.gval
  have hL : LiveC s' c ↔ LiveC s c := by simp only [LiveC, h.Csize]
  by_cases hc : LiveC s c
  · by_cases hq : cSt s c = .quiet
    · rw [h.sz c hc hq, h.P]; simp [hc, hq, hL.mpr hc, (h.q c hc).mpr hq]
    · have : ¬ cSt s' c = .quiet := fun e => hq ((h.q c hc).mp e)
      simp [hq, this]
  · have : ¬ LiveC s' c := fun e => hc (hL.mp e)
    simp [hc, this]

theorem QSame.gvec {s s' : Core} (h : QSame s s') (n : Nat) : gvec n s' = gvec n s := by
  funext i; unfold OrderMaintenance.Proof.gvec; rw [h.gval]

theorem QSame.refl (s : Core) : QSame s s := ⟨rfl, rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

theorem QSame.trans {a b c : Core} (h1 : QSame a b) (h2 : QSame b c) : QSame a c := by
  have hL : ∀ d, LiveC a d → LiveC b d := fun d hd => by simp only [LiveC, h1.Csize]; exact hd
  refine ⟨h2.Csize.trans h1.Csize, h2.P.trans h1.P, fun d hd => (h2.q d (hL d hd)).trans (h1.q d hd),
    fun d hd hq => ?_⟩
  rw [h2.sz d (hL d hd) ((h1.q d hd).mpr hq), h1.sz d hd hq]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### What the group phase leaves alone -/

/-- Chunk fields other than `first`/`last`, the queue and the top structure are unchanged. -/
structure CFrame (s s' : Core) : Prop where
  C : ∀ c, cSz s' c = cSz s c ∧ cSt s' c = cSt s c ∧ cSrc s' c = cSrc s c ∧ cLl s' c = cLl s c ∧
    cRr s' c = cRr s c ∧ cN s' c = cN s c ∧ cP s' c = cP s c ∧ cT s' c = cT s c
  Csize : s'.C.size = s.C.size
  P : s'.P = s.P
  pq : PQSame s s'
  top : s'.nodes = s.nodes ∧ s'.path = s.path ∧ s'.cin = s.cin ∧ s'.lpar = s.lpar ∧
    s'.resJob = s.resJob ∧ s'.prep = s.prep ∧ s'.ready = s.ready ∧ s'.firstChunk = s.firstChunk
  count : s'.count = s.count

theorem CFrame.refl (s : Core) : CFrame s s :=
  ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, PQSame.refl s,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem CFrame.trans {a b c : Core} (h1 : CFrame a b) (h2 : CFrame b c) : CFrame a c := by
  obtain ⟨C1, s1, P1, q1, ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩, c1⟩ := h1
  obtain ⟨C2, s2, P2, q2, ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩, c2⟩ := h2
  refine ⟨fun d => ?_, s2.trans s1, P2.trans P1, q1.trans q2,
    ⟨u1.trans t1, u2.trans t2, u3.trans t3, u4.trans t4, u5.trans t5, u6.trans t6, u7.trans t7,
      u8.trans t8⟩, c2.trans c1⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := C1 d
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := C2 d
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
    b8.trans a8⟩

theorem CFrame.qsame {s s' : Core} (h : CFrame s s') : QSame s s' :=
  ⟨h.Csize, h.P, fun c _ => by rw [(h.C c).2.1], fun c _ _ => (h.C c).1⟩

/-- A frame from equal chunk arrays. -/
theorem CFrame.of_C {s s' : Core} (hC : s'.C = s.C) (hP : s'.P = s.P) (hq : PQSame s s')
    (ht : s'.nodes = s.nodes ∧ s'.path = s.path ∧ s'.cin = s.cin ∧ s'.lpar = s.lpar ∧
      s'.resJob = s.resJob ∧ s'.prep = s.prep ∧ s'.ready = s.ready ∧
      s'.firstChunk = s.firstChunk) (hcnt : s'.count = s.count) : CFrame s s' :=
  ⟨fun c => by simp only [cSz, cSt, cSrc, cLl, cRr, cN, cP, cT, hC, and_self], by rw [hC], hP, hq,
    ht, hcnt⟩

theorem unlinkGroup_cfields (s : Core) (g z : Nat) :
    cSz (unlinkGroup s g) z = cSz s z ∧ cSt (unlinkGroup s g) z = cSt s z ∧
      cSrc (unlinkGroup s g) z = cSrc s z ∧ cLl (unlinkGroup s g) z = cLl s z ∧
      cRr (unlinkGroup s g) z = cRr s z ∧ cN (unlinkGroup s g) z = cN s z ∧
      cP (unlinkGroup s g) z = cP s z ∧ cT (unlinkGroup s g) z = cT s z := by
  simp only [cSz, cSt, cSrc, cLl, cRr, cN, cP, cT, unlinkGroup]
  split_ifs <;> simp only [Array.getX_modify] <;> (try split) <;> simp

theorem cframe_remove (s : Core) (p : Nat) : CFrame s (removeState s p) := by
  have hC : (removeState s p).C = (unlinkGroup s p).C := rfl
  have hu := unlinkGroup_cfields s p
  have hfc : (removeState s p).firstChunk = (unlinkGroup s p).firstChunk := rfl
  have hfc' : (unlinkGroup s p).firstChunk = s.firstChunk :=
    (unlinkGroup_rest (s := s) (g := p)).2.2.2.2.2.1
  have hpq : PQSame s (removeState s p) := by
    unfold removeState unlinkGroup; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have htop : (removeState s p).nodes = s.nodes ∧ (removeState s p).path = s.path ∧
      (removeState s p).cin = s.cin ∧ (removeState s p).lpar = s.lpar ∧
      (removeState s p).resJob = s.resJob ∧ (removeState s p).prep = s.prep ∧
      (removeState s p).ready = s.ready := by
    unfold removeState unlinkGroup; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcnt : (removeState s p).count = s.count := by unfold removeState unlinkGroup; rfl
  refine ⟨fun c => ?_, by rw [hC]; exact (unlinkGroup_rest (s := s) (g := p)).2.1, rfl, hpq,
    ⟨htop.1, htop.2.1, htop.2.2.1, htop.2.2.2.1, htop.2.2.2.2.1, htop.2.2.2.2.2.1,
      htop.2.2.2.2.2.2, hfc.trans hfc'⟩, hcnt⟩
  simp only [cSz, cSt, cSrc, cLl, cRr, cN, cP, cT, hC]
  exact hu c

theorem cframe_moveL (s : Core) (p : Nat) : CFrame s (moveLState s p) :=
  CFrame.of_C rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

theorem cframe_moveR (s : Core) (p : Nat) : CFrame s (moveRState s p) :=
  CFrame.of_C rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

theorem allocGroup_frame (s : Core) (c : Nat) :
    PQSame s (allocGroup s c).2 ∧ (allocGroup s c).2.nodes = s.nodes ∧
      (allocGroup s c).2.path = s.path ∧ (allocGroup s c).2.cin = s.cin ∧
      (allocGroup s c).2.lpar = s.lpar ∧ (allocGroup s c).2.resJob = s.resJob ∧
      (allocGroup s c).2.prep = s.prep ∧ (allocGroup s c).2.ready = s.ready ∧
      (allocGroup s c).2.firstChunk = s.firstChunk ∧ (allocGroup s c).2.count = s.count := by
  unfold allocGroup
  split <;> exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

theorem linkGroupPair_frame (t : Core) (g gl gr labL labR : Nat) :
    PQSame t (linkGroupPair t g gl gr labL labR) ∧ (linkGroupPair t g gl gr labL labR).nodes = t.nodes ∧
      (linkGroupPair t g gl gr labL labR).path = t.path ∧
      (linkGroupPair t g gl gr labL labR).cin = t.cin ∧
      (linkGroupPair t g gl gr labL labR).lpar = t.lpar ∧
      (linkGroupPair t g gl gr labL labR).resJob = t.resJob ∧
      (linkGroupPair t g gl gr labL labR).prep = t.prep ∧
      (linkGroupPair t g gl gr labL labR).ready = t.ready ∧
      (linkGroupPair t g gl gr labL labR).firstChunk = t.firstChunk ∧
      (linkGroupPair t g gl gr labL labR).count = t.count := by
  unfold linkGroupPair
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cframe_split {s : Core} {A : Abs} {g labL labR : Nat} (hI : INV s A) (hg : LiveG s g) :
    CFrame s (splitState s g labL labR) := by
  have S := splitSpec hI (hI.mem_glist_iff.mpr hg) labL labR
  obtain ⟨q1, n1, p1, c1, l1, r1, pr1, rd1, f1, k1⟩ := allocGroup_frame s (gC s g)
  obtain ⟨q2, n2, p2, c2, l2, r2, pr2, rd2, f2, k2⟩ :=
    allocGroup_frame (allocGroup s (gC s g)).2 (gC s g)
  obtain ⟨q3, n3, p3, c3, l3, r3, pr3, rd3, f3, k3⟩ := linkGroupPair_frame
    (allocGroup (allocGroup s (gC s g)).2 (gC s g)).2 g (splitL s g) (splitR s g) labL labR
  refine ⟨fun c => ?_, S.Csize, S.P, q1.trans (q2.trans q3), ⟨(n3.trans n2).trans n1,
    (p3.trans p2).trans p1, (c3.trans c2).trans c1, (l3.trans l2).trans l1, (r3.trans r2).trans r1,
    (pr3.trans pr2).trans pr1, (rd3.trans rd2).trans rd1, (f3.trans f2).trans f1⟩,
    (k3.trans k2).trans k1⟩
  simp only [cSz, cSt, cSrc, cLl, cRr, cN, cP, cT, S.C]
  split <;> simp

/-- **The group phase leaves the chunk fields, the queue and the top structure alone.** -/
theorem xgroup_frame {L : List Nat} {c : Nat} (s₀ : Core) :
    XGroup (CFrame s₀) (CFrame s₀) L c := by
  refine ⟨fun δ p => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t _ _ _ _ _ _ _ hX; exact hX.trans (cframe_moveL t p)
  · intro t _ _ _ _ _ _ _ hX; exact hX.trans (cframe_moveR t p)
  · intro t _ _ _ _ _ _ _ _ _ _ _ _ _ hX; exact hX.trans (cframe_remove t p)
  · intro t A _ g labL labR hI _ _ hg _ _ _ _ hX; exact hX.trans (cframe_split hI hg)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### What the chunk drive leaves alone -/

/-- The queue, the top structure and the chunk list are unchanged, and so are the queued chunks,
their sizes and the game values. -/
structure DFrame (s s' : Core) : Prop where
  Csize : s'.C.size = s.C.size
  P : s'.P = s.P
  pq : PQSame s s'
  top : s'.nodes = s.nodes ∧ s'.path = s.path ∧ s'.cin = s.cin ∧ s'.lpar = s.lpar ∧
    s'.resJob = s.resJob ∧ s'.prep = s.prep ∧ s'.ready = s.ready ∧ s'.firstChunk = s.firstChunk
  links : ∀ c, cN s' c = cN s c ∧ cP s' c = cP s c ∧ cT s' c = cT s c
  inq : ∀ c, inQC s' c = inQC s c
  qsz : ∀ c, inQC s c = true → cSz s' c = cSz s c
  gv : ∀ c, gval s' c = gval s c
  count : s'.count = s.count

theorem DFrame.refl (s : Core) : DFrame s s :=
  ⟨rfl, rfl, PQSame.refl s, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem DFrame.trans {a b c : Core} (h1 : DFrame a b) (h2 : DFrame b c) : DFrame a c := by
  obtain ⟨s1, P1, q1, ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩, l1, i1, z1, g1, c1⟩ := h1
  obtain ⟨s2, P2, q2, ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩, l2, i2, z2, g2, c2⟩ := h2
  refine ⟨s2.trans s1, P2.trans P1, q1.trans q2, ⟨u1.trans t1, u2.trans t2, u3.trans t3,
    u4.trans t4, u5.trans t5, u6.trans t6, u7.trans t7, u8.trans t8⟩, fun d => ?_,
    fun d => (i2 d).trans (i1 d), fun d hd => ?_, fun d => (g2 d).trans (g1 d), c2.trans c1⟩
  · exact ⟨(l2 d).1.trans (l1 d).1, (l2 d).2.1.trans (l1 d).2.1, (l2 d).2.2.trans (l1 d).2.2⟩
  · rw [z2 d (by rw [i1 d]; exact hd), z1 d hd]

theorem PQC.dframe {s s' : Core} (h : PQC s) (D : DFrame s s') : PQC s' := h.frame D.pq D.inq D.qsz

theorem DFrame.gvec {s s' : Core} (D : DFrame s s') (n : Nat) : gvec n s' = gvec n s := by
  funext i; unfold OrderMaintenance.Proof.gvec; rw [D.gv]

/-- A frame from equal quiet sizes and states. -/
theorem DFrame.of_qsame {s s' : Core} (Q : QSame s s') (hq : PQSame s s')
    (ht : s'.nodes = s.nodes ∧ s'.path = s.path ∧ s'.cin = s.cin ∧ s'.lpar = s.lpar ∧
      s'.resJob = s.resJob ∧ s'.prep = s.prep ∧ s'.ready = s.ready ∧ s'.firstChunk = s.firstChunk)
    (hl : ∀ c, cN s' c = cN s c ∧ cP s' c = cP s c ∧ cT s' c = cT s c)
    (hcnt : s'.count = s.count) : DFrame s s' :=
  ⟨Q.Csize, Q.P, hq, ht, hl, Q.inQC, fun c hc => by
    unfold OrderMaintenance.Proof.inQC at hc; simp only [decide_eq_true_eq] at hc; exact Q.sz c hc.1 hc.2.1,
    Q.gval, hcnt⟩

theorem CFrame.dframe {s s' : Core} (h : CFrame s s') : DFrame s s' :=
  DFrame.of_qsame h.qsame h.pq h.top (fun c => ⟨(h.C c).2.2.2.2.2.1, (h.C c).2.2.2.2.2.2.1,
    (h.C c).2.2.2.2.2.2.2⟩) h.count

/-- A chunk-split move leaves the quiet chunks alone. -/
theorem cmoveL_dframe {s : Core} {x : Nat} {u labs : List Nat} (hxy : x ≠ cLl s x)
    (hx : x < s.C.size) (hy : cLl s x < s.C.size) (hxs : cSt s x = .splitting)
    (hys : cSt s (cLl s x) = .overflow) : DFrame s (cmoveLState s x u labs) := by
  have hCs : (moveGroupsLeft s x (cLl s x) u labs).C.size = s.C.size := by simp [moveGroupsLeft]
  have hC := fun c => cmoveSizes_C (t := moveGroupsLeft s x (cLl s x) u labs) (u := u) hxy
    (by rw [hCs]; exact hx) (by rw [hCs]; exact hy) c
  have hCm := fun c => moveGroupsLeft_C (s := s) (u := u) (labs := labs) hxy hx hy c
  have fld : ∀ c, cSt (cmoveLState s x u labs) c = cSt s c ∧ cN (cmoveLState s x u labs) c = cN s c ∧
      cP (cmoveLState s x u labs) c = cP s c ∧ cT (cmoveLState s x u labs) c = cT s c ∧
      (c ≠ x → c ≠ cLl s x → cSz (cmoveLState s x u labs) c = cSz s c) := by
    intro c
    simp only [cSt, cN, cP, cT, cSz, cmoveLState]
    rw [hC c, hCm c]
    by_cases h1 : c = x
    · subst h1; simp only [ite_true, ite_eq_right hxy]; split <;> simp
    · by_cases h2 : c = cLl s x
      · subst h2; simp [h1]
      · simp [h1, h2]
  have hCsz : (cmoveLState s x u labs).C.size = s.C.size := by
    simp [cmoveLState, cmoveSizes, hCs]
  refine DFrame.of_qsame ⟨hCsz, rfl, fun c _ => by rw [(fld c).1], fun c _ hq => ?_⟩
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun c => ⟨(fld c).2.1, (fld c).2.2.1, (fld c).2.2.2.1⟩) rfl
  refine (fld c).2.2.2.2 ?_ ?_
  · rintro rfl; rw [hxs] at hq; cases hq
  · rintro rfl; rw [hys] at hq; cases hq

theorem cmoveR_dframe {s : Core} {x : Nat} {u labs : List Nat} (hxz : x ≠ cRr s x)
    (hx : x < s.C.size) (hz : cRr s x < s.C.size) (hxs : cSt s x = .splitting)
    (hzs : cSt s (cRr s x) = .overflow) : DFrame s (cmoveRState s x u labs) := by
  have hCs : (moveGroupsRight s x (cRr s x) u labs).C.size = s.C.size := by simp [moveGroupsRight]
  have hC := fun c => cmoveSizes_C (t := moveGroupsRight s x (cRr s x) u labs) (u := u) hxz
    (by rw [hCs]; exact hx) (by rw [hCs]; exact hz) c
  have hCm := fun c => moveGroupsRight_C (s := s) (u := u) (labs := labs) hxz hx hz c
  have fld : ∀ c, cSt (cmoveRState s x u labs) c = cSt s c ∧ cN (cmoveRState s x u labs) c = cN s c ∧
      cP (cmoveRState s x u labs) c = cP s c ∧ cT (cmoveRState s x u labs) c = cT s c ∧
      (c ≠ x → c ≠ cRr s x → cSz (cmoveRState s x u labs) c = cSz s c) := by
    intro c
    simp only [cSt, cN, cP, cT, cSz, cmoveRState]
    rw [hC c, hCm c]
    by_cases h1 : c = x
    · subst h1; simp only [ite_true, ite_eq_right hxz]; split <;> simp
    · by_cases h2 : c = cRr s x
      · subst h2; simp [h1]
      · simp [h1, h2]
  have hCsz : (cmoveRState s x u labs).C.size = s.C.size := by
    simp [cmoveRState, cmoveSizes, hCs]
  refine DFrame.of_qsame ⟨hCsz, rfl, fun c _ => by rw [(fld c).1], fun c _ hq => ?_⟩
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun c => ⟨(fld c).2.1, (fld c).2.2.1, (fld c).2.2.2.1⟩) rfl
  refine (fld c).2.2.2.2 ?_ ?_
  · rintro rfl; rw [hxs] at hq; cases hq
  · rintro rfl; rw [hzs] at hq; cases hq

/-- A chunk removal: the siblings turn quiet at sizes at most `θ`, so no game value changes and the
queue stays as it is. -/
theorem cremove_dframe {s : Core} {x : Nat} (hx : x < s.C.size) (hl : cLl s x < s.C.size)
    (hr : cRr s x < s.C.size) (hlx : cLl s x ≠ x) (hrx : cRr s x ≠ x)
    (hxs : cSt s x = .splitting) (hls : cSt s (cLl s x) = .overflow)
    (hrs : cSt s (cRr s x) = .overflow) (hszl : cSz s (cLl s x) ≤ s.P.theta)
    (hszr : cSz s (cRr s x) ≤ s.P.theta) : DFrame s (cremoveState s x) := by
  have hC' := cremoveState_C hx hl hr hlx hrx
  have hsz : ∀ c, cSz (cremoveState s x) c = cSz s c := by
    intro c; simp only [cSz, hC']; split_ifs <;> rfl
  have hlk : ∀ c, cN (cremoveState s x) c = cN s c ∧ cP (cremoveState s x) c = cP s c ∧
      cT (cremoveState s x) c = cT s c := by
    intro c; simp only [cN, cP, cT, hC']; split_ifs <;> simp [deadC, quietC]
  have hst : ∀ c, cSt (cremoveState s x) c = if c = x then .dead
      else if c = cLl s x ∨ c = cRr s x then .quiet else cSt s c := by
    intro c; simp only [cSt, hC']; split_ifs <;> simp [deadC, quietC]
  have hLC : ∀ c, LiveC (cremoveState s x) c ↔ LiveC s c := by
    intro c; simp [LiveC, cremoveState]
  have hP : (cremoveState s x).P = s.P := rfl
  have hval : ∀ c, (cSt (cremoveState s x) c = .quiet ∧ s.P.theta < cSz s c) ↔
      (cSt s c = .quiet ∧ s.P.theta < cSz s c) := by
    intro c
    rw [hst]
    by_cases h1 : c = x
    · subst h1; simp [hxs]
    · by_cases h2 : c = cLl s x ∨ c = cRr s x
      · have hn : ¬ s.P.theta < cSz s c := by rcases h2 with rfl | rfl <;> omega
        simp [h1, h2, hn]
      · simp [h1, h2]
  refine ⟨by simp [cremoveState], hP, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hlk, fun c => ?_, fun c _ => hsz c, fun c => ?_, rfl⟩
  · unfold OrderMaintenance.Proof.inQC
    rw [hsz, hP]
    have := hval c
    by_cases hc : LiveC s c
    · simp only [hc, (hLC c).mpr hc, true_and]; exact decide_eq_decide.mpr this
    · simp [hc, (hLC c).not.mpr hc]
  · unfold gval
    rw [hsz, hP]
    by_cases hc : LiveC s c
    · simp only [hc, (hLC c).mpr hc, true_and]
      by_cases hq : cSt (cremoveState s x) c = .quiet
      · by_cases hq' : cSt s c = .quiet
        · rw [ite_eq_left hq, ite_eq_left hq']
        · rw [ite_eq_left hq, ite_eq_right hq']
          have : ¬ s.P.theta < cSz s c := fun h => hq' ((hval c).mp ⟨hq, h⟩).1
          omega
      · by_cases hq' : cSt s c = .quiet
        · rw [ite_eq_right hq, ite_eq_left hq']
          have : ¬ s.P.theta < cSz s c := fun h => hq ((hval c).mpr ⟨hq', h⟩).1
          omega
        · rw [ite_eq_right hq, ite_eq_right hq']
    · simp [hc, (hLC c).not.mpr hc]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **The chunk drive leaves the queue, the game and the top structure alone**, threaded next to
an invariant `X`. -/
theorem cxsteps_dframe {X Y : Core → Prop} {L : List Nat} {δ δu s₀ : Nat → Nat} {x : Nat}
    (h : CXSteps X Y L δ δu s₀ x) (t₀ : Core) (hcθ : cmax t₀.P ≤ t₀.P.theta) :
    CXSteps (fun t => X t ∧ DFrame t₀ t) (fun t => Y t ∧ DFrame t₀ t) L δ δu s₀ x := by
  refine h.and ?_ ?_ ?_
  · intro t A gh labs hI hel hG hC hxL hst hX
    subst hel
    have Fx := hC.cfam x hxL hst
    exact hX.trans (cmoveL_dframe (Ne.symm (Fx.lx hI hxL)) hxL.2 Fx.lLive.2 hst Fx.lSt)
  · intro t A gh labs hI hel hG hC hxL hst hX
    subst hel
    have Fx := hC.cfam x hxL hst
    exact hX.trans (cmoveR_dframe (Ne.symm (Fx.rx hI hxL)) hxL.2 Fx.rLive.2 hst Fx.rSt)
  · intro t A gh hI hel hG hC hxL hst hl hr hX
    subst hel
    have Fx := hC.cfam x hxL hst
    exact hX.trans (cremove_dframe hxL.2 Fx.lLive.2 Fx.rLive.2 (Fx.lx hI hxL) (Fx.rx hI hxL) hst
      Fx.lSt Fx.rSt (le_trans hl (by rw [hX.P]; exact hcθ)) (le_trans hr (by rw [hX.P]; exact hcθ)))

end OrderMaintenance.Proof

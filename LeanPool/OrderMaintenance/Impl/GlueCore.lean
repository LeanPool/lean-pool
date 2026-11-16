/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.GlueTop
public import LeanPool.OrderMaintenance.Impl.Background
public import Mathlib.Order.Interval.Finset.Nat


/-!
# M6: the glue for the core's parts

Level F's cost proofs establish the hypotheses of the core's run lemmas inside their proofs (the
group drive, the chunk drive, the split starts). Here those places get Level M agreements: each
proof is followed, and its run lemma is paired with the Level M lemma for the same branch.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof
/-- **The capacities a group drive needs**, at state `s`. -/
structure GCaps (κ : Caps) (s : Core) : Prop where
  G : s.Gs.size ≤ κ.tbl .G
  E : s.E.size ≤ κ.tbl .E
  C : s.C.size ≤ κ.tbl .C
  fl : κ.tbl .G ≤ κ.lcap .freeG
  f0 : 0 < κ.lrec .freeG

/-- Transport capacity bounds across changes that preserve the three array sizes. -/
theorem GCaps.of_sizes {κ : Caps} {s t : Core} (K : GCaps κ s)
    (groups : t.Gs.size = s.Gs.size) (elements : t.E.size = s.E.size)
    (chunks : t.C.size = s.C.size) : GCaps κ t := by
  refine ⟨?_, ?_, ?_, K.fl, K.f0⟩
  · rw [groups]; exact K.G
  · rw [elements]; exact K.E
  · rw [chunks]; exact K.C

theorem _root_.OrderMaintenance.Proof.INV.gN_lt {s : Core} {A : Abs} (hI : INV s A) {g : Nat}
  (hg : g ∈ A.glist) : gN s g < s.Gs.size := by
  rw [hI.gList.next g hg]
  rcases succOf_mem_or (l := A.glist) (x := g) with h | h
  · exact hI.gAlloc _ h
  · rw [h]; have := hI.gPos; unfold NIL; omega

theorem _root_.OrderMaintenance.Proof.INV.gP_lt {s : Core} {A : Abs} (hI : INV s A) {g : Nat}
  (hg : g ∈ A.glist) : gP s g < s.Gs.size := by
  rw [hI.gList.prev g hg]
  rcases predOf_mem_or (l := A.glist) (x := g) with h | h
  · exact hI.gAlloc _ h
  · rw [h]; have := hI.gPos; unfold NIL; omega

theorem _root_.OrderMaintenance.Proof.INV.gF_lt {s : Core} {A : Abs} (hI : INV s A) {g : Nat}
  (hg : g ∈ A.glist) :
    gF s g = NIL ∨ gF s g < s.E.size := by
  by_cases h : gF s g = NIL
  · exact Or.inl h
  · obtain ⟨rest, hr⟩ := hI.run_head hg h
    have : gF s g ∈ A.elist := (mem_runOf.mp (hr ▸ (by simp : gF s g ∈ gF s g :: rest))).1
    exact Or.inr ((hI.eAlloc _).mp this).2

theorem _root_.OrderMaintenance.Proof.INV.gLs_lt {s : Core} {A : Abs} (hI : INV s A) {g : Nat}
  (hg : g ∈ A.glist) :
    gLs s g = NIL ∨ gLs s g < s.E.size := by
  by_cases h : gF s g = NIL
  · left
    have hE := hI.gEnds g hg
    rw [hI.elts_eq hg] at hE
    have := (hI.first_nil_iff hg).mp h
    rw [this] at hE; exact hE.2
  · obtain ⟨front, hr⟩ := hI.run_last hg h
    have : gLs s g ∈ A.elist := (mem_runOf.mp (hr ▸ (by simp : gLs s g ∈ front ++ [gLs s g]))).1
    exact Or.inr ((hI.eAlloc _).mp this).2

/-- The free groups are distinct groups below `Gs.size`, other than `NIL`. -/
theorem _root_.OrderMaintenance.Proof.INV.freeG_len {s : Core} {A : Abs} (hI : INV s A) :
  s.freeG.length + 1 ≤ s.Gs.size := by
  have hs : s.freeG.toFinset ⊆ Finset.Ico 1 s.Gs.size := fun g hg => by
    obtain ⟨a, b, -⟩ := hI.free g (List.mem_toFinset.mp hg); simp [Finset.mem_Ico]; omega
  have := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hI.freeNodup, Nat.card_Ico] at this
  have := hI.gPos; omega

theorem moveLState_sizes {t : Core} {p : Nat} :
    (moveLState t p).Gs.size = t.Gs.size ∧ (moveLState t p).C.size = t.C.size ∧ (moveLState t
      p).E.size = t.E.size := by
  simp [moveLState, sizeAdj, moveFirstLeft]

theorem moveRState_sizes {t : Core} {p : Nat} :
    (moveRState t p).Gs.size = t.Gs.size ∧ (moveRState t p).C.size = t.C.size ∧ (moveRState t
      p).E.size = t.E.size := by
  simp [moveRState, sizeAdj, moveLastRight]

theorem removeState_sizes {t : Core} {p : Nat} :
    (removeState t p).Gs.size = t.Gs.size ∧ (removeState t p).C.size = t.C.size ∧
      (removeState t p).E.size = t.E.size := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [removeState, unlinkGroup, Array.size_modify] <;> split_ifs
    <;> simp

/-- **A group split step of a drive agrees** (the cases of `DriveInv.step`). -/
theorem _root_.OrderMaintenance.Proof.DriveInv.stepAgree {X Y : Core → Prop} {s : Core} {L :
  List Nat} {δ : Nat → Nat}
    {p l r a b c j : Nat} {t : Core} (hXs : XSteps X Y L δ p (gC s p))
    (hP : GParams s.P)
    (hTlo : s.P.G ≤ a + b + c) (hThi : a + b + c ≤ s.P.G + s.P.G / (s.P.groupBudget - 1) + 1)
    (hbal0 : a ≤ c + 2 ∧ c ≤ a + 2)
    (hD : DriveInv X s L δ p l r a b c j t) {κ : Caps} (hcg : ∀ g, LiveG t g → gC t g < t.C.size)
    (K : GCaps κ t) :
    ∃ b t', (groupSplitStep p).run t = .ok b t' ∧ StepAgree κ p t t' b ∧ t'.Gs.size = t.Gs.size ∧
      t'.C.size = t.C.size ∧ t'.E.size = t.E.size := by
  obtain ⟨A', hI', hel⟩ := hD.inv
  obtain ⟨gh, hG⟩ := hD.ginv
  subst hel
  have hp := hD.live
  have hs := hD.st
  have Fp := hG.fam p hp hs
  have hp' := hI'.mem_glist_iff.mpr hp
  have hPt := hD.P
  rw [← hPt] at hP hTlo hThi
  have hlL : LiveG t l := hD.ll ▸ Fp.lLive
  have hrL : LiveG t r := hD.rr ▸ Fp.rLive
  have hl' := hI'.mem_glist_iff.mpr hlL
  have hr' := hI'.mem_glist_iff.mpr hrL
  have hlp : l ≠ p := hD.ll ▸ Fp.lp hI' hp
  have hrp : r ≠ p := hD.rr ▸ Fp.rp hI' hp
  have hlr : l ≠ r := hD.ll ▸ hD.rr ▸ Fp.lr hI' hp
  have hsum := hD.sum
  have hcnt := hD.cnt
  have hbal := hD.bal
  have hK2 := hP.K2
  have hI1 := hP.I1
  generalize hq : t.P.G / (t.P.groupBudget - 1) = q at hThi hI1
  have hkG : kG t.P = q + 1 := by unfold kG; rw [hq]
  have hcE := hP.push
  rw [hkG] at hcE
  have hD0 := hP.De
  by_cases hz : gSz t p = 0
  · -- removal
    have he : gF t p = NIL := by
      rw [hI'.first_nil_iff hp', ← List.length_eq_zero_iff, ← hG.sz p hp]; exact hz
    have hszl : gSz t l < t.P.G := by rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszr : gSz t r < t.P.G := by rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hgl : gmin t.P ≤ gSz t l := by
      unfold gmin; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hgr : gmin t.P ≤ gSz t r := by
      unfold gmin; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hfam : famT t p ≤ t.P.G + kG t.P := by
      unfold famT; rw [hD.ll, hD.rr, hkG]; omega
    have hg1 : 1 ≤ gmin t.P := by unfold gmin; have := hP.G4; omega
    have hrun := groupSplitStep_remove hp he (by
      rw [hD.ll, hD.rr]
      exact hlr)
      ⟨by rw [hD.ll]; exact Fp.lSt ▸ hD.ll ▸ rfl, by rw [hD.ll]; exact hD.ll ▸ Fp.lSrc⟩
      ⟨by rw [hD.rr]; exact hD.rr ▸ Fp.rSt, by rw [hD.rr]; exact hD.rr ▸ Fp.rSrc⟩
      (by
        rw [hD.ll]
        exact hszl) (by
        rw [hD.rr]
        exact hszr)
    refine ⟨false, _, hrun, fun Lc hLc => ?_, removeState_sizes⟩
    obtain ⟨L', n, e, hok, hn⟩ := groupSplitStepS_remove κ t Lc hLc hp he (by
      rw [hD.ll, hD.rr]
      exact hlr)
      ⟨by rw [hD.ll]; exact Fp.lSt ▸ hD.ll ▸ rfl, by rw [hD.ll]; exact hD.ll ▸ Fp.lSrc⟩
      ⟨by rw [hD.rr]; exact hD.rr ▸ Fp.rSt, by rw [hD.rr]; exact hD.rr ▸ Fp.rSrc⟩
      (by
        rw [hD.ll]
        exact hszl) (by
        rw [hD.rr]
        exact hszr) (by
        rw [hD.ll]
        exact hlL.2.1)
      (by
        rw [hD.rr]
        exact hrL.2.1) (hI'.gP_lt hp') (hI'.gN_lt hp') (hcg p hp) (by
        have := K.G
        omega)
      (by
        have := K.C
        omega) (by
        have := hI'.freeG_len
        have := K.G
        have := K.fl
        omega) K.f0
    exact ⟨L', n, e, by rw [hok]; rfl, hn⟩
  · have hne : gF t p ≠ NIL := by
      intro h; apply hz
      rw [hG.sz p hp]; exact List.length_eq_zero_iff.mpr ((hI'.first_nil_iff hp').mp h)
    obtain ⟨rest, hrun⟩ := hI'.run_head hp' hne
    have he : gF t p ∈ A'.elist := (mem_runOf.mp (hrun ▸ (by simp : gF t p ∈ gF t p :: rest))).1
    have heS : gF t p < t.E.size := ((hI'.eAlloc _).mp he).2
    obtain ⟨front, hrunL⟩ := hI'.run_last hp' hne
    have heL : gLs t p ∈ A'.elist :=
      (mem_runOf.mp (hrunL ▸ (by simp : gLs t p ∈ front ++ [gLs t p]))).1
    have heLS : gLs t p < t.E.size := ((hI'.eAlloc _).mp heL).2
    by_cases hdir : gSz t l ≤ gSz t r
    · -- move to the left sibling
      have hlst : gSt t l = .overflow := hD.ll ▸ Fp.lSt
      obtain ⟨-, hpush⟩ := hG.ghO l hlL hlst
      have hlsz : gSz t l + 1 ≤ t.P.G + q + 1 := by omega
      have hroom : gF t l ≠ NIL → eL t (gLs t l) + t.P.elementSpacing < 1 <<< t.P.elementBits := by
        intro hfl
        obtain ⟨fr, hfr⟩ := hI'.run_last hl' hfl
        obtain ⟨-, h2⟩ := hG.range l hlL (gLs t l) (by
          rw [hfr]
          simp)
        rw [cE_two _ hP.Be]
        have : (gh.pb l + 1) * t.P.elementSpacing ≤ (t.P.G + (q + 1)) * t.P.elementSpacing :=
          Nat.mul_le_mul_right _ (by omega)
        have : (gh.pb l + 1) * t.P.elementSpacing = gh.pb l * t.P.elementSpacing +
          t.P.elementSpacing := by ring
        omega
      have hok : MoveLOK t p := ⟨hp, hne, by rw [hD.ll, hD.rr]; exact hdir,
        Fp.lAdj, by rw [hD.ll]; exact hroom, by omega, Fp.lC⟩
      have hrun2 := groupSplitStep_left hok
      refine ⟨true, _, hrun2, fun Lc hLc => ?_, moveLState_sizes⟩
      obtain ⟨L', n, e, hok', -, hn⟩ := groupSplitStepS_left κ t Lc hLc hok (by
        rw [hD.ll]
        exact hlL.2.1)
        (by
          rw [hD.rr]
          exact hrL.2.1) heS (by
          rcases hI'.gLs_lt (hD.ll ▸ hl') with h | h
          · rw [h]; have := K.E; unfold NIL; omega
          · have := K.E; omega) (by
            have := K.G
            omega) (by
            have := K.E
            omega)
      exact ⟨L', n, e, by rw [hok']; rfl, by omega⟩
    · -- move to the right sibling
      have hrst : gSt t r = .overflow := hD.rr ▸ Fp.rSt
      obtain ⟨-, hpush⟩ := hG.ghO r hrL hrst
      have hrsz : gSz t r + 1 ≤ t.P.G + q + 1 := by omega
      have hroom : gF t r ≠ NIL → t.P.elementSpacing ≤ eL t (gF t r) := by
        intro hfr
        obtain ⟨rs, hrs⟩ := hI'.run_head hr' hfr
        obtain ⟨h1, -⟩ := hG.range r hrL (gF t r) (by
          rw [hrs]
          simp)
        have : (gh.pf r + 1) * t.P.elementSpacing ≤ (t.P.G + (q + 1)) * t.P.elementSpacing :=
          Nat.mul_le_mul_right _ (by omega)
        have : (gh.pf r + 1) * t.P.elementSpacing = gh.pf r * t.P.elementSpacing +
          t.P.elementSpacing := by ring
        omega
      have hadjR : gP t (gRr t p) = p := by
        rw [← Fp.rAdj]; exact hI'.gP_gN hp' (by
          rw [Fp.rAdj, hD.rr]
          exact hrL.1)
      have hok : MoveROK t p := ⟨hp, hne, by rw [hD.ll, hD.rr]; omega, hadjR,
        by rw [hD.rr]; exact hroom, by omega, Fp.rC⟩
      have hrun2 := groupSplitStep_right hok
      refine ⟨true, _, hrun2, fun Lc hLc => ?_, moveRState_sizes⟩
      obtain ⟨L', n, e, hok', -, hn⟩ := groupSplitStepS_right κ t Lc hLc hok (by
        rw [hD.ll]
        exact hlL.2.1)
        (by
          rw [hD.rr]
          exact hrL.2.1) heLS (by
          rcases hI'.gF_lt (hD.rr ▸ hr') with h | h
          · rw [h]; have := K.E; unfold NIL; omega
          · have := K.E; omega) (by
            have := K.G
            omega) (by
            have := K.E
            omega)
      exact ⟨L', n, e, by rw [hok']; rfl, by omega⟩
/-- **The drive of a splitting group agrees** (the context of `ginv_drive`). -/
theorem ginv_driveAgree {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p :
  Nat}
    (hI : INV s A) (hXs : XSteps X Y A.elist δ p (gC s p)) (hX : X s)
    (hG : GInvE s A.elist gh δ p) (hP : GParams s.P) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hG1 : G1 s δ p)
    (hδ : ∀ z, z ≠ gLl s p → z ≠ p → z ≠ gRr s p → δ z = 0)
    (hδs : δ (gLl s p) + δ p + δ (gRr s p) ≤ 1)
    (hδle : δ (gLl s p) ≤ gSz s (gLl s p) ∧ δ p ≤ gSz s p ∧ δ (gRr s p) ≤ gSz s (gRr s p))
    {κ : Caps} (hXc : ∀ t, X t → ∀ g, LiveG t g → gC t g < t.C.size) (K : GCaps κ s) :
    ∃ s', DriveAgree κ p s s' ∧ s'.Gs.size = s.Gs.size ∧ s'.C.size = s.C.size ∧ s'.E.size =
      s.E.size := by
  have hBounds := hG1.drive_bounds hP.K2 hδs hδle
  generalize hl : gLl s p = l at *
  generalize hr : gRr s p = r at *
  generalize ha : gSz s l = a at *
  generalize hb : gSz s p = b at *
  generalize hc : gSz s r = c at *
  obtain ⟨hTlo, hThi, hbal0⟩ := hBounds
  let I' := fun j t => DriveInv X s A.elist δ p l r a b c j t ∧ t.Gs.size = s.Gs.size ∧ t.C.size
    = s.C.size
  have h0 : I' 0 s := ⟨⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hp, hs, hl, hr, by
    omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩, rfl⟩, rfl, rfl⟩
  have hstepM : ∀ j t, I' j t → ∃ bb t', (groupSplitStep p).run t = .ok bb t' ∧ (bb = true → I'
    (j + 1) t') ∧
      StepAgree κ p t t' bb ∧ t'.Gs.size = s.Gs.size ∧ t'.C.size = s.C.size ∧ t'.E.size =
        s.E.size := by
    intro j t ⟨hD, hGs, hCs⟩
    have K' : GCaps κ t := K.of_sizes hGs hD.ef.size hCs
    obtain ⟨bb, t', hrun, hA, hG', hC', hE'⟩ := hD.stepAgree hXs hP hTlo
      hThi hbal0 (hXc t hD.x) K'
    refine ⟨bb, t', hrun, fun hb => ?_, hA, hG'.trans hGs, hC'.trans hCs, hE'.trans hD.ef.size⟩
    subst hb
    obtain ⟨t1, h1 | h1⟩ := hD.step hXs hP (by
      intro z h1 h2 h3
      exact hδ z h1 h2 h3) hTlo hThi hbal0
    · rw [h1.1] at hrun; injection hrun with _ e; subst e
      exact ⟨h1.2, hG'.trans hGs, hC'.trans hCs⟩
    · rw [h1.1] at hrun; injection hrun with e; cases e
  obtain ⟨s', hA⟩ := driveGroupFromS_agree' κ s I' h0 (fun j t h _ => by
    obtain ⟨bb, t', a1, a2, a3, -⟩ := hstepM j t h; exact ⟨bb, t', a1, a2, a3⟩)
  obtain ⟨t, hrun, hres⟩ := driveGroupFrom_ok (s := s) (p := p) I'
    (fun t => t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size ∧ t.E.size = s.E.size) h0 (fun j t h _
      => by
      obtain ⟨bb, t', a1, a2, -, a4, a5, a6⟩ := hstepM j t h
      cases bb
      · exact ⟨t', Or.inr ⟨a1, a4, a5, a6⟩⟩
      · exact ⟨t', Or.inl ⟨a1, a2 rfl⟩⟩)
  rw [hA.1] at hrun; injection hrun with _ e; subst e
  refine ⟨s', hA, ?_⟩
  rcases hres with ⟨hD, hGs, hCs⟩ | h
  · exact ⟨hGs, hCs, hD.ef.size⟩
  · exact h

theorem allocGroup_size (s : Core) (c : Nat) : (allocGroup s c).2.Gs.size ≤ s.Gs.size + 1 := by
  unfold allocGroup; split <;> simp

theorem linkGroupPair_size (s : Core) (g gl gr labL labR : Nat) :
    (linkGroupPair s g gl gr labL labR).Gs.size = s.Gs.size := by
  unfold linkGroupPair; dsimp only; split_ifs <;> simp

theorem splitState_size (s : Core) (g labL labR : Nat) : (splitState s g labL labR).Gs.size ≤
  s.Gs.size + 2 := by
  unfold splitState; rw [linkGroupPair_size]
  have := allocGroup_size (allocGroup s (gC s g)).2 (gC s g)
  have := allocGroup_size s (gC s g)
  omega

theorem DriveAgree.eq_of_run {κ : Caps} {q : Nat} {s s' s'' : Core} (hA : DriveAgree κ q s s'')
    (h : (driveGroupFrom q).run s = .ok () s') : s'' = s' := by
  rw [hA.1] at h; injection h

/-- A drive that agrees, read off a `DriveAgree` for the run Level F made. -/
theorem DriveAgree.of_run {κ : Caps} {q : Nat} {s s' s'' : Core} (hA : DriveAgree κ q s s'')
    (h : (driveGroupFrom q).run s = .ok () s') : DriveAgree κ q s s' := by
  rw [hA.1] at h; injection h with _ e; subst e; exact hA

/-- **The group phase agrees** (the context of `groupPhase_ok`): the split start, when it runs, and
the drive. -/
theorem groupPhaseAgree {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {g : Nat} (hI : INV s A)
    (hXg : XGroup X Y A.elist (gC s g)) (hX : X s)
    (hG : GInv s A.elist gh (fun b => if b = g then 1 else 0)) (hP : GParams s.P)
    (hg : LiveG s g) (hpos : 1 ≤ gSz s g)
    (hroom : gSt s g = .quiet → s.P.G ≤ gSz s g → SplitRoom s g)
    {κ : Caps} (hXc : ∀ t, X t → ∀ g, LiveG t g → gC t g < t.C.size) (K : GCaps κ s)
    (hG2 : s.Gs.size + 2 ≤ κ.tbl .G) (hF0 : 0 < κ.lrec .freeG) (hF : s.freeG.length ≤ κ.lcap .freeG)
    {s1 s' : Core}
    (h1 : (if ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true then
      startGroupSplit g else pure ()).run s = .ok () s1)
    (h2 : (driveGroup g).run s1 = .ok () s') :
    (((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true →
      ∃ L' n, evalF κ startGroupSplitS s (Machine.State.setLocs (fun _ => 0) ["g"] [g]) = .ok s1
        L' n ∧
        n ≤ 600) ∧
    (∃ L' n, evalF κ driveGroupS s1 (Machine.State.setLocs (fun _ => 0) ["g"] [g]) = .ok s' L' n ∧
      n ≤ 30 + s1.P.groupBudget * 401) ∧
    s'.Gs.size ≤ s.Gs.size + 2 ∧ s'.C.size = s.C.size ∧ s'.E.size = s.E.size ∧ s1.E = s.E ∧ s1.P
      = s.P := by
  have hgl := hI.mem_glist_iff.mpr hg
  have hgT : g < κ.tbl .G := by have := hg.2.1; have := K.G; omega
  have hLg : Machine.State.setLocs (fun _ => 0) ["g"] [g] "g" = g := by
    simp [Machine.State.setLocs, Machine.State.upd]
  have hδle : ∀ p, (fun b => if b = g then 1 else 0) p ≤ gSz s p := by
    intro p; by_cases h : p = g
    · subst h; simp [hpos]
    · simp [h]
  suffices hD : (∀ q, ((s1.Gs.getX g).st = .splitting ∧ q = g ∨
      (s1.Gs.getX g).st = .overflow ∧ q = (s1.Gs.getX g).src) → DriveAgree κ q s1 s') ∧
      s'.Gs.size ≤ s.Gs.size + 2 ∧ s'.C.size = s.C.size ∧ s'.E.size = s.E.size ∧ s1.E = s.E ∧
        s1.P = s.P by
    refine ⟨fun hc => ?_, driveGroupS_agree κ s1 _ hLg hgT h2 hD.1, hD.2⟩
    rw [ite_eq_left hc] at h1
    exact startGroupSplitS_agree κ s _ hLg (by omega) K.C (hI.gP_lt hgl) (hI.gN_lt hgl) (hXc s
      hX g hg)
      (fun x hx => (hI.free x hx).2.1) hF0 hF h1
  · cases hst : gSt s g with
    | quiet =>
      by_cases hsz : s.P.G ≤ gSz s g
      · obtain ⟨labL, labR, hL, hR⟩ := hroom hst hsz
        have hc : ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
          simp only [gSt, gSz] at hst hsz; simp [hst, hsz]
        rw [ite_eq_left hc, startGroupSplit_ok hg hL hR] at h1
        injection h1 with _ e; subst e
        have hgG : gSz s g = s.P.G := by
          have := (hG.quiet g hg hst).1; simp at this; omega
        obtain ⟨hef1, A1, hI1, hel1⟩ := Good.ok_inv (good_startGroupSplit g) hI
          (startGroupSplit_ok hg hL hR)
        have hG1 := ginv_splitStart hI hG hg hst hsz labL labR
        have hX1 := hXg.split s A gh g labL labR hI rfl hG hg hst hgG hL hR hX
        have S := splitSpec hI hgl labL labR
        have hsz2 := splitState_size s g labL labR
        generalize splitState s g labL labR = s1 at hef1 hI1 hG1 hX1 S h2 hsz2 ⊢
        generalize gh.reset (splitL s g) (splitR s g) = gh1 at hG1
        have hg1 : LiveG s1 g := (S.live g).mpr (Or.inr (Or.inr hg))
        have hs1 : gSt s1 g = .splitting := by rw [S.st, ite_eq_left rfl]
        rw [← hel1] at hG1
        have hP1 : GParams s1.P := by rw [S.P]; exact hP
        have hXd : XSteps X Y A1.elist (fun _ => 0) g (gC s1 g) := by
          rw [hel1, S.chk, ite_eq_right (not_or.mpr ⟨S.ggl, S.ggr⟩)]; exact hXg.drive _ g
        have K1 : GCaps κ s1 := ⟨by omega, by rw [S.E]; exact K.E, by rw [S.Csize]; exact K.C,
          K.fl, K.f0⟩
        obtain ⟨s2, hA, hsz⟩ := ginv_driveAgree hI1 hXd hX1 (hG1.weaken g) hP1 hg1 hs1
          (hG1.split g hg1 hs1 hg1.1) (fun _ _ _ _ => rfl) (by simp) (by simp) hXc K1
        have hs1' : (s1.Gs.getX g).st = .splitting := hs1
        rw [driveGroup_split hs1'] at h2
        have e := hA.eq_of_run h2; subst e
        refine ⟨fun q hq => ?_, by omega, by rw [hsz.2.1, S.Csize], by rw [hsz.2.2, S.E], S.E, S.P⟩
        rcases hq with ⟨-, rfl⟩ | ⟨h, -⟩
        · exact hA
        · rw [hs1'] at h; cases h
      · have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true
          := by
          simp only [gSt, gSz] at hst hsz; simp [hst]; omega
        rw [ite_eq_right hc] at h1
        injection h1 with _ e; subst e
        simp only [gSt] at hst
        rw [driveGroup_quiet hst] at h2; injection h2 with _ e; subst e
        refine ⟨fun q hq => ?_, by omega, rfl, rfl, rfl, rfl⟩
        rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hst] at h <;> cases h
    | overflow =>
      have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt] at hst; simp [hst]
      rw [ite_eq_right hc] at h1
      injection h1 with _ e; subst e
      obtain ⟨hp, hps, hlr⟩ := hG.ovf g hg hst
      have Fp := hG.fam _ hp hps
      have hgp : gSrc s g ≠ g := by intro e; rw [e, hst] at hps; cases hps
      have hlr0 : gLl s (gSrc s g) ≠ gRr s (gSrc s g) := Fp.lr hI hp
      have hδs : (fun b => if b = g then 1 else 0) (gLl s (gSrc s g)) +
          (fun b => if b = g then 1 else 0) (gSrc s g) +
          (fun b => if b = g then 1 else 0) (gRr s (gSrc s g)) ≤ 1 := by
        rcases hlr with e | e
        · have : gRr s (gSrc s g) ≠ g := fun h => hlr0 (e.trans h.symm)
          simp [e, hgp, this]
        · have : gLl s (gSrc s g) ≠ g := fun h => hlr0 (h.trans e.symm)
          simp [e, hgp, this]
      have hXd : XSteps X Y A.elist (fun b => if b = g then 1 else 0) (gSrc s g) (gC s (gSrc s
        g)) := by
        rcases hlr with e | e
        · rw [← Fp.lC, e]; exact hXg.drive _ _
        · rw [← Fp.rC, e]; exact hXg.drive _ _
      obtain ⟨s2, hA, hsz⟩ := ginv_driveAgree hI hXd hX (hG.weaken (gSrc s g)) hP hp hps
        (hG.split _ hp hps hp.1)
        (by intro z h1 h2 h3; have : z ≠ g := by
              rintro rfl; rcases hlr with e | e <;> [exact h1 e.symm; exact h3 e.symm]
            simp [this])
        hδs ⟨hδle _, hδle _, hδle _⟩ hXc K
      have hst' : (s.Gs.getX g).st = .overflow := hst
      rw [driveGroup_ovf hst'] at h2
      have e := hA.eq_of_run h2; subst e
      refine ⟨fun q hq => ?_, by omega, hsz.2.1, hsz.2.2, rfl, rfl⟩
      rcases hq with ⟨h, -⟩ | ⟨-, rfl⟩
      · rw [hst'] at h; cases h
      · exact hA
    | splitting =>
      have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt] at hst; simp [hst]
      rw [ite_eq_right hc] at h1
      injection h1 with _ e; subst e
      have Fp := hG.fam g hg hst
      have hl0 : gLl s g ≠ g := Fp.lp hI hg
      have hr0 : gRr s g ≠ g := Fp.rp hI hg
      obtain ⟨s2, hA, hsz⟩ := ginv_driveAgree hI (hXg.drive _ _) hX (hG.weaken g) hP hg hst
        (hG.split g hg hst hg.1) (by
          intro z _ h2 _
          simp [h2]) (by simp [hl0, hr0])
        ⟨hδle _, hδle _, hδle _⟩ hXc K
      have hst' : (s.Gs.getX g).st = .splitting := hst
      rw [driveGroup_split hst'] at h2
      have e := hA.eq_of_run h2; subst e
      refine ⟨fun q hq => ?_, by omega, hsz.2.1, hsz.2.2, rfl, rfl⟩
      rcases hq with ⟨-, rfl⟩ | ⟨h, -⟩
      · exact hA
      · rw [hst'] at h; cases h
    | dead => exact absurd hst (hG.notDead g hg)

theorem cremoveState_sizes {t : Core} {x : Nat} :
    (cremoveState t x).Gs.size = t.Gs.size ∧ (cremoveState t x).C.size = t.C.size ∧
      (cremoveState t x).E.size = t.E.size := by
  simp [cremoveState]

theorem _root_.OrderMaintenance.Proof.INV.mem_chunks {s : Core} {A : Abs} (hI : INV s A) {c :
  Nat} (hc : LiveC s c) :
    c ∈ A.chunks := (hI.cAlloc c).mpr hc

theorem _root_.OrderMaintenance.Proof.INV.cF_lt {s : Core} {A : Abs} (hI : INV s A) {c : Nat}
  (hc : c ∈ A.chunks) :
    cF s c = NIL ∨ cF s c < s.Gs.size := by
  have hE := (hI.cEnds c hc).1
  rcases h : A.grps c with _ | ⟨g, gs⟩
  · rw [h] at hE; exact Or.inl hE
  · rw [h] at hE; simp only [List.headD_cons] at hE
    exact Or.inr (by rw [hE]; exact hI.gAlloc _ (A.grps_sub_glist hc (by
      rw [h]
      simp)))

theorem _root_.OrderMaintenance.Proof.INV.cLs_lt {s : Core} {A : Abs} (hI : INV s A) {c : Nat}
  (hc : c ∈ A.chunks) :
    cLs s c = NIL ∨ cLs s c < s.Gs.size := by
  have hE := (hI.cEnds c hc).2
  rcases (A.grps c).eq_nil_or_concat with h | ⟨l, g, h⟩
  · rw [h] at hE; exact Or.inl hE
  · rw [h] at hE; simp only [List.concat_eq_append, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.getD_some] at hE
    exact Or.inr (by rw [hE]; exact hI.gAlloc _ (A.grps_sub_glist hc (by
      rw [h]
      simp)))

/-- **A chunk split step of a drive agrees** (the cases of `CDriveInv.step`). -/
theorem _root_.OrderMaintenance.Proof.CDriveInv.stepAgree {X Y : Core → Prop} {s : Core} {L :
  List Nat} {δ δu s₀ : Nat → Nat}
    {x y z a b c u₀ j : Nat} {t : Core} (hXs : CXSteps X Y L δ δu s₀ x) (hP : GParams s.P)
    (hCP : CParams s.P)
    (hThi : a + b + c ≤ s.P.T + kC s.P s.P.T)
    (hbal0 : a ≤ c + umax s.P + 1 ∧ c ≤ a + umax s.P + 1)
    (hfam0 : a + b + c ≤ δ y + δ x + δ z + s₀ x + unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1))
    (hδs : δ y + δ x + δ z ≤ 1) (hs0T : s₀ x ≤ s.P.T)
    (hD : CDriveInv X s L δ δu s₀ x y z a b c u₀ j t) {κ : Caps} (K : GCaps κ t) :
    ∃ bb t', (chunkSplitStep x).run t = .ok bb t' ∧ CStepAgree κ x t t' bb ∧ t'.Gs.size =
      t.Gs.size ∧
      t'.C.size = t.C.size ∧ t'.E.size = t.E.size := by
  obtain ⟨A', hI', hel⟩ := hD.inv
  obtain ⟨gh, hG⟩ := hD.ginv
  subst hel
  have hPt := hD.P
  rw [← hPt] at hP hCP hThi hbal0 hfam0 hs0T
  have hC := hD.cinv
  have Fx := hC.cfam x hD.live hD.st
  have hxy : cLl t x ≠ x := Fx.lx hI' hD.live
  have hxz : cRr t x ≠ x := Fx.rx hI' hD.live
  have hyz : cLl t x ≠ cRr t x := Fx.lr hI' hD.live
  have hsum := hD.sum
  have hcnt := hD.cnt
  have hbal := hD.bal
  rw [← hD.ll, ← hD.rr] at hsum hbal hfam0 hδs
  rw [← hPt] at hbal
  have hFB : FamBound t δ s₀ x := ⟨by omega, hδs, hs0T⟩
  have hI4 := hCP.I4
  unfold cmax at hI4
  by_cases he : cF t x = NIL
  · -- removal
    have hcx : cSz t x = 0 := by rw [hC.csz x hD.live, hI'.celts_empty hD.live he]; rfl
    have hszy' : cSz t (cLl t x) ≤ cmax t.P := by
      unfold cmax; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszz' : cSz t (cRr t x) ≤ cmax t.P := by
      unfold cmax; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszy : cSz t (cLl t x) ≤ t.P.theta := by
      rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszz : cSz t (cRr t x) ≤ t.P.theta := by
      rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hrun := chunkSplitStep_remove he hyz hxy hxz hD.live.2 ⟨Fx.lSt, Fx.lSrc⟩ ⟨Fx.rSt, Fx.rSrc⟩
      hszy hszz
    refine ⟨false, _, hrun, fun Lc hLc => ?_, cremoveState_sizes⟩
    obtain ⟨L', n, e, hok, hn⟩ := chunkSplitStepS_remove κ t Lc hLc he hyz hxy hxz hD.live.2
      ⟨Fx.lSt, Fx.lSrc⟩
      ⟨Fx.rSt, Fx.rSrc⟩ hszy hszz Fx.lLive.2 Fx.rLive.2 K.C
    exact ⟨L', n, e, by rw [hok]; rfl, by omega⟩
  · -- a move
    obtain ⟨hxc, t0, ht0⟩ := hI'.run_ne_nil he
    have hg0 : cF t x ∈ A'.glist := A'.grps_sub_glist hxc (by
      rw [ht0]
      simp)
    have hg0L := hI'.mem_glist_iff.mp hg0
    have hg0x : gC t (cF t x) = x := hI'.chk x hxc _ (by
      rw [ht0]
      simp)
    by_cases hdir : cSz t (cLl t x) ≤ cSz t (cRr t x)
    · have lu := left_unit hI' hG he
      have hu : (unitCand t x true).length = 1 ∨ unitOK t x (unitCand t x true) = true := by
        rcases lu with ⟨-, h⟩ | ⟨p, -, -, -, -, h⟩
        · left; rw [h]; rfl
        · right; exact h
      obtain ⟨labs, hlabs, hX'⟩ := hXs.moveL t A' gh hI' rfl hG hC hD.live hD.st he hdir hFB hD.xx
      have hrun := chunkSplitStep_left he hdir hu Fx.lAdj hlabs
      have hlen : labs.length = (unitCand t x true).length := pushBackLabs_len hlabs
      have UF := unit_facts (u := unitCand t x true) (x := x) hI' hG hP (by
        rcases lu with ⟨hq, h⟩ | ⟨p, hp, hps, hl, h, hok⟩
        · left; rw [h]; exact ⟨hq, rfl, hg0L, hg0x⟩
        · right
          refine ⟨p, hp, hps, by rw [h, hl], ?_⟩
          rw [h] at hok; exact (unitOK_three hok).2.2.2.2.1)
      obtain ⟨-, hnd, hmem, hone, hcl, hm1, hm2⟩ := UF
      have M := cmoveL_spec (s := t) (x := x) (u := unitCand t x true) (labs := labs)
        (Ne.symm hxy) hD.live.2 Fx.lLive.2 hnd hlen (fun g hg => (hmem g hg).1.2.1)
      refine ⟨true, _, hrun, fun Lc hLc => ?_, M.Gsize, M.Csize, by rw [M.E]⟩
      obtain ⟨L', n, e, hok, -, hn⟩ := chunkSplitStepS_left κ t Lc hLc he hdir hlabs hD.live.2
        Fx.lLive.2 Fx.rLive.2
        (Ne.symm hxy) K.C K.G (fun g hg => (hmem g hg).1.2.1) (by
          have := hg0L.2.1
          have := K.G
          omega)
        (fun hov => by
          have h2 : gSrc t (cF t x) < t.Gs.size := (hG.ovf _ hg0L hov).1.2.1
          have := K.G
          exact lt_of_lt_of_le h2 (by omega))
        (by rcases hI'.cLs_lt (hI'.mem_chunks Fx.lLive) with h | h
            · rw [h]; have := hg0L.2.1; have := K.G; unfold NIL; omega
            · have := K.G; omega)
      exact ⟨L', n, e, by rw [hok]; rfl, by omega⟩
    · have ru := right_unit hI' hG he
      have hu : (unitCand t x false).length = 1 ∨ unitOK t x (unitCand t x false) = true := by
        rcases ru with ⟨-, h⟩ | ⟨p, -, -, -, -, h⟩
        · left; rw [h]; rfl
        · right; exact h
      have hdir' : cSz t (cRr t x) < cSz t (cLl t x) := by omega
      obtain ⟨labs, hlabs, hX'⟩ := hXs.moveR t A' gh hI' rfl hG hC hD.live hD.st he hdir' hFB hD.xx
      have hrun := chunkSplitStep_right he hdir' hu (Fx.radj hI' hD.live) hlabs
      have hlen : labs.length = (unitCand t x false).length := pushFrontLabs_len hlabs
      obtain ⟨hxc', tl, htl⟩ := hI'.run_ne_nil he
      have hE := hI'.cEnds x hxc'
      have hlm : cLs t x ∈ A'.grps x := by rw [hE.2, htl]; exact getLastD_cons_mem _ _ _
      have hgl : cLs t x ∈ A'.glist := A'.grps_sub_glist hxc' hlm
      have UF := unit_facts (u := unitCand t x false) (x := x) hI' hG hP (by
        rcases ru with ⟨hq, h⟩ | ⟨p, hp, hps, hr, h, hok⟩
        · left; rw [h]
          exact ⟨hq, rfl, hI'.mem_glist_iff.mp hgl, hI'.chk x hxc' _ hlm⟩
        · right
          refine ⟨p, hp, hps, by rw [h, hr], ?_⟩
          rw [h] at hok; exact (unitOK_three hok).2.2.2.2.1)
      obtain ⟨-, hnd, hmem, hone, hcl, hm1, hm2⟩ := UF
      have M := cmoveR_spec (s := t) (x := x) (u := unitCand t x false) (labs := labs)
        (Ne.symm hxz) hD.live.2 Fx.rLive.2 hnd hlen (fun g hg => (hmem g hg).1.2.1)
      have hglL := hI'.mem_glist_iff.mp hgl
      refine ⟨true, _, hrun, fun Lc hLc => ?_, M.Gsize, M.Csize, by rw [M.E]⟩
      obtain ⟨L', n, e, hok, -, hn⟩ := chunkSplitStepS_right κ t Lc hLc he hdir' hlabs hD.live.2
        Fx.lLive.2 Fx.rLive.2
        (Ne.symm hxz) K.C K.G (fun g hg => (hmem g hg).1.2.1) (by
          have := hglL.2.1
          have := K.G
          omega)
        (fun hov => by
          have h2 : gSrc t (cLs t x) < t.Gs.size := (hG.ovf _ hglL hov).1.2.1
          have := K.G
          exact lt_of_lt_of_le h2 (by omega))
        (by rcases hI'.cF_lt (hI'.mem_chunks Fx.rLive) with h | h
            · rw [h]; have := hglL.2.1; have := K.G; unfold NIL; omega
            · have := K.G; omega)
      exact ⟨L', n, e, by rw [hok]; rfl, by omega⟩

/-- **The drive of a splitting chunk agrees** (the context of `cinv_drive`). -/
theorem cinv_driveAgree {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {δ δu s₀ : Nat →
  Nat} {x : Nat}
    (hI : INV s A) (hG : GInv s A.elist gh (fun _ => 0)) (hC : CInvE s A.elist δ δu s₀ x)
    (hC1 : C1 s δ δu s₀ x) (hXs : CXSteps X Y A.elist δ δu s₀ x) (hX : X s) (hP : GParams s.P)
    (hCP : CParams s.P) (hxL : LiveC s x) (hst : cSt s x = .splitting)
    (hδ : ∀ c, c ≠ cLl s x → c ≠ x → c ≠ cRr s x → δ c = 0)
    (hδs : δ (cLl s x) + δ x + δ (cRr s x) ≤ 1)
    (hδle : δ (cLl s x) ≤ cSz s (cLl s x) ∧ δ x ≤ cSz s x ∧ δ (cRr s x) ≤ cSz s (cRr s x))
    {κ : Caps} (K : GCaps κ s) :
    ∃ s', CDriveAgree κ x s s' ∧ s'.Gs.size = s.Gs.size ∧ s'.C.size = s.C.size ∧ s'.E.size =
      s.E.size := by
  have hBounds := hC1.drive_bounds hCP.K2 hδs hδle
  generalize hl : cLl s x = y at *
  generalize hr : cRr s x = z at *
  generalize ha : cSz s y = a at *
  generalize hb : cSz s x = b at *
  generalize hc : cSz s z = c at *
  obtain ⟨hThi, hbal0, hfam0⟩ := hBounds
  have hs0 : s₀ x ≤ s.P.T := hC1.1
  let I' := fun j t => CDriveInv X s A.elist δ δu s₀ x y z a b c (units s x) j t ∧
    t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size
  have h0 : I' 0 s := ⟨⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hC, hxL, hst, hl, hr, by
    omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩⟩, rfl, rfl⟩
  have hstepM : ∀ j t, I' j t → ∃ bb t', (chunkSplitStep x).run t = .ok bb t' ∧ (bb = true → I'
    (j + 1) t') ∧
      CStepAgree κ x t t' bb ∧ t'.Gs.size = s.Gs.size ∧ t'.C.size = s.C.size ∧ t'.E.size =
        s.E.size := by
    intro j t ⟨hD, hGs, hCs⟩
    have K' : GCaps κ t := K.of_sizes hGs hD.ef.size hCs
    obtain ⟨bb, t', hrun, hA, hG', hC', hE'⟩ := hD.stepAgree hXs hP hCP hThi hbal0 hfam0 hδs hs0 K'
    refine ⟨bb, t', hrun, fun hb => ?_, hA, hG'.trans hGs, hC'.trans hCs, hE'.trans hD.ef.size⟩
    subst hb
    obtain ⟨t1, h1 | h1⟩ := hD.step hXs hP hCP (by
      intro c' h1 h2 h3
      exact hδ c' h1 h2 h3) hThi hbal0 hfam0 hδs hs0
    · rw [h1.1] at hrun; injection hrun with _ e; subst e
      exact ⟨h1.2, hG'.trans hGs, hC'.trans hCs⟩
    · rw [h1.1] at hrun; injection hrun with e; cases e
  obtain ⟨s', hA⟩ := driveChunkFromS_agree' κ s I' h0 (fun j t h _ => by
    obtain ⟨bb, t', a1, a2, a3, -⟩ := hstepM j t h; exact ⟨bb, t', a1, a2, a3⟩)
  obtain ⟨t, hrun, hres⟩ := driveChunkFrom_ok (s := s) (x := x) I'
    (fun t => t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size ∧ t.E.size = s.E.size) h0 (fun j t h _
      => by
      obtain ⟨bb, t', a1, a2, -, a4, a5, a6⟩ := hstepM j t h
      cases bb
      · exact ⟨t', Or.inr ⟨a1, a4, a5, a6⟩⟩
      · exact ⟨t', Or.inl ⟨a1, a2 rfl⟩⟩)
  rw [hA.1] at hrun; injection hrun with _ e; subst e
  refine ⟨s', hA, ?_⟩
  rcases hres with ⟨hD, hGs, hCs⟩ | h
  · exact ⟨hGs, hCs, hD.ef.size⟩
  · exact h

theorem CDriveAgree.eq_of_run {κ : Caps} {q : Nat} {s s' s'' : Core} (hA : CDriveAgree κ q s s'')
    (h : (driveChunkFrom q).run s = .ok () s') : s'' = s' := by
  rw [hA.1] at h; injection h

/-- **The chunk phase agrees** (the context of `driveChunk_ok`). -/
theorem driveChunkAgree {t : Core} {A : Abs} {L : List Nat} {gh : GGh} {s₀ δu : Nat → Nat}
    {e : Nat → Nat} {pops c : Nat} (hI : INV t A) (hel : A.elist = L)
    (hG : GInv t L gh (fun _ => 0)) (hC : CInv t L (δ1 c) δu s₀) (hLX : LX s₀ (δ1 c) δu t)
    (hN : CountInv t e pops) (hGP : GParams t.P) (hCP : CParams t.P) (hcL : LiveC t c)
    (hcnd : cSt t c ≠ .dead) (hcsz : 1 ≤ cSz t c) {κ : Caps} (K : GCaps κ t) {t4 : Core}
    (h : (driveChunk c).run t = .ok () t4) :
    (∃ L' n, evalF κ driveChunkS t (Machine.State.setLocs (fun _ => 0) ["x"] [c]) = .ok t4 L' n ∧
      n ≤ 30 + t.P.chunkBudget * 751) ∧ t4.Gs.size = t.Gs.size ∧ t4.C.size = t.C.size ∧
        t4.E.size = t.E.size := by
  have hδu := hC.δu
  have hcθ : cmax t.P ≤ t.P.theta := hCP.I4
  have drive : ∀ x, LiveC t x → cSt t x = .splitting →
      (c = cLl t x ∨ c = x ∨ c = cRr t x) → ∃ t4, CDriveAgree κ x t t4 ∧ t4.Gs.size = t.Gs.size ∧
        t4.C.size = t.C.size ∧ t4.E.size = t.E.size := by
    intro x hxL hxs hcx
    subst hel
    have Fx := hC.cfam x hxL hxs
    have hlx := Fx.lx hI hxL
    have hrx := Fx.rx hI hxL
    have hlr := Fx.lr hI hxL
    have hCx : CInvE t A.elist (δ1 c) δu s₀ x :=
      { hC with c1 := fun z hz hzs _ => hC.c1 z hz hzs (by
        unfold NIL
        have := hz.1
        omega) }
    have hC1 := hC.c1 x hxL hxs (by
      unfold NIL
      have := hxL.1
      omega)
    have hXs := cxsteps_count (cxsteps_dframe (cxsteps_linv (L := A.elist) (δ := δ1 c) (δu := δu)
      (s₀ := s₀) (x := x)) t hcθ)
    exact cinv_driveAgree hI hG hCx hC1 hXs ⟨⟨hLX, DFrame.refl t⟩, e, pops, hN⟩ hGP hCP
      hxL hxs (fun c' h1 h2 h3 => by
        unfold δ1; rw [ite_eq_right]; rintro rfl; rcases hcx with h | h | h <;> contradiction)
      (by
        unfold δ1
        rcases hcx with rfl | rfl | rfl <;> simp [hlx, hrx, hlr, Ne.symm hlx, Ne.symm hrx,
          Ne.symm hlr])
      (by
        unfold δ1
        refine ⟨?_, ?_, ?_⟩ <;> split <;> first | omega | (subst_vars; exact hcsz)) K
  have hxT : c < κ.tbl .C := by have := hcL.2; have := K.C; omega
  have hLx : Machine.State.setLocs (fun _ => 0) ["x"] [c] "x" = c := by
    simp [Machine.State.setLocs, Machine.State.upd]
  cases hs : cSt t c with
  | splitting =>
    have hs' : (t.C.getX c).st = .splitting := hs
    obtain ⟨t5, hA, hsz⟩ := drive c hcL hs (Or.inr (Or.inl rfl))
    rw [driveChunk_split hs'] at h
    have e := hA.eq_of_run h; subst e
    refine ⟨driveChunkS_agree κ t _ hLx hxT (by
      rw [driveChunk_split hs']
      exact h) (fun q hq => ?_), hsz⟩
    rcases hq with ⟨-, rfl⟩ | ⟨h', -⟩
    · exact hA
    · rw [hs'] at h'; cases h'
  | overflow =>
    have hs' : (t.C.getX c).st = .overflow := hs
    obtain ⟨hxL, hxs, hlr⟩ := hC.covf c hcL hs
    obtain ⟨t5, hA, hsz⟩ := drive _ hxL hxs
      (by
        rcases hlr with h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h.symm))
    rw [driveChunk_ovf hs'] at h
    have e := hA.eq_of_run h; subst e
    refine ⟨driveChunkS_agree κ t _ hLx hxT (by
      rw [driveChunk_ovf hs']
      exact h) (fun q hq => ?_), hsz⟩
    rcases hq with ⟨h', -⟩ | ⟨-, rfl⟩
    · rw [hs'] at h'; cases h'
    · exact hA
  | quiet =>
    have hs' : (t.C.getX c).st = .quiet := hs
    have h' := h
    rw [driveChunk_quiet hs'] at h'; injection h' with _ e; subst e
    refine ⟨driveChunkS_agree κ t _ hLx hxT h (fun q hq => ?_), rfl, rfl, rfl⟩
    rcases hq with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [hs'] at h' <;> cases h'
  | dead => exact absurd hs hcnd

theorem ResAgree.mono {κ : Caps} {t t' : Core} {stop : Bool} {D D' : Nat} (h : ResAgree κ t t'
  stop D)
    (hD : D ≤ D') : ResAgree κ t t' stop D' := fun L hdn => by
  obtain ⟨L', n, e, h1, h2⟩ := h L hdn; exact ⟨L', n, e, h1, by omega⟩

/-- **The reservation loop agrees**, from Level F's loop invariant and the agreement of each round:
a job step at a state with a job, a split start at a state with none. -/
theorem reservationAgreeOf {κ : Caps} {s : Core} (L : Loc) (I : Nat → Core → Prop) (Q : Core → Prop)
    {DJ DS : Nat} (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.reservationBudget →
      (t.resJob = none → (t.pqHi = 0 ∧ Q t) ∨
        (t.pqHi ≠ 0 ∧ ∃ c t1 t2, pqPopMax.run t = .ok c t1 ∧ (splitChunkStart c).run t1 = .ok ()
          t2 ∧
          I (j + 1) t2)) ∧
      (∀ job, t.resJob = some job → ∃ r t1, (jobStep job).run t = .ok r t1 ∧
        I (j + 1) {
          t1 with
          resJob := r
        }))
    (hJ : ∀ j t job, I j t → j < s.P.reservationBudget → t.resJob = some job → JobAgree κ t job DJ)
    (hS : ∀ j t c t1, I j t → j < s.P.reservationBudget → t.resJob = none → t.pqHi ≠ 0 →
      pqPopMax.run t = .ok c t1 →
      PQCaps κ t ∧ SplitAgree κ t1 c DS) :
    ∃ t' L' n, (reservation s.P.reservationBudget).run s = .ok () t' ∧ evalF κ reservationS s L
      = .ok t' L' n ∧
      n ≤ 5 + s.P.reservationBudget * (DJ + DS + 340 + 6) := by
  refine reservationS_agree κ s L (D := DJ + DS + 340) (fun j t => I j t) h0 (fun j t hI hj => ?_)
  obtain ⟨hn, hs⟩ := hstep j t hI hj
  cases hjob : t.resJob with
  | none =>
    rcases hn hjob with ⟨hq0, -⟩ | ⟨hq0, c, t1, t2, hp, hsc, hI'⟩
    · exact ⟨true, t, resF_empty hjob hq0, (fun h => absurd h (by decide)), (resAgree_empty hjob
        hq0).mono (by omega)⟩
    · obtain ⟨hq, hA⟩ := hS j t c t1 hI hj hjob hq0 hp
      exact ⟨false, t2, resF_split hjob hq0 hp hsc, fun _ => hI',
        (resAgree_split hjob hq hq0 hp hA hsc).mono (by omega)⟩
  | some job =>
    obtain ⟨r, t1, hr, hI'⟩ := hs job hjob
    exact ⟨false, _, resF_job hjob hr, fun _ => hI', (resAgree_job hjob (hJ j t job hI hj hjob)
      hr).mono (by omega)⟩

/-- The cost bound of the reservation loop of one insertion, from the bounds of a job step and a
split start. -/
def resBound (reservationBudget : Nat) : Nat := 5 + reservationBudget * (jobBound + splitBound
  + 340 + 6)

/-- **The reservation agrees** (the context of `reservation_cost`), relative to a predicate `Mc`
on cores that gives the Level M side conditions and that the rounds keep. -/
theorem reservationAgree_top {TI : Core → Prop} {μ : Core → Nat} {J n R : Nat} {cap : Params → Nat}
    {L : List Nat} {s : Core} {κ : Caps} (Lc : Loc) (hTC : TopContract TI μ J cap) (hTI : ∀ t,
      TI t → OrderMaintenance.Proof.Top.TopInv t)
    (h0 : ResInv TI s.P.reservationBudget J n R μ L s 0 s) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (OrderMaintenance.Zeroing.Hn (n - 1) + 1) ≤ s.P.T)
    (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    (Mc : Core → Prop) (hM0 : Mc s)
    (hMc : ∀ t, Mc t → TopCaps κ t ∧ PQCaps κ t ∧ t.prep = none ∧
      ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j = 0)
    (hMpop : ∀ t c t1, Mc t → pqPopMax.run t = .ok c t1 → Mc t1)
    (hMjob : ∀ j t job r t1, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t → t.resJob
      = some job →
      (jobStep job).run t = .ok r t1 → ResInv TI s.P.reservationBudget J n R μ L s (j + 1) {
        t1 with
        resJob := r
      } →
      Mc {
        t1 with
        resJob := r
      })
    (hMsplit : ∀ j t c t1 t2, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t → t.resJob
      = none → pqPopMax.run t = .ok c t1 →
      (splitChunkStart c).run t1 = .ok () t2 → ResInv TI s.P.reservationBudget J n R μ L s (j +
        1) t2 → Mc t2) :
    ∃ t' L' m, (reservation s.P.reservationBudget).run s = .ok () t' ∧ evalF κ reservationS s
      Lc = .ok t' L' m ∧
      m ≤ resBound s.P.reservationBudget ∧ Mc t' := by
  have hstep := resInv_step (k := s.P.reservationBudget) (L := L) hTC hn hsize hcap hI5
  have hstepI : ∀ j t, (ResInv TI s.P.reservationBudget J n R μ L s j t ∧ Mc t) → j <
    s.P.reservationBudget →
      (t.resJob = none → (t.pqHi = 0 ∧ Mc t) ∨
        (t.pqHi ≠ 0 ∧ ∃ c t1 t2, pqPopMax.run t = .ok c t1 ∧ (splitChunkStart c).run t1 = .ok ()
          t2 ∧
          (ResInv TI s.P.reservationBudget J n R μ L s (j + 1) t2 ∧ Mc t2))) ∧
      (∀ job, t.resJob = some job → ∃ r t1, (jobStep job).run t = .ok r t1 ∧
        (ResInv TI s.P.reservationBudget J n R μ L s (j + 1) {
          t1 with
          resJob := r
        } ∧ Mc {
          t1 with
          resJob := r
        })) := by
    intro j t ⟨hI, hM⟩ hj
    obtain ⟨hn', hs'⟩ := hstep j t hI hj
    refine ⟨fun hnone => ?_, fun job hjob => ?_⟩
    · rcases hn' hnone with ⟨h0, -⟩ | ⟨h0, c, t1, t2, hp, hsc, hI'⟩
      · exact Or.inl ⟨h0, hM⟩
      · exact Or.inr ⟨h0, c, t1, t2, hp, hsc, hI', hMsplit j t c t1 t2 hI hM hnone hp hsc hI'⟩
    · obtain ⟨r, t1, hr, hI'⟩ := hs' job hjob
      exact ⟨r, t1, hr, hI', hMjob j t job r t1 hI hM hjob hr hI'⟩
  obtain ⟨tF, hrunF, hF⟩ := reservation_ok (fun j t => ResInv TI s.P.reservationBudget J n R μ L
    s j t ∧ Mc t) Mc ⟨h0, hM0⟩ hstepI
  obtain ⟨t', L', m, hrun, he, hm⟩ := reservationAgreeOf (κ := κ) (s := s) Lc
    (fun j t => ResInv TI s.P.reservationBudget J n R μ L s j t ∧ Mc t) (fun _ => True) (DJ :=
      jobBound) (DS := splitBound)
    ⟨h0, hM0⟩
    (fun j t hIM hj => by
      obtain ⟨a, b⟩ := hstepI j t hIM hj
      refine ⟨fun hnone => ?_, b⟩
      rcases a hnone with ⟨h0, -⟩ | h
      · exact Or.inl ⟨h0, trivial⟩
      · exact Or.inr h)
    (fun j t job ⟨hI, hM⟩ _ hjob => by
      obtain ⟨hT, -, hpr, -⟩ := hMc t hM
      obtain ⟨-, hTt, -, hPt, -⟩ := hI
      exact jobAgree (hTI t hTt) hjob hpr (by
        rw [hPt]
        exact hpow) hT)
    (fun j t c t1 ⟨hI, hM⟩ _ hnone hq0 hp => by
      obtain ⟨hL, hTt, -, -, -⟩ := hI
      obtain ⟨-, hPQ, -⟩ := hMc t hM
      refine ⟨hPQ, ?_⟩
      obtain ⟨bl, nb, hQ⟩ := hL.pq
      obtain ⟨c', hpop, hcin, -⟩ := pqPopMax_ok hQ hq0
      have hM1 := hMpop t c t1 hM hp
      rw [hpop] at hp; injection hp with e1 e2; subst e1; subst e2
      have hcq := hcin
      unfold inQC at hcq; simp only [decide_eq_true_eq] at hcq
      obtain ⟨hcL, -, -⟩ := hcq
      obtain ⟨A, hIA, -⟩ := hL.inv
      have hD := delSt_only t c'
      have hI1 : INV (delSt t c') A := hIA.of_sameLinks hD.sameLinks (fun d => by
        simp only [cT, hD.C])
      have hT1 : TI (delSt t c') := hTC.frame _ _ hD.topSame hTt
      have hcL1 : LiveC (delSt t c') c' := by simp only [LiveC, hD.C]; exact hcL
      obtain ⟨hTC1, -, hpr1, hrow1⟩ := hMc _ hM1
      obtain ⟨D, hD', hA⟩ := splitAgree_top hI1 (hTI _ hT1) (by
        rw [hD.rest.2.2.2.2.2.2.2.2.1]
        exact hnone) hcL1
        hpr1 hrow1 hTC1
      exact fun t2 h => by
        obtain ⟨L', m, e, hm⟩ := hA t2 h
        exact ⟨L', m, e, by omega⟩)
  rw [hrunF] at hrun; injection hrun with _ e; subst e
  exact ⟨tF, L', m, hrunF, he, by unfold resBound; omega, by
    rcases hF with h | h
    · exact h.2
    · exact h⟩

theorem PQCaps.of_same {κ : Caps} {s s' : Core} (h : PQCaps κ s) (S : PQSame s s') : PQCaps κ s' :=
  ⟨h.cC, h.cB, by rw [S.next]; exact h.next, by rw [S.prev]; exact h.prev, by rw [S.head]; exact
    h.head,
    by rw [S.where_]; exact h.where_, by rw [S.nbn]; exact h.nbN, by rw [S.nbp]; exact h.nbP,
    by rw [S.lo]; exact h.lo, by rw [S.hi]; exact h.hi⟩

/-- The cost bound of the background work of one insertion at Level M. -/
def bgBound (P : Params) : Nat :=
  750 + 600 + (30 + P.groupBudget * 401) + (30 + P.chunkBudget * 751) + resBound
    P.reservationBudget + 100

/-- **The background work agrees** (the context of `background_ok`), relative to a predicate `Mc`
on cores that gives the Level M side conditions of the reservation and that its rounds keep. -/
theorem bgAgree {TI : Core → Prop} {μ : Core → Nat} {J k n R : Nat} {cap : Params → Nat} {L :
  List Nat}
    {s0 s1 s2 : Core} {y g c : Nat} (hTC : TopContract TI μ J cap) (hTI : ∀ t, TI t →
      OrderMaintenance.Proof.Top.TopInv t)
    (hPost : InsPost TI k J n R μ L s0 g c s2) (hy : y ∈ L) (heg1 : eG s1 y = g)
    (hgc1 : gC s1 g = c) (hchunk : (chunkSize c true).run s1 = .ok () s2)
    (hE12 : s2.E = s1.E) (hP1 : s1.P = s0.P) (hkP : s0.P.reservationBudget = k) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s2.count / (s0.P.theta + 1 - cmax s0.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s2.count / (s0.P.theta + 1 - cmax s0.P)) ≤ cap s0.P)
    (hI5 : (s0.P.theta : ℝ) + R * (OrderMaintenance.Zeroing.Hn (n - 1) + 1) ≤ s0.P.T)
    {κ : Caps} (Ly : Loc) (hLy : Ly "y" = y) (hpow : s0.P.a = 2 ^ Nat.log2 s0.P.a)
    (hq1 : PQCaps κ s1) (hcC : c < Ccap κ) (hcB : (s1.C.getX c).size + 1 < Bcap κ)
    (K1 : GCaps κ s1) (hG2 : s1.Gs.size + 2 ≤ κ.tbl .G) (hF0 : 0 < κ.lrec .freeG)
    (hF : s1.freeG.length ≤ κ.lcap .freeG) (hyE : y < κ.tbl .E)
    (Mc : Core → Prop) (hM4 : ∀ t, DFrame s2 t → PQCaps κ t → t.Gs.size ≤ s1.Gs.size + 2 → Mc t)
    (hMc : ∀ t, Mc t → TopCaps κ t ∧ PQCaps κ t ∧ t.prep = none ∧
      ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j = 0)
    (hMpop : ∀ t c t1, Mc t → pqPopMax.run t = .ok c t1 → Mc t1)
    (hMjob : ∀ s j t job r t1, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t →
      t.resJob = some job →
      (jobStep job).run t = .ok r t1 → ResInv TI s.P.reservationBudget J n R μ L s (j + 1) {
        t1 with
        resJob := r
      } →
      Mc {
        t1 with
        resJob := r
      })
    (hMsplit : ∀ s j t c t1 t2, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t →
      t.resJob = none → pqPopMax.run t = .ok c t1 →
      (splitChunkStart c).run t1 = .ok () t2 → ResInv TI s.P.reservationBudget J n R μ L s (j +
        1) t2 → Mc t2) :
    ∃ s', (background y).run s1 = .ok () s' ∧
      (∃ L' m, evalF κ backgroundS s1 Ly = .ok s' L' m ∧ m ≤ bgBound s0.P) ∧ Mc s' := by
  obtain ⟨A, hI, hel⟩ := hPost.inv
  obtain ⟨gh, hG⟩ := hPost.ginv
  obtain ⟨s₀, hC, hLX⟩ := hPost.cinv
  obtain ⟨e, pops, hN⟩ := hPost.cnt
  obtain ⟨⟨lg, hLi⟩, hLP, hGP⟩ := hLX
  have hP2 : s2.P = s0.P := hPost.P
  obtain ⟨hgL, hgc, hpos⟩ := hPost.grp
  have heg2 : eG s2 y = g := by simp only [eG, hE12]; exact heg1
  have hS12 : Same s1 s2 := by have := pres_chunkSize c true s1; rw [hchunk] at this; exact this
  subst hel
  -- the group phase
  have hXg := (((xgroup_cinv (L := A.elist) (δ := δ1 c) (δu := fun _ => 0) (s₀ := s₀) (c := c)
    (by
      unfold δ1
      simp)).and (xgroup_linv (L := A.elist) (s₀ := s₀) (δ := δ1 c)
      (δu := fun _ => 0) (c := c))).and (xgroup_frame (L := A.elist) (c := c) s2)).and
    (xgroup_track (L := A.elist) (c' := c) y c hy)
  have hroom := hPost.split_room
  have hX0 : (((CInv s2 A.elist (δ1 c) (fun _ => 0) s₀ ∧ LX s₀ (δ1 c) (fun _ => 0) s2) ∧
      CFrame s2 s2) ∧ gC s2 (eG s2 y) = c) :=
    ⟨⟨⟨hC, ⟨lg, hLi⟩, hLP, hGP⟩, CFrame.refl s2⟩, by rw [heg2, hgc]⟩
  obtain ⟨s3, hgp, hDD⟩ := groupPhase_ok hI (by
    rw [hgc]
    exact hXg) hX0 hG hGP hgL hpos hroom
  -- the state after the split start
  have hsplit : ∃ s2', (if ((s2.Gs.getX g).st == St.quiet && decide ((s2.Gs.getX g).size ≥
    s2.P.G)) = true then
      startGroupSplit g else pure ()).run s2 = .ok () s2' ∧ (driveGroup g).run s2' = .ok () s3 := by
    by_cases hcond : ((s2.Gs.getX g).st == St.quiet && decide ((s2.Gs.getX g).size ≥ s2.P.G)) = true
    · rw [ite_eq_left hcond] at hgp ⊢
      obtain ⟨u, s2', h2a, h2b⟩ := run_bind_ok hgp
      exact ⟨s2', h2a, h2b⟩
    · rw [ite_eq_right hcond] at hgp ⊢
      exact ⟨s2, rfl, hgp⟩
  obtain ⟨s2', h2a, h2b⟩ := hsplit
  have K2 : GCaps κ s2 := ⟨by rw [hS12.1.Gsize]; exact K1.G, by rw [hS12.1.Esize]; exact K1.E,
    by rw [hS12.1.Csize]; exact K1.C, K1.fl, K1.f0⟩
  have hXc : ∀ t, (((CInv t A.elist (δ1 c) (fun _ => 0) s₀ ∧ LX s₀ (δ1 c) (fun _ => 0) t) ∧
      CFrame s2 t) ∧ gC t (eG t y) = c) → ∀ g, LiveG t g → gC t g < t.C.size :=
    fun t hx g hg => (hx.1.1.1.gchk g hg).1.2
  obtain ⟨mG2, ⟨L3, n3, e3, hn3⟩, hsz3⟩ := groupPhaseAgree hI (by
    rw [hgc]
    exact hXg) hX0 hG hGP hgL hpos hroom
    hXc K2 (by
      rw [hS12.1.Gsize]
      exact hG2) hF0 (by
      rw [hS12.1.freeG]
      exact hF) h2a h2b
  obtain ⟨hGs3, hCs3, hEs3, hE2', hP2'⟩ := hsz3
  -- the state after the group phase
  obtain ⟨A3, hI3, hel3⟩ := hDD.inv
  obtain ⟨gh3, hG3⟩ := hDD.ginv
  have hP3 : s3.P = s2.P := hDD.P
  obtain ⟨δu', hC3, hLX3, hCF, htr⟩ : ∃ δu' : Nat → Nat, CInv s3 A.elist (δ1 c) δu' s₀ ∧
      LX s₀ (δ1 c) δu' s3 ∧ CFrame s2 s3 ∧ gC s3 (eG s3 y) = c := by
    rcases hDD.x with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · exact ⟨_, h1, h2, h3, h4⟩
    · exact ⟨_, h1, h2, h3, h4⟩
  have hQS := hCF.qsame
  have hcL3 : LiveC s3 c := by simp only [LiveC, hCF.Csize]; exact hPost.cL
  have hcnd3 : cSt s3 c ≠ .dead := by
    rw [(hCF.C c).2.1, ← hgc]; exact (hC.gchk g hgL).2
  have hcsz3 : 1 ≤ cSz s3 c := by rw [(hCF.C c).1]; exact hPost.csz
  -- the chunk phase
  obtain ⟨t4, hdc, hCP4⟩ := driveChunk_ok hI3 hel3 hG3 (hel3 ▸ hC3) hLX3
    (hN.frame hQS hCF.count) (by
      rw [hP3]
      exact hGP) (by
      rw [hP3]
      exact hPost.cp) hcL3 hcnd3
    hcsz3
  have K3 : GCaps κ s3 := by
    refine ⟨?_, ?_, ?_, K1.fl, K1.f0⟩
    · have := hS12.1.Gsize; have := K1.G; omega
    · rw [hEs3, hS12.1.Esize]; exact K1.E
    · rw [hCs3, hS12.1.Csize]; exact K1.C
  obtain ⟨⟨L4, n4, e4, hn4⟩, hGs4, -⟩ := driveChunkAgree hI3 hel3 hG3 (hel3 ▸ hC3) hLX3
    (hN.frame hQS hCF.count) (by
      rw [hP3]
      exact hGP) (by
      rw [hP3]
      exact hPost.cp) hcL3 hcnd3
    hcsz3 K3 hdc
  have hD : DFrame s2 t4 := hCF.dframe.trans hCP4.fr
  -- the reservation
  have hk2 : s1.P.reservationBudget = k := by rw [hP1]; exact hkP
  have hP4 : t4.P = s0.P := hD.P.trans hP2
  have h0 := hCP4.reservation_invariant hTC hPost hD
  -- chunkSize at Level M
  have hcs1 : c < s1.C.size := by have := hPost.cL.2; rw [hS12.1.Csize] at this; exact this
  obtain ⟨⟨L1, n1, e1, hn1⟩, hq2⟩ := csP_agree (κ := κ) (L := Machine.State.setLocs (fun _ => 0)
    ["c"] [c])
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) hcs1 (by
        have := K1.C
        omega) hq1 hcC hcB hchunk
  have hq4 : PQCaps κ t4 := hq2.of_same hD.pq
  have hkt : t4.P.reservationBudget = k := by rw [hP4]; exact hkP
  obtain ⟨s', L5, n5, hres, e5, hn5, hMs⟩ := reservationAgree_top (κ := κ)
    (Machine.State.setLocs (fun _ => 0) [] [])
    hTC hTI (by
      rw [hkt]
      exact h0) hn (by
      rw [hD.count, hP4]
      exact hsize) (by
      rw [hD.count, hP4]
      exact hcap)
    (by
      rw [hP4]
      exact hI5) (by
      rw [hP4]
      exact hpow) Mc (hM4 t4 hD hq4 (by
      rw [hGs4]
      have := hS12.1.Gsize
      omega)) hMc hMpop
    (fun j t job r t1 => hMjob t4 j t job r t1) (fun j t c t1 t2 => hMsplit t4 j t c t1 t2)
  rw [hkt] at hres
  -- assembly
  have hgo1 : gOf s1 y = g := heg1
  have hco1 : cOf s1 y = c := by change gC s1 (eG s1 y) = c; rw [heg1, hgc1]
  have hgo2 : gOf s2 y = g := heg2
  have hgo2' : gOf s2' y = g := by change (s2'.E.getX y).grp = g; rw [hE2']; exact heg2
  have hgo3 : gOf s3 y < s3.Gs.size := by
    have := (hI3.mem_glist_iff.mp (hI3.eG_mem (hel3 ▸ hy))).2.1; exact this
  have hco3 : cOf s3 y = c := htr
  have hb : bgSplit s2 y s1.P = ((s2.Gs.getX g).st == St.quiet && decide ((s2.Gs.getX g).size ≥
    s2.P.G)) := by
    simp only [bgSplit, hgo2, hP1, hP2]
  obtain ⟨hrun, L', m, e, hm⟩ := backgroundS_agree (κ := κ) (L := Ly) (s0 := s1) (s1 := s2) (s2
    := s2') (s3 := s3)
    (s4 := t4) (s5 := s') hLy (by
      rw [hco1]
      exact hchunk) (by
      rw [hb, hgo2]
      exact h2a) (by
      rw [hgo2']
      exact h2b)
    (by
      rw [hco3]
      exact hdc) (by
      rw [hk2]
      exact hres)
    ⟨L1, n1, by rw [hco1]; exact e1, hn1⟩
    (fun hc => by
      rw [hb] at hc
      obtain ⟨L2, n2, e2, hn2⟩ := mG2 hc
      exact ⟨L2, n2, by rw [hgo2]; exact e2, hn2⟩)
    ⟨L3, n3, by rw [hgo2']; exact e3, hn3⟩
    ⟨L4, n4, by rw [hco3]; exact e4, hn4⟩
    ⟨L5, n5, e5, hn5⟩
    (by
      rw [hP1, hP2]) hyE (by
        rw [hgo1]
        have := hgL.2.1
        rw [hS12.1.Gsize] at this
        have := K1.G
        omega)
    (by
      rw [hgo2]
      have := hgL.2.1
      have := K2.G
      omega)
    (by
      have := K3.G
      omega)
  refine ⟨s', hrun, ⟨L', m, e, ?_⟩, hMs⟩
  have hP2'' : s2'.P = s0.P := by rw [hP2', hP2]
  have hP3' : s3.P = s0.P := by rw [hP3, hP2]
  rw [hP2'', hP3', hP4] at hm
  unfold bgBound
  generalize resBound s0.P.reservationBudget = RB at hm ⊢
  exact hm


/-- **The capacities an insertion needs** at its start (besides those of the top structure). -/
structure InsCaps (κ : Caps) (s : Core) : Prop where
  E : s.E.size + 2 ≤ κ.tbl .E
  G : s.Gs.size + 2 ≤ κ.tbl .G
  C : s.C.size ≤ κ.tbl .C
  fl : κ.tbl .G ≤ κ.lcap .freeG
  f0 : 0 < κ.lrec .freeG
  pq : PQCaps κ s
  cC : s.C.size ≤ Ccap κ
  cB : ∀ c, LiveC s c → (s.C.getX c).size + 2 < Bcap κ

theorem linkElem_frame (s : Core) (x y lab h : Nat) :
    (linkElem s x y lab h).Gs.size = s.Gs.size ∧ (linkElem s x y lab h).C = s.C ∧
    (linkElem s x y lab h).freeG = s.freeG ∧ (linkElem s x y lab h).E.size = s.E.size + 1 ∧
    PQSame s (linkElem s x y lab h) ∧ (linkElem s x y lab h).nodes = s.nodes ∧
    (linkElem s x y lab h).path = s.path ∧ (linkElem s x y lab h).prep = s.prep ∧
    (linkElem s x y lab h).P = s.P := by
  unfold linkElem; dsimp only
  refine ⟨by simp, rfl, rfl, by split_ifs <;> simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩, rfl, rfl, rfl, rfl⟩

/-- The cost bound of an insertion at Level M. -/
def insBound (P : Params) : Nat := bgBound P + 220

/-- **An insertion agrees** (the context of `insertAfter_cost`), relative to a predicate `Mc` on
cores that gives the Level M side conditions of the reservation and that its rounds keep. -/
theorem insertAgree {TI : Core → Prop} {μ : Core → Nat} {J n R : Nat} {cap : Params → Nat} {L :
  List Nat}
    {s : Core} {x : Nat} (hTC : TopContract TI μ J cap) (hTI : ∀ t, TI t →
      OrderMaintenance.Proof.Top.TopInv t)
    (hC : CostInv TI μ J n R L s)
    (hx : x ∈ L) (hk : 1 ≤ s.P.reservationBudget) (hR : J / s.P.reservationBudget + 1 ≤ R) (hn
      : 1 ≤ n)
    (hsize : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (OrderMaintenance.Zeroing.Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat)
    {κ : Caps} (Lx : Loc) (hLx : Lx "x" = x) (hLh : Lx "h" = hh) (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    (K : InsCaps κ s) (Mc : Core → Prop)
    (hM4 : ∀ t, OrderMaintenance.Proof.Top.ts t = OrderMaintenance.Proof.Top.ts s → t.resJob =
      s.resJob → t.prep = s.prep →
      t.C.size = s.C.size → t.count = s.count + 1 → t.Gs.size ≤ s.Gs.size + 2 → PQCaps κ t → Mc t)
    (hMc : ∀ t, Mc t → TopCaps κ t ∧ PQCaps κ t ∧ t.prep = none ∧
      ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j = 0)
    (hMpop : ∀ t c t1, Mc t → pqPopMax.run t = .ok c t1 → Mc t1)
    (hMjob : ∀ L s j t job r t1, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t →
      t.resJob = some job →
      (jobStep job).run t = .ok r t1 → ResInv TI s.P.reservationBudget J n R μ L s (j + 1) {
        t1 with
        resJob := r
      } →
      Mc {
        t1 with
        resJob := r
      })
    (hMsplit : ∀ L s j t c t1 t2, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t →
      t.resJob = none → pqPopMax.run t = .ok c t1 →
      (splitChunkStart c).run t1 = .ok () t2 → ResInv TI s.P.reservationBudget J n R μ L s (j +
        1) t2 → Mc t2) :
    ∃ s', (insertAfter x hh).run s = .ok s.E.size s' ∧
      (∃ L' m, evalF κ insertAfterP.body s Lx = .ok s' L' m ∧ L' "y" = s.E.size ∧ m ≤ insBound
        s.P) ∧
      CostInv TI μ J n R (OrderMaintenance.Spec.insertAfterL x s.E.size L) s' ∧ s'.count =
        s.count + 1 ∧
      s'.P = s.P ∧ Mc s' := by
  obtain ⟨y, i, a, ip, js, hG, hRO⟩ := hC.game
  have hdiv : s.count / (s.P.theta + 1 - cmax s.P) ≤ (s.count + 1) / (s.P.theta + 1 - cmax s.P) :=
    Nat.div_le_div_right (Nat.le_succ s.count)
  have hcnt0 : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1 := by omega
  obtain ⟨s1, s2, hrun1, hrun2, hPost, heG, hgC, hE12, hP1⟩ := insert_step hTC hC.low hC.ti hG
    hRO hx
    hk hR hn hcnt0 hI5 hh
  have hyL : s.E.size ∈ OrderMaintenance.Spec.insertAfterL x s.E.size L :=
    (OrderMaintenance.Spec.mem_insertAfterL hx).mpr (Or.inl rfl)
  -- the state after the element insertion
  obtain ⟨A, hI, hel⟩ := hC.low.inv
  obtain ⟨gh, hG0⟩ := hC.low.ginv
  obtain ⟨s₀, -, -, -, hGP⟩ := hC.low.cinv
  subst hel
  obtain ⟨lab, hrunE, -⟩ := ins_elem_ok hI hG0 hGP hx hh
  rw [hrunE] at hrun1; injection hrun1 with _ e1; subst e1
  obtain ⟨fG, fC, fF, fE, fPQ, fN, fPa, fPr, fP⟩ := linkElem_frame s x s.E.size lab hh
  set s1 := linkElem s x s.E.size lab hh
  rw [heG, hgC] at hrun2
  have hS12 : Same s1 s2 := by
    have := pres_chunkSize (gC s (eG s x)) true s1; rw [hrun2] at this; exact this
  have hgL : LiveG s (eG s x) := hI.mem_glist_iff.mp (hI.eG_mem hx)
  obtain ⟨s₀', hCI, -⟩ := hC.low.cinv
  have hcL : LiveC s (gC s (eG s x)) := (hCI.gchk _ hgL).1
  obtain ⟨s2', hrun2', hPQ2, -⟩ := chunkSize_ok (lab := lab) (hh := hh) hC.low.pq hcL
  rw [hrun2] at hrun2'; injection hrun2' with _ e2; subst e2
  obtain ⟨-, -, hC2, -, r2⟩ := hPQ2
  obtain ⟨-, -, -, -, -, -, -, hpr2, hjb2, -, hN2, hPa2, hci2, hlp2⟩ := r2
  have hsC : (sizeState s1 (gC s (eG s x))).C.size = s1.C.size := by simp [sizeState]
  have hsN : (sizeState s1 (gC s (eG s x))).nodes = s1.nodes := rfl
  have hsPa : (sizeState s1 (gC s (eG s x))).path = s1.path := rfl
  have hsPr : (sizeState s1 (gC s (eG s x))).prep = s1.prep := rfl
  obtain ⟨s', hbg, ⟨Lb, mb, eb, hmb⟩, hMs⟩ := bgAgree hTC hTI hPost hyL heG hgC hrun2 hE12 hP1
    rfl hn
    (by
      rw [hPost.count]
      exact hsize) (by
      rw [hPost.count]
      exact hcap) hI5
    (Machine.State.setLocs (fun _ => 0) ["y"] [s.E.size]) (by
      simp [Machine.State.setLocs, Machine.State.upd])
    hpow (K.pq.of_same fPQ) (by
      have := hcL.2
      have := K.cC
      omega)
    (by
      rw [fC]
      have := K.cB (gC s (eG s x)) hcL
      omega)
    ⟨by rw [fG]; have := K.G; omega, by rw [fE]; have := K.E; omega, by rw [fC]; exact K.C,
      K.fl, K.f0⟩
    (by
      rw [fG]
      exact K.G) K.f0 (by
      rw [fF]
      have := hI.freeG_len
      have := K.G
      have := K.fl
      omega)
    (by
      have := K.E
      omega) Mc
    (fun t hD hq hGt => hM4 t (by
        have hPt : t.P = s.P := by rw [hD.P, hPost.P]
        have hNt : t.nodes = s.nodes := by rw [hD.top.1, hN2, hsN, fN]
        have hPat : t.path = s.path := by rw [hD.top.2.1, hPa2, hsPa, fPa]
        have hct : t.cin = s.cin := by rw [hD.top.2.2.1, hci2]; rfl
        have hlt : t.lpar = s.lpar := by rw [hD.top.2.2.2.1, hlp2]; rfl
        have htag : ∀ c, (t.C.getX c).tag = (s.C.getX c).tag := fun c => by
          have := (hD.links c).2.2
          change cT t c = cT s c
          rw [this]; change (s2.C.getX c).tag = _
          rw [hC2]; simp only [sizeState, Array.getX_modify]; rw [fC]; split <;> rfl
        unfold OrderMaintenance.Proof.Top.ts; rw [hPt, hNt, hPat, hct, hlt]; simp only [htag])
      (by
        rw [hD.top.2.2.2.2.1, hjb2]
        rfl)
      (by rw [hD.top.2.2.2.2.2.1, hpr2, hsPr, fPr]) (by rw [hD.Csize, hC2, hsC, fC])
      (by rw [hD.count, hPost.count]) (by
        rw [fG] at hGt
        exact hGt) hq)
    hMc hMpop (hMjob _) (hMsplit _)
  have hxs := hI.size_pos hx
  obtain ⟨hrunI, Li, mi, ei, hyi, hmi⟩ := insertAfterP_agree (κ := κ) (L := Lx) hLx hLh hxs.2
    hgL.2.1
    (by rcases hI.eN_mem hx with h | h
        · left; exact h
        · right; exact (hI.size_pos h).2)
    (by
      have := K.E
      omega) (by
      have := K.G
      omega) hrunE hbg
    ⟨Lb, mb, eb, hmb⟩
  obtain ⟨s'', hrun'', -, hCI', hcnt', hP''⟩ := insertAfter_cost hTC hC hx hk hR hn hsize hcap
    hI5 hh
  rw [hrunI] at hrun''; injection hrun'' with _ e; subst e
  exact ⟨s', hrunI, ⟨Li, mi, ei, hyi, by unfold insBound; omega⟩, hCI', hcnt', hP'', hMs⟩


end OrderMaintenance.Impl

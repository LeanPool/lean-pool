/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.InsStep


/-!
# Parts of the background work

Closing Lemma C3's undriven counts; the inserted element stays in its chunk through the group
phase; the chunk count through the chunk drive.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- Undriven insertions can always be forgotten in Lemma C3 (they only gave slack). -/
theorem LInv.close {s : Core} {lg : LGh} {s₀ δ δu : Nat → Nat} (hL : LInv s lg s₀ δ δu)
    (hδu : ∀ c, δu c ≤ δ c) : LInv s lg s₀ (fun _ => 0) (fun _ => 0) := by
  refine { hL with arrS := fun x hx hxs => ?_ }
  have h := hL.arrS x hx hxs
  have := hδu x
  simp only [Nat.add_zero, Nat.mul_zero]
  omega

theorem LX.close {s : Core} {s₀ δ δu : Nat → Nat} (h : LX s₀ δ δu s) (hδu : ∀ c, δu c ≤ δ c) :
    LX s₀ (fun _ => 0) (fun _ => 0) s := by
  obtain ⟨⟨lg, hL⟩, h2, h3⟩ := h; exact ⟨⟨lg, hL.close hδu⟩, h2, h3⟩

/-- **The inserted element stays in its chunk** through the group phase. -/
theorem xgroup_track {L : List Nat} {c' : Nat} (y c : Nat) (hy : y ∈ L) :
    XGroup (fun t => gC t (eG t y) = c) (fun t => gC t (eG t y) = c) L c' := by
  refine ⟨fun δ p => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t A gh hI hel hG hok hst hX
    subst hel
    have hp' := hI.mem_glist_iff.mpr hok.live
    have hl' : gLl t p ∈ A.glist := hI.mem_of_gN hok.adj hok.live.1
    have hlp : gLl t p ≠ p := by
      intro e; have := hok.adj; rw [e, hI.gList.next p hp'] at this
      exact succOf_ne_self hI.gList.nodup p hok.live.1 this
    obtain ⟨rest, hrun⟩ := hI.run_head hp' hok.ne
    have hm := mem_runOf.mp (hrun ▸ (by simp : gF t p ∈ gF t p :: rest))
    have M := moveLState_spec hlp hok.live.2.1 (hI.gAlloc _ hl') ((hI.eAlloc _).mp hm.1).2
    rw [M.eG, M.links.chk]
    split
    · next he => rw [hok.chk, ← hX, he, hm.2]
    · exact hX
  · intro t A gh hI hel hG hok hst hX
    subst hel
    have hp' := hI.mem_glist_iff.mpr hok.live
    have hr' : gRr t p ∈ A.glist := hI.mem_of_gP hok.adj hok.live.1
    have hrp : gRr t p ≠ p := by
      intro e; have := hok.adj; rw [e, hI.gList.prev p hp'] at this
      exact predOf_ne_self hI.gList.nodup p hok.live.1 this
    obtain ⟨front, hrun⟩ := hI.run_last hp' hok.ne
    have hm := mem_runOf.mp (hrun ▸ (by simp : gLs t p ∈ front ++ [gLs t p]))
    have M := moveRState_spec hrp hok.live.2.1 (hI.gAlloc _ hr') ((hI.eAlloc _).mp hm.1).2
    rw [M.eG, M.links.chk]
    split
    · next he => rw [hok.chk, ← hX, he, hm.2]
    · exact hX
  · intro t A gh hI hel hG hp hs he hl hr hl' hr' hc hX
    subst hel
    have Fp := hG.fam p hp hs
    have hpp : gP t p ≠ p := by
      rw [hI.gList.prev p (hI.mem_glist_iff.mpr hp)]; exact predOf_ne_self hI.gList.nodup p hp.1
    have hgPl : gP t p = gLl t p := by
      have := hI.gP_gN (hI.mem_glist_iff.mpr Fp.lLive) (by rw [Fp.lAdj]; exact hp.1)
      rw [Fp.lAdj] at this; exact this
    have R := removeState_spec hp.2.1 Fp.lLive.2.1 Fp.rLive.2.1 hpp
      (fun _ => by rw [hgPl]; exact Fp.lLive.2.1)
    have : eG (removeState t p) y = eG t y := by simp only [eG, R.E]
    rw [this, R.chk]; exact hX
  · intro s A gh g labL labR hI hel hG hg hq hsz hL hR hX
    subst hel
    have S := splitSpec hI (hI.mem_glist_iff.mpr hg) labL labR
    have hyl : LiveG s (eG s y) := hI.mem_glist_iff.mp (hI.eG_mem hy)
    have : eG (splitState s g labL labR) y = eG s y := by simp only [eG, S.E]
    rw [this, S.chk, ite_eq_right]
    · exact hX
    · rintro (h | h)
      · exact S.glOut (h ▸ hyl)
      · exact S.grOut (h ▸ hyl)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem cmoveL_qsame {s : Core} {x : Nat} {u labs : List Nat} (hxy : x ≠ cLl s x)
    (hx : x < s.C.size) (hy : cLl s x < s.C.size) (hxs : cSt s x = .splitting)
    (hys : cSt s (cLl s x) = .overflow) : QSame s (cmoveLState s x u labs) := by
  have hCs : (moveGroupsLeft s x (cLl s x) u labs).C.size = s.C.size := by simp [moveGroupsLeft]
  have hC := fun c => cmoveSizes_C (t := moveGroupsLeft s x (cLl s x) u labs) (u := u) hxy
    (by rw [hCs]; exact hx) (by rw [hCs]; exact hy) c
  have hCm := fun c => moveGroupsLeft_C (s := s) (u := u) (labs := labs) hxy hx hy c
  have fld : ∀ c, cSt (cmoveLState s x u labs) c = cSt s c ∧
      (c ≠ x → c ≠ cLl s x → cSz (cmoveLState s x u labs) c = cSz s c) := by
    intro c
    simp only [cSt, cSz, cmoveLState]
    rw [hC c, hCm c]
    by_cases h1 : c = x
    · subst h1; simp only [ite_true, ite_eq_right hxy]; split <;> simp
    · by_cases h2 : c = cLl s x
      · subst h2; simp [h1]
      · simp [h1, h2]
  refine ⟨by simp [cmoveLState, cmoveSizes, hCs], rfl, fun c _ => by rw [(fld c).1],
    fun c _ hq => (fld c).2 ?_ ?_⟩
  · rintro rfl; rw [hxs] at hq; cases hq
  · rintro rfl; rw [hys] at hq; cases hq

theorem cmoveR_qsame {s : Core} {x : Nat} {u labs : List Nat} (hxz : x ≠ cRr s x)
    (hx : x < s.C.size) (hz : cRr s x < s.C.size) (hxs : cSt s x = .splitting)
    (hzs : cSt s (cRr s x) = .overflow) : QSame s (cmoveRState s x u labs) := by
  have hCs : (moveGroupsRight s x (cRr s x) u labs).C.size = s.C.size := by simp [moveGroupsRight]
  have hC := fun c => cmoveSizes_C (t := moveGroupsRight s x (cRr s x) u labs) (u := u) hxz
    (by rw [hCs]; exact hx) (by rw [hCs]; exact hz) c
  have hCm := fun c => moveGroupsRight_C (s := s) (u := u) (labs := labs) hxz hx hz c
  have fld : ∀ c, cSt (cmoveRState s x u labs) c = cSt s c ∧
      (c ≠ x → c ≠ cRr s x → cSz (cmoveRState s x u labs) c = cSz s c) := by
    intro c
    simp only [cSt, cSz, cmoveRState]
    rw [hC c, hCm c]
    by_cases h1 : c = x
    · subst h1; simp only [ite_true, ite_eq_right hxz]; split <;> simp
    · by_cases h2 : c = cRr s x
      · subst h2; simp [h1]
      · simp [h1, h2]
  refine ⟨by simp [cmoveRState, cmoveSizes, hCs], rfl, fun c _ => by rw [(fld c).1],
    fun c _ hq => (fld c).2 ?_ ?_⟩
  · rintro rfl; rw [hxs] at hq; cases hq
  · rintro rfl; rw [hzs] at hq; cases hq

/-- **The chunk count through the chunk drive.** -/
theorem cxsteps_count {X Y : Core → Prop} {L : List Nat} {δ δu s₀ : Nat → Nat} {x : Nat}
    (h : CXSteps X Y L δ δu s₀ x) :
    CXSteps (fun t => X t ∧ ∃ e pops, CountInv t e pops)
      (fun t => Y t ∧ ∃ e pops, CountInv t e pops) L δ δu s₀ x := by
  refine h.and ?_ ?_ ?_
  · intro t A gh labs hI hel hG hC hxL hst hX
    subst hel
    obtain ⟨e, pops, hN⟩ := hX
    have Fx := hC.cfam x hxL hst
    exact ⟨e, pops, hN.frame (cmoveL_qsame (Ne.symm (Fx.lx hI hxL)) hxL.2 Fx.lLive.2 hst Fx.lSt) rfl⟩
  · intro t A gh labs hI hel hG hC hxL hst hX
    subst hel
    obtain ⟨e, pops, hN⟩ := hX
    have Fx := hC.cfam x hxL hst
    exact ⟨e, pops, hN.frame (cmoveR_qsame (Ne.symm (Fx.rx hI hxL)) hxL.2 Fx.rLive.2 hst Fx.rSt) rfl⟩
  · intro t A gh hI hel hG hC hxL hst hl hr hX
    subst hel
    obtain ⟨e, pops, hN⟩ := hX
    have Fx := hC.cfam x hxL hst
    exact ⟨_, pops, hN.remove hxL.2 Fx.lLive.2 Fx.rLive.2 (Fx.lx hI hxL) (Fx.rx hI hxL) hst Fx.lSt
      Fx.rSt hl hr⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem driveChunk_run_split {t : Core} {c : Nat} (h : cSt t c = .splitting) :
    (driveChunk c).run t = (driveChunkFrom c).run t := by
  unfold driveChunk; simp only [run_getC_bind]; simp only [cSt] at h; rw [h]

theorem driveChunk_run_ovf {t : Core} {c : Nat} (h : cSt t c = .overflow) :
    (driveChunk c).run t = (driveChunkFrom (cSrc t c)).run t := by
  unfold driveChunk; simp only [run_getC_bind]; simp only [cSt] at h; rw [h]

theorem driveChunk_run_quiet {t : Core} {c : Nat} (h : cSt t c = .quiet) :
    (driveChunk c).run t = .ok () t := by
  unfold driveChunk; simp only [run_getC_bind]; simp only [cSt] at h; rw [h]; rfl

/-- What the chunk phase leaves. -/
structure CPost (L : List Nat) (s₀ : Nat → Nat) (t3 t4 : Core) : Prop where
  inv : ∃ A, INV t4 A ∧ A.elist = L
  ginv : ∃ gh, GInv t4 L gh (fun _ => 0)
  cinv : CInv t4 L (fun _ => 0) (fun _ => 0) s₀
  lx : LX s₀ (fun _ => 0) (fun _ => 0) t4
  cnt : ∃ e pops, CountInv t4 e pops
  fr : DFrame t3 t4

/-- **The chunk phase** after an insertion into chunk `c`. -/
theorem driveChunk_ok {t : Core} {A : Abs} {L : List Nat} {gh : GGh} {s₀ δu : Nat → Nat}
    {e : Nat → Nat} {pops c : Nat} (hI : INV t A) (hel : A.elist = L)
    (hG : GInv t L gh (fun _ => 0)) (hC : CInv t L (δ1 c) δu s₀) (hLX : LX s₀ (δ1 c) δu t)
    (hN : CountInv t e pops) (hGP : GParams t.P) (hCP : CParams t.P) (hcL : LiveC t c)
    (hcnd : cSt t c ≠ .dead) (hcsz : 1 ≤ cSz t c) :
    ∃ t4, (driveChunk c).run t = .ok () t4 ∧ CPost L s₀ t t4 := by
  have hδu := hC.δu
  have hcθ : cmax t.P ≤ t.P.theta := hCP.I4
  -- the drive of a family containing `c`
  have drive : ∀ x, LiveC t x → cSt t x = .splitting →
      (c = cLl t x ∨ c = x ∨ c = cRr t x) →
      ∃ t4, (driveChunkFrom x).run t = .ok () t4 ∧ CPost L s₀ t t4 := by
    intro x hxL hxs hcx
    subst hel
    have Fx := hC.cfam x hxL hxs
    have hlx := Fx.lx hI hxL
    have hrx := Fx.rx hI hxL
    have hlr := Fx.lr hI hxL
    have hCx : CInvE t A.elist (δ1 c) δu s₀ x :=
      { hC with c1 := fun z hz hzs _ => hC.c1 z hz hzs (by unfold NIL; have := hz.1; omega) }
    have hC1 := hC.c1 x hxL hxs (by unfold NIL; have := hxL.1; omega)
    have hXs := cxsteps_count (cxsteps_dframe (cxsteps_linv (L := A.elist) (δ := δ1 c) (δu := δu)
      (s₀ := s₀) (x := x)) t hcθ)
    obtain ⟨t4, hrun, hD⟩ := cinv_drive hI hG hCx hC1 hXs ⟨⟨hLX, DFrame.refl t⟩, e, pops, hN⟩ hGP hCP
      hxL hxs (fun c' h1 h2 h3 => by
        unfold δ1; rw [ite_eq_right]; rintro rfl; rcases hcx with h | h | h <;> contradiction)
      (by unfold δ1; rcases hcx with rfl | rfl | rfl <;> simp [hlx, hrx, hlr, Ne.symm hlx,
        Ne.symm hrx, Ne.symm hlr])
      (by
        unfold δ1
        refine ⟨?_, ?_, ?_⟩ <;> split <;> first | omega | (subst_vars; exact hcsz))
    refine ⟨t4, hrun, hD.inv, hD.ginv, hD.cinv, ?_, ?_, ?_⟩
    · rcases hD.xx with ⟨⟨h1, -⟩, -⟩ | ⟨⟨h1, -⟩, -⟩
      · exact h1.close hδu
      · exact h1
    · rcases hD.xx with ⟨-, h2⟩ | ⟨-, h2⟩ <;> exact h2
    · rcases hD.xx with ⟨⟨-, h2⟩, -⟩ | ⟨⟨-, h2⟩, -⟩ <;> exact h2
  cases hst : cSt t c with
  | splitting =>
    rw [driveChunk_run_split hst]
    exact drive c hcL hst (Or.inr (Or.inl rfl))
  | overflow =>
    rw [driveChunk_run_ovf hst]
    obtain ⟨hxL, hxs, hlr⟩ := hC.covf c hcL hst
    exact drive _ hxL hxs (by rcases hlr with h | h; exact Or.inl h.symm; exact Or.inr (Or.inr h.symm))
  | quiet =>
    rw [driveChunk_run_quiet hst]
    -- the undriven insertion is in no family
    have hfree : ∀ x, LiveC t x → cSt t x = .splitting →
        δ1 c (cLl t x) = 0 ∧ δ1 c x = 0 ∧ δ1 c (cRr t x) = 0 ∧ δu x = 0 := by
      intro x hx hxs
      have Fx := hC.cfam x hx hxs
      have h1 : cLl t x ≠ c := by intro e; have := Fx.lSt; rw [e, hst] at this; cases this
      have h2 : x ≠ c := by rintro rfl; rw [hst] at hxs; cases hxs
      have h3 : cRr t x ≠ c := by intro e; have := Fx.rSt; rw [e, hst] at this; cases this
      have h4 : δu x = 0 := by have := hδu x; unfold δ1 at this; rw [ite_eq_right h2] at this; omega
      unfold δ1; simp [h1, h2, h3, h4]
    exact ⟨t, rfl, ⟨A, hI, hel⟩, ⟨gh, hG⟩, hC.drop hfree, hLX.close hδu, ⟨e, pops, hN⟩,
      DFrame.refl t⟩
  | dead => exact absurd hst hcnd

end OrderMaintenance.Proof

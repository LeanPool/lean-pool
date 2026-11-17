/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Chunks


/-!
# The chunk invariant through the group phase

A split start and a split move change no chunk's elements or units; a group removal adds one
unit to its chunk (a family becomes two quiet groups). This is the extra invariant that the group
phase carries (`XGroup`).
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The chunk fields `CInvE` reads are equal. -/
structure CSame (s s' : Core) : Prop where
  Csize : s'.C.size = s.C.size
  size : ∀ c, cSz s' c = cSz s c
  st : ∀ c, cSt s' c = cSt s c
  src : ∀ c, cSrc s' c = cSrc s c
  l : ∀ c, cLl s' c = cLl s c
  r : ∀ c, cRr s' c = cRr s c
  next : ∀ c, cN s' c = cN s c
  P : s'.P = s.P

theorem CSame.liveC {s s' : Core} (h : CSame s s') (c : Nat) : LiveC s' c ↔ LiveC s c := by
  simp only [LiveC, h.Csize]

theorem CSame.cfam {s s' : Core} (h : CSame s s') {x : Nat} (hf : CFamOK s x) : CFamOK s' x := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h.liveC, h.l, h.r, h.next, h.st, h.src] <;> assumption

theorem CSame.c1 {s s' : Core} (h : CSame s s') {δ δu s₀ : Nat → Nat} {x : Nat}
    (hu : units s' x = units s x) (hc : C1 s δ δu s₀ x) : C1 s' δ δu s₀ x := by
  unfold C1 at *; simp only [h.size, h.l, h.r, h.P, hu]; exact hc

/-- Transfer of `CInvE` when the chunk records are the same, the elements' chunks are the same,
the unit counts change as `δu` does, and live groups keep live chunks. -/
theorem CInvE.transfer {s s' : Core} {L : List Nat} {δ δu δu' s₀ : Nat → Nat} {ex : Nat}
    (hC : CInvE s L δ δu s₀ ex) (h : CSame s s')
    (hel : ∀ c, celts s' L c = celts s L c)
    (hu : ∀ c, units s' c - δu' c = units s c - δu c) (hδu : ∀ c, δu' c ≤ δ c)
    (hg : ∀ g, LiveG s' g → LiveC s (gC s' g) ∧ cSt s (gC s' g) ≠ .dead) :
    CInvE s' L δ δu' s₀ ex where
  csz c hc := by rw [h.size, hel]; exact hC.csz c ((h.liveC c).mp hc)
  cfam x hx hs := h.cfam (hC.cfam x ((h.liveC x).mp hx) (h.st x ▸ hs))
  covf c hc hs := by
    have := hC.covf c ((h.liveC c).mp hc) (h.st c ▸ hs)
    simp only [h.liveC, h.src, h.st, h.l, h.r]; exact this
  gchk g hg' := by rw [h.liveC, h.st]; exact hg g hg'
  c1 x hx hs hex := by
    have hc := hC.c1 x ((h.liveC x).mp hx) (h.st x ▸ hs) hex
    unfold C1 at *; simp only [h.size, h.l, h.r, h.P, hu]; exact hc
  δu := hδu

/-! ### Split start -/

theorem cinv_splitStart {s : Core} {A : Abs} {δ δu s₀ : Nat → Nat} {ex g labL labR : Nat}
    (hI : INV s A) (hC : CInvE s A.elist δ δu s₀ ex) (hg : LiveG s g) (hq : gSt s g = .quiet) :
    CInvE (splitState s g labL labR) A.elist δ δu s₀ ex := by
  have S := splitSpec hI (hI.mem_glist_iff.mpr hg) labL labR
  generalize splitState s g labL labR = s' at S ⊢
  generalize splitL s g = gl at S
  generalize splitR s g = gr at S
  have hCs : CSame s s' := by
    refine ⟨S.Csize, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_,
      fun c => ?_, S.P⟩ <;>
      simp only [cSz, cSt, cSrc, cLl, cRr, cN, S.C] <;> split <;> rfl
  have hne : ∀ z, LiveG s z → z ≠ gl ∧ z ≠ gr := fun z hz =>
    ⟨fun e => S.glOut (e ▸ hz), fun e => S.grOut (e ▸ hz)⟩
  refine hC.transfer hCs (fun c => ?_) (fun c => ?_) hC.δu (fun z hz => ?_)
  · unfold celts
    refine List.filter_congr fun e he => ?_
    have hz := hI.mem_glist_iff.mp (hI.eG_mem he)
    simp only [eG, S.E] at hz ⊢
    rw [S.chk, ite_eq_right (not_or.mpr (hne _ hz))]
  · congr 1
    apply units_congr
    intro z
    unfold UnitG
    rw [S.live]
    by_cases h1 : z = gl
    · subst h1; simp [S.st, Ne.symm S.ggl, S.glOut]
    · by_cases h2 : z = gr
      · subst h2; simp [S.st, Ne.symm S.ggr, S.grOut]
      · simp only [h1, h2, false_or, S.chk, S.st, ite_false, or_self]
        by_cases h3 : z = g
        · subst h3; simp [hq]
        · simp [h3]
  · rcases (S.live z).mp hz with h | h | h
    · subst h; rw [S.chk, ite_eq_left (Or.inl rfl)]; exact hC.gchk g hg
    · subst h; rw [S.chk, ite_eq_left (Or.inr rfl)]; exact hC.gchk g hg
    · rw [S.chk, ite_eq_right (not_or.mpr (hne z h))]; exact hC.gchk z h

/-! ### Split moves -/

theorem cinv_move {s s' : Core} {A : Abs} {δ δu s₀ : Nat → Nat} {ex src dst e lab : Nat}
    (hC : CInvE s A.elist δ δu s₀ ex) (M : MoveSpec s s' src dst e lab)
    (he : eG s e = src) (hchk : gC s dst = gC s src) :
    CInvE s' A.elist δ δu s₀ ex := by
  have hK := M.links
  have hCs : CSame s s' := by
    refine ⟨by rw [M.C], fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_,
      fun c => ?_, M.P⟩ <;> simp only [cSz, cSt, cSrc, cLl, cRr, cN, M.C]
  refine hC.transfer hCs (fun c => ?_) (fun c => ?_) hC.δu (fun z hz => ?_)
  · unfold celts
    refine List.filter_congr fun w _ => ?_
    rw [M.eG, hK.chk]
    by_cases hw : w = e
    · subst hw; rw [ite_eq_left rfl, hchk, he]
    · rw [ite_eq_right hw]
  · congr 1
    apply units_congr
    intro z; unfold UnitG; rw [hK.liveG, hK.chk, hK.st]
  · rw [hK.liveG] at hz; rw [hK.chk]; exact hC.gchk z hz

/-! ### Group removal -/

theorem cinv_remove {s : Core} {A : Abs} {gh : GGh} {δg δ δu s₀ : Nat → Nat} {ex p : Nat}
    (hI : INV s A) (hG : GInvE s A.elist gh δg p) (hC : CInvE s A.elist δ δu s₀ ex) (hp : LiveG s p)
    (hs : gSt s p = .splitting) (hδ : δu (gC s p) + 1 ≤ δ (gC s p)) :
    CInvE (removeState s p) A.elist δ (Function.update δu (gC s p) (δu (gC s p) + 1)) s₀ ex := by
  have Fp := hG.fam p hp hs
  have hp' := hI.mem_glist_iff.mpr hp
  have hpp : gP s p ≠ p := by
    rw [hI.gList.prev p hp']; exact predOf_ne_self hI.gList.nodup p hp.1
  have hgPl : gP s p = gLl s p := by
    have := hI.gP_gN (hI.mem_glist_iff.mpr Fp.lLive) (by rw [Fp.lAdj]; exact hp.1)
    rw [Fp.lAdj] at this; exact this
  have R := removeState_spec hp.2.1 Fp.lLive.2.1 Fp.rLive.2.1 hpp
    (fun _ => by rw [hgPl]; exact Fp.lLive.2.1)
  have hU : (unlinkGroup s p).C.size = s.C.size := (unlinkGroup_rest (s := s) (g := p)).2.1
  have hcs : gC s p < s.C.size := (hC.gchk p hp).1.2
  generalize removeState s p = s' at R ⊢
  have hCs : CSame s s' := by
    refine ⟨by rw [R.C, hU], fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_,
      fun c => ?_, R.P⟩ <;>
      simp only [cSz, cSt, cSrc, cLl, cRr, cN, R.C, unlinkGroup_C (s := s) (g := p) c hcs] <;>
      split <;> rfl
  have hlp : gLl s p ≠ p := Fp.lp hI hp
  have hrp : gRr s p ≠ p := Fp.rp hI hp
  have hlr : gLl s p ≠ gRr s p := Fp.lr hI hp
  refine hC.transfer hCs (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun z hz => ?_)
  · unfold celts
    refine List.filter_congr fun w _ => ?_
    simp only [eG, R.E, R.chk]
  · by_cases hc : c = gC s p
    · subst hc
      have : units s' (gC s p) = units s (gC s p) + 1 := by
        refine units_swap (p := p) (l := gLl s p) (r := gRr s p) ⟨hp, rfl, by rw [hs]; simp⟩
          (fun h => h.2.2 Fp.lSt) (fun h => h.2.2 Fp.rSt) hlr ?_ ?_ ?_ ?_
        · refine ⟨(R.live _).mpr ⟨Fp.lLive, hlp⟩, by rw [R.chk, Fp.lC], ?_⟩
          rw [R.st, ite_eq_left (Or.inl rfl)]; simp
        · refine ⟨(R.live _).mpr ⟨Fp.rLive, hrp⟩, by rw [R.chk, Fp.rC], ?_⟩
          rw [R.st, ite_eq_left (Or.inr rfl)]; simp
        · intro h; exact ((R.live p).mp h.1).2 rfl
        · intro z h1 h2 h3
          unfold UnitG; rw [R.live, R.chk, R.st, ite_eq_right (not_or.mpr ⟨h2, h3⟩)]
          simp [h1]
      rw [this, Function.update_self]; omega
    · rw [Function.update_of_ne hc]
      congr 1
      apply units_congr
      intro z
      unfold UnitG; rw [R.live, R.chk, R.st]
      by_cases h1 : z = gLl s p ∨ z = gRr s p
      · rw [ite_eq_left h1]
        have hzc : gC s z = gC s p := by
          rcases h1 with e | e
          · rw [e]; exact Fp.lC
          · rw [e]; exact Fp.rC
        simp only [hzc, Ne.symm hc]; simp
      · rw [ite_eq_right h1]
        by_cases h3 : z = p
        · subst h3; simp [Ne.symm hc]
        · simp [h3]
  · by_cases hc : c = gC s p
    · subst hc; rw [Function.update_self]; exact hδ
    · rw [Function.update_of_ne hc]; exact hC.δu c
  · rw [R.live] at hz; rw [R.chk]; exact hC.gchk z hz.1

/-! ### The group phase's extra invariant -/

/-- Before any removal: the chunk invariant with `δu`. After the removal in chunk `c`: with one
more unit in `c`. -/
theorem xgroup_cinv {L : List Nat} {δ δu s₀ : Nat → Nat} {c : Nat} (hδ : δu c + 1 ≤ δ c) :
    XGroup (fun t => CInv t L δ δu s₀) (fun t => CInv t L δ (Function.update δu c (δu c + 1)) s₀)
      L c := by
  refine ⟨fun δg p => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t A' gh hI hel hG hok _ hX
    subst hel
    have hp' := hI.mem_glist_iff.mpr hok.live
    have hl' : gLl t p ∈ A'.glist := hI.mem_of_gN hok.adj hok.live.1
    have hlp : gLl t p ≠ p := by
      intro e; have := hok.adj; rw [e, hI.gList.next p hp'] at this
      exact succOf_ne_self hI.gList.nodup p hok.live.1 this
    obtain ⟨rest, hrun⟩ := hI.run_head hp' hok.ne
    have hm := mem_runOf.mp (hrun ▸ (by simp : gF t p ∈ gF t p :: rest))
    exact cinv_move hX (moveLState_spec hlp hok.live.2.1 (hI.gAlloc _ hl')
      ((hI.eAlloc _).mp hm.1).2) hm.2 hok.chk
  · intro t A' gh hI hel hG hok _ hX
    subst hel
    have hp' := hI.mem_glist_iff.mpr hok.live
    have hr' : gRr t p ∈ A'.glist := hI.mem_of_gP hok.adj hok.live.1
    have hrp : gRr t p ≠ p := by
      intro e; have := hok.adj; rw [e, hI.gList.prev p hp'] at this
      exact predOf_ne_self hI.gList.nodup p hok.live.1 this
    obtain ⟨front, hrun⟩ := hI.run_last hp' hok.ne
    have hm := mem_runOf.mp (hrun ▸ (by simp : gLs t p ∈ front ++ [gLs t p]))
    exact cinv_move hX (moveRState_spec hrp hok.live.2.1 (hI.gAlloc _ hr')
      ((hI.eAlloc _).mp hm.1).2) hm.2 hok.chk
  · intro t A' gh hI hel hG hp hs he hl hr _ _ hc hX
    subst hel
    have := cinv_remove hI hG hX hp hs (by rw [hc]; exact hδ)
    rw [hc] at this; exact this
  · intro t A gh g labL labR hI hel hG hg hq hsz hL hR hX
    subst hel
    exact cinv_splitStart hI hX hg hq

end OrderMaintenance.Proof

/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.LRoom


/-!
# Lemma C3 inside the group phase and the chunk drive

The drives thread extra invariants through their steps (`XGroup`, `CXSteps`). Here: conjunction of
such invariants, and Lemma C3 (with the parameter conditions it needs) as one of them.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem XGroup.and {X Y X' Y' : Core → Prop} {L : List Nat} {c : Nat} (h1 : XGroup X Y L c)
    (h2 : XGroup X' Y' L c) : XGroup (fun t => X t ∧ X' t) (fun t => Y t ∧ Y' t) L c := by
  refine ⟨fun δ p => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t A gh hI hel hG hok hst hX
    exact ⟨(h1.drive δ p).moveL t A gh hI hel hG hok hst hX.1,
      (h2.drive δ p).moveL t A gh hI hel hG hok hst hX.2⟩
  · intro t A gh hI hel hG hok hst hX
    exact ⟨(h1.drive δ p).moveR t A gh hI hel hG hok hst hX.1,
      (h2.drive δ p).moveR t A gh hI hel hG hok hst hX.2⟩
  · intro t A gh hI hel hG hp hs he hl hr hl' hr' hc hX
    exact ⟨(h1.drive δ p).rem t A gh hI hel hG hp hs he hl hr hl' hr' hc hX.1,
      (h2.drive δ p).rem t A gh hI hel hG hp hs he hl hr hl' hr' hc hX.2⟩
  · intro s A gh g labL labR hI hel hG hg hq hsz hL hR hX
    exact ⟨h1.split s A gh g labL labR hI hel hG hg hq hsz hL hR hX.1,
      h2.split s A gh g labL labR hI hel hG hg hq hsz hL hR hX.2⟩

theorem CXSteps.and {X Y X' Y' : Core → Prop} {L : List Nat} {δ δu s₀ : Nat → Nat} {x : Nat}
    (h1 : CXSteps X Y L δ δu s₀ x)
    (h2L : ∀ t A gh labs, INV t A → A.elist = L → GInv t L gh (fun _ => 0) →
      CInvE t L δ δu s₀ x → LiveC t x → cSt t x = .splitting → X' t →
      X' (cmoveLState t x (unitCand t x true) labs))
    (h2R : ∀ t A gh labs, INV t A → A.elist = L → GInv t L gh (fun _ => 0) →
      CInvE t L δ δu s₀ x → LiveC t x → cSt t x = .splitting → X' t →
      X' (cmoveRState t x (unitCand t x false) labs))
    (h3 : ∀ t A gh, INV t A → A.elist = L → GInv t L gh (fun _ => 0) →
      CInvE t L δ δu s₀ x → LiveC t x → cSt t x = .splitting →
      cSz t (cLl t x) ≤ cmax t.P → cSz t (cRr t x) ≤ cmax t.P → X' t → Y' (cremoveState t x)) :
    CXSteps (fun t => X t ∧ X' t) (fun t => Y t ∧ Y' t) L δ δu s₀ x := by
  refine ⟨?_, ?_, ?_⟩
  · intro t A gh hI hel hG hC hxL hst hne hdir hFB hX
    obtain ⟨labs, hrun, hX1⟩ := h1.moveL t A gh hI hel hG hC hxL hst hne hdir hFB hX.1
    exact ⟨labs, hrun, hX1, h2L t A gh labs hI hel hG hC hxL hst hX.2⟩
  · intro t A gh hI hel hG hC hxL hst hne hdir hFB hX
    obtain ⟨labs, hrun, hX1⟩ := h1.moveR t A gh hI hel hG hC hxL hst hne hdir hFB hX.1
    exact ⟨labs, hrun, hX1, h2R t A gh labs hI hel hG hC hxL hst hX.2⟩
  · intro t A gh hI hel hG hC hxL hst hne hl hr hFB hX
    exact ⟨h1.rem t A gh hI hel hG hC hxL hst hne hl hr hFB hX.1,
      h3 t A gh hI hel hG hC hxL hst hl hr hX.2⟩

/-- Lemma C3's invariant, with the parameter conditions it needs. -/
def LX (s₀ δ δu : Nat → Nat) (t : Core) : Prop :=
  (∃ lg, LInv t lg s₀ δ δu) ∧ LParams t.P ∧ GParams t.P

/-- **Lemma C3 through the group phase.** -/
theorem xgroup_linv {L : List Nat} {s₀ δ δu : Nat → Nat} {c : Nat} :
    XGroup (LX s₀ δ δu) (LX s₀ δ (Function.update δu c (δu c + 1))) L c := by
  refine ⟨fun δg p => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t A' gh hI hel hG hok hst hX
    subst hel
    obtain ⟨⟨lg, hL⟩, hLP, hP⟩ := hX
    have hp' := hI.mem_glist_iff.mpr hok.live
    have hl' : gLl t p ∈ A'.glist := hI.mem_of_gN hok.adj hok.live.1
    have hlp : gLl t p ≠ p := by
      intro e; have := hok.adj; rw [e, hI.gList.next p hp'] at this
      exact succOf_ne_self hI.gList.nodup p hok.live.1 this
    obtain ⟨rest, hrun⟩ := hI.run_head hp' hok.ne
    have hm := mem_runOf.mp (hrun ▸ (by simp : gF t p ∈ gF t p :: rest))
    have hne : 1 ≤ gSz t p := by rw [hG.sz p hok.live, hrun]; simp
    have M := moveLState_spec hlp hok.live.2.1 (hI.gAlloc _ hl') ((hI.eAlloc _).mp hm.1).2
    exact ⟨⟨lg, linv_move hI hG hL M hok.live hst (Or.inl rfl) hne⟩, by rwa [M.P], by rwa [M.P]⟩
  · intro t A' gh hI hel hG hok hst hX
    subst hel
    obtain ⟨⟨lg, hL⟩, hLP, hP⟩ := hX
    have hp' := hI.mem_glist_iff.mpr hok.live
    have hr' : gRr t p ∈ A'.glist := hI.mem_of_gP hok.adj hok.live.1
    have hrp : gRr t p ≠ p := by
      intro e; have := hok.adj; rw [e, hI.gList.prev p hp'] at this
      exact predOf_ne_self hI.gList.nodup p hok.live.1 this
    obtain ⟨front, hrun⟩ := hI.run_last hp' hok.ne
    have hm := mem_runOf.mp (hrun ▸ (by simp : gLs t p ∈ front ++ [gLs t p]))
    have hne : 1 ≤ gSz t p := by rw [hG.sz p hok.live, hrun]; simp
    have M := moveRState_spec hrp hok.live.2.1 (hI.gAlloc _ hr') ((hI.eAlloc _).mp hm.1).2
    exact ⟨⟨lg, linv_move hI hG hL M hok.live hst (Or.inr rfl) hne⟩, by rwa [M.P], by rwa [M.P]⟩
  · intro t A' gh hI hel hG hp hs he hl hr hl' hr' hc hX
    subst hel
    obtain ⟨⟨lg, hL⟩, hLP, hP⟩ := hX
    have he0 : gSz t p = 0 := by
      rw [hG.sz p hp, (hI.first_nil_iff (hI.mem_glist_iff.mpr hp)).mp he]; rfl
    have h2 : 2 * gmin t.P ≤ t.P.G := by unfold gmin; omega
    have := linv_remove hI hG hL hp hs he0 hl' hr' h2
    rw [hc] at this
    have hPr : (removeState t p).P = t.P := rfl
    exact ⟨⟨lg, this⟩, by rwa [hPr], by rwa [hPr]⟩
  · intro t A gh g labL labR hI hel hG hg hq hsz hL hR hX
    subst hel
    obtain ⟨⟨lg, hLi⟩, hLP, hP⟩ := hX
    have hPs : (splitState t g labL labR).P = t.P := by
      show (linkGroupPair _ g _ _ labL labR).P = t.P
      simp only [linkGroupPair, allocGroup_P]
    exact ⟨⟨_, linv_splitStart hI hG hLi hg hq hsz hL hR⟩, by rwa [hPs], by rwa [hPs]⟩

/-- **Lemma C3 through the chunk drive.** -/
theorem cxsteps_linv {L : List Nat} {δ δu s₀ : Nat → Nat} {x : Nat} :
    CXSteps (LX s₀ δ δu) (LX s₀ (fun _ => 0) (fun _ => 0)) L δ δu s₀ x := by
  refine ⟨?_, ?_, ?_⟩
  · intro t A gh hI hel hG hC hxL hst hne _ hFB hX
    subst hel
    obtain ⟨⟨lg, hL⟩, hLP, hP⟩ := hX
    obtain ⟨labs, hrun, lg', hL'⟩ := linv_cmoveL hI hG hP hLP hC hL hxL hst hne hFB
    have hPm : (cmoveLState t x (unitCand t x true) labs).P = t.P := rfl
    exact ⟨labs, hrun, ⟨lg', hL'⟩, by rwa [hPm], by rwa [hPm]⟩
  · intro t A gh hI hel hG hC hxL hst hne _ hFB hX
    subst hel
    obtain ⟨⟨lg, hL⟩, hLP, hP⟩ := hX
    obtain ⟨labs, hrun, lg', hL'⟩ := linv_cmoveR hI hG hP hLP hC hL hxL hst hne hFB
    have hPm : (cmoveRState t x (unitCand t x false) labs).P = t.P := rfl
    exact ⟨labs, hrun, ⟨lg', hL'⟩, by rwa [hPm], by rwa [hPm]⟩
  · intro t A gh hI hel hG hC hxL hst hne _ _ hFB hX
    subst hel
    obtain ⟨⟨lg, hL⟩, hLP, hP⟩ := hX
    have hPm : (cremoveState t x).P = t.P := rfl
    exact ⟨⟨_, linv_cremove hI hC hL hxL hst hFB⟩, by rwa [hPm], by rwa [hPm]⟩

end OrderMaintenance.Proof

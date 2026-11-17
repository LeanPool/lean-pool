/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.Core


/-!
# Theorem W, stage B1: the size bounds from the cost invariants

The cost proof threads extra invariants through the group drive (`XGroup`, `XSteps`) and the
chunk drive (`CXSteps`). Each hook sees the step's context: INV-S, `GInv`, `CInv`, the family.
Here the stored-value bound rides on those hooks.

* **Sizes (Sz).** A live group's size is its run in the element list `L` (`GInv.sz`), a live
  chunk's is its element count (`CInv.csz`); both are at most `|L|`. A move adds one element to a
  live sibling (`≤ |L| + 1`); a chunk move adds at most three live groups to a live sibling
  (`≤ 4·|L|`). So `4·|L| + 4 ≤ 2^K` covers every size written by a drive.
* **Fresh groups (F).** A group phase allocates at most two groups: one split start, at its
  beginning. The predicate `XG` records the room: `Gs.size ≤ G0` before the split; after it every
  quiet group is below `G`, so no further split can start.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof
variable {K : Nat}

/-! ### Sizes are at most `|L|` -/

theorem runOf_len_le (s : Core) (L : List Nat) (g : Nat) : (runOf s L g).length ≤ L.length :=
  List.length_filter_le _ _

theorem celts_len_le (s : Core) (L : List Nat) (c : Nat) : (celts s L c).length ≤ L.length :=
  List.length_filter_le _ _

theorem sum_le_of_le {f : Nat → Nat} {B : Nat} : ∀ (u : List Nat), (∀ g ∈ u, f g ≤ B) →
    (u.map f).sum ≤ u.length * B
  | [], _ => by simp
  | a :: t, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := sum_le_of_le t (fun g hg => h g (by simp [hg]))
    have := h a (by simp)
    rw [Nat.succ_mul]; omega

/-! ### What the group steps change -/

section gsteps
variable (t : Core) (p : Nat)

theorem moveLState_P : (moveLState t p).P = t.P := rfl
theorem moveRState_P : (moveRState t p).P = t.P := rfl
theorem removeState_P : (removeState t p).P = t.P := rfl

theorem moveLState_Gsize : (moveLState t p).Gs.size = t.Gs.size := by
  simp [moveLState, sizeAdj, moveFirstLeft]
theorem moveRState_Gsize : (moveRState t p).Gs.size = t.Gs.size := by
  simp [moveRState, sizeAdj, moveLastRight]
theorem removeState_Gsize : (removeState t p).Gs.size = t.Gs.size := by
  simp only [removeState, unlinkGroup, Array.size_modify', Array.size_ite]; split_ifs <;> rfl

theorem moveLState_g (z : Nat) : gSt (moveLState t p) z = gSt t z ∧ gA (moveLState t p) z = gA t z ∧
    (z ≠ p → z ≠ gLl t p → gSz (moveLState t p) z = gSz t z) := by
  simp only [moveLState, sizeAdj, moveFirstLeft, gSt, gA, gSz, Array.getX_modify,
    Array.size_modify']
  refine ⟨?_, ?_, fun h1 h2 => ?_⟩ <;> split_ifs <;> simp_all

theorem moveRState_g (z : Nat) : gSt (moveRState t p) z = gSt t z ∧ gA (moveRState t p) z = gA t z ∧
    (z ≠ p → z ≠ gRr t p → gSz (moveRState t p) z = gSz t z) := by
  simp only [moveRState, sizeAdj, moveLastRight, gSt, gA, gSz, Array.getX_modify,
    Array.size_modify']
  refine ⟨?_, ?_, fun h1 h2 => ?_⟩ <;> split_ifs <;> simp_all

theorem removeState_g {z : Nat} (hl : gLl t p < t.Gs.size) (hr : gRr t p < t.Gs.size) :
    gSt (removeState t p) z = (if z = gLl t p ∨ z = gRr t p then .quiet else gSt t z) ∧
    (gA (removeState t p) z = true → gA t z = true) ∧ gSz (removeState t p) z = gSz t z := by
  have key := removeState_getX (z := z) hl hr
  have U := unlinkGroup_getX_lr t p z
  have hA := unlinkGroup_gA (s := t) (g := p) z
  simp only [gA] at hA
  simp only [gSt, gA, gSz, key]
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp_all [quietG]

end gsteps

/-! ### The group phase -/

/-- The group phase's extra invariant: stored values, the parameters `P`, and room for its one
split start (`G0` is the group count when the phase starts). -/
def XG (K : Nat) (P : Params) (G0 : Nat) (t : Core) : Prop :=
  WB K t ∧ t.P = P ∧ t.Gs.size ≤ G0 + 2 ∧
    (t.Gs.size ≤ G0 ∨ ∀ g, LiveG t g → gSt t g = .quiet → gSz t g < t.P.G)

theorem xg_moveL {P : Params} {G0 : Nat} {L : List Nat} (hL : LabRoom K P) (hlen : L.length + 2
  ≤ 2 ^ K)
    {t : Core} {gh : GGh} {δ : Nat → Nat} {p : Nat} (hG : GInvE t L gh δ p)
    (hok : MoveLOK t p) (hst : gSt t p = .splitting) (hX : XG K P G0 t) : XG K P G0 (moveLState
      t p) := by
  obtain ⟨hW, hP, hGs, hor⟩ := hX
  have F := hG.fam p hok.live hst
  have hsz : gSz t (gLl t p) + 1 < 2 ^ K := by
    have := hG.sz _ F.lLive; have := runOf_len_le t L (gLl t p); omega
  refine ⟨wb_moveLState hW (hP ▸ hL) hok.room hsz, hP, by rw [moveLState_Gsize]; exact hGs, ?_⟩
  rw [moveLState_Gsize]
  rcases hor with h | h
  · exact Or.inl h
  · right
    intro g hg hq
    obtain ⟨e1, e2, e3⟩ := moveLState_g t p g
    have hg' : LiveG t g := by
      refine ⟨hg.1, ?_, ?_⟩
      · rw [← moveLState_Gsize t p]; exact hg.2.1
      · rw [← e2]; exact hg.2.2
    have hq' : gSt t g = .quiet := by rw [← e1]; exact hq
    have hgp : g ≠ p := by rintro rfl; rw [hst] at hq'; cases hq'
    have hgl : g ≠ gLl t p := by rintro rfl; rw [F.lSt] at hq'; cases hq'
    rw [e3 hgp hgl, moveLState_P]
    exact h g hg' hq'

theorem xg_moveR {P : Params} {G0 : Nat} {L : List Nat} (hL : LabRoom K P) (hlen : L.length + 2
  ≤ 2 ^ K)
    {t : Core} {gh : GGh} {δ : Nat → Nat} {p : Nat} (hG : GInvE t L gh δ p)
    (hok : MoveROK t p) (hst : gSt t p = .splitting) (hX : XG K P G0 t) : XG K P G0 (moveRState
      t p) := by
  obtain ⟨hW, hP, hGs, hor⟩ := hX
  have F := hG.fam p hok.live hst
  have hsz : gSz t (gRr t p) + 1 < 2 ^ K := by
    have := hG.sz _ F.rLive; have := runOf_len_le t L (gRr t p); omega
  refine ⟨wb_moveRState hW (hP ▸ hL) hsz, hP, by rw [moveRState_Gsize]; exact hGs, ?_⟩
  rw [moveRState_Gsize]
  rcases hor with h | h
  · exact Or.inl h
  · right
    intro g hg hq
    obtain ⟨e1, e2, e3⟩ := moveRState_g t p g
    have hg' : LiveG t g := by
      refine ⟨hg.1, ?_, ?_⟩
      · rw [← moveRState_Gsize t p]; exact hg.2.1
      · rw [← e2]; exact hg.2.2
    have hq' : gSt t g = .quiet := by rw [← e1]; exact hq
    have hgp : g ≠ p := by rintro rfl; rw [hst] at hq'; cases hq'
    have hgr : g ≠ gRr t p := by rintro rfl; rw [F.rSt] at hq'; cases hq'
    rw [e3 hgp hgr, moveRState_P]
    exact h g hg' hq'

theorem xg_rem {P : Params} {G0 : Nat} (hroom : G0 + 2 ≤ 2 ^ K) {t : Core} {p : Nat} (hp : LiveG
  t p)
    (hlL : LiveG t (gLl t p)) (hrL : LiveG t (gRr t p))
    (hl : gSz t (gLl t p) < t.P.G) (hr : gSz t (gRr t p) < t.P.G) (hX : XG K P G0 t) :
    XG K P G0 (removeState t p) := by
  obtain ⟨hW, hP, hGs, hor⟩ := hX
  have hp2 : p < 2 ^ K := by have := hp.2.1; omega
  refine ⟨wb_removeState hW hp2, hP, by rw [removeState_Gsize]; exact hGs, ?_⟩
  rw [removeState_Gsize]
  rcases hor with h | h
  · exact Or.inl h
  · right
    intro g hg hq
    have F2 : gLl t p < t.Gs.size ∧ gRr t p < t.Gs.size := ⟨hlL.2.1, hrL.2.1⟩
    obtain ⟨e1, e2, e3⟩ := removeState_g t p (z := g) F2.1 F2.2
    have hg' : LiveG t g := ⟨hg.1, by rw [← removeState_Gsize t p]; exact hg.2.1, e2 hg.2.2⟩
    rw [e3, removeState_P]
    rw [e1] at hq
    split_ifs at hq with h1
    · rcases h1 with rfl | rfl
      · exact hl
      · exact hr
    · exact h g hg' hq

theorem splitState_P (s : Core) (g labL labR : Nat) : (splitState s g labL labR).P = s.P := by
  change (allocGroup (allocGroup s (gC s g)).2 (gC s g)).2.P = s.P
  rw [allocGroup_P', allocGroup_P']

theorem splitState_size_le (s : Core) (g labL labR : Nat) :
    (splitState s g labL labR).Gs.size ≤ s.Gs.size + 2 := by
  have h1 := allocGroup_size_le s (gC s g)
  have h2 := allocGroup_size_le (allocGroup s (gC s g)).2 (gC s g)
  have : (splitState s g labL labR).Gs.size = (allocGroup (allocGroup s (gC s g)).2 (gC s
    g)).2.Gs.size := by
    simp only [splitState, linkGroupPair, Array.size_modify', Array.size_ite]; split_ifs <;> rfl
  omega

theorem xg_split {P : Params} {G0 : Nat} (hL : LabRoom K P) (hroom : G0 + 2 ≤ 2 ^ K) {s : Core}
  {A : Abs}
    {gh : GGh} {g labL labR : Nat} (hI : INV s A)
    (hG : GInv s A.elist gh (fun b => if b = g then 1 else 0)) (hg : LiveG s g)
    (hq : gSt s g = .quiet) (hsz : gSz s g = s.P.G) (hLb : (labBefore g).run s = .ok labL s)
    (hLa : (labAfter g).run s = .ok labR s) (hX : XG K P G0 s) : XG K P G0 (splitState s g labL
      labR) := by
  obtain ⟨hW, hP, hGs, hor⟩ := hX
  have hG0 : s.Gs.size ≤ G0 := by
    rcases hor with h | h
    · exact h
    · have := h g hg hq; omega
  have hlL : labL < 2 ^ K := ((ht_labBefore (P0 := P) g).ok hW hP hLb).2
  have hlR : labR < 2 ^ K := ((ht_labAfter (P0 := P) g hL).ok hW hP hLa).2
  have hg2 : g < 2 ^ K := by have := hg.2.1; omega
  have S := splitSpec hI (hI.mem_glist_iff.mpr hg) labL labR
  refine ⟨wb_splitState hW hg2 hlL hlR (by omega), by rw [splitState_P]; exact hP,
    by have := splitState_size_le s g labL labR; omega, Or.inr ?_⟩
  intro z hz hzq
  rw [splitState_P]
  rcases (S.live z).mp hz with rfl | rfl | hz'
  · rw [S.st, ite_eq_right (Ne.symm S.ggl), ite_eq_left (Or.inl rfl)] at hzq; cases hzq
  · rw [S.st, ite_eq_right (Ne.symm S.ggr), ite_eq_left (Or.inr rfl)] at hzq; cases hzq
  · rw [S.st] at hzq
    by_cases hzg : z = g
    · rw [ite_eq_left hzg] at hzq; cases hzq
    · rw [ite_eq_right hzg] at hzq
      by_cases hzlr : z = splitL s g ∨ z = splitR s g
      · rw [ite_eq_left hzlr] at hzq; cases hzq
      · rw [ite_eq_right hzlr] at hzq
        rw [S.sz, ite_eq_right hzlr]
        have := (hG.quiet z hz' hzq).1
        simp only [ite_eq_right hzg] at this
        omega

/-- **The stored-value bound through the group phase.** -/
theorem xgroup_wb {P : Params} {G0 : Nat} {L : List Nat} {c : Nat} (hL : LabRoom K P)
    (hroom : G0 + 2 ≤ 2 ^ K) (hlen : L.length + 2 ≤ 2 ^ K) :
    XGroup (XG K P G0) (XG K P G0) L c := by
  refine ⟨fun δ p => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t A' gh _ _ hG hok hst hX; exact xg_moveL hL hlen hG hok hst hX
  · intro t A' gh _ _ hG hok hst hX; exact xg_moveR hL hlen hG hok hst hX
  · intro t A' gh _ _ hG hp hs _ hl hr _ _ _ hX
    have F := hG.fam p hp hs
    exact xg_rem hroom hp F.lLive F.rLive hl hr hX
  · intro s A gh g labL labR hI hel hG hg hq hsz hLb hLa hX
    subst hel
    exact xg_split hL hroom hI hG hg hq hsz hLb hLa hX

/-! ### The chunk phase -/

/-- Combine a chunk-drive invariant with one that needs the labels of the move (which the first
one's run provides). -/
theorem _root_.OrderMaintenance.Proof.CXSteps.andRun {X Y W : Core → Prop} {L : List Nat} {δ δu
  s₀ : Nat → Nat} {x : Nat}
    (h : CXSteps X Y L δ δu s₀ x)
    (hl : ∀ t A gh labs, INV t A → A.elist = L → GInv t L gh (fun _ => 0) → CInvE t L δ δu s₀ x →
      LiveC t x → cSt t x = .splitting → cF t x ≠ NIL →
      (pushLabsL t x (unitCand t x true).length).run t = .ok labs t → W t →
      W (cmoveLState t x (unitCand t x true) labs))
    (hr : ∀ t A gh labs, INV t A → A.elist = L → GInv t L gh (fun _ => 0) → CInvE t L δ δu s₀ x →
      LiveC t x → cSt t x = .splitting → cF t x ≠ NIL →
      (pushLabsR t x (unitCand t x false).length).run t = .ok labs t → W t →
      W (cmoveRState t x (unitCand t x false) labs))
    (hrem : ∀ t, W t → W (cremoveState t x)) :
    CXSteps (fun t => X t ∧ W t) (fun t => Y t ∧ W t) L δ δu s₀ x := by
  refine ⟨?_, ?_, ?_⟩
  · intro t A gh hI hel hG hC hxL hst hne hdir hFB hX
    obtain ⟨labs, hrun, hX'⟩ := h.moveL t A gh hI hel hG hC hxL hst hne hdir hFB hX.1
    exact ⟨labs, hrun, hX', hl t A gh labs hI hel hG hC hxL hst hne hrun hX.2⟩
  · intro t A gh hI hel hG hC hxL hst hne hdir hFB hX
    obtain ⟨labs, hrun, hX'⟩ := h.moveR t A gh hI hel hG hC hxL hst hne hdir hFB hX.1
    exact ⟨labs, hrun, hX', hr t A gh labs hI hel hG hC hxL hst hne hrun hX.2⟩
  · intro t A gh hI hel hG hC hxL hst he hl' hr' hFB hX
    exact ⟨h.rem t A gh hI hel hG hC hxL hst he hl' hr' hFB hX.1, hrem t hX.2⟩

/-- The groups of a chunk-split unit are live, and there are at most three. -/
theorem unit_live {t : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} (hI : INV t A)
    (hG : GInv t A.elist gh δ) {x : Nat} (hne : cF t x ≠ NIL) (left : Bool) :
    (∀ g ∈ unitCand t x left, LiveG t g) ∧ (unitCand t x left).length ≤ 3 := by
  cases left with
  | true =>
    rcases left_unit hI hG hne with ⟨-, hu⟩ | ⟨p, hp, hps, hl, hu, -⟩
    · rw [hu]
      obtain ⟨hx, r, hr⟩ := hI.run_ne_nil hne
      have hg0 : cF t x ∈ A.glist := A.grps_sub_glist hx (by rw [hr]; simp)
      refine ⟨fun g hg => ?_, by simp⟩
      simp only [List.mem_singleton] at hg; subst hg
      exact hI.mem_glist_iff.mp hg0
    · rw [hu]
      have F := hG.fam p hp hps
      refine ⟨fun g hg => ?_, by simp⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · rw [← hl]; exact F.lLive
      · exact hp
      · exact F.rLive
  | false =>
    rcases right_unit hI hG hne with ⟨-, hu⟩ | ⟨p, hp, hps, hr, hu, -⟩
    · rw [hu]
      obtain ⟨hx, r, hr⟩ := hI.run_ne_nil hne
      have hE := hI.cEnds x hx
      have hlm : cLs t x ∈ A.grps x := by rw [hE.2, hr]; exact getLastD_cons_mem _ _ _
      have hg0 : cLs t x ∈ A.glist := A.grps_sub_glist hx hlm
      refine ⟨fun g hg => ?_, by simp⟩
      simp only [List.mem_singleton] at hg; subst hg
      exact hI.mem_glist_iff.mp hg0
    · rw [hu]
      have F := hG.fam p hp hps
      refine ⟨fun g hg => ?_, by simp⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact F.lLive
      · exact hp
      · rw [← hr]; exact F.rLive

theorem unit_sum_le {t : Core} {A : Abs} {gh : GGh} (hI : INV t A)
    (hG : GInv t A.elist gh (fun _ => 0)) {x : Nat} (hne : cF t x ≠ NIL) (left : Bool) :
    ((unitCand t x left).map fun g => gSz t g).sum ≤ 3 * A.elist.length := by
  obtain ⟨hl, hlen⟩ := unit_live hI hG hne left
  have := sum_le_of_le (f := fun g => gSz t g) (B := A.elist.length) (unitCand t x left)
    (fun g hg => by rw [hG.sz g (hl g hg)]; exact runOf_len_le _ _ _)
  have := Nat.mul_le_mul_right A.elist.length hlen
  omega

/-- **The stored-value bound through the chunk drive.** -/
theorem cxsteps_wb {X Y : Core → Prop} {P : Params} {L : List Nat} {δ δu s₀ : Nat → Nat} {x : Nat}
    (h : CXSteps X Y L δ δu s₀ x) (hL : LabRoom K P) (hlen : 4 * L.length + 1 ≤ 2 ^ K) :
    CXSteps (fun t => X t ∧ (WB K t ∧ t.P = P)) (fun t => Y t ∧ (WB K t ∧ t.P = P)) L δ δu s₀ x
      := by
  refine h.andRun ?_ ?_ (fun t hW => ⟨wb_cremoveState hW.1, hW.2⟩)
  · intro t A gh labs hI hel hG hC hxL hst hne hrun hW
    subst hel
    obtain ⟨hW, hP⟩ := hW
    have Fx := hC.cfam x hxL hst
    have hlabs := ((ht_pushLabsL (P0 := t.P) (hP ▸ hL) x _).ok hW rfl hrun).2
    have h1 : cSz t (cLl t x) ≤ A.elist.length := by
      rw [hC.csz _ Fx.lLive]; exact celts_len_le _ _ _
    have h2 := unit_sum_le hI hG hne true
    exact ⟨wb_cmoveLState hW (unitCand_lt hW x true) hlabs (by omega), hP⟩
  · intro t A gh labs hI hel hG hC hxL hst hne hrun hW
    subst hel
    obtain ⟨hW, hP⟩ := hW
    have Fx := hC.cfam x hxL hst
    have hlabs := ((ht_pushLabsR (P0 := t.P) hW (hP ▸ hL) x _).ok hW rfl hrun).2
    have h1 : cSz t (cRr t x) ≤ A.elist.length := by
      rw [hC.csz _ Fx.rLive]; exact celts_len_le _ _ _
    have h2 := unit_sum_le hI hG hne false
    exact ⟨wb_cmoveRState hW (unitCand_lt hW x false) hlabs (by omega), hP⟩

end OrderMaintenance.Proof.Word

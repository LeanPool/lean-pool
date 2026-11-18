/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.CPhase


/-!
# Chunk-split steps, field by field

What a chunk-split move (`moveUnit` with `moveSizes`) and chunk removal do, under the conditions
that make their guards pass.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Running a chunk-split move -/

/-- Transfers the total size of the moved groups from the source chunk to the destination. -/
def cmoveSizes (s : Core) (x dst : Nat) (u : List Nat) : Core :=
  let moved := (u.map fun g => (s.Gs.getX g).size).sum
  let s1 := { s with C := s.C.modify x fun X => { X with size := X.size - moved } }
  { s1 with C := s1.C.modify dst fun X => { X with size := X.size + moved } }

/-- The state after moving unit `u` from the front of `x` to the end of its left sibling. -/
def cmoveLState (s : Core) (x : Nat) (u labs : List Nat) : Core :=
  cmoveSizes (moveGroupsLeft s x (cLl s x) u labs) x (cLl s x) u

/-- The state after moving unit `u` from the back of `x` to the front of its right sibling. -/
def cmoveRState (s : Core) (x : Nat) (u labs : List Nat) : Core :=
  cmoveSizes (moveGroupsRight s x (cRr s x) u labs) x (cRr s x) u

/-- The labels pushed at the end of the left sibling. -/
def pushLabsL (s : Core) (x k : Nat) : CM (List Nat) :=
  pushBackLabs (1 <<< (s.P.groupBits - 1)) s.P.groupSpacing s.P.groupBits
    (if cF s (cLl s x) = NIL then none else some (gL s (cLs s (cLl s x)))) k

/-- The labels pushed at the front of the right sibling. -/
def pushLabsR (s : Core) (x k : Nat) : CM (List Nat) :=
  pushFrontLabs (1 <<< (s.P.groupBits - 1)) s.P.groupSpacing
    (if cF s (cRr s x) = NIL then none else some (gL s (cF s (cRr s x)))) k

theorem unit_ok {s : Core} {x : Nat} {left : Bool}
    (h : (unitCand s x left).length = 1 ∨ unitOK s x (unitCand s x left) = true) :
    (unit x left).run s = .ok (unitCand s x left) s := by
  rcases unit_run s x left with ⟨_, hr⟩ | ⟨_, hr⟩ | ⟨msg, hr⟩
  · exact hr
  · exact hr
  · exfalso; revert hr; unfold unit
    simp only [run_get_bind]
    rcases h with h | h
    · simp only [h, BEq.rfl, ↓reduceIte, EStateM.run_pure, reduceCtorEq, imp_self]
    · by_cases hl : (unitCand s x left).length = 1
      · simp only [hl, BEq.rfl, ↓reduceIte, EStateM.run_pure, reduceCtorEq, imp_self]
      · rw [ite_eq_right (by simpa using hl), run_require_bind, ite_eq_left h]; simp only [
          EStateM.run_pure,
          reduceCtorEq,
          imp_self]

theorem moveUnit_left_ok {s : Core} {x : Nat} {labs : List Nat} (hne : cF s x ≠ NIL)
    (hu : (unitCand s x true).length = 1 ∨ unitOK s x (unitCand s x true) = true)
    (hadj : cN s (cLl s x) = x)
    (hlabs : (pushLabsL s x (unitCand s x true).length).run s = .ok labs s) :
    (moveUnit x true).run s =
      .ok (cLl s x, unitCand s x true) (moveGroupsLeft s x (cLl s x) (unitCand s x true) labs) := by
  unfold moveUnit
  rw [run_getP_bind, run_getC_bind, run_require_bind,
    ite_eq_left (by simp only [bne_iff_ne, ne_eq]; exact hne), run_bind, unit_ok hu]
  dsimp only
  rw [ite_eq_left rfl, run_getC_bind, run_require_bind, ite_eq_left (beq_iff_eq.mpr hadj),
    run_getG_bind,
    run_bind]
  unfold pushLabsL at hlabs
  have : (if ((s.C.getX (s.C.getX x).l).first == NIL) = true then none
      else some (s.Gs.getX (s.C.getX (s.C.getX x).l).last).lab) =
      (if cF s (cLl s x) = NIL then none else some (gL s (cLs s (cLl s x)))) := by
    simp only [cF, cLl, gL, cLs, beq_iff_eq]
  rw [this, hlabs]
  rfl

theorem moveUnit_right_ok {s : Core} {x : Nat} {labs : List Nat} (hne : cF s x ≠ NIL)
    (hu : (unitCand s x false).length = 1 ∨ unitOK s x (unitCand s x false) = true)
    (hadj : cP s (cRr s x) = x)
    (hlabs : (pushLabsR s x (unitCand s x false).length).run s = .ok labs s) :
    (moveUnit x false).run s =
      .ok (cRr s x, unitCand s x false) (moveGroupsRight s x (cRr s x) (unitCand s x false)
        labs) := by
  unfold moveUnit
  rw [run_getP_bind, run_getC_bind, run_require_bind,
    ite_eq_left (by simp only [bne_iff_ne, ne_eq]; exact hne), run_bind, unit_ok hu]
  dsimp only
  rw [ite_eq_right Bool.false_ne_true, run_getC_bind, run_require_bind,
    ite_eq_left (beq_iff_eq.mpr hadj),
    run_getG_bind, run_bind]
  unfold pushLabsR at hlabs
  have : (if ((s.C.getX (s.C.getX x).r).first == NIL) = true then none
      else some (s.Gs.getX (s.C.getX (s.C.getX x).r).first).lab) =
      (if cF s (cRr s x) = NIL then none else some (gL s (cF s (cRr s x)))) := by
    simp only [cF, cRr, gL, beq_iff_eq]
  rw [this, hlabs]
  rfl

theorem chunkSplitStep_left {s : Core} {x : Nat} {labs : List Nat} (hne : cF s x ≠ NIL)
    (hdir : cSz s (cLl s x) ≤ cSz s (cRr s x))
    (hu : (unitCand s x true).length = 1 ∨ unitOK s x (unitCand s x true) = true)
    (hadj : cN s (cLl s x) = x)
    (hlabs : (pushLabsL s x (unitCand s x true).length).run s = .ok labs s) :
    (chunkSplitStep x).run s = .ok true (cmoveLState s x (unitCand s x true) labs) := by
  unfold chunkSplitStep
  rw [run_getC_bind, ite_eq_right (fun h => hne (beq_iff_eq.mp h)), run_getC_bind, run_getC_bind,
    run_bind]
  have hd : decide ((s.C.getX (s.C.getX x).l).size ≤ (s.C.getX (s.C.getX x).r).size) = true := by
    simp only [cSz, cLl, cRr] at hdir; simp only [hdir, decide_true]
  rw [hd, moveUnit_left_ok hne hu hadj hlabs]
  rfl

theorem chunkSplitStep_right {s : Core} {x : Nat} {labs : List Nat} (hne : cF s x ≠ NIL)
    (hdir : cSz s (cRr s x) < cSz s (cLl s x))
    (hu : (unitCand s x false).length = 1 ∨ unitOK s x (unitCand s x false) = true)
    (hadj : cP s (cRr s x) = x)
    (hlabs : (pushLabsR s x (unitCand s x false).length).run s = .ok labs s) :
    (chunkSplitStep x).run s = .ok true (cmoveRState s x (unitCand s x false) labs) := by
  unfold chunkSplitStep
  rw [run_getC_bind, ite_eq_right (fun h => hne (beq_iff_eq.mp h)), run_getC_bind, run_getC_bind,
    run_bind]
  have hd : decide ((s.C.getX (s.C.getX x).l).size ≤ (s.C.getX (s.C.getX x).r).size) = false := by
    simp only [cSz, cLl, cRr] at hdir; simp only [decide_eq_false_iff_not, not_le]; omega
  rw [hd, moveUnit_right_ok hne hu hadj hlabs]
  rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Chunk removal -/

/-- Marks an emptied chunk as dead while retaining its other fields. -/
def deadC (X : Chunk) : Chunk := { X with st := .dead }
/-- Finishes a chunk split by clearing its state and source pointer. -/
def quietC (X : Chunk) : Chunk := { X with st := .quiet, src := NIL }

/-- The state after removing the emptied chunk `x`: it is dead, its siblings are quiet. -/
def cremoveState (s : Core) (x : Nat) : Core :=
  let s1 := { s with C := s.C.modify x deadC }
  let s2 := { s1 with C := s1.C.modify (cLl s x) quietC }
  { s2 with C := s2.C.modify (cRr s x) quietC }

@[simp] theorem run_getC' (i : Nat) (s : Core) : (getC i).run s = .ok (s.C.getX i) s := rfl

theorem removeChunk_ok {s : Core} {x : Nat} (hlr : cLl s x ≠ cRr s x) (hlx : cLl s x ≠ x)
    (hrx : cRr s x ≠ x) (hx : x < s.C.size)
    (hl : cSt s (cLl s x) = .overflow ∧ cSrc s (cLl s x) = x)
    (hr : cSt s (cRr s x) = .overflow ∧ cSrc s (cRr s x) = x)
    (hszl : cSz s (cLl s x) ≤ s.P.theta) (hszr : cSz s (cRr s x) ≤ s.P.theta) :
    (removeChunk x).run s = .ok () (cremoveState s x) := by
  unfold removeChunk pqEnterIfAbove
  simp only [cLl, cRr, cSt, cSrc, cSz] at hlr hlx hrx hl hr hszl hszr
  have nl : ¬ (s.C.getX (s.C.getX x).l).size > s.P.theta := by omega
  have nr : ¬ (s.C.getX (s.C.getX x).r).size > s.P.theta := by omega
  simp only [modC, Bool.and_eq_true, beq_iff_eq, gt_iff_lt, bind_pure_comp, map_bind,
      List.forIn_cons, List.forIn_nil, bind_assoc, id_map', EStateM.run_bind,
      EStateM.run_modify, run_getC', Array.getX_modify, hx, and_self, ↓reduceIte, Ne.symm hlx,
      and_true, hl, bind_map_left, Array.size_modify, true_and, apply_ite (f := Chunk.size),
      ite_self, run_getP', nl, pure_bind, hlr, false_and, Ne.symm hrx, hr, nr,
      EStateM.run_pure, EStateM.Result.ok.injEq]
  rfl

theorem chunkSplitStep_remove {s : Core} {x : Nat} (he : cF s x = NIL) (hlr : cLl s x ≠ cRr s x)
    (hlx : cLl s x ≠ x) (hrx : cRr s x ≠ x) (hx : x < s.C.size)
    (hl : cSt s (cLl s x) = .overflow ∧ cSrc s (cLl s x) = x)
    (hr : cSt s (cRr s x) = .overflow ∧ cSrc s (cRr s x) = x)
    (hszl : cSz s (cLl s x) ≤ s.P.theta) (hszr : cSz s (cRr s x) ≤ s.P.theta) :
    (chunkSplitStep x).run s = .ok false (cremoveState s x) := by
  unfold chunkSplitStep
  rw [run_getC_bind, ite_eq_left (beq_iff_eq.mpr he), run_bind,
    removeChunk_ok hlr hlx hrx hx hl hr hszl hszr]
  rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The unit at an end of a chunk -/

theorem succOf_ne_head {h : Nat} {t : List Nat} (hnd : (h :: t).Nodup) (h0 : h ≠ NIL) (a : Nat) :
    succOf (h :: t) a ≠ h := by
  intro e
  obtain ⟨l1, l2, e2⟩ := succOf_split e h0
  rw [e2] at hnd
  cases l1 with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at e2
    rw [← e2.1] at hnd; simp only [List.nil_append, List.nodup_cons, List.mem_cons, true_or,
        not_true_eq_false, false_and] at hnd
  | cons b l1' =>
    simp only [List.cons_append, List.cons.injEq] at e2
    rw [← e2.1] at hnd
    simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons, true_or,
        or_true, not_true_eq_false, false_and] at hnd

/-- No group of chunk `x` precedes its first group. -/
theorem INV.not_before_first {s : Core} {A : Abs} (hI : INV s A) {x a : Nat} (hne : cF s x ≠ NIL)
    (ha : a ∈ A.glist) (hac : gC s a = x) : gN s a ≠ cF s x := by
  intro e
  obtain ⟨hx, t, ht⟩ := hI.run_ne_nil hne
  have hax := hI.mem_grps_of_chk ha hac
  have h1 := hI.gN_in_run hx hax (by rw [e]; exact hne) (by
    rw [e]; have := hI.chk x hx (cF s x) (by rw [ht]; simp); exact this)
  rw [e, ht] at h1
  have hnd := hI.grps_nodup hx
  rw [ht] at hnd
  exact succOf_ne_head hnd hne a h1.symm

/-- No group of chunk `x` follows its last group. -/
theorem INV.not_after_last {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hne : cF s x ≠ NIL)
    {a : Nat} (hlast : gN s (cLs s x) = a) (ha0 : a ≠ NIL) : gC s a ≠ x := by
  intro hac
  obtain ⟨hx, t, ht⟩ := hI.run_ne_nil hne
  have hE := hI.cEnds x hx
  have hl : cLs s x ∈ A.grps x := by
    rw [hE.2, ht]; exact getLastD_cons_mem _ _ _
  have h1 := hI.gN_in_run hx hl (by rw [hlast]; exact ha0) (by rw [hlast]; exact hac)
  rw [hlast] at h1
  -- the successor of the last member inside the run is `NIL`
  have hnd := hI.grps_nodup hx
  obtain ⟨r0, hr0⟩ : ∃ r0, A.grps x = r0 ++ [cLs s x] := by
    rcases (A.grps x).eq_nil_or_concat with h | ⟨r, z, h⟩
    · rw [ht] at h; simp only [reduceCtorEq] at h
    · refine ⟨r, ?_⟩; rw [h]; rw [h] at hE; have := hE.2; simp only [List.concat_eq_append,
        List.getLastD_eq_getLast?,
        List.getLast?_append,
        List.getLast?_singleton,
        Option.some_or,
        Option.getD_some] at this; rw [this]; simp only [
        List.concat_eq_append]
  rw [hr0] at h1 hnd
  rw [show r0 ++ [cLs s x] = r0 ++ cLs s x :: [] by simp, succOf_mid (by simpa using hnd)] at h1
  exact ha0 h1

/-- **The left unit of a non-empty chunk** is its first group, quiet, or the whole family of
which that group is the left sibling. -/
theorem left_unit {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} (hI : INV s A)
    (hG : GInv s A.elist gh δ) {x : Nat} (hne : cF s x ≠ NIL) :
    (gSt s (cF s x) = .quiet ∧ unitCand s x true = [cF s x]) ∨
    (∃ p, LiveG s p ∧ gSt s p = .splitting ∧ gLl s p = cF s x ∧
      unitCand s x true = [cF s x, p, gRr s p] ∧ unitOK s x (unitCand s x true) = true) := by
  obtain ⟨hx, t, ht⟩ := hI.run_ne_nil hne
  have hg0 : cF s x ∈ A.glist := A.grps_sub_glist hx (by rw [ht]; simp)
  have hgL := hI.mem_glist_iff.mp hg0
  have hgx : gC s (cF s x) = x := hI.chk x hx _ (by rw [ht]; simp)
  cases hst : gSt s (cF s x) with
  | quiet =>
    left; refine ⟨rfl, ?_⟩
    simp only [unitCand, ite_true]; simp only [gSt, cF] at hst; simp only [hst, bne_iff_ne,
        ne_eq, reduceCtorEq,
        not_false_eq_true,
        ↓reduceIte]
  | splitting =>
    exfalso
    have F := hG.fam _ hgL hst
    exact hI.not_before_first hne (hI.mem_glist_iff.mpr F.lLive) (by rw [F.lC, hgx]) F.lAdj
  | overflow =>
    right
    obtain ⟨hp, hps, hlr⟩ := hG.ovf _ hgL hst
    have F := hG.fam _ hp hps
    have hpx : gC s (gSrc s (cF s x)) = x := by
      rcases hlr with e | e
      · rw [← F.lC, e, hgx]
      · rw [← F.rC, e, hgx]
    have hl : gLl s (gSrc s (cF s x)) = cF s x := by
      rcases hlr with e | e
      · exact e
      · exfalso
        exact hI.not_before_first hne (hI.mem_glist_iff.mpr hp) hpx (by rw [F.rAdj, e])
    refine ⟨gSrc s (cF s x), hp, hps, hl, ?_, ?_⟩
    · simp only [unitCand, ite_true]
      simp only [gSt, cF, gSrc, gLl, gRr] at hst hl ⊢
      simp only [hst, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hl, BEq.rfl,
          Bool.and_self]
    · have hu : unitCand s x true = [cF s x, gSrc s (cF s x), gRr s (gSrc s (cF s x))] := by
        simp only [unitCand, ite_true]
        simp only [gSt, cF, gSrc, gLl, gRr] at hst hl ⊢
        simp only [hst, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hl, BEq.rfl,
            Bool.and_self]
      rw [hu]
      simp only [unitOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
        ne_eq, beq_iff_eq, List.tail_cons, List.zip_cons_cons, List.zip_nil_right]
      refine ⟨⟨⟨hgL.1, hgx⟩, ⟨hp.1, hpx⟩, ⟨F.rLive.1, by
        change gC s (gRr s (gSrc s (cF s x))) = x; rw [F.rC, hpx]⟩⟩, ?_, ?_⟩
      · have := F.lAdj; rw [hl] at this; exact this
      · exact F.rAdj
  | dead => exact absurd hst (hG.notDead _ hgL)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **The right unit of a non-empty chunk** is its last group, quiet, or the whole family of which
that group is the right sibling. -/
theorem right_unit {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} (hI : INV s A)
    (hG : GInv s A.elist gh δ) {x : Nat} (hne : cF s x ≠ NIL) :
    (gSt s (cLs s x) = .quiet ∧ unitCand s x false = [cLs s x]) ∨
    (∃ p, LiveG s p ∧ gSt s p = .splitting ∧ gRr s p = cLs s x ∧
      unitCand s x false = [gLl s p, p, cLs s x] ∧ unitOK s x (unitCand s x false) = true) := by
  obtain ⟨hx, t, ht⟩ := hI.run_ne_nil hne
  have hE := hI.cEnds x hx
  have hlm : cLs s x ∈ A.grps x := by rw [hE.2, ht]; exact getLastD_cons_mem _ _ _
  have hg0 : cLs s x ∈ A.glist := A.grps_sub_glist hx hlm
  have hgL := hI.mem_glist_iff.mp hg0
  have hgx : gC s (cLs s x) = x := hI.chk x hx _ hlm
  cases hst : gSt s (cLs s x) with
  | quiet =>
    left; refine ⟨rfl, ?_⟩
    simp only [unitCand, Bool.false_eq_true, ite_false]; simp only [gSt, cLs] at hst; simp only [
        hst,
        bne_iff_ne,
        ne_eq,
        reduceCtorEq,
        not_false_eq_true,
        ↓reduceIte]
  | splitting =>
    exfalso
    have F := hG.fam _ hgL hst
    exact hI.not_after_last hne F.rAdj F.rLive.1 (by rw [F.rC, hgx])
  | overflow =>
    right
    obtain ⟨hp, hps, hlr⟩ := hG.ovf _ hgL hst
    have F := hG.fam _ hp hps
    have hpx : gC s (gSrc s (cLs s x)) = x := by
      rcases hlr with e | e
      · rw [← F.lC, e, hgx]
      · rw [← F.rC, e, hgx]
    have hr : gRr s (gSrc s (cLs s x)) = cLs s x := by
      rcases hlr with e | e
      · exfalso
        have := F.lAdj; rw [e] at this
        exact hI.not_after_last hne this hp.1 hpx
      · exact e
    have hu : unitCand s x false = [gLl s (gSrc s (cLs s x)), gSrc s (cLs s x), cLs s x] := by
      simp only [unitCand, Bool.false_eq_true, ite_false, Bool.false_and, Bool.not_false,
        Bool.true_and]
      simp only [gSt, cLs, gSrc, gLl, gRr] at hst hr ⊢
      simp only [hst, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hr, BEq.rfl]
    refine ⟨gSrc s (cLs s x), hp, hps, hr, hu, ?_⟩
    rw [hu]
    simp only [unitOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
      ne_eq, beq_iff_eq, List.tail_cons, List.zip_cons_cons, List.zip_nil_right]
    refine ⟨⟨⟨F.lLive.1, by change gC s (gLl s (gSrc s (cLs s x))) = x; rw [F.lC, hpx]⟩,
      ⟨hp.1, hpx⟩, ⟨hgL.1, hgx⟩⟩, F.lAdj, ?_⟩
    have := F.rAdj; rw [hr] at this; exact this
  | dead => exact absurd hst (hG.notDead _ hgL)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The records after a chunk-split move -/

/-- What a chunk-split move of unit `u` from `x` to `dst` does. -/
structure CMoveSpec (s s' : Core) (x dst : Nat) (u labs : List Nat) : Prop where
  E : s'.E = s.E
  head : s'.head = s.head
  P : s'.P = s.P
  Gsize : s'.Gs.size = s.Gs.size
  G : ∀ g, s'.Gs.getX g = if g ∈ u then
      { s.Gs.getX g with chk := dst, lab := labs.getD (u.idxOf g) 0 } else s.Gs.getX g
  Csize : s'.C.size = s.C.size
  csz : ∀ c, cSz s' c = if c = x then cSz s x - (u.map fun g => gSz s g).sum
      else if c = dst then cSz s dst + (u.map fun g => gSz s g).sum else cSz s c
  cst : ∀ c, cSt s' c = cSt s c
  csrc : ∀ c, cSrc s' c = cSrc s c
  cl : ∀ c, cLl s' c = cLl s c
  cr : ∀ c, cRr s' c = cRr s c
  cnext : ∀ c, cN s' c = cN s c
  cprev : ∀ c, cP s' c = cP s c
  ctag : ∀ c, cT s' c = cT s c
  fl : ∀ c, c ≠ x → c ≠ dst → cF s' c = cF s c ∧ cLs s' c = cLs s c
  rest : s'.pqHead = s.pqHead ∧ s'.pqNext = s.pqNext ∧ s'.pqPrev = s.pqPrev ∧
    s'.pqWhere = s.pqWhere ∧ s'.nbNext = s.nbNext ∧ s'.nbPrev = s.nbPrev ∧ s'.pqHi = s.pqHi ∧
    s'.pqLo = s.pqLo ∧ s'.resJob = s.resJob ∧ s'.nodes = s.nodes ∧ s'.path = s.path ∧
    s'.cin = s.cin ∧ s'.lpar = s.lpar ∧ s'.count = s.count ∧ s'.firstChunk = s.firstChunk ∧
    s'.firstGroup = s.firstGroup ∧ s'.freeG = s.freeG ∧ s'.tail = s.tail

theorem cmoveSizes_C {t : Core} {x dst : Nat} {u : List Nat} (hxd : x ≠ dst) (hx : x < t.C.size)
    (hd : dst < t.C.size) (c : Nat) :
    (cmoveSizes t x dst u).C.getX c =
      if c = x then { t.C.getX c with size := (t.C.getX c).size - (u.map fun g => gSz t g).sum }
      else if c = dst then
        { t.C.getX c with size := (t.C.getX c).size + (u.map fun g => gSz t g).sum }
      else t.C.getX c := by
  simp only [cmoveSizes, Array.getX_modify, Array.size_modify']
  by_cases h1 : c = x
  · subst h1; simp only [Ne.symm hxd, false_and, ↓reduceIte, hx, and_self]
  · by_cases h2 : c = dst
    · subst h2; simp only [hd, and_self, ↓reduceIte, Ne.symm h1, false_and, h1]
    · simp only [Ne.symm h2, false_and, ↓reduceIte, Ne.symm h1, h1, h2]

theorem cmoveL_spec {s : Core} {x : Nat} {u labs : List Nat} (hxy : x ≠ cLl s x)
    (hx : x < s.C.size) (hy : cLl s x < s.C.size) (hnd : u.Nodup) (hlen : labs.length = u.length)
    (hsz : ∀ g ∈ u, g < s.Gs.size) :
    CMoveSpec s (cmoveLState s x u labs) x (cLl s x) u labs := by
  have hG : ∀ g, (moveGroupsLeft s x (cLl s x) u labs).Gs.getX g = _ := fun g =>
    moveGroups_G (s := s) (d := cLl s x) hnd hlen hsz g
  have hGs : (moveGroupsLeft s x (cLl s x) u labs).Gs.size = s.Gs.size := by
    simp only [moveGroupsLeft, List.getLastD_eq_getLast?, beq_iff_eq, List.headD_eq_head?_getD,
        foldChk_size]
  have hCm : ∀ c, (moveGroupsLeft s x (cLl s x) u labs).C.getX c = _ := fun c =>
    moveGroupsLeft_C (s := s) (u := u) (labs := labs) hxy hx hy c
  have hCs : (moveGroupsLeft s x (cLl s x) u labs).C.size = s.C.size := by
    simp only [moveGroupsLeft, List.getLastD_eq_getLast?, beq_iff_eq, List.headD_eq_head?_getD,
      Array.size_modify]
  have hgsz : ∀ g, gSz (moveGroupsLeft s x (cLl s x) u labs) g = gSz s g := by
    intro g; simp only [gSz, hG]; split <;> rfl
  have hC : ∀ c, (cmoveLState s x u labs).C.getX c = _ := fun c =>
    cmoveSizes_C (t := moveGroupsLeft s x (cLl s x) u labs) (u := u) hxy (by rw [hCs]; exact hx)
      (by rw [hCs]; exact hy) c
  simp only [hgsz] at hC
  have fld : ∀ c, ((cmoveLState s x u labs).C.getX c).st = (s.C.getX c).st ∧
      ((cmoveLState s x u labs).C.getX c).src = (s.C.getX c).src ∧
      ((cmoveLState s x u labs).C.getX c).l = (s.C.getX c).l ∧
      ((cmoveLState s x u labs).C.getX c).r = (s.C.getX c).r ∧
      ((cmoveLState s x u labs).C.getX c).next = (s.C.getX c).next ∧
      ((cmoveLState s x u labs).C.getX c).prev = (s.C.getX c).prev ∧
      ((cmoveLState s x u labs).C.getX c).tag = (s.C.getX c).tag := by
    intro c
    rw [hC c, hCm c]
    split_ifs <;> simp_all
  refine ⟨rfl, rfl, rfl, by simp only [cmoveLState, cmoveSizes, hGs], fun g => hG g,
    by simp only [cmoveLState, cmoveSizes, Array.size_modify, hCs], fun c => ?_, fun c => (fld c).1,
    fun c => (fld c).2.1, fun c => (fld c).2.2.1, fun c => (fld c).2.2.2.1,
    fun c => (fld c).2.2.2.2.1, fun c => (fld c).2.2.2.2.2.1, fun c => (fld c).2.2.2.2.2.2,
    fun c h1 h2 => ⟨?_, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩⟩
  · simp only [cSz]; rw [hC c, hCm c]
    by_cases hcx : c = x
    · subst hcx; simp only [ite_true, ite_eq_right hxy]; split <;> rfl
    · by_cases hcy : c = cLl s x
      · subst hcy; simp only [hcx, ↓reduceIte, List.headD_eq_head?_getD,
          List.getLastD_eq_getLast?]
      · simp only [hcx, ↓reduceIte, hcy]
  · simp only [cF]; rw [hC c, hCm c]; simp only [h1, ↓reduceIte, h2]
  · simp only [cLs]; rw [hC c, hCm c]; simp only [h1, ↓reduceIte, h2]

theorem cmoveR_spec {s : Core} {x : Nat} {u labs : List Nat} (hxz : x ≠ cRr s x)
    (hx : x < s.C.size) (hz : cRr s x < s.C.size) (hnd : u.Nodup) (hlen : labs.length = u.length)
    (hsz : ∀ g ∈ u, g < s.Gs.size) :
    CMoveSpec s (cmoveRState s x u labs) x (cRr s x) u labs := by
  have hG : ∀ g, (moveGroupsRight s x (cRr s x) u labs).Gs.getX g = _ := fun g =>
    moveGroups_G (s := s) (d := cRr s x) hnd hlen hsz g
  have hGs : (moveGroupsRight s x (cRr s x) u labs).Gs.size = s.Gs.size := by
    simp only [moveGroupsRight, List.headD_eq_head?_getD, beq_iff_eq, List.getLastD_eq_getLast?,
        foldChk_size]
  have hCm : ∀ c, (moveGroupsRight s x (cRr s x) u labs).C.getX c = _ := fun c =>
    moveGroupsRight_C (s := s) (u := u) (labs := labs) hxz hx hz c
  have hCs : (moveGroupsRight s x (cRr s x) u labs).C.size = s.C.size := by
    simp only [moveGroupsRight, List.headD_eq_head?_getD, beq_iff_eq, List.getLastD_eq_getLast?,
      Array.size_modify]
  have hgsz : ∀ g, gSz (moveGroupsRight s x (cRr s x) u labs) g = gSz s g := by
    intro g; simp only [gSz, hG]; split <;> rfl
  have hC : ∀ c, (cmoveRState s x u labs).C.getX c = _ := fun c =>
    cmoveSizes_C (t := moveGroupsRight s x (cRr s x) u labs) (u := u) hxz (by rw [hCs]; exact hx)
      (by rw [hCs]; exact hz) c
  simp only [hgsz] at hC
  have fld : ∀ c, ((cmoveRState s x u labs).C.getX c).st = (s.C.getX c).st ∧
      ((cmoveRState s x u labs).C.getX c).src = (s.C.getX c).src ∧
      ((cmoveRState s x u labs).C.getX c).l = (s.C.getX c).l ∧
      ((cmoveRState s x u labs).C.getX c).r = (s.C.getX c).r ∧
      ((cmoveRState s x u labs).C.getX c).next = (s.C.getX c).next ∧
      ((cmoveRState s x u labs).C.getX c).prev = (s.C.getX c).prev ∧
      ((cmoveRState s x u labs).C.getX c).tag = (s.C.getX c).tag := by
    intro c
    rw [hC c, hCm c]
    split_ifs <;> simp_all
  refine ⟨rfl, rfl, rfl, by simp only [cmoveRState, cmoveSizes, hGs], fun g => hG g,
    by simp only [cmoveRState, cmoveSizes, Array.size_modify, hCs], fun c => ?_, fun c => (fld c).1,
    fun c => (fld c).2.1, fun c => (fld c).2.2.1, fun c => (fld c).2.2.2.1,
    fun c => (fld c).2.2.2.2.1, fun c => (fld c).2.2.2.2.2.1, fun c => (fld c).2.2.2.2.2.2,
    fun c h1 h2 => ⟨?_, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩⟩
  · simp only [cSz]; rw [hC c, hCm c]
    by_cases hcx : c = x
    · subst hcx; simp only [ite_true, ite_eq_right hxz]; split <;> rfl
    · by_cases hcz : c = cRr s x
      · subst hcz; simp only [hcx, ↓reduceIte, List.headD_eq_head?_getD,
          List.getLastD_eq_getLast?]
      · simp only [hcx, ↓reduceIte, hcz]
  · simp only [cF]; rw [hC c, hCm c]; simp only [h1, ↓reduceIte, h2]
  · simp only [cLs]; rw [hC c, hCm c]; simp only [h1, ↓reduceIte, h2]

end OrderMaintenance.Proof

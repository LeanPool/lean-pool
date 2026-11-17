/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.Lists


/-!
# What the top structure and the priority queue may change

* `Same s s'`: every field INV-S reads is unchanged (tags included).
* `Safe s s'`: the links are unchanged, and INV-S is preserved. Tags may change, but only by
  guarded writes (`guardedSetTag`).

The priority queue, the top tree's tables, paths and jobs, and the sizes and states of groups
and chunks are invisible to INV-S, so every function that touches only them preserves `Same`;
the top structure's tag writes preserve `Safe`.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- Preserve all structural links and every chunk order tag. -/
def Same (s s' : Core) : Prop := SameLinks s s' ∧ ∀ c, cT s' c = cT s c
/-- Preserve structural links and carry every established core invariant to the new state. -/
def Safe (s s' : Core) : Prop := SameLinks s s' ∧ ∀ A, INV s A → INV s' A

instance : IsPre Same where
  refl s := ⟨SameLinks.refl s, fun _ => rfl⟩
  trans _ _ _ h1 h2 := ⟨h1.1.trans h2.1, fun c => (h2.2 c).trans (h1.2 c)⟩

instance : IsPre Safe where
  refl s := ⟨SameLinks.refl s, fun _ h => h⟩
  trans _ _ _ h1 h2 := ⟨h1.1.trans h2.1, fun A h => h2.2 A (h1.2 A h)⟩

theorem Same.safe {s s' : Core} (h : Same s s') : Safe s s' :=
  ⟨h.1, fun _ hI => hI.of_sameLinks h.1 h.2⟩

theorem Pres.same_safe {α : Type} {m : CM α} (h : Pres Same m) : Pres Safe m :=
  h.mono fun _ _ => Same.safe

/-- Close a goal `∀ s, Same s (f s)` for a state update `f` that leaves INV-S's fields alone. -/
syntax "same" : tactic
macro_rules
  | `(tactic| same) => `(tactic| (
      intro s
      refine ⟨?_, fun _ => ?_⟩
      all_goals (try constructor)
      all_goals (try intro _)
      all_goals simp [eN, eP, eG, eL, gN, gP, gF, gLs, gC, gL, gA, cN, cP, cF, cLs, cT,
        apply_ite (f := Chunk.next), apply_ite (f := Chunk.prev), apply_ite (f := Chunk.first),
        apply_ite (f := Chunk.last), apply_ite (f := Chunk.tag),
        apply_ite (f := Group.next), apply_ite (f := Group.prev), apply_ite (f := Group.first),
        apply_ite (f := Group.last), apply_ite (f := Group.chk), apply_ite (f := Group.lab),
        apply_ite (f := Group.alive)]))

/-! ### Reads -/

theorem pres_getE {R : Core → Core → Prop} [IsPre R] (i : Nat) : Pres R (getE i) := by
  unfold getE; pres
theorem pres_getG {R : Core → Core → Prop} [IsPre R] (i : Nat) : Pres R (getG i) := by
  unfold getG; pres
theorem pres_getC {R : Core → Core → Prop} [IsPre R] (i : Nat) : Pres R (getC i) := by
  unfold getC; pres
theorem pres_getN {R : Core → Core → Prop} [IsPre R] (i : Nat) : Pres R (getN i) := by
  unfold getN; pres
theorem pres_getP {R : Core → Core → Prop} [IsPre R] : Pres R getP := by
  unfold getP; pres
theorem pres_getPath {R : Core → Core → Prop} [IsPre R] (c : Nat) : Pres R (getPath c) := by
  unfold getPath; pres
theorem pres_getLpar {R : Core → Core → Prop} [IsPre R] (c : Nat) : Pres R (getLpar c) := by
  unfold getLpar; pres
theorem pres_pqEmpty {R : Core → Core → Prop} [IsPre R] : Pres R pqEmpty := by
  unfold pqEmpty; pres

/-! ### Top structure: tables, paths, nodes -/

theorem pres_modN (i : Nat) (f : Node → Node) : Pres Same (modN i f) := by
  unfold modN; pres; same
theorem pres_setPath (c : Nat) (p : Array Nat) : Pres Same (setPath c p) := by
  unfold setPath; pres; same
theorem pres_setPathAt (c j v : Nat) : Pres Same (setPathAt c j v) := by
  unfold setPathAt; pres; same
theorem pres_setLpar (c v : Nat) : Pres Same (setLpar c v) := by
  unfold setLpar; pres; same
theorem pres_inTablesOf (e h : Nat) : Pres Same (inTablesOf e h) := by
  unfold inTablesOf; pres [pres_getN _]
theorem pres_setInTables (e h : Nat) (l : List Nat) : Pres Same (setInTables e h l) := by
  unfold setInTables; pres [pres_modN _ _]; same
theorem pres_resetTop : Pres Same resetTop := by
  unfold resetTop; pres; same
theorem pres_newNode (h : Nat) : Pres Same (newNode h) := by
  unfold newNode; pres; same
theorem pres_tagOf (c : Nat) : Pres Same (tagOf c) := by
  unfold tagOf; pres [pres_getP, pres_getPath _, pres_getN _]
theorem pres_guardTag (c t : Nat) : Pres Same (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem pres_roomNextTo (t e : Nat) (b : Bool) : Pres Same (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem pres_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) :
    Pres Same (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, pres_modN _ _]
theorem pres_sameDrain (a b : Nat) : Pres Same (sameDrain a b) := by
  unfold sameDrain; pres
theorem pres_addTable (h t e : Nat) : Pres Same (addTable h t e) := by
  unfold addTable; pres [pres_inTablesOf _ _, pres_setInTables _ _ _]
theorem pres_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) :
    Pres Same (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [pres_tableInsert _ _ _ _ _]
theorem pres_setParent (h w e : Nat) : Pres Same (setParent h w e) := by
  unfold setParent; pres [pres_setLpar _ _, pres_modN _ _]
theorem pres_startDrain (v : Nat) : Pres Same (startDrain v) := by
  unfold startDrain
  pres [pres_getP, pres_getN _, pres_roomNextTo _ _ _, pres_newNode _,
    pres_insertAroundIn _ _ _ _, pres_modN _ _, pres_addTable _ _ _, pres_setParent _ _ _]
theorem pres_dropTable (h v e : Nat) : Pres Same (dropTable h v e) := by
  unfold dropTable; pres [pres_inTablesOf _ _, pres_setInTables _ _ _]
theorem pres_dropEntry (v T : Nat) : Pres Same (dropEntry v T) := by
  unfold dropEntry; pres [pres_getN _, pres_modN _ _]
theorem pres_release (v t : Nat) : Pres Same (release v t) := by
  unfold release; pres [pres_getN _, pres_modN _ _]
theorem pres_finishDrain (v : Nat) : Pres Same (finishDrain v) := by
  unfold finishDrain
  pres [pres_getN _, pres_dropTable _ _ _, pres_dropEntry _ _, pres_release _ _, pres_modN _ _]

/-! ### Priority queue, sizes and states -/

theorem pres_pqLinkAfter (s p : Nat) : Pres Same (pqLinkAfter s p) := by
  unfold pqLinkAfter; pres <;> same
theorem pres_pqAdd (c s p : Nat) : Pres Same (pqAdd c s p) := by
  unfold pqAdd; pres [pres_pqLinkAfter _ _] <;> same
theorem pres_pqDel (c : Nat) : Pres Same (pqDel c) := by
  unfold pqDel; pres <;> same
theorem pres_pqInsertScan (c s : Nat) : Pres Same (pqInsertScan c s) := by
  unfold pqInsertScan; pres [pres_pqAdd _ _ _]
theorem pres_pqAdjust (c old new : Nat) : Pres Same (pqAdjust c old new) := by
  unfold pqAdjust; pres [pres_getP, pres_pqInsertScan _ _, pres_pqDel _, pres_pqAdd _ _ _]
theorem pres_pqEnterIfAbove (c : Nat) : Pres Same (pqEnterIfAbove c) := by
  unfold pqEnterIfAbove; pres [pres_getC _, pres_getP, pres_pqInsertScan _ _]
theorem pres_pqPopMax : Pres Same pqPopMax := by
  unfold pqPopMax; pres [pres_pqDel _]
theorem pres_chunkSize (c : Nat) (inc : Bool) : Pres Same (chunkSize c inc) := by
  unfold chunkSize; pres [pres_getC _, pres_pqAdjust _ _ _] <;> same
theorem pres_removeChunk (x : Nat) : Pres Same (removeChunk x) := by
  unfold removeChunk; pres [pres_getC _, pres_pqEnterIfAbove _] <;> same

end OrderMaintenance.Proof

/-! ### Guarded tag writes -/

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The guard of a tag write: `t` lies strictly between the tags of `c`'s neighbours. -/
def TagOK (s : Core) (c t : Nat) : Prop :=
  (cP s c ≠ NIL → cT s (cP s c) < t) ∧ (cN s c ≠ NIL → t < cT s (cN s c))

theorem guardTag_run (c t : Nat) (s : Core) :
    ((guardTag c t).run s = .ok () s ∧ TagOK s c t) ∨
      ∃ msg, (guardTag c t).run s = .error (.guard msg) s := by
  unfold guardTag getC TagOK
  by_cases h1 : cP s c ≠ NIL ∧ ¬ cT s (cP s c) < t
  · right
    refine ⟨"top: tag not above predecessor", ?_⟩
    simp only [cP, cT] at h1
    simp [ h1]
  · by_cases h2 : cN s c ≠ NIL ∧ ¬ t < cT s (cN s c)
    · right
      refine ⟨"top: tag not below successor", ?_⟩
      simp only [cP, cN, cT] at h1 h2
      simp only [not_and, not_not] at h1
      by_cases hp : (s.C.getX c).prev = NIL
      · simp [ h2, hp]
      · have := h1 hp
        simp [ h2, hp, Nat.not_le.mpr this, Nat.not_lt.mp h2.2]
    · left
      simp only [cP, cN, cT, not_and, not_not, ne_eq] at h1 h2 ⊢
      refine ⟨?_, fun hp => Nat.lt_of_not_le fun hle => ?_,
        fun hn => Nat.lt_of_not_le fun hle => ?_⟩
      · by_cases hp : (s.C.getX c).prev = NIL <;> by_cases hn : (s.C.getX c).next = NIL
        · simp_all []; rfl
        · simp_all [ Nat.not_le.mpr (h2 hn)]
        · simp_all [ Nat.not_le.mpr (h1 hp)]; rfl
        · simp [ hp, hn, Nat.not_le.mpr (h1 hp), Nat.not_le.mpr (h2 hn)]
      · exact absurd (h1 hp) (Nat.not_lt.mpr hle)
      · exact absurd (h2 hn) (Nat.not_lt.mpr hle)

/-- Writing a tag that passed its guard preserves INV-S. -/
theorem inv_setTag {s : Core} {A : Abs} (h : INV s A) {c t : Nat} (hg : TagOK s c t) :
    INV { s with C := s.C.modify c fun C => { C with tag := t } } A := by
  have hsl : SameLinks s { s with C := s.C.modify c fun C => { C with tag := t } } := by
    constructor <;> (try intro _) <;>
      simp [cN, cP, cF, cLs, apply_ite (f := Chunk.next), apply_ite (f := Chunk.prev),
        apply_ite (f := Chunk.first), apply_ite (f := Chunk.last)]
  refine h.of_sameLinks' hsl ?_
  have hT : ∀ d, cT { s with C := s.C.modify c fun C => { C with tag := t } } d =
      if c = d ∧ c < s.C.size then t else cT s d := by
    intro d; simp [cT, apply_ite (f := Chunk.tag)]
  by_cases hc : c ∈ A.chunks
  · have hcs : c < s.C.size := ((h.cAlloc c).mp hc).2
    refine isChain_update h.cList.nodup h.cSorted hc (fun d _ hd => ?_) ?_ ?_ h.cList.nonil
    · rw [hT]; simp [Ne.symm hd]
    · intro hp
      rw [hT]; simp only [hcs, and_true, ite_true]
      rw [← h.cList.prev c hc] at hp ⊢
      exact hg.1 hp
    · intro hn
      rw [hT]; simp only [hcs, and_true, ite_true]
      rw [← h.cList.next c hc] at hn ⊢
      exact hg.2 hn
  · have : A.chunks.map (cT { s with C := s.C.modify c fun C => { C with tag := t } }) =
        A.chunks.map (cT s) := by
      refine List.map_congr_left fun d hd => ?_
      rw [hT]; simp [show c ≠ d from fun e => hc (e ▸ hd)]
    rw [this]; exact h.cSorted

theorem pres_guardedSetTag (c t : Nat) : Pres Safe (guardedSetTag c t) := by
  intro s
  unfold guardedSetTag modC
  rw [run_bind]
  rcases guardTag_run c t s with ⟨hr, hg⟩ | ⟨msg, hr⟩
  · rw [hr]
    simp only [run_modify]
    refine ⟨?_, fun A hI => inv_setTag hI hg⟩
    constructor <;> (try intro _) <;>
      simp [cN, cP, cF, cLs, apply_ite (f := Chunk.next), apply_ite (f := Chunk.prev),
        apply_ite (f := Chunk.first), apply_ite (f := Chunk.last)]
  · rw [hr]; exact IsPre.refl (R := Safe) s

/-! ### The top structure's jobs -/

theorem pres_belowOf {R : Core → Core → Prop} [IsPre R] (h y : Nat) : Pres R (belowOf h y) := by
  unfold belowOf; pres [pres_getPath _]

theorem pres_drainStep (v : Nat) : Pres Safe (drainStep v) := by
  unfold drainStep
  pres [pres_getP, pres_getN _, pres_getC _, pres_getPath _, (pres_finishDrain _).same_safe,
    pres_belowOf _ _,
    pres_guardedSetTag _ _, (pres_setPathAt _ _ _).same_safe, (pres_modN _ _).same_safe]

theorem pres_fundLoop (j : Job) (v up src k : Nat) : Pres Safe (fundLoop j v up src k) := by
  unfold fundLoop; pres [pres_getP, pres_drainStep _]

theorem pres_afterDrain (j : Job) (v up : Nat) : Pres Safe (afterDrain j v up) := by
  unfold afterDrain; pres [pres_getN _, pres_fundLoop _ _ _ _ _]

theorem pres_walkBody (j : Job) (v : Nat) : Pres Safe (walkBody j v) := by
  unfold walkBody
  pres [pres_getP, pres_getN _, (pres_modN _ _).same_safe, (pres_startDrain _).same_safe,
    pres_afterDrain _ _ _]

theorem pres_jobStep (j : Job) : Pres Safe (jobStep j) := by
  unfold jobStep
  pres [pres_getP, pres_getN _, pres_getPath _, pres_getLpar _, (pres_setPathAt _ _ _).same_safe,
    (pres_modN _ _).same_safe, pres_walkBody _ _, pres_afterDrain _ _ _,
    pres_fundLoop _ _ _ _ _]

end OrderMaintenance.Proof

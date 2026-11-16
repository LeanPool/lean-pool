/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.PQ


/-!
# What the top structure may change

`TopRel s s'`: everything below the top structure is unchanged, except chunk tags. The top
structure's own fields (`nodes`, `path`, `cin`, `lpar`), the deferred construction (`prep`) and the
running job (`resJob`) may change. Every top-structure operation is in this relation, whether it
succeeds or fails a guard.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
structure TopRel (s s' : Core) : Prop where
  E : s'.E = s.E
  Gs : s'.Gs = s.Gs
  Csize : s'.C.size = s.C.size
  C : ∀ c, s'.C.getX c = { s.C.getX c with tag := (s'.C.getX c).tag }
  pq : s'.pqHead = s.pqHead ∧ s'.pqNext = s.pqNext ∧ s'.pqPrev = s.pqPrev ∧
    s'.pqWhere = s.pqWhere ∧ s'.nbNext = s.nbNext ∧ s'.nbPrev = s.nbPrev ∧ s'.pqHi = s.pqHi ∧
    s'.pqLo = s.pqLo
  rest : s'.P = s.P ∧ s'.count = s.count ∧ s'.head = s.head ∧ s'.tail = s.tail ∧
    s'.firstGroup = s.firstGroup ∧ s'.firstChunk = s.firstChunk ∧ s'.freeG = s.freeG ∧
    s'.fallbacks = s.fallbacks ∧ s'.ready = s.ready

theorem TopRel.refl (s : Core) : TopRel s s :=
  ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem TopRel.trans {a b c : Core} (h1 : TopRel a b) (h2 : TopRel b c) : TopRel a c := by
  obtain ⟨e1, g1, s1, c1, ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩, ⟨r1, r2, r3, r4, r5, r6, r7, r8,
    r9⟩⟩ := h1
  obtain ⟨e2, g2, s2, c2, ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, ⟨t1, t2, t3, t4, t5, t6, t7, t8,
    t9⟩⟩ := h2
  refine ⟨e2.trans e1, g2.trans g1, s2.trans s1, fun x => ?_,
    ⟨q1.trans p1, q2.trans p2, q3.trans p3, q4.trans p4, q5.trans p5, q6.trans p6, q7.trans p7,
      q8.trans p8⟩,
    ⟨t1.trans r1, t2.trans r2, t3.trans r3, t4.trans r4, t5.trans r5, t6.trans r6, t7.trans r7,
      t8.trans r8, t9.trans r9⟩⟩
  rw [c2 x, c1 x]

instance : IsPre TopRel := ⟨TopRel.refl, fun _ _ _ => TopRel.trans⟩

/-- Updates that leave everything but the top structure's fields alone. -/
theorem TopRel.of_top (s : Core) (nodes : Array Node) (path : Array (Array Nat))
    (cin : Array (List Nat)) (lpar : Array Nat) :
    TopRel s { s with nodes := nodes, path := path, cin := cin, lpar := lpar } :=
  ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem TopRel.of_tag (s : Core) (c t : Nat) :
    TopRel s { s with C := s.C.modify c fun C => { C with tag := t } } := by
  refine ⟨rfl, rfl, by simp, fun d => ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [Array.getX_modify]; split <;> rfl

/-- Close `∀ s, TopRel s (f s)` for a top-only update. -/
syntax "topsame" : tactic
macro_rules
  | `(tactic| topsame) => `(tactic| (intro s; first
      | exact TopRel.of_top s _ _ _ _
      | exact TopRel.of_tag s _ _
      | exact TopRel.refl s))

theorem top_modN (i : Nat) (f : Node → Node) : Pres TopRel (modN i f) := by
  unfold modN; pres; intro s; exact TopRel.of_top s _ s.path s.cin s.lpar
theorem top_setPath (c : Nat) (p : Array Nat) : Pres TopRel (setPath c p) := by
  unfold setPath; pres; intro s; exact TopRel.of_top s s.nodes _ s.cin s.lpar
theorem top_setPathAt (c j v : Nat) : Pres TopRel (setPathAt c j v) := by
  unfold setPathAt; pres; intro s; exact TopRel.of_top s s.nodes _ s.cin s.lpar
theorem top_setLpar (c v : Nat) : Pres TopRel (setLpar c v) := by
  unfold setLpar; pres; intro s; exact TopRel.of_top s s.nodes s.path s.cin _
theorem top_inTablesOf (e h : Nat) : Pres TopRel (inTablesOf e h) := by
  unfold inTablesOf; pres [pres_getN _]
theorem top_setInTables (e h : Nat) (l : List Nat) : Pres TopRel (setInTables e h l) := by
  unfold setInTables; pres [top_modN _ _]; intro s; exact TopRel.of_top s s.nodes s.path _ s.lpar
theorem top_newNode (h : Nat) : Pres TopRel (newNode h) := by
  unfold newNode; pres; intro s; exact TopRel.of_top s _ s.path s.cin s.lpar
theorem top_guardTag (c t : Nat) : Pres TopRel (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem top_guardedSetTag (c t : Nat) : Pres TopRel (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [top_guardTag _ _]; intro s; exact TopRel.of_tag s c t
theorem top_roomNextTo (t e : Nat) (b : Bool) : Pres TopRel (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem top_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) :
    Pres TopRel (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, top_modN _ _]
theorem top_sameDrain (a b : Nat) : Pres TopRel (sameDrain a b) := by
  unfold sameDrain; pres
theorem top_addTable (h t e : Nat) : Pres TopRel (addTable h t e) := by
  unfold addTable; pres [top_inTablesOf _ _, top_setInTables _ _ _]
theorem top_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) :
    Pres TopRel (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [top_tableInsert _ _ _ _ _]
theorem top_setParent (h w e : Nat) : Pres TopRel (setParent h w e) := by
  unfold setParent; pres [top_setLpar _ _, top_modN _ _]
theorem top_startDrain (v : Nat) : Pres TopRel (startDrain v) := by
  unfold startDrain
  pres [pres_getP, pres_getN _, top_roomNextTo _ _ _, top_newNode _, top_insertAroundIn _ _ _ _,
    top_modN _ _, top_addTable _ _ _, top_setParent _ _ _]
theorem top_dropTable (h v e : Nat) : Pres TopRel (dropTable h v e) := by
  unfold dropTable; pres [top_inTablesOf _ _, top_setInTables _ _ _]
theorem top_dropEntry (v T : Nat) : Pres TopRel (dropEntry v T) := by
  unfold dropEntry; pres [pres_getN _, top_modN _ _]
theorem top_release (v t : Nat) : Pres TopRel (release v t) := by
  unfold release; pres [pres_getN _, top_modN _ _]
theorem top_finishDrain (v : Nat) : Pres TopRel (finishDrain v) := by
  unfold finishDrain
  pres [pres_getN _, top_dropTable _ _ _, top_dropEntry _ _, top_release _ _, top_modN _ _]
theorem top_drainStep (v : Nat) : Pres TopRel (drainStep v) := by
  unfold drainStep
  pres [pres_getP, pres_getN _, top_finishDrain _, pres_getPath _, pres_getC _,
    top_guardedSetTag _ _, top_setPathAt _ _ _, top_modN _ _, pres_belowOf _ _]
theorem top_fundLoop (j : Job) (v up src k : Nat) : Pres TopRel (fundLoop j v up src k) := by
  unfold fundLoop; pres [pres_getP, top_drainStep _]
theorem top_afterDrain (j : Job) (v up : Nat) : Pres TopRel (afterDrain j v up) := by
  unfold afterDrain; pres [pres_getN _, top_fundLoop _ _ _ _ _]
theorem top_walkBody (j : Job) (v : Nat) : Pres TopRel (walkBody j v) := by
  unfold walkBody; pres [pres_getP, pres_getN _, top_modN _ _, top_startDrain _, top_afterDrain
    _ _ _]
theorem top_jobStep (j : Job) : Pres TopRel (jobStep j) := by
  unfold jobStep
  pres [pres_getP, pres_getPath _, top_setPathAt _ _ _, pres_getN _, top_modN _ _,
    pres_getLpar _, top_walkBody _ _, top_afterDrain _ _ _, top_fundLoop _ _ _ _ _]
theorem top_insertAroundPrep (x : Nat) : Pres TopRel (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, top_roomNextTo _ _ _, pres_getN _, pres_getC _, pres_getLpar _]
theorem top_insertAroundFinish (x y z : Nat) (tabs ly lz : List Nat) (lp : Nat) :
    Pres TopRel (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish joinChunk
  pres [pres_getP, top_insertAroundIn _ _ _ _, top_setPath _ _, top_setInTables _ _ _,
    top_setLpar _ _, top_modN _ _]
theorem top_insertAround (x y z : Nat) : Pres TopRel (insertAround x y z) := by
  unfold insertAround
  pres [top_insertAroundPrep _, top_guardedSetTag _ _, top_insertAroundFinish _ _ _ _ _ _ _]

end OrderMaintenance.Proof

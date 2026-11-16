/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.InsStart


/-!
# M5: running `startDrain`

The data `startDrain v` computes from the state (children, weights, the cut, the sides, the two
parts), and its run as a sequence of pure state updates.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### The data -/

section data
variable (t : Core) (v : Nat)

abbrev sH : Nat := (t.nodes.getX v).height
abbrev sKids : List Nat := (t.nodes.getX v).children
abbrev sWt : Nat → Nat := drainWt t.nodes (sH t v)
abbrev sWs : List Nat := (sKids t v).map (sWt t v)
abbrev sPr : Nat → Bool := drainPr t.nodes (sKids t v)
abbrev sK : Nat := drainCut (sWs t v) (sPr t v) (decide (sH t v > 1))
abbrev sB : Nat := (sKids t v).getD (sK t v) 0
abbrev sEntries : List Nat := drainEntries t.nodes (t.nodes.getX v)
abbrev sSideO : Option (List (Nat × Side)) := drainSide t.nodes (t.nodes.getX v) (sB t v)

variable (side : List (Nat × Side))
abbrev sLeft : List Nat := (sEntries t v).filter (lookup side · == some .left)
abbrev sRight : List Nat := (sEntries t v).filter (lookup side · == some .right)
abbrev sCh1 : List Nat := (sKids t v).filter (lookup side · == some .left)
abbrev sCh2 : List Nat := (sKids t v).filter (lookup side · == some .right)

end data

/-! ### The updates -/

/-- `addTable h w e`, as a state update. -/
def addTableS (h w e : Nat) (s : Core) : Core :=
  if h = 0 then { s with cin := s.cin.setX e (s.cin.getX e ++ [w]) }
  else { s with nodes := s.nodes.modify e fun n => { n with inTables := (s.nodes.getX e).inTables ++ [w] } }

/-- `setParent h w e`, as a state update. -/
def setParentS (h w e : Nat) (s : Core) : Core :=
  if h = 1 then { s with lpar := s.lpar.setX e w } else { s with nodes := s.nodes.modify e fun n => { n with livePar := w } }

theorem addTable_run (h w e : Nat) (s : Core) : (addTable h w e).run s = .ok ⟨⟩ (addTableS h w e s) := by
  unfold addTable addTableS inTablesOf setInTables
  by_cases h0 : h = 0
  · subst h0; simp
  · simp [h0]

theorem setParent_run (h w e : Nat) (s : Core) : (setParent h w e).run s = .ok ⟨⟩ (setParentS h w e s) := by
  unfold setParent setParentS setLpar
  by_cases h1 : h = 1
  · subst h1; simp
  · simp [h1]

section stages
variable (t : Core) (v : Nat) (side : List (Nat × Side))

/-- The labels of `v1`, `v2` in table `T`. -/
def sF (T : Nat) : Nat × Nat :=
  (roomL t.P.beta (t.nodes.getX T).table v true, roomL t.P.beta (t.nodes.getX T).table v false)

/-- The two new nodes. -/
def sd1 : Core := { t with nodes := (t.nodes.push { height := sH t v }).push { height := sH t v } }

/-- `v1`, `v2` around `v` in every table holding `v`. -/
def sd2 : Core := { sd1 t v with nodes := (t.nodes.getX v).inTables.foldl (fun ns T => ns.modify T (aroundF (sd1 t v) v t.nodes.size (t.nodes.size + 1) (sF t v) T)) (sd1 t v).nodes }

/-- The tables of `v1`, `v2`. -/
def sd4 : Core :=
  let s3 := { sd2 t v with nodes := (sd2 t v).nodes.modify t.nodes.size fun n => { n with inTables := (t.nodes.getX v).inTables, table := evenTable t.P.beta (sLeft t v side) } }
  { s3 with nodes := s3.nodes.modify (t.nodes.size + 1) fun n => { n with inTables := (t.nodes.getX v).inTables, table := evenTable t.P.beta (sRight t v side) } }

/-- The entries learn their new tables. -/
def sd6 : Core :=
  let s5 := (sLeft t v side).foldl (fun s e => addTableS (sH t v - 1) t.nodes.size e s) (sd4 t v side)
  (sRight t v side).foldl (fun s e => addTableS (sH t v - 1) (t.nodes.size + 1) e s) s5

/-- The children of `v1`. -/
def sd8 : Core :=
  let s7 := (sCh1 t v side).foldl (fun s e => setParentS (sH t v) t.nodes.size e s) (sd6 t v side)
  { s7 with nodes := s7.nodes.modify t.nodes.size fun n => { n with children := sCh1 t v side, weight := ((sCh1 t v side).map (sWt t v)).sum, livePar := (t.nodes.getX v).livePar, overflowOf := v } }

/-- The children of `v2`. -/
def sd10 : Core :=
  let s9 := (sCh2 t v side).foldl (fun s e => setParentS (sH t v) (t.nodes.size + 1) e s) (sd8 t v side)
  { s9 with nodes := s9.nodes.modify (t.nodes.size + 1) fun n => { n with children := sCh2 t v side, weight := ((sCh2 t v side).map (sWt t v)).sum, livePar := (t.nodes.getX v).livePar, overflowOf := v } }

/-- **The state after `startDrain v`.** -/
def sdS : Core :=
  let s11 := { sd10 t v side with nodes := (sd10 t v side).nodes.modify (t.nodes.getX v).livePar fun n => { n with children := n.children.replace1 v [t.nodes.size, t.nodes.size + 1] } }
  { s11 with nodes := s11.nodes.modify v fun n => { n with draining := true, t1 := t.nodes.size, t2 := t.nodes.size + 1, side := side, livePar := NIL, children := [] } }

end stages

/-! ### What the stages keep -/

theorem setParentS_children (h w e : Nat) (s : Core) (u : Nat) :
    ((setParentS h w e s).nodes.getX u).children = (s.nodes.getX u).children := by
  unfold setParentS; split
  · rfl
  · simp only [Array.getX_modify]; split <;> rfl

theorem addTableS_children (h w e : Nat) (s : Core) (u : Nat) :
    ((addTableS h w e s).nodes.getX u).children = (s.nodes.getX u).children := by
  unfold addTableS; split
  · rfl
  · simp only [Array.getX_modify]; split <;> rfl

theorem fold_setParentS_children (h w : Nat) (u : Nat) : ∀ (l : List Nat) (s : Core),
    ((l.foldl (fun s e => setParentS h w e s) s).nodes.getX u).children = (s.nodes.getX u).children
  | [], _ => rfl
  | e :: l, s => by
    simp only [List.foldl_cons]; rw [fold_setParentS_children h w u l, setParentS_children]

theorem fold_addTableS_children (h w : Nat) (u : Nat) : ∀ (l : List Nat) (s : Core),
    ((l.foldl (fun s e => addTableS h w e s) s).nodes.getX u).children = (s.nodes.getX u).children
  | [], _ => rfl
  | e :: l, s => by
    simp only [List.foldl_cons]; rw [fold_addTableS_children h w u l, addTableS_children]

theorem fold_aroundF_children (s0 : Core) (e n1 n2 : Nat) (f : Nat → Nat × Nat) (u : Nat) :
    ∀ (l : List Nat) (ns : Array Node),
      ((l.foldl (fun ns T => ns.modify T (aroundF s0 e n1 n2 f T)) ns).getX u).children = (ns.getX u).children
  | [], _ => rfl
  | T :: l, ns => by
    simp only [List.foldl_cons]; rw [fold_aroundF_children s0 e n1 n2 f u l]
    simp only [Array.getX_modify]; split <;> rfl

/-! ### The run -/

theorem zip_map_map {α β γ : Type} (l : List α) (f : α → β) (g : α → γ) :
    l.zip ((l.map f).zip (l.map g)) = l.map fun x => (x, f x, g x) := by
  induction l with
  | nil => rfl
  | cons x r ih => simp [ih]

theorem RoomOK.lt {s : Core} {e T : Nat} (h : RoomOK s e T) : T < s.nodes.size := by
  obtain ⟨A, le, Bs, htab, -⟩ := h
  by_contra hT
  have : s.nodes.getX T = default := by unfold Array.getX Array.getD; rw [dite_eq_right hT]
  have hd : (default : Node).table = [] := rfl
  rw [this, hd] at htab; exact absurd htab.symm (by simp)

theorem startDrain_run {t : Core} {v : Nat} {side : List (Nat × Side)}
    (hk2 : 2 ≤ (sKids t v).length) (hk0 : ¬(sH t v > 1 ∧ sK t v = 0))
    (hside : sSideO t v = some side)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T)
    (hnd : (t.nodes.getX v).inTables.Nodup)
    (hall : ∀ e ∈ sKids t v, (lookup side e).isSome)
    (hpar : v ∈ (t.nodes.getX (t.nodes.getX v).livePar).children) (hv : v < t.nodes.size) :
    (startDrain v).run t = .ok ⟨⟩ (sdS t v side) := by
  unfold startDrain
  simp only [run_getP_bind, run_getN_bind]
  rw [ite_eq_right (by have : (t.nodes.getX v).children.length ≥ 2 := hk2; omega)]
  simp only [run_get_bind]
  rw [ite_eq_right (by simpa using hk0)]
  have hside' : drainSide t.nodes (t.nodes.getX v) ((t.nodes.getX v).children.getD
      (drainCut (List.map (drainWt t.nodes (t.nodes.getX v).height) (t.nodes.getX v).children)
        (drainPr t.nodes (t.nodes.getX v).children) (decide ((t.nodes.getX v).height > 1))) 0) =
      some side := hside
  rw [hside']
  simp only
  rw [run_bind, mapM_run _ _ (fun T => roomL t.P.beta (t.nodes.getX T).table v true) t
    (fun T hT => roomNextTo_run' (hroom T hT) true)]
  simp only
  rw [run_bind, mapM_run _ _ (fun T => roomL t.P.beta (t.nodes.getX T).table v false) t
    (fun T hT => roomNextTo_run' (hroom T hT) false)]
  simp only
  -- the new nodes
  rw [run_bind, show (newNode (t.nodes.getX v).height).run t = .ok t.nodes.size
    { t with nodes := t.nodes.push { height := (t.nodes.getX v).height } } from rfl]
  simp only
  rw [run_bind, show (newNode (t.nodes.getX v).height).run
      { t with nodes := t.nodes.push { height := (t.nodes.getX v).height } } =
      .ok (t.nodes.push { height := (t.nodes.getX v).height }).size (sd1 t v) from rfl]
  simp only [Array.size_push]
  -- the insertions around `v`
  rw [zip_map_map, run_bind, forM_around_run v t.nodes.size (t.nodes.size + 1)
    (fun T => (roomL t.P.beta (t.nodes.getX T).table v true, roomL t.P.beta (t.nodes.getX T).table v false))
    (by omega) _ _ hnd]
  swap
  · intro T hT
    have hlt := (hroom T hT).lt
    obtain ⟨A, le, Bs, htab, hA, hside, -⟩ := hroom T hT
    have e : (sd1 t v).nodes.getX T = t.nodes.getX T := by
      show ((t.nodes.push _).push _).getX T = _
      rw [Array.getX_push, Array.getX_push, ite_eq_right (by simp; omega), ite_eq_right (by omega)]
    exact ⟨A, le, Bs, by rw [e]; exact htab, hA, by rw [e]; exact hside⟩
  simp only [run_modN_bind]
  -- the entries' tables
  rw [run_bind, forM_run' _ _ (fun e s => addTableS ((t.nodes.getX v).height - 1) t.nodes.size e s)
    (fun e s => addTable_run _ _ _ _)]
  simp only
  rw [run_bind,
    forM_run' _ _ (fun e s => addTableS ((t.nodes.getX v).height - 1) (t.nodes.size + 1) e s)
    (fun e s => addTable_run _ _ _ _)]
  simp only
  rw [ite_eq_right (by rw [show (t.nodes.getX v).children.all (fun e => (lookup side e).isSome) = true from
    List.all_eq_true.mpr hall]; simp)]
  -- the children
  rw [run_bind, forM_run' _ _ (fun e s => setParentS (t.nodes.getX v).height t.nodes.size e s)
    (fun e s => setParent_run _ _ _ _)]
  simp only [run_modN_bind]
  rw [run_bind, forM_run' _ _ (fun e s => setParentS (t.nodes.getX v).height (t.nodes.size + 1) e s)
    (fun e s => setParent_run _ _ _ _)]
  simp only [run_modN_bind, run_getN_bind]
  have hL : (t.nodes.getX v).livePar < t.nodes.size := by
    generalize (t.nodes.getX v).livePar = L at hpar
    by_contra hL
    have : t.nodes.getX L = default := by unfold Array.getX Array.getD; rw [dite_eq_right hL]
    rw [this] at hpar; exact absurd hpar (by show ¬ v ∈ ([] : List Nat); simp)
  rw [ite_eq_right]
  swap
  · simp only [Array.getX_modify, fold_setParentS_children, fold_addTableS_children,
    fold_aroundF_children,
      sd1, Array.getX_push, Array.size_push, Nat.ne_of_lt hL,
      show t.nodes.size ≠ (t.nodes.getX v).livePar by omega,
      show t.nodes.size + 1 ≠ (t.nodes.getX v).livePar by omega, false_and, ite_false]
    rw [ite_eq_right (show ¬((t.nodes.getX v).livePar = t.nodes.size + 1) by omega)]
    simpa using hpar
  simp only [run_modN_bind, run_modN]
  simp only [sdS, sd10, sd8, sd6, sd4, sd2, sLeft, sRight, sCh1, sCh2, sEntries, sWt, sH, sKids]
  rfl

end OrderMaintenance.Proof.Top

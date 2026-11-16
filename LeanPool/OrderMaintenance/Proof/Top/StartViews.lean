/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.RunStart


/-!
# M5: the state after `startDrain`, field by field
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Folds of the entry and child updates -/

theorem fold_addTableS_node {h : Nat} (hh : h ≠ 0) (w : Nat) :
    ∀ (l : List Nat), l.Nodup → ∀ (s : Core),
      (l.foldl (fun s e => addTableS h w e s) s) =
        {
          s with
          nodes := l.foldl (fun ns e => ns.modify e fun n => {
            n with
            inTables := n.inTables ++ [w]
          }) s.nodes
        }
  | [], _, s => rfl
  | e :: l, hl, s => by
    have hn := List.nodup_cons.mp hl
    simp only [List.foldl_cons]
    rw [fold_addTableS_node hh w l hn.2]
    unfold addTableS; rw [ite_eq_right hh]
    simp only
    congr 1
    congr 1
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_modify]
      split
      · next he =>
        subst he
        have h1' : e < s.nodes.size := by simpa using h1
        simp [Array.getX, Array.getD, h1']
      · rfl

theorem fold_addTableS_cin (w : Nat) :
    ∀ (l : List Nat) (s : Core),
      (l.foldl (fun s e => addTableS 0 w e s) s) =
        {
          s with
          cin := l.foldl (fun cs e => cs.setX e (cs.getX e ++ [w])) s.cin
        }
  | [], s => rfl
  | e :: l, s => by
    simp only [List.foldl_cons]
    rw [fold_addTableS_cin w l]
    unfold addTableS; rw [ite_eq_left rfl]

theorem fold_setX_append_getX (w : Nat) :
    ∀ (l : List Nat), l.Nodup → ∀ (cs : Array (List Nat)) (c : Nat),
      (l.foldl (fun cs e => cs.setX e (cs.getX e ++ [w])) cs).getX c =
        if c ∈ l then cs.getX c ++ [w] else cs.getX c
  | [], _, cs, c => by simp
  | e :: l, hl, cs, c => by
    have hn := List.nodup_cons.mp hl
    simp only [List.foldl_cons]
    rw [fold_setX_append_getX w l hn.2, Array.getX_setX]
    by_cases hc : c = e
    · subst hc; simp [hn.1]
    · simp [hc]

theorem fold_setParentS_node {h : Nat} (hh : h ≠ 1) (w : Nat) :
    ∀ (l : List Nat) (s : Core),
      (l.foldl (fun s e => setParentS h w e s) s) =
        {
          s with
          nodes := l.foldl (fun ns e => ns.modify e fun n => {
            n with
            livePar := w
          }) s.nodes
        }
  | [], s => rfl
  | e :: l, s => by
    simp only [List.foldl_cons]
    rw [fold_setParentS_node hh w l]
    unfold setParentS; rw [ite_eq_right hh]

theorem fold_setParentS_lpar (w : Nat) :
    ∀ (l : List Nat) (s : Core),
      (l.foldl (fun s e => setParentS 1 w e s) s) = {
        s with
        lpar := l.foldl (fun ls e => ls.setX e w) s.lpar
      }
  | [], s => rfl
  | e :: l, s => by
    simp only [List.foldl_cons]
    rw [fold_setParentS_lpar w l]
    unfold setParentS; rw [ite_eq_left rfl]

theorem fold_setX_getX (w : Nat) :
    ∀ (l : List Nat) (ls : Array Nat) (c : Nat),
      (l.foldl (fun ls e => ls.setX e w) ls).getX c = if c ∈ l then w else ls.getX c
  | [], ls, c => by simp
  | e :: l, ls, c => by
    simp only [List.foldl_cons]
    rw [fold_setX_getX w l, Array.getX_setX]
    by_cases hc : c = e
    · subst hc; simp
    · simp [hc]

/-! ### The nodes after the drain starts -/

section node
variable (t : Core) (v : Nat) (side : List (Nat × Side))

/-- Node `u` after `startDrain v` (`v1 = N`, `v2 = N + 1`, `N` the old node count). -/
def sdNode (u : Nat) : Node :=
  let N := t.nodes.size
  let V := t.nodes.getX v
  if u = N then {
    height := sH t v
    livePar := V.livePar
    children := sCh1 t v side
    weight := ((sCh1 t v side).map (sWt t v)).sum
    table := evenTable t.P.beta (sLeft t v side)
    inTables := V.inTables
    overflowOf := v
  }
  else if u = N + 1 then {
    height := sH t v
    livePar := V.livePar
    children := sCh2 t v side
    weight := ((sCh2 t v side).map (sWt t v)).sum
    table := evenTable t.P.beta (sRight t v side)
    inTables := V.inTables
    overflowOf := v
  }
  else if u < N then
    let n1 := if u ∈ V.inTables then aroundF t v N (N + 1) (sF t v) u (t.nodes.getX u) else
      t.nodes.getX u
    let n2 := if sH t v - 1 ≠ 0 ∧ u ∈ sLeft t v side then {
      n1 with
      inTables := n1.inTables ++ [N]
    } else n1
    let n3 := if sH t v - 1 ≠ 0 ∧ u ∈ sRight t v side then {
      n2 with
      inTables := n2.inTables ++ [N + 1]
    } else n2
    let n4 := if sH t v ≠ 1 ∧ u ∈ sCh1 t v side then {
      n3 with
      livePar := N
    } else n3
    let n5 := if sH t v ≠ 1 ∧ u ∈ sCh2 t v side then {
      n4 with
      livePar := N + 1
    } else n4
    let n6 := if u = V.livePar then {
      n5 with
      children := n5.children.replace1 v [N, N + 1]
    } else n5
    if u = v then {
      n6 with
      draining := true
      t1 := N
      t2 := N + 1
      side := side
      livePar := NIL
      children := []
    } else n6
  else default

variable {t v side}

theorem sd1_getX (u : Nat) : (sd1 t v).nodes.getX u =
    if u = t.nodes.size + 1 then {
      height := sH t v
    } else if u = t.nodes.size then {
      height := sH t v
    }
    else t.nodes.getX u := by
  change ((t.nodes.push _).push _).getX u = _
  rw [Array.getX_push, Array.getX_push, Array.size_push]

theorem sd1_size : (sd1 t v).nodes.size = t.nodes.size + 2 := by
  change ((t.nodes.push _).push _).size = _; simp

theorem sd2_getX (hnd : (t.nodes.getX v).inTables.Nodup)
    (htabs : ∀ T ∈ (t.nodes.getX v).inTables, T < t.nodes.size) (u : Nat) :
    (sd2 t v).nodes.getX u = if u ∈ (t.nodes.getX v).inTables then
      aroundF t v t.nodes.size (t.nodes.size + 1) (sF t v) u (t.nodes.getX u) else (sd1 t
        v).nodes.getX u := by
  change ((t.nodes.getX v).inTables.foldl (fun ns T => ns.modify T (aroundF (sd1 t v) v t.nodes.size
    (t.nodes.size + 1) (sF t v) T)) (sd1 t v).nodes).getX u = _
  rw [foldl_modify_getX' _ _ hnd, sd1_size]
  by_cases hu : u ∈ (t.nodes.getX v).inTables
  · have hlt := htabs u hu
    rw [ite_eq_left ⟨hu, by omega⟩, ite_eq_left hu]
    unfold aroundF
    rw [sd1_getX, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right (fun h => hu h.1), ite_eq_right hu]

theorem sd2_size : (sd2 t v).nodes.size = t.nodes.size + 2 := by
  change ((t.nodes.getX v).inTables.foldl _ (sd1 t v).nodes).size = _
  have := foldl_modify_size (t.nodes.getX v).inTables (fun x => x)
    (fun T => aroundF (sd1 t v) v t.nodes.size (t.nodes.size + 1) (sF t v) T) (sd1 t v).nodes
  rw [this, sd1_size]

theorem fold_modify_getX_nd {f : Node → Node} :
    ∀ (l : List Nat), l.Nodup → ∀ (a : Array Node) (u : Nat),
      (l.foldl (fun ns e => ns.modify e f) a).getX u = if u ∈ l ∧ u < a.size then f (a.getX u)
        else a.getX u :=
  foldl_modify_getX' (fun _ => f)

theorem fold_modify_size_nd (f : Node → Node) (l : List Nat) (a : Array Node) :
    (l.foldl (fun ns e => ns.modify e f) a).size = a.size :=
  foldl_modify_size l (fun x => x) (fun _ => f) a

/-- The node array after the entry updates. -/
theorem sd6_nodes (hln : (sLeft t v side).Nodup) (hrn : (sRight t v side).Nodup) :
    (sd6 t v side).nodes = if sH t v - 1 = 0 then (sd4 t v side).nodes else
      (sRight t v side).foldl (fun ns e => ns.modify e fun n => {
        n with
        inTables := n.inTables ++ [t.nodes.size + 1]
      })
        ((sLeft t v side).foldl (fun ns e => ns.modify e fun n => {
          n with
          inTables := n.inTables ++ [t.nodes.size]
        })
          (sd4 t v side).nodes) := by
  unfold sd6; simp only []
  by_cases hA : sH t v - 1 = 0
  · rw [ite_eq_left hA]; simp only [hA]; rw [fold_addTableS_cin, fold_addTableS_cin]
  · rw [ite_eq_right hA, fold_addTableS_node hA _ _ hln, fold_addTableS_node hA _ _ hrn]

section keep
variable (h w : Nat) (l : List Nat) (s : Core)

theorem fold_addTableS_lpar : (l.foldl (fun s e => addTableS h w e s) s).lpar = s.lpar := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold addTableS; split <;> rfl
theorem fold_addTableS_path : (l.foldl (fun s e => addTableS h w e s) s).path = s.path := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold addTableS; split <;> rfl
theorem fold_addTableS_P : (l.foldl (fun s e => addTableS h w e s) s).P = s.P := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold addTableS; split <;> rfl
theorem fold_addTableS_C : (l.foldl (fun s e => addTableS h w e s) s).C = s.C := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold addTableS; split <;> rfl
theorem fold_addTableS_cin' (hh : h ≠ 0) : (l.foldl (fun s e => addTableS h w e s) s).cin =
  s.cin := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold addTableS; rw [ite_eq_right hh]
theorem fold_setParentS_cin : (l.foldl (fun s e => setParentS h w e s) s).cin = s.cin := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold setParentS; split <;> rfl
theorem fold_setParentS_path : (l.foldl (fun s e => setParentS h w e s) s).path = s.path := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold setParentS; split <;> rfl
theorem fold_setParentS_P : (l.foldl (fun s e => setParentS h w e s) s).P = s.P := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold setParentS; split <;> rfl
theorem fold_setParentS_C : (l.foldl (fun s e => setParentS h w e s) s).C = s.C := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold setParentS; split <;> rfl
theorem fold_setParentS_lpar' (hh : h ≠ 1) : (l.foldl (fun s e => setParentS h w e s) s).lpar =
  s.lpar := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; unfold setParentS; rw [ite_eq_right hh]

end keep

/-- The other fields after `startDrain`. -/
theorem sdS_rest : (sdS t v side).path = t.path ∧ (sdS t v side).P = t.P ∧ (sdS t v side).C =
  t.C := by
  unfold sdS sd10 sd8 sd6 sd4 sd2 sd1
  simp only [fold_setParentS_path, fold_setParentS_P, fold_setParentS_C, fold_addTableS_path,
    fold_addTableS_P, fold_addTableS_C, and_self]

theorem sdS_cin (hln : (sLeft t v side).Nodup) (hrn : (sRight t v side).Nodup) (c : Nat) :
    (sdS t v side).cin.getX c =
    if sH t v - 1 = 0 then
      (if c ∈ sRight t v side then (if c ∈ sLeft t v side then t.cin.getX c ++ [t.nodes.size]
        else t.cin.getX c) ++
        [t.nodes.size + 1] else (if c ∈ sLeft t v side then t.cin.getX c ++ [t.nodes.size] else
          t.cin.getX c))
    else t.cin.getX c := by
  unfold sdS sd10 sd8 sd6 sd4 sd2 sd1
  simp only [fold_setParentS_cin]
  by_cases hA : sH t v - 1 = 0
  · rw [ite_eq_left hA]; simp only [hA]
    rw [fold_addTableS_cin, fold_addTableS_cin]
    simp only []
    rw [fold_setX_append_getX _ _ hrn, fold_setX_append_getX _ _ hln]
  · rw [ite_eq_right hA, fold_addTableS_cin' _ _ _ _ hA, fold_addTableS_cin' _ _ _ _ hA]

theorem sdS_lpar (c : Nat) : (sdS t v side).lpar.getX c =
    if sH t v = 1 then
      (if c ∈ sCh2 t v side then t.nodes.size + 1 else if c ∈ sCh1 t v side then t.nodes.size
        else t.lpar.getX c)
    else t.lpar.getX c := by
  unfold sdS sd10 sd8 sd6 sd4 sd2 sd1
  simp only []
  by_cases hB : sH t v = 1
  · rw [ite_eq_left hB]; simp only [hB]
    rw [fold_setParentS_lpar, fold_setParentS_lpar]
    simp only []
    rw [fold_setX_getX, fold_setX_getX]
    simp only [fold_addTableS_lpar]
  · rw [ite_eq_right hB, fold_setParentS_lpar' _ _ _ _ hB, fold_setParentS_lpar' _ _ _ _ hB]
    simp only [fold_addTableS_lpar]

/-- The node array after `startDrain`, with its folds as plain modifications. -/
theorem sdS_nodes (hln : (sLeft t v side).Nodup) (hrn : (sRight t v side).Nodup) :
    (sdS t v side).nodes =
      let N := t.nodes.size
      let V := t.nodes.getX v
      let a4 := (((sd2 t v).nodes.modify N fun n => {
        n with
        inTables := V.inTables
        table := evenTable t.P.beta (sLeft t v side)
      }).modify (N + 1) fun n => {
        n with
        inTables := V.inTables
        table := evenTable t.P.beta (sRight t v side)
      })
      let a6 := if sH t v - 1 = 0 then a4 else (sRight t v side).foldl (fun ns e => ns.modify e
        fun n => {
          n with
          inTables := n.inTables ++ [N + 1]
        }) ((sLeft t v side).foldl (fun ns e => ns.modify e fun n => {
        n with
        inTables := n.inTables ++ [N]
      }) a4)
      let a7 := if sH t v = 1 then a6 else (sCh1 t v side).foldl (fun ns e => ns.modify e fun n => {
        n with
        livePar := N
      }) a6
      let a8 := a7.modify N fun n => {
        n with
        children := sCh1 t v side
        weight := ((sCh1 t v side).map (sWt t v)).sum
        livePar := V.livePar
        overflowOf := v
      }
      let a9 := if sH t v = 1 then a8 else (sCh2 t v side).foldl (fun ns e => ns.modify e fun n => {
        n with
        livePar := N + 1
      }) a8
      let a10 := a9.modify (N + 1) fun n => {
        n with
        children := sCh2 t v side
        weight := ((sCh2 t v side).map (sWt t v)).sum
        livePar := V.livePar
        overflowOf := v
      }
      let a11 := a10.modify V.livePar fun n => {
        n with
        children := n.children.replace1 v [N, N + 1]
      }
      a11.modify v fun n => {
        n with
        draining := true
        t1 := N
        t2 := N + 1
        side := side
        livePar := NIL
        children := []
      } := by
  unfold sdS sd10 sd8 sd6 sd4
  simp only []
  by_cases hA : sH t v - 1 = 0 <;> by_cases hB : sH t v = 1
  · rw [ite_eq_left hA, ite_eq_left hB, ite_eq_left hB]
    simp only [hA]
    rw [fold_addTableS_cin, fold_addTableS_cin]
    simp only [hB]
    rw [fold_setParentS_lpar, fold_setParentS_lpar]
  · rw [ite_eq_left hA, ite_eq_right hB, ite_eq_right hB]
    simp only [hA]
    rw [fold_addTableS_cin, fold_addTableS_cin, fold_setParentS_node hB, fold_setParentS_node hB]
  · rw [ite_eq_right hA, ite_eq_left hB, ite_eq_left hB]
    rw [fold_addTableS_node hA _ _ hln, fold_addTableS_node hA _ _ hrn]
    simp only [hB]
    rw [fold_setParentS_lpar, fold_setParentS_lpar]
  · rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right hB]
    rw [fold_addTableS_node hA _ _ hln, fold_addTableS_node hA _ _ hrn, fold_setParentS_node hB,
      fold_setParentS_node hB]

/-- A field that an update keeps. -/
theorem proj_modify {α : Type} (f : Node → α) {g : Node → Node} (hg : ∀ n, f (g n) = f n) (a :
  Array Node)
    (i u : Nat) : f ((a.modify i g).getX u) = f (a.getX u) := by
  rw [Array.getX_modify]; split
  · exact hg _
  · rfl

theorem proj_fold {α : Type} (f : Node → α) {g : Node → Node} (hg : ∀ n, f (g n) = f n) (u : Nat) :
    ∀ (l : List Nat) (a : Array Node), f ((l.foldl (fun ns e => ns.modify e g) a).getX u) = f
      (a.getX u)
  | [], _ => rfl
  | e :: l, a => by simp only [List.foldl_cons]; rw [proj_fold f hg u l, proj_modify f hg]

theorem proj_ite_fold {α : Type} (f : Node → α) {g : Node → Node} (hg : ∀ n, f (g n) = f n) (c :
  Prop)
    [Decidable c] (l : List Nat) (a : Array Node) (u : Nat) :
    f ((if c then a else l.foldl (fun ns e => ns.modify e g) a).getX u) = f (a.getX u) := by
  split
  · rfl
  · exact proj_fold f hg u l a

theorem proj_ite_fold2 {α : Type} (f : Node → α) {g g' : Node → Node} (hg : ∀ n, f (g n) = f n)
    (hg' : ∀ n, f (g' n) = f n) (c : Prop) [Decidable c] (l l' : List Nat) (a : Array Node) (u :
      Nat) :
    f ((if c then a else l'.foldl (fun ns e => ns.modify e g') (l.foldl (fun ns e => ns.modify e
      g) a)).getX u) =
      f (a.getX u) := by
  split
  · rfl
  · rw [proj_fold f hg' u l', proj_fold f hg u l]

theorem size_ite_fold {g : Node → Node} (c : Prop) [Decidable c] (l : List Nat) (a : Array Node) :
    (if c then a else l.foldl (fun ns e => ns.modify e g) a).size = a.size := by
  split
  · rfl
  · exact fold_modify_size_nd g l a

theorem size_ite_fold2 {g g' : Node → Node} (c : Prop) [Decidable c] (l l' : List Nat) (a :
  Array Node) :
    (if c then a else l'.foldl (fun ns e => ns.modify e g') (l.foldl (fun ns e => ns.modify e g)
      a)).size =
      a.size := by
  split
  · rfl
  · rw [fold_modify_size_nd, fold_modify_size_nd]

theorem getX_modify_ne {g : Node → Node} {a : Array Node} {i u : Nat} (h : i ≠ u) :
    (a.modify i g).getX u = a.getX u := by
  rw [Array.getX_modify, ite_eq_right (fun h' => h h'.1)]

theorem getX_modify_eq {g : Node → Node} {a : Array Node} {i : Nat} (h : i < a.size) :
    (a.modify i g).getX i = g (a.getX i) := by
  rw [Array.getX_modify, ite_eq_left ⟨rfl, h⟩]

theorem getX_ge {α : Type} [Inhabited α] {a : Array α} {u : Nat} (h : a.size ≤ u) : a.getX u =
  default := by
  unfold Array.getX Array.getD; rw [dite_eq_right (by omega)]

theorem sdS_size (hln : (sLeft t v side).Nodup) (hrn : (sRight t v side).Nodup) :
    (sdS t v side).nodes.size = t.nodes.size + 2 := by
  rw [sdS_nodes hln hrn]; simp only []
  rw [Array.size_modify', Array.size_modify', Array.size_modify', size_ite_fold,
    Array.size_modify', size_ite_fold,
    size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]

theorem ite_fold_livePar (c : Prop) [Decidable c] (w : Nat) {l : List Nat} (hl : l.Nodup) (a :
  Array Node)
    {u : Nat} (hu : u < a.size) :
    ((if c then a else l.foldl (fun ns e => ns.modify e fun n => {
      n with
      livePar := w
    }) a).getX u).livePar =
      if ¬c ∧ u ∈ l then w else (a.getX u).livePar := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_right (fun h => h.1 hc)]
  · rw [ite_eq_right hc, fold_modify_getX_nd _ hl]
    by_cases hm : u ∈ l
    · rw [ite_eq_left ⟨hm, hu⟩, ite_eq_left ⟨hc, hm⟩]
    · rw [ite_eq_right (fun h => hm h.1), ite_eq_right (fun h => hm h.2)]

section fields
variable (hln : (sLeft t v side).Nodup) (hrn : (sRight t v side).Nodup) (hc1 : (sCh1 t v
  side).Nodup)
  (hc2 : (sCh2 t v side).Nodup) (hnd : (t.nodes.getX v).inTables.Nodup)
  (htabs : ∀ T ∈ (t.nodes.getX v).inTables, T < t.nodes.size)
include hln hrn hc1 hc2 hnd htabs

omit hc1 hc2 in
theorem sdS_height (u : Nat) : ((sdS t v side).nodes.getX u).height =
    if u = t.nodes.size ∨ u = t.nodes.size + 1 then sH t v else (t.nodes.getX u).height := by
  have e : ((sdS t v side).nodes.getX u).height = ((sd2 t v).nodes.getX u).height := by
    rw [sdS_nodes hln hrn]; simp only []
    simp (disch := (intro n; rfl)) only [proj_modify Node.height, proj_ite_fold Node.height,
      proj_ite_fold2 Node.height]
  rw [e, sd2_getX hnd htabs]
  by_cases hu : u ∈ (t.nodes.getX v).inTables
  · have := htabs u hu
    rw [ite_eq_left hu,
      ite_eq_right (show ¬(u = t.nodes.size ∨ u = t.nodes.size + 1) by omega)]; rfl
  · rw [ite_eq_right hu, sd1_getX]
    by_cases h1 : u = t.nodes.size + 1
    · rw [ite_eq_left h1, ite_eq_left (Or.inr h1)]
    · rw [ite_eq_right h1]
      by_cases h2 : u = t.nodes.size
      · rw [ite_eq_left h2, ite_eq_left (Or.inl h2)]
      · rw [ite_eq_right h2, ite_eq_right (fun h => h.elim h2 h1)]

omit hln hrn hc1 hc2 in
/-- The common tail: below the new nodes, fields that only `sd2` touches. -/
theorem sd2_proj {α : Type} (f : Node → α) (hf : ∀ (n : Node) tab sd, f (setTS tab sd n) = f n)
  {u : Nat}
    (h1 : u ≠ t.nodes.size) (h2 : u ≠ t.nodes.size + 1) :
    f ((sd2 t v).nodes.getX u) = f (t.nodes.getX u) := by
  rw [sd2_getX hnd htabs]
  split
  · exact hf _ _ _
  · rw [sd1_getX, ite_eq_right h2, ite_eq_right h1]

theorem sdS_weight (hv : v < t.nodes.size) (hL : (t.nodes.getX v).livePar < t.nodes.size) (u :
  Nat) :
    ((sdS t v side).nodes.getX u).weight =
      if u = t.nodes.size then ((sCh1 t v side).map (sWt t v)).sum
      else if u = t.nodes.size + 1 then ((sCh2 t v side).map (sWt t v)).sum
      else (t.nodes.getX u).weight := by
  rw [sdS_nodes hln hrn]; simp only []
  by_cases h1 : u = t.nodes.size
  · subst h1
    rw [getX_modify_ne (by omega), getX_modify_ne (by omega), getX_modify_ne (by omega)]
    simp (disch := (intro n; rfl)) only [proj_ite_fold Node.weight]
    rw [getX_modify_eq (by
      rw [size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega)]
    rfl
  · by_cases h2 : u = t.nodes.size + 1
    · subst h2
      rw [getX_modify_ne (by omega), getX_modify_ne (by omega),
        getX_modify_eq (by
          rw [size_ite_fold, Array.size_modify', size_ite_fold, size_ite_fold2,
            Array.size_modify', Array.size_modify', sd2_size]; omega)]
      simp only [ite_eq_right h1]; rfl
    · rw [ite_eq_right h1, ite_eq_right h2]
      simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify Node.weight,
        proj_ite_fold Node.weight, proj_ite_fold2 Node.weight]
      exact sd2_proj hnd htabs Node.weight (fun _ _ _ => rfl) h1 h2

omit hln hrn hc1 hc2 in
theorem sd2_field {α : Type} (f : Node → α) (hf : ∀ (n : Node) tab sd, f (setTS tab sd n) = f n)
  (u : Nat) :
    f ((sd2 t v).nodes.getX u) = if u = t.nodes.size ∨ u = t.nodes.size + 1 then f {
      height := sH t v
    }
      else f (t.nodes.getX u) := by
  rw [sd2_getX hnd htabs]
  by_cases hu : u ∈ (t.nodes.getX v).inTables
  · have := htabs u hu
    rw [ite_eq_left hu,
      ite_eq_right (show ¬(u = t.nodes.size ∨ u = t.nodes.size + 1) by omega)]; exact hf _ _ _
  · rw [ite_eq_right hu, sd1_getX]
    by_cases h1 : u = t.nodes.size + 1
    · rw [ite_eq_left h1, ite_eq_left (Or.inr h1)]
    · rw [ite_eq_right h1]
      by_cases h2 : u = t.nodes.size
      · rw [ite_eq_left h2, ite_eq_left (Or.inl h2)]
      · rw [ite_eq_right h2, ite_eq_right (fun h => h.elim h2 h1)]

theorem sdS_alive (u : Nat) : ((sdS t v side).nodes.getX u).alive =
    if u = t.nodes.size ∨ u = t.nodes.size + 1 then true else (t.nodes.getX u).alive := by
  rw [sdS_nodes hln hrn]; simp only []
  simp (disch := first | (intro n; rfl) | omega) only [ proj_modify Node.alive, proj_ite_fold
    Node.alive, proj_ite_fold2 Node.alive]
  exact sd2_field hnd htabs Node.alive (fun _ _ _ => rfl) u

theorem sdS_first (u : Nat) : ((sdS t v side).nodes.getX u).first =
    if u = t.nodes.size ∨ u = t.nodes.size + 1 then NIL else (t.nodes.getX u).first := by
  rw [sdS_nodes hln hrn]; simp only []
  simp (disch := first | (intro n; rfl) | omega) only [ proj_modify Node.first, proj_ite_fold
    Node.first, proj_ite_fold2 Node.first]
  exact sd2_field hnd htabs Node.first (fun _ _ _ => rfl) u

theorem sdS_last (u : Nat) : ((sdS t v side).nodes.getX u).last =
    if u = t.nodes.size ∨ u = t.nodes.size + 1 then NIL else (t.nodes.getX u).last := by
  rw [sdS_nodes hln hrn]; simp only []
  simp (disch := first | (intro n; rfl) | omega) only [ proj_modify Node.last, proj_ite_fold
    Node.last, proj_ite_fold2 Node.last]
  exact sd2_field hnd htabs Node.last (fun _ _ _ => rfl) u

theorem sdS_overflowOf (hv : v < t.nodes.size) (hL : (t.nodes.getX v).livePar < t.nodes.size) (u
  : Nat) :
    ((sdS t v side).nodes.getX u).overflowOf =
      if u = t.nodes.size then v else if u = t.nodes.size + 1 then v else (t.nodes.getX
        u).overflowOf := by
  rw [sdS_nodes hln hrn]; simp only []
  by_cases h1 : u = t.nodes.size
  · subst h1
    rw [getX_modify_ne (by omega), getX_modify_ne (by omega), getX_modify_ne (by omega)]
    simp (disch := (intro n; rfl)) only [proj_ite_fold Node.overflowOf]
    rw [getX_modify_eq (by
      rw [size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega)]
    rfl
  · by_cases h2 : u = t.nodes.size + 1
    · subst h2
      rw [getX_modify_ne (by omega), getX_modify_ne (by omega),
        getX_modify_eq (by
          rw [size_ite_fold, Array.size_modify', size_ite_fold, size_ite_fold2,
            Array.size_modify', Array.size_modify', sd2_size]; omega)]
      simp only [ite_eq_right h1]; rfl
    · rw [ite_eq_right h1, ite_eq_right h2]
      simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify
        Node.overflowOf, proj_ite_fold Node.overflowOf, proj_ite_fold2 Node.overflowOf]
      exact sd2_proj hnd htabs Node.overflowOf (fun _ _ _ => rfl) h1 h2

theorem sdS_draining (hv : v < t.nodes.size) (u : Nat) : ((sdS t v side).nodes.getX u).draining =
    if u = v then true else if u = t.nodes.size ∨ u = t.nodes.size + 1 then false
    else (t.nodes.getX u).draining := by
  rw [sdS_nodes hln hrn]; simp only []
  by_cases hu : u = v
  · subst hu; rw [getX_modify_eq (by
    rw [Array.size_modify', Array.size_modify', size_ite_fold, Array.size_modify',
      size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega),
        ite_eq_left rfl]
  · rw [ite_eq_right hu]
    simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify
      Node.draining, proj_ite_fold Node.draining, proj_ite_fold2 Node.draining]
    exact sd2_field hnd htabs Node.draining (fun _ _ _ => rfl) u

theorem sdS_t1 (hv : v < t.nodes.size) (u : Nat) : ((sdS t v side).nodes.getX u).t1 =
    if u = v then t.nodes.size else if u = t.nodes.size ∨ u = t.nodes.size + 1 then NIL
    else (t.nodes.getX u).t1 := by
  rw [sdS_nodes hln hrn]; simp only []
  by_cases hu : u = v
  · subst hu; rw [getX_modify_eq (by
    rw [Array.size_modify', Array.size_modify', size_ite_fold, Array.size_modify',
      size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega),
        ite_eq_left rfl]
  · rw [ite_eq_right hu]
    simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify Node.t1,
      proj_ite_fold Node.t1, proj_ite_fold2 Node.t1]
    exact sd2_field hnd htabs Node.t1 (fun _ _ _ => rfl) u

theorem sdS_t2 (hv : v < t.nodes.size) (u : Nat) : ((sdS t v side).nodes.getX u).t2 =
    if u = v then t.nodes.size + 1 else if u = t.nodes.size ∨ u = t.nodes.size + 1 then NIL
    else (t.nodes.getX u).t2 := by
  rw [sdS_nodes hln hrn]; simp only []
  by_cases hu : u = v
  · subst hu; rw [getX_modify_eq (by
    rw [Array.size_modify', Array.size_modify', size_ite_fold, Array.size_modify',
      size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega),
        ite_eq_left rfl]
  · rw [ite_eq_right hu]
    simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify Node.t2,
      proj_ite_fold Node.t2, proj_ite_fold2 Node.t2]
    exact sd2_field hnd htabs Node.t2 (fun _ _ _ => rfl) u

theorem sdS_side (hv : v < t.nodes.size) (u : Nat) : ((sdS t v side).nodes.getX u).side =
    if u = v then side else if u = t.nodes.size ∨ u = t.nodes.size + 1 then []
    else if u ∈ (t.nodes.getX v).inTables then sideAround (t.nodes.getX u) v t.nodes.size
      (t.nodes.size + 1)
    else (t.nodes.getX u).side := by
  rw [sdS_nodes hln hrn]; simp only []
  by_cases hu : u = v
  · subst hu; rw [getX_modify_eq (by
    rw [Array.size_modify', Array.size_modify', size_ite_fold, Array.size_modify',
      size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega),
        ite_eq_left rfl]
  · rw [ite_eq_right hu]
    simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify Node.side,
      proj_ite_fold Node.side, proj_ite_fold2 Node.side]
    rw [sd2_getX hnd htabs]
    by_cases ht : u ∈ (t.nodes.getX v).inTables
    · have := htabs u ht
      rw [ite_eq_left ht, ite_eq_right (show ¬(u = t.nodes.size ∨ u = t.nodes.size + 1) by omega),
        ite_eq_left ht]; rfl
    · rw [ite_eq_right ht, sd1_getX]
      by_cases h1 : u = t.nodes.size + 1
      · rw [ite_eq_left h1, ite_eq_left (Or.inr h1)]
      · by_cases h2 : u = t.nodes.size
        · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (Or.inl h2)]
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (fun h => h.elim h2 h1),
          ite_eq_right ht]

omit hc1 hc2 in
theorem sdS_table (hv : v < t.nodes.size) (hL : (t.nodes.getX v).livePar < t.nodes.size) (u : Nat) :
    ((sdS t v side).nodes.getX u).table =
      if u = t.nodes.size then evenTable t.P.beta (sLeft t v side)
      else if u = t.nodes.size + 1 then evenTable t.P.beta (sRight t v side)
      else if u ∈ (t.nodes.getX v).inTables then
        aroundT (t.nodes.getX u).table v t.nodes.size (t.nodes.size + 1) (sF t v u).1 (sF t v u).2
      else (t.nodes.getX u).table := by
  rw [sdS_nodes hln hrn]; simp only []
  by_cases h1 : u = t.nodes.size
  · subst h1
    simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify Node.table,
      proj_ite_fold Node.table, proj_ite_fold2 Node.table]
    rw [getX_modify_eq (by rw [sd2_size]; omega)]
    rfl
  · by_cases h2 : u = t.nodes.size + 1
    · subst h2
      simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify
        Node.table, proj_ite_fold Node.table, proj_ite_fold2 Node.table]
      rw [getX_modify_eq (by rw [Array.size_modify', sd2_size]; omega)]
      simp only [ite_eq_right h1]; rfl
    · rw [ite_eq_right h1, ite_eq_right h2]
      simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify
        Node.table, proj_ite_fold Node.table, proj_ite_fold2 Node.table]
      rw [sd2_getX hnd htabs]
      by_cases ht : u ∈ (t.nodes.getX v).inTables
      · rw [ite_eq_left ht, ite_eq_left ht]; rfl
      · rw [ite_eq_right ht, ite_eq_right ht, sd1_getX, ite_eq_right h2, ite_eq_right h1]

omit hc1 hc2 in
theorem sdS_inTables (hent : sH t v - 1 ≠ 0 → ∀ e ∈ sEntries t v, e < t.nodes.size) (u : Nat) :
  ((sdS t v
      side).nodes.getX u).inTables =
      if u = t.nodes.size ∨ u = t.nodes.size + 1 then (t.nodes.getX v).inTables
      else (t.nodes.getX u).inTables ++ (if sH t v - 1 ≠ 0 ∧ u ∈ sLeft t v side then
        [t.nodes.size] else []) ++
        (if sH t v - 1 ≠ 0 ∧ u ∈ sRight t v side then [t.nodes.size + 1] else []) := by
  rw [sdS_nodes hln hrn]; simp only []
  simp (disch := first | (intro n; rfl) | omega) only [ proj_modify Node.inTables, proj_ite_fold
    Node.inTables]
  by_cases hA : sH t v - 1 = 0
  · rw [ite_eq_left hA]
    by_cases h1 : u = t.nodes.size
    · subst h1; rw [getX_modify_ne (by omega), getX_modify_eq (by rw [sd2_size]; omega)]; simp
    · by_cases h2 : u = t.nodes.size + 1
      · subst h2; rw [getX_modify_eq (by rw [Array.size_modify', sd2_size]; omega)]; simp
      · rw [getX_modify_ne (by omega), getX_modify_ne (by omega),
        ite_eq_right (fun h => h.elim h1 h2)]
        rw [sd2_proj hnd htabs Node.inTables (fun _ _ _ => rfl) h1 h2]
        simp [hA]
  · have hlm : ∀ e ∈ sLeft t v side, e < t.nodes.size := fun e he =>
      hent hA e (List.mem_of_mem_filter he)
    have hrm : ∀ e ∈ sRight t v side, e < t.nodes.size := fun e he => hent hA e
      (List.mem_of_mem_filter he)
    rw [ite_eq_right hA, fold_modify_getX_nd _ hrn, fold_modify_getX_nd _ hln, fold_modify_size_nd,
      Array.size_modify', Array.size_modify', sd2_size]
    by_cases h1 : u = t.nodes.size
    · subst h1
      rw [ite_eq_right (fun h => by have := hrm _ h.1; omega),
        ite_eq_right (fun h => by have := hlm _ h.1; omega),
        getX_modify_ne (by omega), getX_modify_eq (by rw [sd2_size]; omega)]; simp
    · by_cases h2 : u = t.nodes.size + 1
      · subst h2
        rw [ite_eq_right (fun h => by have := hrm _ h.1; omega),
          ite_eq_right (fun h => by have := hlm _ h.1; omega),
          getX_modify_eq (by rw [Array.size_modify', sd2_size]; omega)]; simp
      · rw [ite_eq_right (show ¬(u = t.nodes.size ∨ u = t.nodes.size + 1) from fun h => h.elim
        h1 h2)]
        have e0 := sd2_proj hnd htabs Node.inTables (fun _ _ _ => rfl) h1 h2
        by_cases hr : u ∈ sRight t v side <;> by_cases hl : u ∈ sLeft t v side
        · have := hrm u hr
          rw [ite_eq_left ⟨hr, by omega⟩, ite_eq_left ⟨hl, by omega⟩]
          simp only [getX_modify_ne (Ne.symm h1), getX_modify_ne (Ne.symm h2), e0,
            ite_eq_left (And.intro hA hl),
            ite_eq_left (And.intro hA hr), List.append_assoc]
        · have := hrm u hr
          rw [ite_eq_left ⟨hr, by omega⟩, ite_eq_right (fun h => hl h.1)]
          simp only [getX_modify_ne (Ne.symm h1), getX_modify_ne (Ne.symm h2), e0, hl, and_false,
            ite_false,
            ite_eq_left (And.intro hA hr), List.append_nil]
        · have := hlm u hl
          rw [ite_eq_right (fun h => hr h.1), ite_eq_left ⟨hl, by omega⟩]
          simp only [getX_modify_ne (Ne.symm h1), getX_modify_ne (Ne.symm h2), e0, hr, and_false,
            ite_false,
            ite_eq_left (And.intro hA hl), List.append_nil]
        · rw [ite_eq_right (fun h => hr h.1), ite_eq_right (fun h => hl h.1)]
          simp only [getX_modify_ne (Ne.symm h1), getX_modify_ne (Ne.symm h2), e0, hr, hl,
            and_false, ite_false,
            List.append_nil]

theorem sdS_children (hv : v < t.nodes.size) (hL : (t.nodes.getX v).livePar < t.nodes.size)
    (hLv : (t.nodes.getX v).livePar ≠ v) (u : Nat) : ((sdS t v side).nodes.getX u).children =
      if u = v then [] else if u = t.nodes.size then sCh1 t v side
      else if u = t.nodes.size + 1 then sCh2 t v side
      else if u = (t.nodes.getX v).livePar then
        (t.nodes.getX (t.nodes.getX v).livePar).children.replace1 v [t.nodes.size, t.nodes.size + 1]
      else (t.nodes.getX u).children := by
  rw [sdS_nodes hln hrn]; simp only []
  by_cases hu : u = v
  · subst hu; rw [getX_modify_eq (by
    rw [Array.size_modify', Array.size_modify', size_ite_fold, Array.size_modify',
      size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega),
        ite_eq_left rfl]
  · rw [ite_eq_right hu]
    by_cases h1 : u = t.nodes.size
    · subst h1
      rw [getX_modify_ne (by omega), getX_modify_ne (by omega), getX_modify_ne (by omega)]
      simp (disch := (intro n; rfl)) only [proj_ite_fold Node.children]
      rw [getX_modify_eq (by
        rw [size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size];
          omega)]
      rfl
    · by_cases h2 : u = t.nodes.size + 1
      · subst h2
        rw [getX_modify_ne (by omega), getX_modify_ne (by omega),
          getX_modify_eq (by
            rw [size_ite_fold, Array.size_modify', size_ite_fold, size_ite_fold2,
              Array.size_modify', Array.size_modify', sd2_size]; omega)]
        simp only [ite_eq_right h1]; rfl
      · rw [ite_eq_right h1, ite_eq_right h2]
        by_cases h3 : u = (t.nodes.getX v).livePar
        · subst h3
          rw [getX_modify_ne (Ne.symm hu),
            getX_modify_eq (by
              rw [Array.size_modify', size_ite_fold, Array.size_modify', size_ite_fold,
                size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega),
                  ite_eq_left rfl]
          change List.replace1 _ _ _ = _
          congr 1
          simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify
            Node.children, proj_ite_fold Node.children, proj_ite_fold2 Node.children]
          exact sd2_proj hnd htabs Node.children (fun _ _ _ => rfl) h1 h2
        · rw [ite_eq_right h3]
          simp (disch := first | (intro n; rfl) | omega) only [getX_modify_ne, proj_modify
            Node.children, proj_ite_fold Node.children, proj_ite_fold2 Node.children]
          exact sd2_proj hnd htabs Node.children (fun _ _ _ => rfl) h1 h2

theorem sdS_livePar (hv : v < t.nodes.size) (hL : (t.nodes.getX v).livePar < t.nodes.size)
    (hkid : sH t v ≠ 1 → ∀ e ∈ sKids t v, e < t.nodes.size) (u : Nat) : ((sdS t v
      side).nodes.getX u).livePar =
      if u = v then NIL else if u = t.nodes.size ∨ u = t.nodes.size + 1 then (t.nodes.getX
        v).livePar
      else if sH t v ≠ 1 ∧ u ∈ sCh2 t v side then t.nodes.size + 1
      else if sH t v ≠ 1 ∧ u ∈ sCh1 t v side then t.nodes.size
      else (t.nodes.getX u).livePar := by
  have h1m : sH t v ≠ 1 → ∀ e ∈ sCh1 t v side, e < t.nodes.size := fun hh e he =>
    hkid hh e (List.mem_of_mem_filter he)
  have h2m : sH t v ≠ 1 → ∀ e ∈ sCh2 t v side, e < t.nodes.size := fun hh e he =>
    hkid hh e (List.mem_of_mem_filter he)
  by_cases hbig : t.nodes.size + 2 ≤ u
  · rw [getX_ge (by rw [sdS_size hln hrn]; omega), getX_ge (a := t.nodes) (u := u) (by omega),
      ite_eq_right (show u ≠ v by omega), ite_eq_right (show ¬(u = t.nodes.size ∨ u =
        t.nodes.size + 1) by omega),
      ite_eq_right (fun h => by have := h2m h.1 _ h.2; omega), ite_eq_right (fun h => by have :=
        h1m h.1 _ h.2; omega)]
  rw [sdS_nodes hln hrn]; simp only []
  by_cases hu : u = v
  · subst hu; rw [getX_modify_eq (by
    rw [Array.size_modify', Array.size_modify', size_ite_fold, Array.size_modify',
      size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega),
        ite_eq_left rfl]
  · rw [ite_eq_right hu, getX_modify_ne (Ne.symm hu)]
    simp (disch := (intro n; rfl)) only [proj_modify Node.livePar]
    by_cases h2 : u = t.nodes.size + 1
    · subst h2
      rw [getX_modify_eq (by
        rw [size_ite_fold, Array.size_modify', size_ite_fold, size_ite_fold2,
          Array.size_modify', Array.size_modify', sd2_size]; omega), ite_eq_left (Or.inr rfl)]
    · rw [getX_modify_ne (Ne.symm h2)]
      rw [ite_fold_livePar _ _ hc2 _ (by
        rw [Array.size_modify', size_ite_fold, size_ite_fold2, Array.size_modify',
          Array.size_modify', sd2_size] omega)]
      by_cases h1 : u = t.nodes.size
      · subst h1
        rw [ite_eq_right (fun h => by have := h2m h.1 _ h.2; omega),
          getX_modify_eq (by
            rw [size_ite_fold, size_ite_fold2, Array.size_modify', Array.size_modify',
              sd2_size]; omega), ite_eq_left (Or.inl rfl)]
      · rw [ite_eq_right (show ¬(u = t.nodes.size ∨ u = t.nodes.size + 1) from fun h => h.elim
        h1 h2),
          getX_modify_ne (Ne.symm h1)]
        congr 1
        rw [ite_fold_livePar _ _ hc1 _ (by
          rw [size_ite_fold2, Array.size_modify', Array.size_modify', sd2_size]; omega)]
        congr 1
        simp (disch := (intro n; rfl)) only [proj_ite_fold2 Node.livePar]
        rw [getX_modify_ne (Ne.symm h2), getX_modify_ne (Ne.symm h1)]
        exact sd2_proj hnd htabs Node.livePar (fun _ _ _ => rfl) h1 h2

end fields

end node

end OrderMaintenance.Proof.Top

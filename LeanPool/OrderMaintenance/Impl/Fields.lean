/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Batteries.Tactic.SeqFocus
public import LeanPool.OrderMaintenance.Impl.Compile
public import LeanPool.OrderMaintenance.ArrayLemmas


/-!
# M6: reading back what was written

A write to field `f` of record `i` changes exactly that value (`Fld.get_set`), keeps every
table size and the parameters, and a `push` changes no value at all (a pushed record is a
default record, which reads like a record past the end).
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top (getX_modify' getX_setX' getX_push')

theorem b2n_not_beq {v : Nat} (h : v ≤ 1) : b2n (!(v == 0)) = v := by
  rcases v with _ | _ | v <;> simp [b2n] at *
theorem b2n_bne {v : Nat} (h : v ≤ 1) : b2n (v != 0) = v := by
  rcases v with _ | _ | v <;> simp [b2n] at * <;> omega

theorem EF.get_set (x : Elem) (v : Nat) (k k' : EF) (h : k.ok v = true) :
    EF.get (EF.set x v k) k' = if k' = k then v else EF.get x k' := by
  cases k <;> cases k' <;> simp_all [EF.get, EF.set, EF.ok, b2n_not_beq]

theorem GF.get_set (x : Group) (v : Nat) (k k' : GF) (h : k.ok v = true) :
    GF.get (GF.set x v k) k' = if k' = k then v else GF.get x k' := by
  cases k <;> cases k' <;> simp_all [GF.get, GF.set, GF.ok, b2n_not_beq, St.toN_ofN]

theorem CF.get_set (x : Chunk) (v : Nat) (k k' : CF) (h : k.ok v = true) :
    CF.get (CF.set x v k) k' = if k' = k then v else CF.get x k' := by
  cases k <;> cases k' <;> simp_all [CF.get, CF.set, CF.ok, b2n_not_beq, St.toN_ofN]

theorem NF.get_set (x : Node) (v : Nat) (k k' : NF) (h : k.ok v = true) :
    NF.get (NF.set x v k) k' = if k' = k then v else NF.get x k' := by
  cases k <;> cases k' <;> simp_all [NF.get, NF.set, NF.ok, b2n_not_beq, b2n_bne]

theorem AF.get_set (s : Core) (a : Array Nat) (k k' : AF) :
    k'.get (k.set s a) = if k' = k then a else k'.get s := by
  cases k <;> cases k' <;> rfl

theorem SF.get_set (s : Core) (v : Nat) (k k' : SF) (h : k.ok v = true) :
    k'.get (k.set s v) = if k' = k then v else k'.get s := by
  cases k <;> cases k' <;> simp_all [SF.get, SF.set, SF.ok, b2n_not_beq]

/-- What an `AF` write keeps. -/
theorem AF.set_keep (s : Core) (a : Array Nat) (k : AF) :
    (k.set s a).E = s.E ∧ (k.set s a).Gs = s.Gs ∧ (k.set s a).C = s.C ∧ (k.set s a).nodes =
      s.nodes ∧
      (k.set s a).P = s.P ∧ ∀ k' : SF, k'.get (k.set s a) = k'.get s := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl, fun k' => by cases k' <;> rfl⟩

/-- What a scalar write keeps. -/
theorem SF.set_keep (s : Core) (v : Nat) (k : SF) :
    (k.set s v).E = s.E ∧ (k.set s v).Gs = s.Gs ∧ (k.set s v).C = s.C ∧ (k.set s v).nodes =
      s.nodes ∧
      (k.set s v).P = s.P ∧ ∀ k' : AF, k'.get (k.set s v) = k'.get s := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl, fun k' => by cases k' <;> rfl⟩

theorem Fld.cap_scalar {κ : Caps} {k : SF} {j : Nat} (h : j < (Fld.s k).cap κ) : j = 0 := by
  simp [Fld.cap] at h; exact h

/-- **A write changes exactly the written value.** -/
theorem Fld.get_set {κ : Caps} {s s' : Core} {i v : Nat} {f : Fld} (h : f.set κ s i v = some s')
    (g : Fld) {j : Nat} (hj : j < g.cap κ) :
    g.get s' j = if g = f ∧ j = i then v else g.get s j := by
  cases f with
  | e k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    cases g with
    | e k' =>
      simp only [Fld.get, getX_modify']
      by_cases e1 : j = i
      · subst e1; rw [ite_eq_left ⟨rfl, hc.1⟩, EF.get_set _ _ _ _ hc.2]; by_cases e2 : k' = k
        <;> simp [e2]
      · rw [ite_eq_right (fun h => e1 h.1)]; simp [e1]
    | _ k' => cases k' <;> simp [Fld.get, AF.get, SF.get]
  | g k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    cases g with
    | g k' =>
      simp only [Fld.get, getX_modify']
      by_cases e1 : j = i
      · subst e1; rw [ite_eq_left ⟨rfl, hc.1⟩, GF.get_set _ _ _ _ hc.2]; by_cases e2 : k' = k
        <;> simp [e2]
      · rw [ite_eq_right (fun h => e1 h.1)]; simp [e1]
    | _ k' => cases k' <;> simp [Fld.get, AF.get, SF.get]
  | c k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    cases g with
    | c k' =>
      simp only [Fld.get, getX_modify']
      by_cases e1 : j = i
      · subst e1; rw [ite_eq_left ⟨rfl, hc.1⟩, CF.get_set _ _ _ _ hc.2]; by_cases e2 : k' = k
        <;> simp [e2]
      · rw [ite_eq_right (fun h => e1 h.1)]; simp [e1]
    | _ k' => cases k' <;> simp [Fld.get, AF.get, SF.get]
  | n k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    cases g with
    | n k' =>
      simp only [Fld.get, getX_modify']
      by_cases e1 : j = i
      · subst e1; rw [ite_eq_left ⟨rfl, hc.1⟩, NF.get_set _ _ _ _ hc.2]; by_cases e2 : k' = k
        <;> simp [e2]
      · rw [ite_eq_right (fun h => e1 h.1)]; simp [e1]
    | _ k' => cases k' <;> simp [Fld.get, AF.get, SF.get]
  | a k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    obtain ⟨hE, hG, hC, hN, -, hS⟩ := AF.set_keep s ((k.get s).setX i v) k
    cases g with
    | a k' =>
      simp only [Fld.get, AF.get_set]
      by_cases e2 : k' = k
      · subst e2; rw [ite_eq_left rfl, getX_setX']; by_cases e1 : j = i <;> simp [e1]
      · simp [e2]
    | e k' => simp only [Fld.get, hE]; simp
    | g k' => simp only [Fld.get, hG]; simp
    | c k' => simp only [Fld.get, hC]; simp
    | n k' => simp only [Fld.get, hN]; simp
    | s k' => simp only [Fld.get, hS]; simp
  | s k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    obtain ⟨hE, hG, hC, hN, -, hS⟩ := SF.set_keep s v k
    cases g with
    | s k' =>
      have hj0 := Fld.cap_scalar hj
      have hi0 : i = 0 := by omega
      subst hj0; subst hi0
      simp only [Fld.get, SF.get_set _ _ _ _ hc.2]
      by_cases e2 : k' = k <;> simp [e2]
    | e k' => simp only [Fld.get, hE]; simp
    | g k' => simp only [Fld.get, hG]; simp
    | c k' => simp only [Fld.get, hC]; simp
    | n k' => simp only [Fld.get]; rw [hN]; simp
    | a k' =>
      cases k <;> cases k' <;> simp [Fld.get, SF.set, AF.get]

/-- A write keeps the table sizes and the parameters. -/
theorem Fld.set_keep {κ : Caps} {s s' : Core} {i v : Nat} {f : Fld} (h : f.set κ s i v = some s') :
    (∀ t : Tbl, t.size s' = t.size s) ∧ s'.P = s.P := by
  cases f with
  | e k | g k | c k | n k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h; exact ⟨fun t => by cases t <;> simp [Tbl.size], rfl⟩
  | a k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    obtain ⟨hE, hG, hC, hN, hP, -⟩ := AF.set_keep s ((k.get s).setX i v) k
    exact ⟨fun t => by cases t <;> simp [Tbl.size, hE, hG, hC, hN], hP⟩
  | s k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    obtain ⟨hE, hG, hC, hN, hP, -⟩ := SF.set_keep s v k
    exact ⟨fun t => by cases t <;> simp [Tbl.size, hE, hG, hC, hN], hP⟩

theorem getX_push_default {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    (a.push default).getX i = a.getX i := by
  rw [getX_push']
  split
  · next h => subst h; unfold Array.getX; simp [Array.getD]
  · rfl

/-- **A push changes no value**, and adds one to its table's size. -/
theorem Tbl.push_get (s : Core) (t : Tbl) (f : Fld) (i : Nat) : f.get (t.push s) i = f.get s i := by
  cases t <;> cases f <;> (rename_i k; cases k) <;>
    simp only [Tbl.push, Fld.get, AF.get, SF.get, getX_push_default]

theorem Tbl.push_size (s : Core) (t t' : Tbl) :
    t'.size (t.push s) = if t' = t then t.size s + 1 else t'.size s := by
  cases t <;> cases t' <;> simp [Tbl.push, Tbl.size]

theorem Tbl.push_P (s : Core) (t : Tbl) : (t.push s).P = s.P := by cases t <;> rfl

end OrderMaintenance.Impl

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top (getX_modify' getX_setX' getX_push')

/-! ### Lists, paths and optional records under field writes and pushes -/

theorem NF.set_lists (x : Node) (v : Nat) (k : NF) :
    (NF.set x v k).children = x.children ∧ (NF.set x v k).table = x.table ∧
      (NF.set x v k).inTables = x.inTables ∧ (NF.set x v k).side = x.side := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A field write keeps every list, path row and optional record. -/
theorem Fld.set_rest {κ : Caps} {s s' : Core} {i v : Nat} {f : Fld} (h : f.set κ s i v = some s') :
    (∀ (k : LK) j, k.view s' j = k.view s j) ∧ (∀ c, rowOf s' c = rowOf s c) ∧ (∀ o : OF,
      o.get s' = o.get s) := by
  cases f with
  | e k | g k | c k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    exact ⟨fun k' j => by cases k' <;> rfl, fun c => rfl, fun o => by cases o <;> rfl⟩
  | n k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    refine ⟨fun k' j => ?_, fun c => rfl, fun o => by cases o <;> rfl⟩
    cases k' <;> simp only [LK.view, getX_modify'] <;> (try split) <;> simp [NF.set_lists]
  | a k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    cases k <;> exact ⟨fun k' j => by cases k' <;> rfl, fun c => rfl, fun o => by cases o <;> rfl⟩
  | s k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    cases k <;> exact ⟨fun k' j => by cases k' <;> rfl, fun c => rfl, fun o => by cases o <;> rfl⟩

theorem Tbl.push_rest (s : Core) (t : Tbl) :
    (∀ (k : LK) j, k.view (t.push s) j = k.view s j) ∧ (∀ c, rowOf (t.push s) c = rowOf s c) ∧
      (∀ o : OF, o.get (t.push s) = o.get s) := by
  refine ⟨fun k j => ?_, fun c => by cases t <;> rfl, fun o => by cases t <;> cases o <;> rfl⟩
  cases t <;> cases k <;> simp only [Tbl.push, LK.view, getX_push_default]

/-! ### Lists under list writes -/

/-- Numeric node fields are unchanged when its `children` list is replaced. -/
@[simp] theorem NF.get_children (x : Node) (k : NF) (values : List Nat) :
    NF.get { x with children := values } k = NF.get x k := by
  cases k <;> rfl

/-- Numeric node fields are unchanged when its `table` list is replaced. -/
@[simp] theorem NF.get_table (x : Node) (k : NF) (values : List (Nat × Nat)) :
    NF.get { x with table := values } k = NF.get x k := by
  cases k <;> rfl

/-- Numeric node fields are unchanged when its `inTables` list is replaced. -/
@[simp] theorem NF.get_inTables (x : Node) (k : NF) (values : List Nat) :
    NF.get { x with inTables := values } k = NF.get x k := by
  cases k <;> rfl

/-- Numeric node fields are unchanged when its `side` list is replaced. -/
@[simp] theorem NF.get_side (x : Node) (k : NF) (values : List (Nat × Side)) :
    NF.get { x with side := values } k = NF.get x k := by
  cases k <;> rfl

theorem NF.get_lists (x : Node) (k : NF) (a : List Nat) (b : List (Nat × Nat)) (c : List Nat)
    (d : List (Nat × Side)) :
    NF.get { x with children := a } k = NF.get x k ∧ NF.get { x with table := b } k = NF.get x k ∧
      NF.get { x with inTables := c } k = NF.get x k ∧ NF.get { x with side := d } k = NF.get
        x k := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- What a list replacement keeps. -/
theorem LK.put_keep (s : Core) (i : Nat) (l : List (Nat × Nat)) (k : LK) :
    (∀ (f : Fld) j, f.get (k.put s i l) j = f.get s j) ∧ (∀ t : Tbl, t.size (k.put s i l) =
      t.size s) ∧
      (k.put s i l).P = s.P ∧ (∀ c, rowOf (k.put s i l) c = rowOf s c) ∧
      (∀ o : OF, o.get (k.put s i l) = o.get s) := by
  refine ⟨fun f j => ?_, fun t => ?_, by cases k <;> rfl, fun c => by cases k <;> rfl,
    fun o => by cases k <;> cases o <;> rfl⟩
  · cases k <;> cases f <;> simp only [LK.put, Fld.get, getX_modify'] <;> (try split) <;>
      first | rfl | simp
  · cases k <;> cases t <;> simp [LK.put, Tbl.size]

theorem sideN_ofN {v : Nat} (h : v ≤ 1) : sideN (sideOfN v) = v := by
  rcases v with _ | _ | v <;> first | rfl | omega

theorem map_pair0 {l : List (Nat × Nat)} (h : (l.all fun q => q.2 == 0) = true) :
    (l.map (·.1)).map (fun e => (e, 0)) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, ih h.2]
    rw [← h.1]

theorem map_side {l : List (Nat × Nat)} (h : (l.all fun q => decide (q.2 ≤ 1)) = true) :
    (l.map fun q => (q.1, sideOfN q.2)).map (fun q => (q.1, sideN q.2)) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, ih h.2, sideN_ofN h.1]

theorem map_pair0' {l : List (Nat × Nat)} (h : (l.all fun q => q.2 == 0) = true) :
    l.map (fun q => (q.1, 0)) = l := by
  have := map_pair0 h; simpa [List.map_map, Function.comp_def] using this

theorem map_side' {l : List (Nat × Nat)} (h : (l.all fun q => decide (q.2 ≤ 1)) = true) :
    l.map (fun q => (q.1, sideN (sideOfN q.2))) = l := by
  have := map_side h; simpa [List.map_map, Function.comp_def] using this

theorem map_pair0_mem {l : List (Nat × Nat)} (h : ∀ q ∈ l, q.2 = 0) : l.map (fun q => (q.1,
  0)) = l := by
  apply map_pair0'; simpa using h

theorem map_side_mem {l : List (Nat × Nat)} (h : ∀ q ∈ l, q.2 ≤ 1) :
    l.map (fun q => (q.1, sideN (sideOfN q.2))) = l := by
  apply map_side'; simpa using h

/-- **A list replacement reads back**, and touches no other list. -/
theorem LK.view_put {s : Core} {i : Nat} {l : List (Nat × Nat)} {k : LK} (hr : k.recOk s i = true)
    (hv : k.valid l = true) (k' : LK) (j : Nat) :
    k'.view (k.put s i l) j = if k' = k ∧ j = i then l else k'.view s j := by
  cases k <;> simp only [LK.recOk, decide_eq_true_eq, LK.valid] at hr hv
  all_goals (try have hl := map_pair0' hv)
  all_goals (try have hl := map_side' hv)
  all_goals (cases k' <;> simp only [LK.view, LK.put, getX_modify', getX_setX'] <;>
    by_cases e : j = i <;> (try subst hr) <;> simp [*, Function.comp_def])

end OrderMaintenance.Impl

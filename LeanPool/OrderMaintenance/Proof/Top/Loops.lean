/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.RunDrain
public import LeanPool.OrderMaintenance.Proof.Top.Lists


/-!
# M5: running loops

`forM` and `mapM` in `CM`, when every iteration succeeds: the result is a fold (`forM_run`,
`mapM_run`). And folds of array updates at distinct indices (`foldl_modify_getX`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- A `forM` whose iterations succeed, with an invariant over the remaining list. -/
theorem forM_run {α : Type} (l : List α) (f : α → CM PUnit) (g : α → Core → Core)
    (Inv : List α → Core → Prop) :
    ∀ s, Inv l s → (∀ x rest t, Inv (x :: rest) t → (f x).run t = .ok ⟨⟩ (g x t) ∧ Inv rest (g x t)) →
      (l.forM f).run s = .ok ⟨⟩ (l.foldl (fun t x => g x t) s) := by
  induction l with
  | nil => intro s _ _; rfl
  | cons x t ih =>
    intro s hI h
    obtain ⟨h1, h2⟩ := h x t s hI
    show (do f x; t.forM f).run s = _
    rw [run_bind, h1]
    exact ih (g x s) h2 h

/-- A `forM` whose iterations always succeed. -/
theorem forM_run' {α : Type} (l : List α) (f : α → CM PUnit) (g : α → Core → Core)
    (h : ∀ x t, (f x).run t = .ok ⟨⟩ (g x t)) (s : Core) :
    (l.forM f).run s = .ok ⟨⟩ (l.foldl (fun t x => g x t) s) :=
  forM_run l f g (fun _ _ => True) s trivial fun x _ t _ => ⟨h x t, trivial⟩

/-- A `mapM` of reads that succeed. -/
theorem mapM_run {α β : Type} (l : List α) (f : α → CM β) (g : α → β) (s : Core)
    (h : ∀ x ∈ l, (f x).run s = .ok (g x) s) : (l.mapM f).run s = .ok (l.map g) s := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.mapM_cons, List.map_cons]
    rw [run_bind, h x (by simp)]
    simp only
    rw [run_bind, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

/-- Updates at distinct indices, folded. -/
theorem foldl_modify_getX {α γ : Type} [Inhabited α] (l : List γ) (idx : γ → Nat) (F : γ → α → α)
    (hl : (l.map idx).Nodup) (a : Array α) (u : Nat) :
    (l.foldl (fun b x => b.modify (idx x) (F x)) a).getX u =
      match l.find? (fun x => idx x == u) with
      | some x => if u < a.size then F x (a.getX u) else a.getX u
      | none => a.getX u := by
  induction l generalizing a with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    simp only [List.foldl_cons]
    rw [ih hl.2]
    simp only [List.find?_cons]
    by_cases hx : idx x = u
    · subst hx
      have : t.find? (fun y => idx y == idx x) = none := by
        rw [List.find?_eq_none]; intro y hy; simp only [beq_iff_eq]
        intro e; exact hl.1 (e ▸ List.mem_map_of_mem hy)
      simp [this, Array.getX_modify]
    · simp only [show (idx x == u) = false by simpa using hx]
      cases t.find? (fun y => idx y == u) with
      | some y => simp [Array.getX_modify, hx]
      | none => simp [Array.getX_modify, hx]

/-- Updates at distinct indices, folded (the index is the element). -/
theorem foldl_modify_getX' {α : Type} [Inhabited α] (F : Nat → α → α) :
    ∀ (l : List Nat), l.Nodup → ∀ (a : Array α) (u : Nat),
      (l.foldl (fun b x => b.modify x (F x)) a).getX u =
        if u ∈ l ∧ u < a.size then F u (a.getX u) else a.getX u
  | [], _, a, u => by simp
  | x :: t, hl, a, u => by
    have hx := List.nodup_cons.mp hl
    simp only [List.foldl_cons]
    rw [foldl_modify_getX' F t hx.2, Array.size_modify', Array.getX_modify]
    by_cases hux : u = x
    · subst hux
      simp [hx.1]
    · simp only [List.mem_cons, hux, false_or,
      show ¬(x = u ∧ x < a.size) from fun h => hux h.1.symm,
        ite_false]

theorem foldl_modify_size {α γ : Type} [Inhabited α] (l : List γ) (idx : γ → Nat) (F : γ → α → α)
    (a : Array α) : (l.foldl (fun b x => b.modify (idx x) (F x)) a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons x t ih => simp [ih]

end OrderMaintenance.Proof.Top

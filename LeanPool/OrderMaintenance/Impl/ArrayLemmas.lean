/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Notation


/-!
# M6: array identities for the agreement lemmas
-/


@[expose] public section

namespace OrderMaintenance.Impl

theorem Array.modify_modify_same {α : Type} (a : Array α) (i : Nat) (f g : α → α) :
    (a.modify i f).modify i g = a.modify i (g ∘ f) := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_modify]
    by_cases e : i = j <;> simp [e]

theorem Array.modify_push_size {α : Type} (a : Array α) (x : α) (f : α → α) :
    (a.push x).modify a.size f = a.push (f x) := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_modify, Array.getElem_push]
    by_cases e : a.size = j
    · subst e; simp
    · simp only [e, ite_false]
      have : j < a.size := by simp at h2; omega
      simp [this]

end OrderMaintenance.Impl

namespace OrderMaintenance.Impl

/-- Two updates of cell `i` agree if they agree on its current value. -/
theorem Array.modify_congr_getX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (f g : α → α)
    (h : f (a.getX i) = g (a.getX i)) : a.modify i f = a.modify i g := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_modify]
    by_cases e : i = j
    · subst e
      have : a[i]'(by simpa using h1) = a.getX i := by
        simp [Array.getX, Array.getD, show i < a.size by simpa using h1]
      simp [this, h]
    · simp [e]

end OrderMaintenance.Impl

namespace OrderMaintenance.Impl

/-- Evaluate a core-language program symbolically (with extra facts). -/
macro "dsl_simp" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [evalF, Exp.ev, evList, Res.bind, Res.addCost, Fld.set, Fld.get, Fld.cap, EF.get,
      GF.get,
      CF.get, NF.get, SF.get, AF.get, EF.ok, GF.ok, CF.ok, NF.ok, SF.ok, SF.set, AF.set, Exp.sc,
      Stm.wsc, Exp.ar,
      Stm.war, Machine.State.upd, Exp.cost, costList, PF.get, Tbl.size, Tbl.push,
      pushCost, Proc.call,
      $ls,*])

/-- `set!` is a `modify` with a constant. -/
theorem Array.set!_eq_modify {α : Type} (a : Array α) (i : Nat) (v : α) :
    a.set! i v = a.modify i (fun _ => v) := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_modify, Array.set!]
    by_cases e : i = j
    · subst e; simp
    · rw [Array.getElem_setIfInBounds_ne (by simpa using h2) e]; simp [e]

end OrderMaintenance.Impl

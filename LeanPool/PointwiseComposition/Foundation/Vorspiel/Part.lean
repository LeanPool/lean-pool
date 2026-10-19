/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.PFun

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace Part

open _root_.Part

@[simp]
lemma mem_vector_mOfFn {n : ℕ} {w : List.Vector α n} {v : Fin n → Part α} :
    w ∈ List.Vector.mOfFn v ↔ ∀ i, w.get i ∈ v i := by
  induction n with
  | zero => simp [List.Vector.mOfFn, List.Vector.eq_nil]
  | succ n
    ih =>
    suffices
      (∃ a ∈ v 0, ∃ u, (∀ i : Fin n, u.get i ∈ v i.succ) ∧ w = a ::ᵥ u) ↔
        ∀ i : Fin (n + 1), w.get i ∈ v i
      by simpa [List.Vector.mOfFn, ih]
    constructor
    · rintro ⟨a, ha, u, hu, rfl⟩ i
      cases i using Fin.cases <;> simp [ha, hu]
    · intro h
      exact ⟨w.head, by simpa using h 0, w.tail, fun i => by simpa using h i.succ, by simp⟩

lemma unit_dom_iff (x : Part Unit) : x.Dom ↔ () ∈ x := by
  simp [dom_iff_mem, show ∀ x : Unit, x = () by intro x; rfl]

end Part

end

end PointwiseComposition

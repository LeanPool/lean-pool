/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SimpleGridPathPointTrichotomy
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathVertexIncidentEdge

-- [TABLET NODE: P3192T1SimplePathOrientation]

/-!
# P3192T1SimplePathOrientation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3192T1SimplePathOrientation
    (V : Set GaussianInt) (E : Set (Finset GaussianInt))
    (x y : GaussianInt) (hpath : SimpleGridPath V E)
    (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y)
    (hxone : ∀ e f : Finset GaussianInt, x ∈ e → x ∈ f →
      e ∈ E → f ∈ E → e = f)
    (hyone : ∀ e f : Finset GaussianInt, y ∈ e → y ∈ f →
      e ∈ E → f ∈ E → e = f) :
    SimpleGridPathBetween V E x y := by
-- BODY
  classical
  obtain ⟨p, hp, hlen, hV, hstep, hE⟩ := hpath
  have hpne : p ≠ [] := by
    intro h
    simp [h] at hlen
  let a := p.head hpne
  let b := p.getLast hpne
  have hhead : p.head? = some a := List.head?_eq_some_head hpne
  have hlast : p.getLast? = some b := List.getLast?_eq_some_getLast hpne
  have hbetween : SimpleGridPathBetween V E a b :=
    ⟨p, hp, hlen, hhead, hlast, hV, hstep, hE⟩
  have classify (z : GaussianInt) (hz : z ∈ V)
      (hone : ∀ e f : Finset GaussianInt, z ∈ e → z ∈ f →
        e ∈ E → f ∈ E → e = f) : z = a ∨ z = b := by
    obtain ⟨e, hze, he⟩ := SimpleGridPathVertexIncidentEdge V E
      ⟨p, hp, hlen, hV, hstep, hE⟩ z hz
    rcases SimpleGridPathPointTrichotomy V E a b z hbetween ⟨e, hze, he⟩ with
      h | h | ⟨e, f, hne, hze, hzf, he, hf⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact (hne (hone e f hze hzf he hf)).elim
  have hxend := classify x hx hxone
  have hyend := classify y hy hyone
  have reverse_raw (r : List GaussianInt) (e : Finset GaussianInt) :
      (∃ u v l₁ l₂, r = l₁ ++ u :: v :: l₂ ∧ e = {u, v}) →
        ∃ u v l₁ l₂, r.reverse = l₁ ++ u :: v :: l₂ ∧ e = {u, v} := by
    rintro ⟨u, v, l₁, l₂, hr, he⟩
    refine ⟨v, u, l₂.reverse, l₁.reverse, ?_, ?_⟩
    · rw [hr]
      simp [List.reverse_append, List.append_assoc]
    · simpa [Finset.pair_comm] using he
  have hreverse : SimpleGridPathBetween V E b a := by
    refine ⟨p.reverse, List.nodup_reverse.mpr hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hlen
    · simpa using hlast
    · simpa using hhead
    · simpa using hV
    · intro u v l₁ l₂ hr
      have hpform : p = l₂.reverse ++ v :: u :: l₁.reverse := by
        have hh := congrArg List.reverse hr
        simpa [List.reverse_append, List.append_assoc] using hh
      rcases hstep v u l₂.reverse l₁.reverse hpform with h | h | h | h
      · exact Or.inr (Or.inl (by rw [h]; simp))
      · exact Or.inl (by rw [h]; simp)
      · exact Or.inr (Or.inr (Or.inr (by rw [h]; simp)))
      · exact Or.inr (Or.inr (Or.inl (by rw [h]; simp)))
    · intro e
      constructor
      · intro he
        exact reverse_raw p e ((hE e).mp he)
      · intro he
        apply (hE e).mpr
        simpa using reverse_raw p.reverse e he
  rcases hxend with rfl | rfl <;> rcases hyend with rfl | rfl
  · exact (hxy rfl).elim
  · exact hbetween
  · exact hreverse
  · exact (hxy rfl).elim

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ChordGeometry
public import LeanPool.GraphMinor.Surface.CircleMove

/-!
# The finite meeting points of the source edge arcs

XII (4.5), pages 252--253, numbers the crossings before subdividing
the edges. In the port construction, two distinct supporting lines
meet at most once. Complete edges meet away from vertices only
where their inner chords meet. Thus each pair has at most one such
point, the whole set is finite, and no third edge passes through it.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The meetings of distinct edge arcs away from the vertices,
to be numbered in the source construction of XII (4.5), page 252. -/
@[expose] def edgeMeetingPoints {S α β : Type*} (V : α → S) (E : β → Set S) : Set S :=
  {x | ∃ i j, i ≠ j ∧ x ∈ E i ∩ E j ∧ x ∉ range V}

/-- A finite arc family with finite pairwise intersections has
only finitely many meetings away from vertices. This numbers the
meeting points in XII (4.5), page 252. -/
theorem finite_edgeMeetingPoints {α β : Type*} [Finite β] (V : α → ℂ) (E : β → Set ℂ)
    (hfinite : ∀ i j, i ≠ j → (E i ∩ E j).Finite) :
    (edgeMeetingPoints V E).Finite := by
  classical
  let X : β → β → Set ℂ := fun i j => if i = j then ∅ else (E i ∩ E j) \ range V
  have hX : (⋃ i, ⋃ j, X i j).Finite := by
    refine finite_iUnion fun i => finite_iUnion fun j => ?_
    dsimp [X]
    split_ifs with hij
    · exact finite_empty
    · exact (hfinite i j hij).sdiff
  apply hX.subset
  rintro x ⟨i, j, hij, hx, hxV⟩
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, by simpa [X, hij] using And.intro hx hxV⟩⟩

/-- Two port edges meet in at most one point away from vertices.
This makes their crossing label unambiguous in XII (4.5), page 252. -/
theorem pair_edge_meetings_subsingleton {m n : ℕ}
    (V : Fin m → ℂ) (E : Fin n → Set ℂ) (s : Fin n × Bool → ℝ)
    (hinj : Function.Injective (fun x => (ee (s x) : ℂ)))
    (hinter : ∀ i j, i ≠ j → E i ∩ E j ⊆
      (segment ℝ (ee (s (i, false)) : ℂ) (ee (s (i, true)) : ℂ) ∩
        segment ℝ (ee (s (j, false)) : ℂ) (ee (s (j, true)) : ℂ)) ∪ range V)
    {i j : Fin n} (hij : i ≠ j) :
    ((E i ∩ E j) \ range V).Subsingleton := by
  let a : Fin n × Bool → ℂ := fun x => (ee (s x) : ℂ)
  have hab : a (i, false) ≠ a (i, true) := by
    intro h
    exact Bool.false_ne_true (congrArg Prod.snd (hinj h))
  have hne : line[ℝ, a (i, false), a (i, true)] ≠ line[ℝ, a (j, false), a (j, true)] := by
    intro heq
    have hjline : a (j, false) ∈ line[ℝ, a (i, false), a (i, true)] := by
      rw [heq]
      exact left_mem_affineSpan_pair _ _ _
    have hends := (unit_circle_mem_line_iff (by simp [a]) (by simp [a]) hab (by simp [a])).mp hjline
    exact hends.elim (fun h => hij (congrArg Prod.fst (hinj h)).symm)
      (fun h => hij (congrArg Prod.fst (hinj h)).symm)
  have hsub : (E i ∩ E j) \ range V ⊆
      (line[ℝ, a (i, false), a (i, true)] : Set ℂ) ∩
        (line[ℝ, a (j, false), a (j, true)] : Set ℂ) := by
    intro x hx
    have hc := (hinter i j hij hx.1).resolve_right hx.2
    exact ⟨(line[ℝ, a (i, false), a (i, true)]).convex.segment_subset
        (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hc.1,
      (line[ℝ, a (j, false), a (j, true)]).convex.segment_subset
        (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hc.2⟩
  intro x hx y hy
  exact subsingleton_inter_of_ne_lines hne (hsub hx) (hsub hy)

/-- A meeting away from vertices lies on exactly its two edge
arcs when triple meetings are confined to vertices. This is the
uniqueness of the crossing pair used in XII (4.5), page 252. -/
theorem edge_eq_of_mem_pair_meeting {α β : Type*}
    (V : α → ℂ) (E : β → Set ℂ)
    (htriple : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → E i ∩ E j ∩ E k ⊆ range V)
    {i j k : β} (hij : i ≠ j) {x : ℂ}
    (hx : x ∈ (E i ∩ E j) \ range V) (hxk : x ∈ E k) : k = i ∨ k = j := by
  by_cases hki : k = i
  · exact Or.inl hki
  by_cases hkj : k = j
  · exact Or.inr hkj
  exact False.elim (hx.2 (htriple i j k hij (fun h => hkj h.symm)
    (fun h => hki h.symm) ⟨hx.1, hxk⟩))

end GraphMinor.GM12

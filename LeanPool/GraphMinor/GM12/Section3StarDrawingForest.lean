/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3StarDrawing
public import LeanPool.GraphMinor.GM12.Section3StarForest
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.Surface.SurfaceGraph
import Mathlib.Data.Set.Insert

/-!
# The finite star drawing is a forest

The drawing in XII (3.1), page 245, has one open line per prescribed
leaf. Its edge closures meet the vertex set exactly at the centre and
that leaf. Thus every edge joins the centre to a leaf, and the leaf
has no second incident edge. The star forest lemma applies.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The actual drawing of a finite family of lines meeting only at
one centre has no circuits. -/
theorem isGraphForest_star_drawing
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Z : Set S} (c : S) (L : S → Set S)
    (hline : ∀ a ∈ Z, IsLineWithEnds (L a) c a)
    (hmeet : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → L a ∩ L b = {c})
    (hcZ : c ∉ Z) (H : Drawing S) (hV : H.V = insert c Z)
    (hE : H.E = (fun a => L a \ {c, a}) '' Z) : IsGraphForest H.toGraph := by
  have hinter : ∀ a ∈ Z, L a ∩ insert c Z = {c, a} := by
    intro a ha
    apply Subset.antisymm
    · rintro x ⟨hxL, hxV⟩
      rcases hxV with hxc | hxZ
      · exact Or.inl hxc
      · by_cases hxa : x = a
        · exact Or.inr hxa
        · have hx : x ∈ L a ∩ L x := ⟨hxL, (hline x hxZ).right_mem⟩
          rw [hmeet a ha x hxZ (Ne.symm hxa)] at hx
          exact Or.inl hx
    · rintro x (hxc | hxa)
      · subst x
        exact ⟨(hline a ha).left_mem, Or.inl rfl⟩
      · subst x
        exact ⟨(hline a ha).right_mem, Or.inr ha⟩
  have hlinks : ∀ {e x y}, H.toGraph.IsLink e x y →
      ∃ a ∈ Z, e = L a \ {c, a} ∧ ((x = c ∧ y = a) ∨ (x = a ∧ y = c)) := by
    intro e x y he
    have hem : e ∈ H.E := he.1
    rw [hE] at hem
    obtain ⟨a, ha, hea⟩ := hem
    have hend := he.2.2.2
    rw [← hea, closure_sdiff_pair (hline a ha), hV, hinter a ha] at hend
    refine ⟨a, ha, hea.symm, ?_⟩
    exact pair_eq_pair_iff.mp hend.symm
  apply isGraphForest_of_star H.toGraph c
  · intro e x y he
    obtain ⟨a, ha, _, hends⟩ := hlinks he
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun heq => hcZ (heq ▸ ha), Or.inl rfl⟩
    · exact ⟨fun heq => hcZ (heq ▸ ha), Or.inr rfl⟩
  · intro x hxc e f y z he hf
    obtain ⟨a, ha, hea, hendsa⟩ := hlinks he
    obtain ⟨b, hb, hfb, hendsb⟩ := hlinks hf
    have hxa : x = a := hendsa.resolve_left (fun h => hxc h.1) |>.1
    have hxb : x = b := hendsb.resolve_left (fun h => hxc h.1) |>.1
    rw [hea, hfb, hxa.symm.trans hxb]

/-- A finite star of lines supplies a drawing with the stated support
and vertex set and with no circuits, for the feasibility forest of
XII (3.1), page 245. -/
theorem exists_forest_drawing_of_finite_star
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Z : Set S} (hZ : Z.Finite) (c : S) (L : S → Set S)
    (hline : ∀ a ∈ Z, IsLineWithEnds (L a) c a)
    (hmeet : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → L a ∩ L b = {c})
    (hcZ : c ∉ Z) :
    ∃ H : Drawing S, H.U = {c} ∪ ⋃ a ∈ Z, L a ∧ H.V = insert c Z ∧
      H.E = (fun a => L a \ {c, a}) '' Z ∧ IsGraphForest H.toGraph := by
  obtain ⟨H, hU, hV, hE⟩ := exists_drawing_of_finite_star hZ c L hline hmeet hcZ
  exact ⟨H, hU, hV, hE, isGraphForest_star_drawing c L hline hmeet hcZ H hV hE⟩

end GraphMinor.GM12

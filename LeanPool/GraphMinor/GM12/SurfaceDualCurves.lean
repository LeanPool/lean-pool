/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.ArcDrawings
public import LeanPool.GraphMinor.GM11.RadialExists
public import LeanPool.GraphMinor.GM12.Section4FiniteLineDrawing
import LeanPool.GraphMinor.Surface.Circle

/-!
# A drawing from finitely many lines and `O`-arcs

`exists_drawing_of_curves` is `exists_drawing_of_finite_lines` with loops allowed. The dual of a
drawing may have a loop, so we need this form.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Surface GM11 unitInterval

/-- An `O`-arc less one of its points is path connected. -/
theorem isPathConnected_oArc_sdiff {S : Type*} [TopologicalSpace S] {F : Set S}
    (hF : IsOArc F) {a : S} (ha : a ∈ F) : IsPathConnected (F \ {a}) :=
  hF.isPathConnected_sdiff_singleton ha

/-- The drawing on a single `O`-arc, with one vertex. -/
theorem exists_loop_drawing_E {S : Type*} [TopologicalSpace S] [T2Space S] {F : Set S}
    (hF : IsOArc F) {a : S} (ha : a ∈ F) :
    ∃ D : Drawing S, D.U = F ∧ D.V = {a} ∧ D.E = {F \ {a}} := by
  obtain ⟨D, hU, hV⟩ := exists_loop_drawing hF ha
  refine ⟨D, hU, hV, ?_⟩
  have hc := isPathConnected_oArc_sdiff hF ha
  change arcComponentsIn (D.U \ D.V) = _
  rw [hU, hV]
  apply subset_antisymm
  · rintro C ⟨-, hs, -, hmax⟩
    exact (hmax _ Subset.rfl hc hs).symm
  · rintro _ rfl
    exact ⟨hc.nonempty, Subset.rfl, hc, fun E hE _ hsub => subset_antisymm hE hsub⟩

/-- See the module docstring. Each curve is a line with two ends or an `O`-arc with one vertex,
which
`hone` says in a uniform way. -/
theorem exists_drawing_of_curves {S ι : Type*} [TopologicalSpace S] [T2Space S] {V : Set S}
    (hV : V.Finite) {E : Set ι} (hE : E.Finite) (L : ι → Set S) (u v : ι → S)
    (hone : ∀ i ∈ E, ∃ D : Drawing S, D.U = L i ∧ D.V = {u i, v i} ∧ D.E = {L i \ {u i, v i}})
    (hends : ∀ i ∈ E, L i ∩ V = {u i, v i})
    (hmeet : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → L i ∩ L j ⊆ V) :
    ∃ H : Drawing S, H.U = V ∪ ⋃ i ∈ E, L i ∧ H.V = V ∧
      H.E = (fun i => L i \ {u i, v i}) '' E := by
  revert hone hends hmeet
  induction E, hE using Set.Finite.induction_on with
  | empty =>
    intro _ _ _
    refine ⟨pointsDrawing hV, ?_, rfl, ?_⟩
    · change V = V ∪ ⋃ i ∈ (∅ : Set ι), L i
      simp
    · rw [pointsDrawing_E, image_empty]
  | @insert i E hi hE ih =>
    intro hone hends hmeet
    obtain ⟨H, hHU, hHV, hHE⟩ := ih (fun j hj => hone j (Or.inr hj))
      (fun j hj => hends j (Or.inr hj))
      (fun j hj k hk hjk => hmeet j (Or.inr hj) k (Or.inr hk) hjk)
    obtain ⟨K, hKU, hKV, hKE⟩ := hone i (Or.inl rfl)
    have hKiV : K.V ⊆ V := by
      rw [hKV, ← hends i (Or.inl rfl)]
      exact inter_subset_right
    have hglue : H.U ∩ K.U ⊆ H.V ∩ K.V := by
      rintro x ⟨hxH, hxK⟩
      have hxL : x ∈ L i := hKU ▸ hxK
      have hxV : x ∈ V := by
        rw [hHU] at hxH
        rcases hxH with hxV | hxH
        · exact hxV
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxH
          exact hmeet j (Or.inr hj) i (Or.inl rfl)
            (fun heq => hi (heq ▸ hj)) ⟨hxj, hxL⟩
      refine ⟨hHV.symm ▸ hxV, ?_⟩
      rw [hKV, ← hends i (Or.inl rfl)]
      exact ⟨hxL, hxV⟩
    refine ⟨H.glue K hglue, ?_, ?_, ?_⟩
    · change H.U ∪ K.U = _
      rw [hHU, hKU, biUnion_insert]
      ac_rfl
    · change H.V ∪ K.V = V
      rw [hHV]
      exact union_eq_left.mpr hKiV
    · rw [Drawing.glue_E, hHE, hKE, image_insert_eq, union_singleton]

end GraphMinor.GM12

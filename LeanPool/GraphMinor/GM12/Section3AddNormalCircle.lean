/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# Adding a normal circle to a drawing

In the one-cuff candidate-existence argument used by XII (3.1),
page 245, add the prescribed disc boundary to the drawing. Mark every
original vertex on the circle and one additional circle point. The
circle drawing then meets the original drawing only at common
vertices, so their union is a drawing. Any set normal to this union
is normal to the original drawing as well.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A normal circle can be added to a drawing without weakening
normality for the original drawing. -/
theorem exists_drawing_add_normal_oArc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) {F : Set S} (hF : IsOArc F) (hn : Γ.IsNormal F) :
    ∃ G : Drawing S, G.U = Γ.U ∪ F ∧
      ∀ X, G.IsNormal X → Γ.IsNormal X := by
  classical
  obtain ⟨e⟩ := hF
  let x := (e 1).val
  have hx : x ∈ F := (e 1).property
  let A := insert x (Γ.V ∩ F)
  have hA : A.Finite := (Γ.finite_V.subset inter_subset_left).insert x
  have hAF : A ⊆ F := by
    rintro z (rfl | hz)
    · exact hx
    · exact hz.2
  obtain ⟨D, hDU, hDV⟩ := exists_drawing_on_oArc ⟨e⟩ hA ⟨x, mem_insert x _⟩ hAF
  have hmeet : Γ.U ∩ D.U ⊆ Γ.V ∩ D.V := by
    intro z hz
    have hzF : z ∈ F := hDU ▸ hz.2
    have hzV := hn ⟨hzF, hz.1⟩
    exact ⟨hzV, hDV.symm ▸ (show z ∈ A from Or.inr ⟨hzV, hzF⟩)⟩
  let G := Γ.glue D hmeet
  refine ⟨G, ?_, ?_⟩
  · change Γ.U ∪ D.U = Γ.U ∪ F
    rw [hDU]
  · intro X hnX z hz
    have hzG : z ∈ G.U := Or.inl hz.2
    have hzV : z ∈ Γ.V ∪ D.V := hnX ⟨hz.1, hzG⟩
    rcases hzV with hzV | hzD
    · exact hzV
    · have hzF := hAF (hDV ▸ hzD)
      exact hn ⟨hzF, hz.2⟩

end GraphMinor.GM12

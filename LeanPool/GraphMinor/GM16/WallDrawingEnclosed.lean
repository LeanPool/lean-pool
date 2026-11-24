/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallRowsEnclosed
import LeanPool.GraphMinor.GM11.Walks

/-!
# The whole even wall is inside its enclosed disc

The row and side inclusions cover all coordinates of wall vertices
and all closed unit edge lines. The specified vertex and edge maps
of the sphere drawing therefore place its entire support in the
embedded enclosed disc. This makes the complementary disc empty
of drawing in its interior, as required for the outer face of
XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Topology Surface

/-- Every closed edge line of an even-height wall lies in its enclosed disc. -/
theorem sphereWall_line_subset_enclosed {θ : ℕ} (hθ : 2 ≤ θ) (hEven : Even θ)
    {e : Sym2 (Fin (2 * θ + 1) × Fin θ)} (he : e ∈ (sphereWallSimpleGraph θ).edgeSet) :
    rectangularGridLine e ⊆ wallEnclosedSet θ := by
  have heGrid := SimpleGraph.edgeSet_mono (sphereWallSimpleGraph_le_rectangular θ) he
  rcases rectangularGridLine_spec heGrid with ⟨k,l,hb,_,hLine⟩ | ⟨k,l,hb,heq,hLine⟩
  · rw [hLine]
    rintro p ⟨hx,hy⟩
    apply wall_horizontal_row_subset_enclosed hEven l.isLt
    have hTop : (k.val : ℝ)+1 ≤ 2*(θ : ℝ) := by
      exact_mod_cast (show k.val+1 ≤ 2 * θ by omega)
    exact ⟨⟨(Nat.cast_nonneg k.val).trans hx.1,hx.2.trans hTop⟩,hy⟩
  · have hParity : Even (k.val+l.val) := by
      rw [heq] at he
      have hAdj : (sphereWallSimpleGraph θ).Adj (k,l) (k,⟨l.val+1,hb⟩) := he
      rcases hAdj with ⟨hEq,_⟩ | ⟨_,hStep⟩
      · have h := congrArg Fin.val hEq
        simp only at h
        omega
      · rcases hStep with ⟨_,h⟩ | ⟨h,_⟩
        · exact h
        · simp only at h
          omega
    rw [hLine]
    exact wall_vertical_side_subset_enclosed hθ k.isLt hb hParity

/-- The coordinate sphere drawing of an even-height wall is contained
in the embedded disc enclosed by its brick rows. -/
theorem sphereWall_drawing_subset_enclosed {S : Type*} [TopologicalSpace S]
    {θ : ℕ} (hθ : 2 ≤ θ) (hEven : Even θ)
    (f : (ℝ × ℝ) → S) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val) :
    Γ.drawing.U ⊆ f '' wallEnclosedSet θ := by
  intro x hx
  rw [Γ.drawing.U_eq] at hx
  rcases hx with hx | hx
  · obtain ⟨v,hv⟩ := hV ▸ hx
    have hSource : rectangularGridPoint v ∈ wallEnclosedSet θ := by
      apply wall_horizontal_row_subset_enclosed hEven v.2.isLt
      have hi : (v.1.val : ℝ) ≤ 2*(θ : ℝ) := by
        exact_mod_cast (show v.1.val ≤ 2 * θ by omega)
      exact ⟨⟨Nat.cast_nonneg _,hi⟩,rfl⟩
    exact ⟨rectangularGridPoint v,hSource,hv⟩
  · obtain ⟨e,he,hxe⟩ := mem_iUnion₂.mp hx
    let e₀ : E(sphereWallGraph θ) := Γ.iso.edgeEquiv.symm ⟨e,he⟩
    have hmap : (Γ.iso.edgeEquiv e₀).val = e :=
      congrArg Subtype.val (Γ.iso.edgeEquiv.apply_symm_apply ⟨e,he⟩)
    have hxLine : x ∈ f '' rectangularGridLine e₀.val := by
      rw [← hE e₀,hmap]
      exact hxe
    exact image_mono (sphereWall_line_subset_enclosed hθ hEven e₀.property) hxLine

end GraphMinor.GM16

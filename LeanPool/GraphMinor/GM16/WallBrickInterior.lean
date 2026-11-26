/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
import Mathlib.Tactic.Linarith
import LeanPool.GraphMinor.GM11.Walks

/-!
# The interiors of the wall's bricks miss its drawing

The bounded faces of the wall in XVI (4.2), page 53, are rectangles
of width two and height one. Horizontal grid lines miss their interiors.
The only possible vertical line through an interior would be the
middle line, which the alternating parity rule deletes. These
coordinate checks supply the empty interiors used for the dials.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph

/-- No lattice vertex lies strictly between two consecutive horizontal
lattice lines. -/
theorem rectangularGridPoint_notMem_open_brick {m n : ℕ}
    (v : Fin m × Fin n) (i j : ℕ) :
    rectangularGridPoint v ∉ Ioo (i : ℝ) ((i : ℝ)+2) ×ˢ Ioo (j : ℝ) ((j : ℝ)+1) := by
  intro hv
  have hy : (j : ℝ) < (v.2.val : ℝ) ∧ (v.2.val : ℝ) < (j : ℝ)+1 := hv.2
  have h₁ : j < v.2.val := by exact_mod_cast hy.1
  have h₂ : v.2.val < j + 1 := by exact_mod_cast hy.2
  omega

/-- The closed line of a wall edge misses every brick interior whose
left bottom corner has even coordinate sum. -/
theorem sphereWall_edge_disjoint_open_brick {θ : ℕ}
    {e : Sym2 (Fin (2 * θ + 1) × Fin θ)} (he : e ∈ (sphereWallSimpleGraph θ).edgeSet)
    (i j : ℕ) (hEven : Even (i + j)) :
    Disjoint (rectangularGridLine e)
      (Ioo (i : ℝ) ((i : ℝ)+2) ×ˢ Ioo (j : ℝ) ((j : ℝ)+1)) := by
  apply Set.disjoint_left.mpr
  intro x hx hxB
  have heGrid : e ∈ (pathGraph (2 * θ + 1) □ pathGraph θ).edgeSet :=
    (SimpleGraph.edgeSet_mono (sphereWallSimpleGraph_le_rectangular θ)) he
  rcases rectangularGridLine_spec heGrid with ⟨k,l,_,_,hLine⟩ | ⟨k,l,hb,heq,hLine⟩
  · rw [hLine] at hx
    have hy : x.2 = (l.val : ℝ) := hx.2
    have h₁ : j < l.val := by exact_mod_cast (hy ▸ hxB.2.1)
    have h₂ : l.val < j + 1 := by exact_mod_cast (hy ▸ hxB.2.2)
    omega
  · rw [hLine] at hx
    have hxk : x.1 = (k.val : ℝ) := hx.1
    have h₁ : i < k.val := by exact_mod_cast (hxk ▸ hxB.1.1)
    have h₂ : k.val < i+2 := by exact_mod_cast (hxk ▸ hxB.1.2)
    have hk : k.val = i+1 := by omega
    have hl₁ : (l.val : ℝ) < (j : ℝ)+1 := lt_of_le_of_lt hx.2.1 hxB.2.2
    have hl₂ : (j : ℝ) < (l.val : ℝ)+1 := lt_of_lt_of_le hxB.2.1 hx.2.2
    have hl₁' : l.val < j + 1 := by exact_mod_cast hl₁
    have hl₂' : j < l.val+1 := by exact_mod_cast hl₂
    have hl : l.val = j := by omega
    rw [heq] at he
    have hAdj : (sphereWallSimpleGraph θ).Adj (k,l) (k,⟨l.val+1,hb⟩) := he
    have hEven' : Even (k.val+l.val) := by
      rcases hAdj with ⟨hEq,_⟩ | ⟨_,hStep⟩
      · have h := congrArg Fin.val hEq
        simp only at h
        omega
      · rcases hStep with ⟨_,h⟩ | ⟨h,_⟩
        · exact h
        · simp only at h
          omega
    obtain ⟨a,ha⟩ := hEven
    obtain ⟨b,hb⟩ := hEven'
    omega

/-- The open bricks miss the point set of the wall drawing, also after
embedding the coordinate plane in a sphere. -/
theorem sphereWall_drawing_disjoint_open_brick {S : Type*}
    [TopologicalSpace S] {θ : ℕ}
    (f : (ℝ × ℝ) → S) (hf : Function.Injective f)
    (Γ : GraphMinor.Surface.GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val =
      f '' rectangularGridLine e.val)
    (i j : ℕ) (hEven : Even (i + j)) :
    Disjoint Γ.drawing.U
      (f '' (Ioo (i : ℝ) ((i : ℝ)+2) ×ˢ Ioo (j : ℝ) ((j : ℝ)+1))) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨y,hy,hxy⟩
  rw [Γ.drawing.U_eq] at hx
  rcases hx with hx | hx
  · obtain ⟨v,hv⟩ := hV ▸ hx
    have heq : rectangularGridPoint v = y := hf (hv.trans hxy.symm)
    exact rectangularGridPoint_notMem_open_brick v i j (heq.symm ▸ hy)
  · obtain ⟨e,he,hxe⟩ := mem_iUnion₂.mp hx
    let e₀ : E(sphereWallGraph θ) := Γ.iso.edgeEquiv.symm ⟨e,he⟩
    have hmap : (Γ.iso.edgeEquiv e₀).val = e :=
      congrArg Subtype.val (Γ.iso.edgeEquiv.apply_symm_apply ⟨e,he⟩)
    have heLine : x ∈ f '' rectangularGridLine e₀.val := by
      rw [← hE e₀, hmap]
      exact hxe
    obtain ⟨z,hz,hzx⟩ := heLine
    have hzy : z = y := hf (hzx.trans hxy.symm)
    exact (Set.disjoint_left.mp (sphereWall_edge_disjoint_open_brick e₀.property i j hEven))
      hz (hzy.symm ▸ hy)

end GraphMinor.GM16

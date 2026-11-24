/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
import LeanPool.GraphMinor.GM11.Walks

/-!
# The retained lattice lines belong to the wall drawing

The graph isomorphism for the coordinate drawing identifies each
edge closure with its retained unit lattice line. In particular,
all horizontal lines and the even vertical lines belong to its
support. These are the sides of the closed brick faces in the
rigidity check for XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface

/-- Every horizontal unit line of the wall lies in its drawing. -/
theorem sphereWall_horizontal_line_subset_U {S : Type*} [TopologicalSpace S]
    {θ : ℕ} (f : (ℝ × ℝ) → S) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {i j : ℕ} (hi : i+1 < 2*θ+1) (hj : j < θ) :
    f '' horizontalLatticeLine i j ⊆ Γ.drawing.U := by
  let v : Fin (2*θ+1) × Fin θ := (⟨i,by omega⟩,⟨j,hj⟩)
  let w : Fin (2*θ+1) × Fin θ := (⟨i+1,hi⟩,⟨j,hj⟩)
  let e : E(sphereWallGraph θ) := ⟨s(v,w),Or.inl ⟨rfl,Or.inl rfl⟩⟩
  have hLine : rectangularGridLine e.val = horizontalLatticeLine i j := by
    change rectangularGridLinePair v w = _
    simp only [rectangularGridLinePair,v,w,ite_true,min_self]
    rw [min_eq_left (Nat.le_succ i)]
  have hSub := Γ.drawing.closure_subset_U (Γ.iso.edgeEquiv e).property
  rwa [hE e,hLine] at hSub

/-- A vertical unit line retained by the parity rule lies in the drawing. -/
theorem sphereWall_vertical_line_subset_U {S : Type*} [TopologicalSpace S]
    {θ : ℕ} (f : (ℝ × ℝ) → S) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {i j : ℕ} (hi : i < 2*θ+1) (hj : j+1 < θ) (hEven : Even (i+j)) :
    f '' verticalLatticeLine i j ⊆ Γ.drawing.U := by
  let v : Fin (2*θ+1) × Fin θ := (⟨i,hi⟩,⟨j,by omega⟩)
  let w : Fin (2*θ+1) × Fin θ := (⟨i,hi⟩,⟨j+1,hj⟩)
  let e : E(sphereWallGraph θ) := ⟨s(v,w),Or.inr ⟨rfl,Or.inl ⟨rfl,hEven⟩⟩⟩
  have hNe : v.2 ≠ w.2 := by
    intro he
    have h := congrArg Fin.val he
    change j = j+1 at h
    omega
  have hLine : rectangularGridLine e.val = verticalLatticeLine i j := by
    change rectangularGridLinePair v w = _
    rw [rectangularGridLinePair,ite_eq_right hNe]
    dsimp only [v,w]
    rw [min_self,min_eq_left (Nat.le_succ j)]
  have hSub := Γ.drawing.closure_subset_U (Γ.iso.edgeEquiv e).property
  rwa [hE e,hLine] at hSub

end GraphMinor.GM16

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallRigidDrawing
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM16.SubdivisionDrawing
import LeanPool.GraphMinor.GM16.WallSupportRigidity

/-!
# A rigid drawing of the wall subdivision

Draw the wall rigidly, then draw the replacing paths on its edge
closures and glue their isomorphisms. The support is unchanged,
so the proved face geometry also gives rigidity for the new
drawing. This supplies the rigidity and drawing assertion about
`N₄` in the last paragraph of XVI (4.2), page 54.
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM09 GM14
universe u v w

/-- A path system describing a subdivision of the even wall has a
rigid drawing in every sphere, with the branch centres explicitly mapped. -/
theorem exists_rigid_wall_subdivision_drawing
    {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ} (hθ : 4 ≤ θ) (hEven : Even θ)
    {N : Graph α β} (c : Fin (2 * θ + 1) × Fin θ → α) (hc : Function.Injective c)
    (P : (sphereWallSimpleGraph θ).edgeSet → Graph α β)
    (hPaths : ∀ e, ∃ a b, e.val = s(a, b) ∧ (sphereWallSimpleGraph θ).Adj a b ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a, c b})
    (hInter : ∀ e f, e ≠ f → Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c)
    (hVN : V(N) = range c ∪ ⋃ e, V(P e)) (hEN : E(N) = ⋃ e, E(P e)) :
    ∃ (f : (ℝ × ℝ) → S) (Γ : GraphDrawing N S), IsOpenEmbedding f ∧ IsRigid Γ.drawing ∧
      ∀ v (x : V(N)), x.val=c v → (Γ.iso.vertexEquiv x).val=f (rectangularGridPoint v) := by
  obtain ⟨f,Γ,hf,hV,hVertices,hEdges,_⟩ := exists_rigid_sphereWall_drawing hS hSphere hθ hEven
  obtain ⟨Γ',hU,hCentre⟩ := exists_subdivision_drawing c hc P hPaths hInter hVN hEN
    (sphereWall_no_isolated θ) Γ
  refine ⟨f,Γ',hf,sphereWall_same_support_isRigid hS hSphere hθ hEven f hf Γ hV hEdges hU,?_⟩
  intro v x hx
  exact (hCentre v x hx).trans (hVertices ⟨v,mem_univ _⟩)

end GraphMinor.GM16

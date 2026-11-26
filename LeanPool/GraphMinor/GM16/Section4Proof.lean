/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4
import LeanPool.GraphMinor.GM16.Section4Control
import LeanPool.GraphMinor.GM16.SubcubicSubdivision
import LeanPool.GraphMinor.GM16.WallSubdivisionRigidity
import LeanPool.GraphMinor.GM16.InducedTangleEdgePatterns
import LeanPool.GraphMinor.GM16.GraphDrawingControlledTangle
import LeanPool.GraphMinor.GM16.SphereRespectful
import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.GM11.PlaneFacts

/-!
# Graph Minors XVI (4.2): a sphere span

Increase the desired order to an even height at least four.
The row-defined wall tangle and the controlled grid minor give a
wall minor whose induced tangle is contained in the ambient one.
Replace its subcubic branch sets by centres and disjoint arms,
retaining the same chosen edges inside the subdivision subgraph.
Draw that subdivision rigidly on the sphere wall's support.
The identical chosen edge map compares the two induced tangles,
and transporting the subdivision tangle to its drawing gives the
required controlled respectful tangle and hence the sphere span.
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph Topology Surface GM10 GM14 GM15
universe u v w

/-- Graph Minors XVI, (4.2), pages 53–54. Every sufficiently high-order
graph tangle has a sphere span of the prescribed order. The wall,
subdivision, drawing, and induced-tangle steps of the paper are all
proved; the initial height is increased to an even value at least four. -/
theorem theorem_4_2_proof : GM16Theorem42Statement.{u,v,w} := by
  intro θ _hθ
  let height := 2*(θ+2)
  have hHeight : 4 ≤ height := by dsimp only [height]; omega
  have hEven : Even height := ⟨θ+2,by dsimp only [height]; omega⟩
  have hTwo : 2 ≤ height := by omega
  obtain ⟨θ₀,hθ₀,hWall⟩ := exists_conformal_wall_minor height hTwo
  refine ⟨θ₀+height,by omega,?_⟩
  intro α β G θG Tstar hT hOrder S _ _ hS hConn hSphere
  let : ConnectedSpace S := hConn
  have hHeightG : height ≤ θG := by omega
  obtain ⟨ηv,ηe,hModelG,KG,hVKG,hEKG,_,hImageG,_,_,hConformalG⟩ :=
    hWall G θG Tstar hT (by omega)
  obtain ⟨N,c,P,hNG,hcInj,_,hVN,hEN,hPaths,hInter,ηv',hModelN⟩ :=
    exists_subcubic_subdivision_with_minor hModelG (sphereWall_neighborSet_ncard_le_three height)
  have hNV : V(N).Finite := hT.finite_V.subset hNG.vertexSet_mono
  have hNE : E(N).Finite := hT.finite_E.subset hNG.edgeSet_mono
  let W := Hypergraph.ofGraph (sphereWallGraph height) (Set.toFinite _) (Set.toFinite _)
  obtain ⟨KN,hVKN,hEKN,_,hImageN,_,hTN₀⟩ := exists_model_induced_tangle
    (Set.toFinite _) (Set.toFinite _) hNV hNE hModelN hTwo (theorem_4_2_claim_1 hTwo)
  let TN := inducedTangle (Hypergraph.ofGraph N hNV hNE) (imageHypergraph ηv' ηe W)
    (imageHypergraphTangle ηv' ηe (sphereWallTangle height)) height
  have hTN : IsTangle (Hypergraph.ofGraph N hNV hNE) height TN := by
    simpa only [TN,W,sphereWallGraph,hImageN] using hTN₀
  have hChosen : ηe '' W.edgeSet ⊆ (Hypergraph.ofGraph N hNV hNE).edgeSet := by
    rintro e ⟨e₀,he₀,rfl⟩
    exact hModelN.edge_mem e₀ he₀
  have hConformalN : inducedTangle (Hypergraph.ofGraph G hT.finite_V hT.finite_E)
      (Hypergraph.ofGraph N hNV hNE) TN height ⊆ Tstar := by
    have hSub := inducedTangle_subset_of_same_edge_pattern W
      (Hypergraph.ofGraph G hT.finite_V hT.finite_E) (Hypergraph.ofGraph N hNV hNE)
      ηv ηv' ηe (sphereWallTangle height) height hChosen
    apply hSub.trans
    simpa only [hImageG] using hConformalG
  have hPathData (e : (sphereWallSimpleGraph height).edgeSet) :
      ∃ a b, e.val=s(a,b) ∧ (sphereWallSimpleGraph height).Adj a b ∧
        GM09.IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b} := by
    obtain ⟨a,b,he,ha,hp,_,hRange⟩ := hPaths e
    exact ⟨a,b,he,ha,hp,hRange⟩
  obtain ⟨_,Γ,_,hRigid,_⟩ := exists_rigid_wall_subdivision_drawing hS hSphere hHeight hEven
    c hcInj P hPathData hInter hVN hEN
  let v₀ : Fin (2*height+1) × Fin height := (⟨0,by omega⟩,⟨0,by omega⟩)
  let : Nonempty α := ⟨c v₀⟩
  let : Nonempty β := ⟨ηe s(v₀,v₀)⟩
  obtain ⟨η,T,_,hControl⟩ := exists_controlled_drawing_tangle hT hHeightG hNG hNV hNE Γ TN hTN
    hConformalN
  have hU : Γ.drawing.U.Nonempty := by
    have hv : c v₀ ∈ V(N) := hVN.symm ▸ Or.inl (mem_range_self v₀)
    exact ⟨(Γ.iso.vertexEquiv ⟨c v₀,hv⟩).val,
      Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨c v₀,hv⟩).property⟩
  have hRespectful : IsRespectfulDrawingTangle Γ.drawing height T :=
    ⟨⟨hConn,fun _ hr => isOpenDisc_region_of_isRigid hS hRigid hU hr⟩,
      hControl.isTangle_H,drawing_tangle_isRespectful_of_isSphere hS hSphere Γ.drawing
        hControl.isTangle_H⟩
  have hBd : bd S=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx (hS.2.2 x)
  refine ⟨Γ.drawing,η,height,T,?_,?_⟩
  · dsimp only [height]
    omega
  · exact ⟨IsClosedSurface.isSurface hS,hConn,hBd,hRigid,hRespectful,hControl⟩

end GraphMinor.GM16

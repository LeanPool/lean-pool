/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
import LeanPool.GraphMinor.GM16.Section9BattlefieldNeighborhood
import LeanPool.GraphMinor.GM16.Section9BattlefieldLinked
import LeanPool.GraphMinor.GM16.Section9InnerCapture
import LeanPool.GraphMinor.GM16.Section9Claim10
import LeanPool.GraphMinor.GM16.Section9NestedZones
import LeanPool.GraphMinor.GM16.AnnularComposition
import LeanPool.GraphMinor.GM16.RuralLinkage
import LeanPool.GraphMinor.GM16.ZoneBoundaryLinkage
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section88

import LeanPool.GraphMinor.GM09.Bridge

/-!
# The rural linkage in XVI (8.1), Claim (11)

Construct the rural battlefield annulus, prove its breadth and the
linkedness of the chosen boundary set, and compose it with the inner
society. Claim (10) supplies a disjoint outer-boundary linkage.
IX (10.5) replaces its boundary ends by the chosen free set. Counting
then gives a path avoiding the separator, with no other outer-boundary
vertex. All paths stay in the closed battlefield disc.
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The rural-linkage argument of XVI (8.1), Claim (11), page 74.
The path is contained in the closed battlefield disc and has exactly
one vertex on its outer boundary, as needed for the cleared drawing. -/
theorem section9_boundary_path_avoiding_separator
     (hS : IsClosedSurface S)
    {H C : Drawing S} {θ β κ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {y : S} {Λ M X Z : Set S}
    (hMet : HasTangleMetric H θ T d) (hy : y ∈ H.V)
    (hBattle : IsBattlefield H T d θ β {y} Λ C X)
    (hM : IsLambdaZoneAround H d (κ + 2) {y} M)
    (hCapture : ∀ a ∈ H.A, d {y} a < κ → a ⊆ M)
    (hκ : 3 ≤ κ) (hβ : κ + 3 ≤ β) (hθ : κ + (3 * β + 3) < θ)
    (hZ : Z.Finite) (hZκ : Z.ncard < κ) :
    ∃ b ∈ X, ∃ a ∈ H.V ∩ subBd M, ∃ P : Drawing S,
      P.IsPathBetween b a ∧ P.IsSubdrawing H ∧ P.U ⊆ closure Λ ∧
      P.V ∩ (H.V ∩ subBd Λ) = {b} ∧ Disjoint P.V Z := by
  classical
  obtain ⟨D₀, N, hD₀, hD₀D, hD₀bd, hNG, hΩ, hΩ₀, hRural, hBreadth⟩ :=
    section9_battlefield_neighborhood hS hBattle
  have hLinked := section9_battlefield_linked hS hBattle hD₀ hD₀D hD₀bd N hNG hΩ hΩ₀
  have hInt : discInt D₀ = interior D₀ := by
    change D₀ \ discBd D₀ = interior D₀
    rw [← IsClosedDisc.subBd_eq_discBd hS hD₀, subBd_eq_frontier, self_sdiff_frontier]
  have hfr₀ : frontier D₀ = C.U := by
    rw [← subBd_eq_frontier, IsClosedDisc.subBd_eq_discBd hS hD₀, hD₀bd]
  have hNG' : N.G = (H.interSet (closure Λ \ interior D₀)).toGraph := by
    simpa only [hInt] using hNG
  have hInner : N.Ω₀.bar = (H.interSet (closure Λ \ interior D₀)).V ∩ frontier D₀ := by
    simpa only [hInt, hfr₀] using hΩ₀
  obtain ⟨S_comp, S₀, hSG, hSΩ, hS₀G, hComp⟩ := exists_annular_composition H
    isClosed_closure hD₀.isCompact.isClosed hD₀D
    (hfr₀.symm ▸ IsCircuit.isOArc_U hBattle.circuit_and_paths.1)
    (hfr₀.symm ▸ hBattle.circuit_and_paths.2.1.U_subset) N hNG' hInner
  let Y := H.V ∩ subBd M
  have hCaptureInner : closure M ⊆ discInt D₀ := section9_zone_inside_inner_disc
    hS hBattle hD₀ hD₀D hD₀bd hM (by omega)
  have hYS₀ : Y ⊆ V(S₀.G) := by
    rw [hS₀G]
    intro v hv
    exact (mem_interSet_V_iff hD₀.isCompact.isClosed).mpr
      ⟨hv.1, (hCaptureInner hv.2.1).1⟩
  obtain ⟨P, hP, hDis⟩ := theorem_8_1_claim_10 hS hMet hy hBattle hM hCapture hκ hβ hθ
  have hYΛ : Y ⊆ Λ := fun _ hv => (section9_zone_inside_battlefield hBattle hM hβ) hv.2.1
  obtain ⟨Q, hQ, hQdis⟩ := linkage_inside_closed_zone hBattle.isZone hYΛ P hP hDis
  have hQ' : ∀ i, IsFromToPath S_comp.G (Q i) S_comp.Ω.bar Y := by
    intro i
    rw [hSG, hSΩ, hΩ]
    exact hQ i
  obtain ⟨R, hR, hRdis⟩ := rural_linkage_of_boundary_linkage S_comp S₀ N κ X Y
    hRural (hasBreadthGe_mono hBreadth (by omega)) hLinked
    (by rw [hBattle.isFree_X.2.1]; omega) hComp hYS₀ Q hQ' hQdis
  obtain ⟨b, hb, a, ha, R₀, hR₀, hR₀Z⟩ := rural_linkage_avoids_small_set R hR hRdis hZ hZκ
  have hRpath : IsGraphPathWithEnds (H.interSet (closure Λ)).toGraph R₀ b a := by
    rw [← hSG]
    exact hR₀.1
  obtain ⟨J, hJPath, hJSub, hJR⟩ := exists_drawing_of_graphPath hRpath
  refine ⟨b, hb, a, ha, J, hJPath, hJSub.trans interSet_isSub,
    fun _ hx => interSet_U_subset isClosed_closure (hJSub.U_subset hx), ?_, ?_⟩
  · change V(J.toGraph) ∩ (H.V ∩ subBd Λ) = {b}
    rw [hJR, ← hΩ, ← hSΩ]
    exact hR₀.2.1
  · change Disjoint V(J.toGraph) Z
    rw [hJR]
    exact hR₀Z

/-- Graph Minors XVI, proof of (8.1), Claim (11), page 74.
For the family of separated battlefields cleared in Section 9, the
path has exactly one vertex in the resulting cleared drawing. -/
theorem theorem_8_1_claim_11
     (hS : IsClosedSurface S)
    {H : Drawing S} {θ β κ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {Y : Set S} {y : S}
    {Λ : S → Set S} {C : S → Drawing S} {X : S → Set S} {M Z : Set S}
    (hMet : HasTangleMetric H θ T d) (hY : Y ⊆ H.V) (hy : y ∈ Y)
    (hBattle : ∀ z ∈ Y, IsBattlefield H T d θ β {z} (Λ z) (C z) (X z))
    (hSep : ∀ z ∈ Y, ∀ w ∈ Y, z ≠ w → 2 * (3 * β + 3) < d {z} {w})
    (hM : IsLambdaZoneAround H d (κ + 2) {y} M)
    (hCapture : ∀ a ∈ H.A, d {y} a < κ → a ⊆ M)
    (hκ : 3 ≤ κ) (hβ : κ + 3 ≤ β) (hθ : κ + (3 * β + 3) < θ)
    (hZ : Z.Finite) (hZκ : Z.ncard < κ) :
    ∃ b ∈ X y, ∃ a ∈ H.V ∩ subBd M, ∃ P : Drawing S,
      P.IsPathBetween b a ∧ P.IsSubdrawing H ∧
      P.V ∩ (clearEnvelopeDrawing H Y Λ).V = {b} ∧ Disjoint P.V Z := by
  obtain ⟨b, hb, a, ha, P, hPath, hPH, hPU, hOuter, hPZ⟩ :=
    section9_boundary_path_avoiding_separator hS hMet (hY hy) (hBattle y hy)
      hM hCapture hκ hβ hθ hZ hZκ
  have hZone := fun z hz => (hBattle z hz).isZone
  obtain ⟨_, _, _, hSymm, hTri, _⟩ :=
    GM11.gm15_theorem_9_1 H θ T d hS inferInstance hMet
  have hdis : ∀ z ∈ Y, ∀ w ∈ Y, z ≠ w →
      Disjoint (closure (Λ z)) (closure (Λ w)) := by
    intro z hz w hw hzw
    exact section9_disjoint_zones (hZone z hz) (hZone w hw) hSymm hTri
      (Nat.le_refl _) (hSep z hz w hw hzw)
  have hbOuter := (hBattle y hy).isFree_X.1 hb
  have hbU : b ∈ (clearEnvelopeDrawing H Y Λ).U :=
    zone_boundary_subset_clearFamily hZone hdis hy hbOuter.2
  have hbOut : b ∉ ⋃ z ∈ Y, Λ z := (clearFamily_U hZone ▸ hbU).2
  have hClosed : IsClosed (univ \ ⋃ z ∈ Y, Λ z) :=
    isClosed_univ.sdiff (isOpen_iUnion fun z => isOpen_iUnion fun hz =>
      (hZone z hz).isOpenDisc.1)
  have hbV : b ∈ (clearEnvelopeDrawing H Y Λ).V :=
    (mem_interSet_V_iff hClosed).mpr ⟨hbOuter.1, mem_univ _, hbOut⟩
  refine ⟨b, hb, a, ha, P, hPath, hPH, ?_, hPZ⟩
  apply subset_antisymm
  · rintro v ⟨hvP, hvClear⟩
    have hvU := (clearEnvelopeDrawing H Y Λ).V_subset_U hvClear
    have hvOld := (clearFamily_U hZone ▸ hvU).1
    have hvOut := (clearFamily_U hZone ▸ hvU).2
    have hvNot : v ∉ Λ y := fun h => hvOut (mem_iUnion₂.mpr ⟨y, hy, h⟩)
    have hvBd : v ∈ subBd (Λ y) :=
      ⟨hPU (P.V_subset_U hvP), subset_closure ⟨mem_univ _, hvNot⟩⟩
    have hvH : v ∈ H.V := (interSet_isSub (Γ := H)).1 hvClear
    exact hOuter ▸ ⟨hvP, hvH, hvBd⟩
  · rintro v rfl
    exact ⟨(graphPath_of_drawingPath hPH hPath).left_mem, hbV⟩

end GraphMinor.GM16

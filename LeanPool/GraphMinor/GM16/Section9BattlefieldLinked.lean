/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM16.AnnularPathTrim
import LeanPool.GraphMinor.GM16.LineBoundarySide
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM09.Basic

/-!
# The battlefield boundary set is linked in its annulus

Trim each of the disjoint battlefield paths at its last inner-circle
vertex. The original path stays in the closed battlefield disc because
it meets the outer boundary only at its outer end. Its trimmed path
stays outside the inner disc and meets each boundary just once. Thus
these paths witness linkedness for IX (10.5), as used in XVI (8.1),
Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- The disjoint paths in a battlefield witness linkedness of its
chosen outer set in the annular neighborhood of XVI (8.1), Claim (11). -/
theorem section9_battlefield_linked (hS : IsClosedSurface S)
    {H C : Drawing S} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ β : ℕ} {z Λ X D₀ : Set S}
    (hB : IsBattlefield H T d θ β z Λ C X)
    (hD₀ : IsClosedDisc D₀) (hD₀D : D₀ ⊆ closure Λ) (hD₀bd : discBd D₀ = C.U)
    (N : Neighborhood S (Set S))
    (hG : N.G = (H.interSet (closure Λ \ discInt D₀)).toGraph)
    (hΩ : N.Ω.bar = H.V ∩ subBd Λ)
    (hΩ₀ : N.Ω₀.bar = (H.interSet (closure Λ \ discInt D₀)).V ∩ C.U) :
    N.IsLinked X := by
  classical
  let Q := H.interSet (closure Λ \ discInt D₀)
  have hInt : discInt D₀ = interior D₀ := by
    change D₀ \ discBd D₀ = interior D₀
    rw [← IsClosedDisc.subBd_eq_discBd hS hD₀, subBd_eq_frontier, self_sdiff_frontier]
  have hfr₀ : frontier D₀ = C.U := by
    rw [← subBd_eq_frontier, IsClosedDisc.subBd_eq_discBd hS hD₀, hD₀bd]
  have hfr : frontier (closure Λ) = subBd Λ := by
    rw [← subBd_eq_frontier]
    exact subBd_closure_eq_subBd_of_isOpenDisc hS hB.isZone.isOpenDisc
      hB.isZone.isOArc_bd hB.isZone.isClosedDisc_closure
  have hΛdis := (isOpen_disjoint_subBd_and_closure_eq hB.isZone.isOpenDisc.1).1
  have hOut : ∀ v ∈ X, v ∉ D₀ := by
    intro v hv hvD
    have hvbd := (hB.isFree_X.1 hv).2
    have hvni : v ∉ interior (closure Λ) := (hfr.symm ▸ hvbd).2
    have hvn₀ : v ∉ interior D₀ := fun hi => hvni (interior_mono hD₀D hi)
    have hvfr : v ∈ frontier D₀ := ⟨subset_closure hvD, hvn₀⟩
    exact hΛdis.notMem_of_mem_left
      (hB.circuit_and_paths.2.2.1 (hfr₀ ▸ hvfr)) hvbd
  obtain ⟨P, hP, hDis⟩ := hB.circuit_and_paths.2.2.2
  choose a ha b hb hPath hPH hBoundary using hP
  have hInside (i : Fin β) : (P i).U ⊆ closure Λ := by
    have haΛ := hB.circuit_and_paths.2.2.1 (C.V_subset_U (ha i))
    have hbBd := (hB.isFree_X.1 (hb i)).2
    have hab : a i ≠ b i := fun heq =>
      hΛdis.notMem_of_mem_left (heq ▸ haΛ) hbBd
    apply line_subset_closed_of_boundary_end isClosed_closure
      (GM11.isLine_of_isPathBetween (hPath i) hab) (subset_closure haΛ) hab hbBd.1
    intro x hx
    exact (hBoundary i ▸ (show x ∈ (P i).U ∩ (H.U ∩ subBd Λ) from
      ⟨hx.1, (hPH i).U_subset hx.1, hfr ▸ hx.2⟩))
  have hTrim (i : Fin β) := exists_annular_terminal_path
    hB.circuit_and_paths.2.1 (hPH i) (hPath i) (ha i)
    hD₀.isCompact.isClosed hfr₀ (hOut (b i) (hb i)) (hInside i)
  choose c hc J hJPath hJP hJU hJVC hJUC using hTrim
  have hJQ (i : Fin β) : (J i).IsSubdrawing Q := by
    apply subdrawing_interSet_of_U_subset ((hJP i).trans (hPH i))
    rw [hInt]
    exact hJU i
  have hJG (i : Fin β) : IsGraphPathWithEnds N.G (J i).toGraph (b i) (c i) := by
    rw [hG]
    exact graphPath_of_drawingPath (hJQ i) (hJPath i)
  constructor
  · exact hΩ.symm ▸ hB.isFree_X.1
  · rw [hB.isFree_X.2.1]
    refine ⟨fun i => (J i).toGraph, ?_, ?_⟩
    · intro i
      refine ⟨b i, hb i, c i, ?_, hJG i, ?_, ?_⟩
      · rw [hΩ₀]
        exact ⟨(hJQ i).1 (hJG i).right_mem, C.V_subset_U (hc i)⟩
      · rw [hΩ]
        apply subset_antisymm
        · rintro x ⟨hxJ, hxH, hxbd⟩
          have hxP := (hJP i).U_subset ((J i).V_subset_U hxJ)
          exact hBoundary i ▸ ⟨hxP, hxH |> H.V_subset_U, hxbd⟩
        · rintro x rfl
          exact ⟨(hJG i).left_mem, hB.isFree_X.1 (hb i)⟩
      · rw [hΩ₀]
        apply subset_antisymm
        · rintro x ⟨hxJ, _, hxC⟩
          exact hJUC i ▸ ⟨(J i).V_subset_U hxJ, hxC⟩
        · rintro x rfl
          exact ⟨(hJG i).right_mem, (hJQ i).1 (hJG i).right_mem, C.V_subset_U (hc i)⟩
    · intro i j hij
      exact (hDis hij).mono (hJP i).1 (hJP j).1

end GraphMinor.GM16

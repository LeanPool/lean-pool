/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# Drawing a nest in a rural presentation

Disjoint circuits bounding nested closed discs give a nest in the
plane presentation obtained by transporting the enclosing disc.
This identifies the geometric nest in XVI (8.1), Claim (11), with
the breadth required by IX (10.5).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11
universe u
variable {S : Type u} [TopologicalSpace S]

/-- Nested discs bounded by disjoint subdrawing circuits witness
breadth in the transported presentation. -/
theorem hasBreadthGe_of_drawing_nest {N : Neighborhood S (Set S)}
    (P : Presentation N) (Q : Drawing S) (hG : N.G = Q.toGraph)
    {D D₀ : Set S} {f : S → EuclideanPlane}
    (hΔ : P.Δ = f '' D) (hΔ₀ : P.Δ₀ = f '' D₀)
    (hdisc : ∀ E ⊆ D, IsClosedDisc E →
      IsClosedDisc (f '' E) ∧ subBd (f '' E) = f '' discBd E)
    (hpoints : ∀ J : Drawing S, J.IsSubdrawing Q →
      graphDrawingSubgraphU P.Γ J.toGraph = f '' J.U)
    {s : ℕ} (K : Fin s → Drawing S) (E : Fin s → Set S)
    (hK : ∀ i, (K i).IsSubdrawing Q ∧ (K i).IsCircuit)
    (hDis : Pairwise (fun i j => Disjoint (K i).U (K j).U))
    (hE : ∀ i, IsClosedDisc (E i) ∧ discBd (E i) = (K i).U ∧ D₀ ⊆ E i ∧ E i ⊆ D)
    (hNest : ∀ i j, i ≤ j → E i ⊆ E j) : N.HasBreadthGe s := by
  refine ⟨P, fun i => (K i).toGraph, ?_, ?_, fun i => f '' E i, ?_, ?_, ?_⟩
  · intro i
    rw [hG]
    refine ⟨⟨(hK i).1.1, ?_⟩, (hK i).2⟩
    intro e x y hl
    exact ((hK i).1.isLink_iff hl.1).mp hl
  · intro i j hij
    exact (hDis hij).mono (K i).V_subset_U (K j).V_subset_U
  · intro i
    obtain ⟨hEi, hBd, _, hED⟩ := hE i
    obtain ⟨hFi, hFb⟩ := hdisc (E i) hED hEi
    refine ⟨hFi, ?_⟩
    change subBd (f '' E i) = graphDrawingSubgraphU P.Γ (K i).toGraph
    rw [hFb, hBd, hpoints (K i) (hK i).1]
  · intro i
    rw [hΔ₀, hΔ]
    exact ⟨image_mono (hE i).2.2.1, image_mono (hE i).2.2.2⟩
  · intro i j hij
    exact image_mono (hNest i j hij)

end GraphMinor.GM16

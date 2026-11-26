/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9AnnularSeparation
import LeanPool.GraphMinor.GM16.Section9NoAnnularSeparation
import LeanPool.GraphMinor.GM16.Section9NestedZones
import LeanPool.GraphMinor.GM16.DrawingSkeletonPaths
import LeanPool.GraphMinor.Menger.Basic

/-!
# Claim (10) in the proof of XVI (8.1)

Apply Menger between the inner and outer boundary vertices. A smaller
separator can be moved into the annulus without increasing its order.
The radial boundary argument then produces the short circuit ruled
out in Claim (10). Lift Menger's skeleton paths back to subdrawings.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Graph Minors XVI, proof of (8.1), Claim (10), page 73.
There are `κ` mutually disjoint paths of `H` between the two zone
boundaries. The planar Menger duality step is supplied by the proved
annular separation and radial boundary lemmas. -/
theorem theorem_8_1_claim_10 (hS : IsClosedSurface S)
    {H C : Drawing S} {θ β κ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {y : S} {Λ M X : Set S}
    (hMet : HasTangleMetric H θ T d) (hy : y ∈ H.V)
    (hBattle : IsBattlefield H T d θ β {y} Λ C X)
    (hM : IsLambdaZoneAround H d (κ + 2) {y} M)
    (hCapture : ∀ a ∈ H.A, d {y} a < κ → a ⊆ M)
    (hκ : 3 ≤ κ) (hβ : κ + 3 ≤ β) (hθ : κ + (3 * β + 3) < θ) :
    ∃ P : Fin κ → Drawing S,
      (∀ i, ∃ u ∈ H.V ∩ subBd M, ∃ v ∈ H.V ∩ subBd Λ,
        (P i).IsPathBetween u v ∧ (P i).IsSubdrawing H) ∧
      Pairwise (fun i j => Disjoint (P i).V (P j).V) := by
  have hNest : closure M ⊆ Λ := section9_zone_inside_battlefield hBattle hM hβ
  have hCriterion : ∀ A B : Hypergraph S (Set S), H.toHypergraph.IsSeparation A B →
      H.V ∩ subBd M ⊆ A.vertexSet → H.V ∩ subBd Λ ⊆ B.vertexSet →
      κ ≤ Hypergraph.separationOrder A B := by
    intro A B hSep hInner hOuter
    by_contra hsmall
    obtain ⟨A', B', hSep', hOrder', hEdgesOuter, hEdgesInner⟩ :=
      exists_annular_separation hBattle.isZone hM hNest hSep hInner hOuter
    exact section9_no_annular_separation hS hMet hy hBattle.isZone hM hCapture hκ hθ hSep'
      (lt_of_le_of_lt hOrder' (Nat.lt_of_not_ge hsmall)) hEdgesOuter hEdgesInner
  obtain ⟨p, hDis⟩ := (GraphMinor.menger H.toHypergraph (H.V ∩ subBd M) (H.V ∩ subBd Λ)
    inter_subset_left inter_subset_left κ).mp hCriterion
  have hex : ∀ i : Fin κ, ∃ P : Drawing S,
      P.IsPathBetween (p i).first (p i).last ∧ P.IsSubdrawing H ∧
      P.V = {x | x ∈ (p i).walk.support} := by
    intro i
    exact drawing_path_of_skeleton_path (p i).first_mem.1 (p i).walk (p i).isPath
  choose P hP using hex
  refine ⟨P, fun i => ⟨(p i).first, (p i).first_mem, (p i).last, (p i).last_mem,
    (hP i).1, (hP i).2.1⟩, ?_⟩
  intro i j hij
  rw [(hP i).2.2, (hP j).2.2]
  exact hDis hij

end GraphMinor.GM16

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ClippedHalfEdges
public import LeanPool.GraphMinor.GM12.Section4ResidualStarDiscs

/-!
# Feasible endpoint classes from a crossing half-edge system

For XII (4.5), claim (1), page 253, clip the source half-edges
outside the crossing discs and thicken each vertex star. The
contacts of each resulting vertex disc are exactly the ends
assigned to that vertex. Ends of different residual half-edges
are distinct, since the residual arcs are disjoint. This gives
the source endpoint partition together with its disc witnesses.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A half-edge system meeting only at its source vertices or
inside the crossing-disc set yields disjoint vertex discs whose
contacts are exactly the assigned, distinct half-edge ends.
This combines the source clipping and thickening steps of
XII (4.5), claim (1), page 253. -/
theorem exists_halfedge_contact_discs
    {S V ι : Type} [TopologicalSpace S] [T2Space S] [NormalSpace S] [ConnectedSpace S]
    [Finite V] [Finite ι]
    (hS : IsClosedSurface S) (v : V → S) (hinj : Function.Injective v)
    (owner : ι → V) (x : ι → S) (L : ι → Set S)
    (hL : ∀ i, IsLineWithEnds (L i) (v (owner i)) (x i))
    (hLV : ∀ i w, v w ∈ L i → w = owner i)
    (hLL : ∀ i j, i ≠ j → L i ∩ L j ⊆ range v ∪ range x)
    (Z : Set S) (hZ : IsClosed Z) (hvZ : ∀ w, v w ∉ Z)
    (hxZ : ∀ i, x i ∈ interior Z) :
    ∃ q : ι → S, Function.Injective q ∧ (∀ i, q i ∈ L i ∩ frontier Z) ∧
      ∃ D : V → Set S, (∀ w, IsClosedDisc (D w)) ∧
        (∀ w z, w ≠ z → Disjoint (D w) (D z)) ∧
        ∀ w, D w ∩ Z = {z | ∃ i, owner i = w ∧ q i = z} := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite ι
  obtain ⟨A, b, hA, hAA, hAZ, hb, hbb, hb0, hb1, hcontact, hsub, hfront⟩ :=
    exists_clipped_halfedge_family hS v hinj owner x L hL hLV hLL Z hZ hvZ hxZ
  obtain ⟨D, hD, hDD, -, hDZ⟩ := exists_residual_star_discs hS A owner b Z hA hAA hZ hAZ
    hb hbb hb0 hb1 hcontact
  have hq : Function.Injective (fun i => b i 1) := by
    intro i j hij
    by_contra hne
    exact disjoint_left.mp (hbb i j hne) (mem_range_self 1)
      ⟨1, hij.symm⟩
  exact ⟨(fun i => b i 1), hq, (fun i => ⟨hsub i (mem_range_self 1), hfront i⟩), D, hD, hDD, hDZ⟩

end GraphMinor.GM12

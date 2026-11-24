/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.EdgeSides
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Vertex discs avoiding the other residual half-edges

For XII (4.5), claim (1), page 253, choose small disjoint discs
at the source vertices before clipping the edge halves. Each
disc avoids the crossing-disc set and every half-edge whose
vertex owner is different. These are finitely many closed sets
missing its centre, so a small disc can be chosen in their
complement.
-/

public section

namespace GraphMinor.GM12

open Set Surface Topology

/-- Small source vertex discs can avoid a prescribed closed set
and all half-edge arcs owned by other vertices. This is the
vertex-neighborhood choice for XII (4.5), claim (1), page 253. -/
theorem exists_crossing_vertex_disc_family
    {S V ι : Type*} [TopologicalSpace S] [T2Space S] [Finite V] [Finite ι]
    (hS : IsClosedSurface S) (v : V → S) (hinj : Function.Injective v)
    (owner : ι → V) (L : ι → Set S) (hL : ∀ i, IsClosed (L i))
    (hLV : ∀ i w, v w ∈ L i → w = owner i)
    (Z : Set S) (hZ : IsClosed Z) (hvZ : ∀ w, v w ∉ Z) :
    ∃ A : V → Set S, (∀ w, IsClosedDisc (A w) ∧ v w ∈ interior (A w)) ∧
      (∀ w z, w ≠ z → Disjoint (A w) (A z)) ∧
      (∀ w, Disjoint (A w) Z) ∧
      ∀ w i, w ≠ owner i → Disjoint (A w) (L i) := by
  classical
  let vertexFintype := Fintype.ofFinite V
  let indexFintype := Fintype.ofFinite ι
  obtain ⟨U, hU, hUU⟩ := (finite_range v).t2_separation
  let C := fun w => Z ∪ ⋃ i, if w = owner i then ∅ else L i
  have hC : ∀ w, IsClosed (C w) := by
    intro w
    apply hZ.union
    apply isClosed_iUnion_of_finite
    intro i
    split_ifs <;> first | exact isClosed_empty | exact hL i
  have hvC : ∀ w, v w ∉ C w := by
    intro w hw
    rcases hw with hz | hlines
    · exact hvZ w hz
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hlines
      by_cases hwi : w = owner i
      · simp only [hwi, ↓reduceIte, mem_empty_iff_false] at hi
      · have hvL : v w ∈ L i := by simpa only [hwi, ↓reduceIte] using hi
        exact hwi (hLV i w hvL)
  have hex : ∀ w, ∃ A : Set S, IsClosedDisc A ∧ v w ∈ interior A ∧ A ⊆ U (v w) ∩ (C w)ᶜ := by
    intro w
    obtain ⟨A, A', hd, ho, hp, hsub, hAU, -⟩ := GM11.exists_closedDisc_nbhd hS
      ((hU (v w)).2.inter (hC w).isOpen_compl) ⟨(hU (v w)).1, hvC w⟩
    exact ⟨A, hd, mem_interior.mpr ⟨A', hsub, ho, hp⟩, hAU⟩
  choose A hA hvA hsub using hex
  refine ⟨A, (fun w => ⟨hA w, hvA w⟩), ?_, ?_, ?_⟩
  · intro w z hwz
    exact (hUU (mem_range_self w) (mem_range_self z) (fun h => hwz (hinj h))).mono
      (fun x hx => (hsub w hx).1) (fun x hx => (hsub z hx).1)
  · intro w
    exact disjoint_left.mpr (fun x hx hz => (hsub w hx).2 (Or.inl hz))
  · intro w i hwi
    apply disjoint_left.mpr
    intro x hx hxi
    apply (hsub w hx).2
    exact Or.inr (mem_iUnion.mpr ⟨i, by simpa only [hwi, ↓reduceIte] using hxi⟩)

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RegionWalk
import LeanPool.GraphMinor.GM12.Section4SplitDrawing

/-!
# Branch sets recovering a subdivided drawing

The replacement in XII (4.3), page 249, must contain the original
graph as a minor. After subdividing each edge, contract its right
half. The branch at an original vertex consists of that vertex
and the midpoints whose right end is this vertex. Midpoints lie
in distinct original edges and never in the original vertex set,
so these branches are disjoint.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The branch obtained by contracting the right half of each
subdivided edge, in the target replacement of XII (4.3), page 249. -/
@[expose] def splitBranch {S : Type*} [TopologicalSpace S] (Γ : Drawing S)
    (m y : Set S → S) (v : S) : Set S :=
  insert v (m '' {e ∈ Γ.E | y e = v})

/-- An original vertex belongs only to its own subdivision branch. -/
theorem mem_splitBranch_of_original_vertex_iff
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) {v z : S} (hz : z ∈ Γ.V) :
    z ∈ splitBranch Γ m y v ↔ z = v := by
  constructor
  · rintro (hzv | ⟨e, ⟨he, _⟩, hme⟩)
    · exact hzv
    · exact False.elim (hd.mid_notMem he (hme.symm ▸ hz))
  · intro hzv
    exact Or.inl hzv

/-- A midpoint belongs to the branch of its original right end. -/
theorem mem_splitBranch_of_midpoint_iff
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) {v : S} (hv : v ∈ Γ.V)
    {e : Set S} (he : e ∈ Γ.E) :
    m e ∈ splitBranch Γ m y v ↔ y e = v := by
  constructor
  · rintro (hmev | ⟨f, ⟨hf, hyv⟩, hmfe⟩)
    · exact False.elim (hd.mid_notMem he (hmev ▸ hv))
    · have hfe : f = e := hd.mid_inj hf he hmfe
      exact hfe ▸ hyv
  · intro hyv
    exact Or.inr ⟨e, ⟨he, hyv⟩, rfl⟩

/-- Every subdivision branch consists of vertices of the subdivided drawing. -/
theorem splitBranch_subset_vertices
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) {v : S} (hv : v ∈ Γ.V) :
    splitBranch Γ m y v ⊆ H.V := by
  rintro z (hzv | ⟨e, ⟨he, _⟩, hme⟩)
  · exact hzv ▸ hd.V_sub hv
  · exact hme ▸ hd.mid_V₂ he

/-- Distinct original vertices have disjoint subdivision branches. -/
theorem splitBranch_disjoint
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) {v w : S} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V)
    (hvw : v ≠ w) : Disjoint (splitBranch Γ m y v) (splitBranch Γ m y w) := by
  apply Set.disjoint_left.mpr
  intro z hzv hzw
  rcases hzv with hzv | ⟨e, ⟨he, hye⟩, hme⟩
  · have hzΓ : z ∈ Γ.V := hzv ▸ hv
    exact hvw (hzv.symm.trans ((mem_splitBranch_of_original_vertex_iff hd hzΓ).mp hzw))
  · have hmid : m e ∈ splitBranch Γ m y w := hme.symm ▸ hzw
    have hye' := (mem_splitBranch_of_midpoint_iff hd hw he).mp hmid
    exact hvw (hye.symm.trans hye')

/-- No right half of a subdivided edge is one of the chosen left halves. -/
theorem split_right_notMem_left_image
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) {e : Set S} (he : e ∈ Γ.E) : B e ∉ A '' Γ.E := by
  rintro ⟨f, hf, hAB⟩
  have hfe : f = e := hd.edge_of_piece hf he (Or.inr (Or.inl hAB))
  subst f
  exact hd.ne_AB he hAB

end GraphMinor.GM12

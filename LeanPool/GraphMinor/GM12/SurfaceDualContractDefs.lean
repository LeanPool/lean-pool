/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDual
public import LeanPool.GraphMinor.GM12.Section76

/-!
# The setting of the contracted dual in Case 2 of XII (7.5)

The structures for `exists_contracted_dual`, in `SurfaceDualContract.lean`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The vertex `v` with the closures of the edges of `K` at `v`. -/
def radialStar (K : Drawing S) (v : S) : Set S :=
  {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e

/-- The part of the conclusion of `exists_supported_radial_star_contraction` that we use. The map
`f`
collapses the star of `v` in `K` to `v`, and it fixes all points off the interior of a closed disc
`D`
in the region `r`. The drawing `H` is the image of `K`, and `J` is a subdrawing of `H` on the same
vertices. -/
structure IsStarContraction (K : Drawing S) (v : S) (r D : Set S) (f : C(S, S)) (H J : Drawing S) :
    Prop where
  disc : IsClosedDisc D
  sub : D ⊆ r
  fix : ∀ x ∉ discInt D, f x = x
  collapse : ∀ x ∈ radialStar K v, f x = v
  fibre : ∀ x y, f x = f y ↔ x = y ∨ x ∈ radialStar K v ∧ y ∈ radialStar K v
  H_U : H.U = f '' K.U
  H_V : H.V = f '' K.V
  J_sub : J.IsSubdrawing H
  J_V : J.V = H.V

/-- The conclusion of `exists_contracted_dual`, for `Z = V(Γ) ∩ (rBar - r)` and `Γ₂ = Γ₁ \ r*`. The
first
four fields say what `Γ₃` is. The others give the correspondence between atoms that the end of Case
2
uses: an edge `e` of `Γ` off `Z` is fixed by `f`, an edge `e` not in `rBar - r` lies with some edge
of
`Γ₂` in one region of `K`, and its image lies with that edge in one region of `J`, a region of `Γ₁`
around a vertex off `Z` is a region of `Γ₂`, an edge off `Z` is not in `rBar - r`, a vertex in `Z`
is sent
to `v`, and the duals of the atoms
of `rBar - r` are incident with `v`. -/
structure IsContractedDual (Γ Γ₁ K J : Drawing S) (f : C(S, S)) (r : Set S) (v : S)
  (Γ₃ : Drawing S) :
    Prop where
  radial : (PaintingOrDrawing.drawing Γ₃).IsRadialDrawing J
  nonempty_E : Γ₃.E.Nonempty
  V_eq : Γ₃.V = (Γ.V \ (closure r \ r)) ∪ {v}
  delete_eq : deleteVertices Γ₃ {v} = deleteVertices Γ (Γ.V ∩ (closure r \ r))
  E_eq : Γ₃.E = (fun e => f '' e) '' {e ∈ Γ.E | ¬ e ⊆ closure r \ r}
  fixed : ∀ e ∈ Γ.E, Disjoint (closure e ∩ Γ.V) (closure r \ r) → f '' e = e
  edge_corr : ∀ e ∈ Γ.E, ¬ e ⊆ closure r \ r → ∃ g ∈ (deleteVertices Γ₁ {v}).E,
    (∃ s ∈ K.R, e ⊆ s ∧ g ⊆ s) ∧ ∃ s ∈ J.R, f '' e ⊆ s ∧ g ⊆ s
  vertex_corr : ∀ w ∈ Γ.V \ (closure r \ r), ∀ t ∈ Γ₁.R, w ∈ t → t ∈ (deleteVertices Γ₁ {v}).R
  not_sub : ∀ e ∈ Γ.E, Disjoint (closure e ∩ Γ.V) (closure r \ r) → ¬ e ⊆ closure r \ r
  collapse : ∀ u ∈ Γ.V, u ∈ closure r → f u = v
  edge_bd : ∀ e ∈ Γ.E, e ⊆ closure r \ r →
    ∃ g ∈ Γ₁.E, v ∈ closure g ∧ ∃ s ∈ K.R, e ⊆ s ∧ g ⊆ s
  vertex_bd : ∀ u ∈ Γ.V, u ∈ closure r → ∀ t ∈ Γ₁.R, u ∈ t → v ∈ closure t

end GraphMinor.GM12

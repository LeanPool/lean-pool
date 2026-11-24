/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM14.Section6a
public import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# The form of (8.4)

`Theorem84DiscStatement` is the statement of XIV (8.4), with the cylinder given as a difference of
discs. `theorem_8_4` in `Section8.lean` proves it.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11

universe u v w

/-- Graph Minors XIV, (8.4) (pages 41–42), with the cylinder as a difference of discs.

The cylinder `Σ` is `D \ discInt D₂`, for closed discs `D₂ ⊆ D` of a connected closed surface `S`,
with `F₁ = discBd D` and `F₂ = discBd D₂`. The circuits `C₁, C₂` bound closed discs `E₁, E₂`, with
`D₂ ⊆ E₂`, `E₂ ⊆ E₁ \ C₁.U` and `E₁ ⊆ D`. So the component of `Σ - U(C₁)` that includes `U(C₂)` is
the part of `E₁ \ C₁.U` in `Σ`. That `H` is a rigid drawing in `Σ` is `IsRigidIn H Σ`, and every
disc
of the arrangement lies in `Σ`. The paths are paths of the graph `H.toGraph`.

`H` is a subgraph of `N.G` by `η`, and `(N.G, N.Ω, N.Ω₀)` is the neighbourhood `(G_1, Ω_1, Ω_2)`.
The
society `S_G` is `(G, Ω_1)` and `S_G0` is `(G, Ω_0)`. The map `μ` reads a vertex of `V(C₁)` in `N.G`
as a point. The last two lines of the conclusion say that `U(P ∩ H) - {u, v}` is in that component,
for vertices and for edges. `∃ a b` names the ends of `p`. -/
def Theorem84DiscStatement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {α : Type u} {β : Type v}
    {H C₁ C₂ : Drawing S} {D D₂ E₁ E₂ X : Set S} {pi : ℕ} {N : Neighborhood α β}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {S_G S₂ S_G0 : Society α β} {μ : α → S}
    (P : Fin (2 * pi + 8) → Graph S (Set S)) (η : SpanEmbedding H N.G),
    IsClosedSurface S →
    IsClosedDisc D → IsClosedDisc D₂ → IsClosedDisc E₁ → IsClosedDisc E₂ →
    D₂ ⊆ E₂ → E₂ ⊆ E₁ \ C₁.U → E₁ ⊆ D →
    IsRigidIn H (D \ discInt D₂) →
    C₁.IsCircuit ∧ C₁.IsSubdrawing H → C₂.IsCircuit ∧ C₂.IsSubdrawing H →
    discBd E₁ = C₁.U → discBd E₂ = C₂.U →
    pi ≠ 1 → pi ≠ 3 → pi + 4 ≤ regionalDistance H C₂.U C₁.U →
    X ⊆ C₁.V →
    (∀ i, ∃ x ∈ X, ∃ y ∈ C₂.V, IsGraphPathWithEnds H.toGraph (P i) x y ∧ V(P i) ∩ C₁.V = {x}) →
    (Pairwise fun i j => Disjoint V(P i) V(P j)) →
    IsThreeSegregation N.G S_seg →
    IsSurfaceArrangement S_seg α_disc α_pt →
    IsCompatibleWith N.G H η S_seg α_disc α_pt →
    (∀ S₀ ∈ S_seg, α_disc S₀ ⊆ D \ discInt D₂) →
    IsPullbackPerm S_seg α_pt (discBd D) N.Ω →
    IsPullbackPerm S_seg α_pt (discBd D₂) N.Ω₀ →
    S_G.IsComposition S₂ N →
    S_G0.G = S_G.G →
    S_G0.Ω.bar = η.vMap '' C₁.V →
    (∀ v ∈ C₁.V, μ (η.vMap v) = v) →
    IsNaturalOrderFrom μ S_G0.Ω (discBd E₁) →
    (∃ P_set : Set (Graph α β), S_G.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard) →
    ∃ P_set : Set (Graph α β), S_G0.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard ∧
      S_G0.transactionEnds P_set ⊆ η.vMap '' X ∧
      ∀ p ∈ P_set, ∃ a b : α, S_G0.IsOmegaPathWithEnds p a b ∧
        (∀ v ∈ H.V, η.vMap v ∈ V(p) → η.vMap v = a ∨ η.vMap v = b ∨ v ∈ E₁ \ C₁.U) ∧
        (∀ e ∈ H.E, η.eMap e ∈ E(p) → e ⊆ E₁ \ C₁.U)

end GraphMinor.GM14

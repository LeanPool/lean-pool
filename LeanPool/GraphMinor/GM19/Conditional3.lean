/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15p

/-!
# Graph Minors XIX, (15.2): the topological step

Steps (2) and (3) of the proof of (15.2) move the edges `β(e)` onto the edges of `Γ₀` by a
homeomorphism of the surface, and pull back a star at each vertex of `Γ₀`. What the rest of the
proof uses is the topological feasibility condition of (3.2) of
Graph Minors XII for the discs of `exists_discFamily`. We state just that here, and we prove it in
`Feasibility.lean`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- **Steps (2) and (3) of the proof of (15.2).** The discs on the cuffs and on the internal edges
allow disjoint closed discs, one for each vertex `v` of `Γ₀`, that meet the discs of the family just
in the ends that correspond to `v`.

Here the disc of an edge of size 3 lies in the closed disc of the edge, and the disc of a cuff lies
in the disc pasted onto the cuff. That fixes the cyclic order of the ends around each disc. The
hypothesis on orientations is the one in (15.2). -/
def Theorem152FeasibilityStatement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) (cap : IsCappedSurface S Shat) (χ : ColourScheme S β) (P₀ : ColouredPainting χ)
      (D : TangleDatum cap χ) (n : ℕ) (b : Set S → Set S),
    (¬ IsOrientableSurface S ∨ ∃ o : SurfaceOrientation S, ∀ P ∈ ({P₀, D.P} : Set _), ∀ e ∈ P.Γ.E,
      (tilde e).ncard = 3 → ∀ a b c : S, P.Γ.γ e = [a, b, c] → o.pos (closure e) a b c) →
    D.IsMatchSetting P₀ n b →
    ∀ Δ : TangleDatum.DiscIndex S P₀ → Set Shat, (∀ i, IsClosedDisc (Δ i)) →
      (∀ i, TangleDatum.discEnds cap b P₀ i ⊆ discBd (Δ i)) → (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j))
        →
      (∀ Θ : {Θ : Set S // Θ ∈ cuffs S}, Δ (.inl Θ) ⊆ closure (cap.cuffDisc Θ.1)) →
      (∀ e : {e : Set S // e ∈ P₀.Γ.E ∧ Painting.IsInternal e}, (tilde (b e.1)).ncard = 3 → Δ
        (.inr e) ⊆ cap.emb '' closure (b e.1)) →
      ∃ Dv : S → Set Shat, (∀ v ∈ P₀.Γ.V, IsClosedDisc (Dv v)) ∧ (∀ v ∈ P₀.Γ.V, ∀ v' ∈ P₀.Γ.V, v ≠
        v' → Disjoint (Dv v) (Dv v')) ∧
        ∀ v ∈ P₀.Γ.V, Dv v ∩ ⋃ i, Δ i = TangleDatum.endClass cap P₀ D.P b v

end GraphMinor.GM19

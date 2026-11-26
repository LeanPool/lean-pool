/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section12
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.ArcDisc
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.RegionBoundary
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode
import LeanPool.GraphMinor.GM17.IndentMain
import Mathlib.Data.DFinsupp.WellFounded

import LeanPool.GraphMinor.GM17.Section8Proved

import LeanPool.GraphMinor.GM17.Section9bProved

/-!
# Graph Minors XVII, Section 12: from a portrayal of `G \ e` to a portrayal of `G`

This file continues Section 12 of Robertson and Seymour, *Graph Minors. XVII. Taming a Vortex*, J.
Combin. Theory Ser. B 77 (1999), 162–210:

- **(12.4)** (`theorem_12_4`, page 200).
- **(12.5)** (`theorem_12_5`, page 200).

We also prove that a central portrayal resembling a `z`-redundant one is `z`-redundant, and that
there is a true one among them (`exists_true_resembling`). The paper uses this in the first line of
the proof of (12.4), and at the end of the proofs of (13.4) and (14.2).
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

variable {α : Type u} {β : Type v} {G : Hypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)}

/-- Redundancy depends only on the warps and the surface, so it passes to a portrayal that
resembles. -/
theorem Portrayal.IsRedundant.of_resembles {π₁ π₂ : Portrayal G} {θ z : ℕ} (hr : π₁.Resembles π₂)
  (h : π₂.IsRedundant 𝒯 θ z) : π₁.IsRedundant 𝒯 θ z :=
  ⟨h.1, fun Z hZ hc π' hπ' hs => h.2 Z hZ hc π' hπ' (hr.isSimpler_iff.mp hs)⟩

/-- Among the central portrayals resembling a redundant `π`, one with least truth is true. Truths
are ordered lexicographically on `ℕ⁶`, which is a well-order. -/
theorem exists_true_resembling {π : Portrayal G} {θ z : ℕ} (h𝒯 : IsTangle G θ 𝒯)
  (hc : π.IsCentral 𝒯) (hred : π.IsRedundant 𝒯 θ z) :
    ∃ π' : Portrayal G, π'.IsTrue 𝒯 ∧ π'.Resembles π ∧ π'.IsRedundant 𝒯 θ z := by
  let Q : Set (Fin 6 → ℕ) := {t | ∃ π' : Portrayal G, π'.IsCentral 𝒯 ∧ π'.Resembles π ∧ π'.truth
    = t}
  have hQ : Q.Nonempty := ⟨π.truth, π, hc, Portrayal.Resembles.refl π, rfl⟩
  have hwf : WellFounded (Pi.Lex (· < ·) (· < ·) : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop)
    := InvImage.wf toLex (wellFounded_lt (α := Lex (Fin 6 → ℕ)))
  obtain ⟨t, ⟨π₀, hc₀, hr₀, rfl⟩, hmin⟩ := hwf.has_min Q hQ
  refine ⟨π₀, ⟨hc₀, hr₀.isZeroRedundant (hred.isZeroRedundant h𝒯), fun π' hc' htr hr' => ?_⟩,
    hr₀, hred.of_resembles hr₀⟩
  obtain ⟨k, h1, h2⟩ := htr
  exact hmin π'.truth ⟨π', hc', hr'.trans hr₀, rfl⟩ ⟨k, fun i hi => h1 i hi, h2⟩

/-- **Graph Minors XVII, (12.4)** (page 200): "Let $e$ be an edge of a hypergraph $G$, such that the
set of ends of $e$ is a clique of $G \setminus e$. Let $\mathscr{T}$ be a tangle in $G \setminus e$,
of order $>4p+9$, inducing a tangle $\mathscr{T}'$ in $G$. Let $\pi$ be a $(2p+7)$-redundant,
$\mathscr{T}$-central portrayal of $G \setminus e$ with warp $\le p$. Then there is a
$\mathscr{T}'$-central portrayal of $G$ resembling $\pi$." -/
theorem theorem_12_4_proof {e : β} (he : e ∈ G.edgeSet) (hK : IsClique (G.deleteEdges {e})
  (G.ends e))
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle (G.deleteEdges {e}) θ 𝒯)
      (hθ : 4 * p + 9 < θ)
    (π : Portrayal (G.deleteEdges {e})) (hc : π.IsCentral 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 7))
      (hwarp : π.warp ≤ p) :
    ∃ π' : Portrayal G, π'.IsCentral (inducedSubhypergraphTangle G (G.deleteEdges {e}) 𝒯 θ)
      ∧ π'.Resembles π := by
  obtain ⟨π₁, htrue, hr₁, hred₁⟩ := exists_true_resembling h𝒯 hc hred
  have hw₁ : π₁.warp ≤ p := hr₁.warp_eq ▸ hwarp
  have hred3 : π₁.IsRedundant 𝒯 θ (2 * p + 3) := hred₁.mono (by omega)
  have hθ5 : 4 * p + 5 < θ := by omega
  rcases theorem_12_2_proof h𝒯 π₁ htrue hred₁ hw₁ hθ hK with ⟨Δ, hΔ, hsmall, hKΔ, -, hnorm, hcard⟩
    | ⟨c, hc₁, hKc⟩
  · have hdom : π₁.domγ = π₁.Γ.N :=
      theorem_8_4_proof h𝒯 π₁ htrue hred3 hw₁ hθ5
    obtain ⟨-, -, h82_node⟩ := theorem_8_2_proof h𝒯 π₁ htrue hred3 hw₁ hθ5
    obtain ⟨π₂, -, hc₂, hr₂, ⟨c, hc₂c, hsub⟩, himp, -⟩ := theorem_7_2_cell h𝒯
      (by omega) π₁ htrue.1 hΔ hnorm hcard (fun n hn => h82_node n (π₁.domγ_subset hn.2)) hsmall
    have hdisj₁ : ∀ n ∈ π₁.Γ.N ∩ bd π₁.S, Disjoint (π₁.borderSet n) (π₁.nodeVertex '' π₁.domγ)
      := fun n hn =>
      (theorem_9_7_proof h𝒯 π₁ htrue hred3 hw₁ hθ5 hn).mono_right (image_mono π₁.domγ_subset)
    have hends : G.ends e ⊆ (π₂.cellGraph c).vertexSet := fun x hx => by
      rw [hdom] at hsub
      refine hsub ?_
      rcases hKΔ hx with h1 | ⟨n, hn, rfl⟩
      · exact .inl h1
      · exact .inr ⟨n, ⟨hn.1, hn.2⟩, rfl⟩
    have h := addEdgePortrayal_central_resembles he hK h𝒯 (by omega) π₂ hc₂
      ((hred₁.of_resembles hr₂).mono (by omega)) (hr₂.warp_eq ▸ hw₁) (himp hdisj₁) hc₂c hends
    exact ⟨_, h.1, h.2.trans (hr₂.trans hr₁)⟩
  · have h := theorem_12_3_proof he hK h𝒯 (by omega) π₁ htrue (hred₁.mono (by omega)) hw₁ hc₁ hKc
    exact ⟨_, h.1, h.2.trans hr₁⟩

end GraphMinor.GM17

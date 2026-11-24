/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section13b
public import LeanPool.GraphMinor.Surface.DrawCarry

/-!
# Graph Minors XVII, Section 13: a redundant portrayal

This file states (13.1) of Robertson and Seymour, *Graph Minors. XVII. Taming a Vortex*, J. Combin.
Theory Ser. B 77 (1999), 162-210, for graphs. The refinement (13.4) is proved in `Section13Proved`.

- `Theorem131Statement`: the statement of (13.1) (page 202), for graphs.

(13.4) is proved in `Section13Proved` by the paper's argument, with `a*`, `b*` as on page 207. Truth
comes from `exists_true_resembling`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

/-- **Graph Minors XVII, (13.1)** (page 202), for graphs: "For any graph $H$ there are numbers $p$,
$q$, $z$ and $\theta > z$, such that for every hypergraph $G$ and every tangle $\mathcal{T}$ in $G$
of order $\ge \theta$, either (i) $\mathcal{T}$ controls an $H$-minor of $G^*$, or (ii) there exists
$Z \subseteq V(G)$ with $|Z| \le z$ and a $\mathcal{T} \setminus Z$-central portrayal $\pi =
(\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G \setminus Z$ with warp $\le p$, such that $\Sigma$
has $\le q$ cuffs and $H$ cannot be drawn in $\Sigma$."

The paper says "hypergraph", but its proof starts from "every graph", and (13.4) and (14.2) use it
only for graphs. -/
@[expose] def Theorem131Statement : Prop :=
  ∀ {α' β' : Type} (H : Hypergraph α' β'), H.IsGraph →
    ∃ p q z θ : ℕ, z < θ ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph → ∀ (θ' : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' →
      ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ z ∧ ∃ π : Portrayal (G.deleteVertices Z),
        π.IsCentral (deleteVerticesTangle G Z 𝒯 θ') ∧ π.warp ≤ p ∧ (cuffs π.S).encard ≤ q
          ∧ ¬ CanBeDrawn π.S H

end GraphMinor.GM17

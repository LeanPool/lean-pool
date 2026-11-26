/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM06.Defs

/-!
# Open Statements for Graph Minors VII

This file holds explicit named `Prop` statements (`...Statement`) for surface-topology facts used in
Graph Minors VII.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## Open surface-topology statements for Section 4 -/

/-- A surface `S'` with associated quotient surjection `φ : S' → S` is obtained from `S` by
*cutting along `U(J)`*, where `J` is a proper graph in `S` with no isolated vertices
(Graph Minors VII, Section 2, page 215, and Section 4, page 223). -/
structure IsCutAlongGraph (J : Drawing S) (S' : Type u) [TopologicalSpace S']
    (φ : S' → S) : Prop where
  isProper : J.IsProper
  noIsolated : HasNoIsolatedVertices J
  isSurface : IsSurface S'
  quotientMap : Topology.IsQuotientMap φ
  preimage_bd_union_U : φ ⁻¹' (bd S ∪ J.U) = bd S'
  interior_inj : ∀ x ∈ (bd S')ᶜ, ∀ y : S', φ x = φ y → x = y
  /-- Cutting never collapses an arc of `bd(S')` to a point. -/
  finite_fiber : ∀ x, (φ ⁻¹' {x}).Finite

/-! ## Open surface-topology statements for Sections 5, 6, and 7 -/

/-- A surface `S_e` with associated surjection `φ_e : S_e → S` and cut graph
`G_e = φ_e⁻¹(G \ e)` is obtained from `(S, G)` by deleting a non-loop edge `e ∈ G.E` with
`closure e ∩ bd S = ∅` and cutting `S` along `closure e`
(Graph Minors VII, Section 7, page 238: "If $e$ is an edge of $G$, let $G \setminus e$ be the graph
obtained from $G$ by deleting $e$. Let $\Sigma_e$ be the surface obtained from $\Sigma$ by cutting
along $\bar{e}$. Let $\phi_e$ be the associated surjection. Then $\phi_e^{-1}(G \setminus e)$ is a
proper graph in $\Sigma_e$; and provided $\bar{e} \cap bd(\Sigma) = \emptyset$ and $e$ is not a
loop, we have $\Sigma_e \cong \Sigma(a, b, c + 1)$.").

The last four fields say what cutting means. Off `e` the map is one to one, so each end of `e` has
one point over it. The
preimage of `closure e` is a new cuff. Pasting a disc on the new cuff gives `S` back,
and the inclusion is homotopic to `φ_e`. Without these fields `φ_e` could collapse a small cuff to a
point of `S`, far from `e`,
and (7.1) and (7.2) would fail. -/
structure IsCutAlongEdge (G : Drawing S) (e : Set S) (a b c : ℕ)
    (S_e : Type u) [TopologicalSpace S_e] (φ_e : S_e → S) (G_e : Drawing S_e) : Prop where
  mem_E : e ∈ G.E
  not_loop : (tilde e).ncard = 2
  disjoint_bd : closure e ∩ bd S = ∅
  isSurface : IsSurface S_e
  homeo_model : Nonempty (S_e ≃ₜ SurfaceModel a b (c + 1))
  quotientMap : Topology.IsQuotientMap φ_e
  isProper : G_e.IsProper
  preimage_U : G_e.U = φ_e ⁻¹' (G.U \ e)
  preimage_V : G_e.V = φ_e ⁻¹' G.V
  inj : ∀ x y, φ_e x = φ_e y → x = y ∨ φ_e x ∈ e
  newCuff : φ_e ⁻¹' closure e ∈ cuffs S_e
  bd_eq : bd S_e = φ_e ⁻¹' (bd S ∪ closure e)
  uncut : ∃ (ι : S_e → S) (E : Set S) (H : unitInterval × S_e → S), IsCappedCuff
    (φ_e ⁻¹' closure e) S ι E ∧
    Continuous H ∧ (∀ y, H (0, y) = ι y) ∧ ∀ y, H (1, y) = φ_e y
  /-- Cutting never collapses an arc to a point, as in `IsCutAlongGraph`. -/
  finite_fiber : ∀ x, (φ_e ⁻¹' {x}).Finite
  /-- Each point has at most two points over it. -/
  fiber_two : ∀ x, (φ_e ⁻¹' {x}).ncard ≤ 2
  /-- Each point of `e` has at least two points over it. -/
  two_le : ∀ x ∈ e, 2 ≤ (φ_e ⁻¹' {x}).ncard

end GraphMinor.GM07

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs

/-!
# Statements that Graph Minors XI cites

Graph Minors XI quotes these results from outside the paper. Each is a `Prop` about the actual
definitions, and the theorems of the paper take them as hypotheses.

- `GM07Theorem112Statement`, `GM07Theorem1110Statement`: Graph Minors VII, (11.2) and (11.10).

Two classical facts on the plane, which the paper uses silently when it says that a drawing without
circuits has only one region, are proved in `GraphMinor/GM11/PlaneFacts.lean`.

Graph Minors X, (2.7), which the paper also cites, is `GM10.theorem_2_7`, already proved. XI (7.1)
quotes Epstein's Theorem 1.7 for disc bounding in the ambient manifold. Robertson and Seymour's
XI (7.2) keeps the disc inside the subset of the null-homotopy. `Surface.EpsteinStatement` supplies
that relative conclusion; the other topological statements are in `Surface/TopologyStatements.lean`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

/-- Graph Minors VII, (11.2) (page 249): "If $\Sigma$ is a surface, and $\phi \colon S^1 \to \Sigma$
is continuous and
non-null-homotopic, there is a non-null-homotopic $O$-arc included in $|\phi|$." -/
def GM07Theorem112Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S → ∀ φ : C(Circle, S),
    ¬ ClosedCurveIsNullHomotopicIn univ φ →
      ∃ F : Set S, IsOArc F ∧ F ⊆ range φ ∧ ¬ IsNullHomotopicOArc F

/-- Graph Minors VII, (11.10) (page 253): "If $\Sigma$ is connected and $Z \subseteq \Sigma$ is
solid and flat, then either $Z =
\Sigma$ or $Z$ is planar." -/
def GM07Theorem1110Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S], IsSurface S → ConnectedSpace S →
    ∀ Z : Set S, IsSolid Z → IsFlat Z → Z = univ ∨ IsPlanar Z

end GraphMinor.GM11

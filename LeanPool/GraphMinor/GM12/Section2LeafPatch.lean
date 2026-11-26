/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM11.Rotation

/-!
# The local patch needed at a leaf

The omitted entry-edge existence proof of XII, page 243, also applies
at a leaf. A neighbourhood with the incident edge removed, and its
leaf vertex restored, needs a simply-connected patch. The punctured
patch must stay path connected so that incoming points can be joined
to points on the radial spoke without passing through the vertex.
This file states that local topological claim separately.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- The local patch claim needed in the leaf case of the omitted entry
lemma of XII, page 243. This is a topological step of that proof, rather
than a cited result of another paper. The other valencies are handled
by sector patches or by exclusion of isolated vertices. -/
def LeafEntryPatchStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ (Γ : Drawing S) (γ : Set S → unitInterval → S), EdgePar Γ γ →
    ∀ v ∈ Γ.V, Nat.card (halfEdges Γ γ v) = 1 →
    ∀ r ∈ Γ.R, v ∈ closure r →
      ∃ N X : Set S, IsOpen N ∧ v ∈ N ∧ v ∈ X ∧
        IsSimplyConnectedSet X ∧ IsPathConnected (X \ {v}) ∧
        X ⊆ r ∪ {v} ∧ N \ Γ.U ⊆ X

end GraphMinor.GM12

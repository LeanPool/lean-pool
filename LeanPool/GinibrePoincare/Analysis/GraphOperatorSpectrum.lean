/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialGeneratorSpectrum.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-! # Bounded resolvents on an operator graph

The Ginibre spectrum is the complement of Tau Ceti's resolvent set. The graph
form lets proofs use their existing descriptions of the unbounded domains.
-/

@[expose] public section
namespace GinibrePoincare

open LinearPMap TauCeti.LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The ordinary bounded resolvent condition for a graph-defined operator. -/
abbrev HasBoundedGraphResolvent (L : H →ₗ.[ℂ] H) (zeta : ℂ) : Prop :=
  zeta ∈ resolventSet L

/-- A bounded resolvent exists exactly when a bounded map satisfies the two inverse
identities on the graph. -/
theorem hasBoundedGraphResolvent_iff (L : H →ₗ.[ℂ] H) (zeta : ℂ) :
    HasBoundedGraphResolvent L zeta ↔
      ∃ R : H →L[ℂ] H,
        (∀ f, (R f, zeta • R f - f) ∈ L.graph) ∧
        (∀ u v, (u, v) ∈ L.graph → R (zeta • u - v) = u) := by
  change zeta ∈ resolventSet L ↔ _
  rw [mem_resolventSet_iff]
  constructor
  · rintro ⟨R, hR⟩
    obtain ⟨hRight, hLeft⟩ := isResolventAt_iff_forall_mem_graph.mp hR
    exact ⟨R, hRight, fun u v huv => hLeft (u, v) huv⟩
  · rintro ⟨R, hRight, hLeft⟩
    exact ⟨R, isResolventAt_iff_forall_mem_graph.mpr
      ⟨hRight, fun point hpoint => hLeft point.1 point.2 hpoint⟩⟩

/-- Spectrum of an unbounded operator: the complement of its bounded resolvent set. -/
def graphOperatorSpectrum (L : H →ₗ.[ℂ] H) : Set ℂ :=
  {zeta | ¬ HasBoundedGraphResolvent L zeta}

/-- A nonzero eigenvector prevents a bounded two-sided resolvent. -/
theorem eigenpair_mem_graphOperatorSpectrum (L : H →ₗ.[ℂ] H) (zeta : ℂ)
    (u : H) (hu : u ≠ 0) (hg : (u, zeta • u) ∈ L.graph) :
    zeta ∈ graphOperatorSpectrum L := by
  change ¬ HasBoundedGraphResolvent L zeta
  intro hzeta
  obtain ⟨R, _, hleft⟩ := (hasBoundedGraphResolvent_iff L zeta).mp hzeta
  have h := hleft u (zeta • u) hg
  rw [sub_self, map_zero] at h
  exact hu h.symm

end GinibrePoincare

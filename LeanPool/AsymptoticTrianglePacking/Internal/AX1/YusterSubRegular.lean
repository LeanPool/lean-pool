/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Yuster (edge-based) — majority near-regularity + codegree bound for `triangleHypergraphSub`

Standalone, Mathlib-only. Assembles the `NibbleTheoremMost` input for the CORRECT (edge-based) triangle
hypergraph `triangleHypergraphSub G`, whose matchings are edge-disjoint triangle packings (`ν₃`).

* The **codegree side is trivial**: `triangleHypergraphSub` has hypergraph-codegree `≤ 1`
  (`triangleHypergraphSub_codegree_le_one`), so `CodegreeBounded C` for any `C ≥ 1` (in particular
  `C = μd ≥ 1`).
* The **degree side** (`NearlyRegularMost`) is packaged from per-edge lower/upper bounds and the
  exceptional (non-regular-degree) edge count `≤ η|E|`, supplied by the edge counting (②a).

* `triangleHypergraphSub_codegreeBounded` — `1 ≤ C → CodegreeBounded (triangleHypergraphSub G) C`.
* `triangleHypergraphSub_nearlyRegularMost_of_bounds` — package `NearlyRegularMost` from per-edge bounds.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdgeType
public import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost
public import Mathlib.Analysis.RCLike.Basic

/-! # YusterSubRegular -/

@[expose] public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Codegree side (trivial).** The edge-based triangle hypergraph has hypergraph-codegree `≤ 1`, so it
is `CodegreeBounded C` for any `C ≥ 1` — in particular `C = μd` once `μd ≥ 1`. -/
theorem triangleHypergraphSub_codegreeBounded {C : ℝ} (hC : 1 ≤ C) :
    CodegreeBounded (triangleHypergraphSub G) C := by
  intro E E' hEE'
  calc (codegree (triangleHypergraphSub G) E E' : ℝ)
      ≤ 1 := by exact_mod_cast triangleHypergraphSub_codegree_le_one G hEE'
    _ ≤ C := hC

/-- **Majority near-regularity (packaging).** Given a per-edge degree window on all but an exceptional
set `Exc` of size `≤ η|E(G)|`, the edge-based triangle hypergraph is `NearlyRegularMost d μ η`. The
per-edge bounds and the exceptional count are supplied by the edge counting (②a). -/
theorem triangleHypergraphSub_nearlyRegularMost_of_bounds {d μ η : ℝ}
    (Exc : Finset (EdgeV G))
    (hExc : (Exc.card : ℝ) ≤ η * (Fintype.card (EdgeV G) : ℝ))
    (hlo : ∀ E ∉ Exc, (1 - μ) * d ≤ (degree (triangleHypergraphSub G) E : ℝ))
    (hhi : ∀ E ∉ Exc, (degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) :
    NearlyRegularMost (triangleHypergraphSub G) d μ η :=
  ⟨Exc, hExc, fun E hE => ⟨hlo E hE, hhi E hE⟩⟩

end Nibble.YusterE

/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Buffered countable ball covers of open sets

Positive contained closed balls are chosen at actual points of an open set.
A countable subfamily of the half-radius open balls covers that set. This is
metric localization only: no convexity, measure, finite dimension, compactness
or nonemptiness hypothesis. The two consumers are local contact null images
and compact-patch localization of domain Monge–Ampere equations for Letwin
arXiv:2607.24164v1 Lemma 2.2 / BB arXiv:1207.6128v1 Theorem 2.24(ii).
-/

@[expose] public section

noncomputable section
open Set Metric

namespace FunctionalInequalities.Analysis

/-- An open set in a second-countable pseudometric space has a countable cover
by half-radius balls whose full closed balls lie in the set. Centers are actual
points of the open set, including when it is empty. -/
theorem exists_countable_buffered_ball_cover
    {E : Type*} [PseudoMetricSpace E] [SecondCountableTopology E]
    {Ω : Set E} (hΩ : IsOpen Ω) :
    ∃ (R : Ω → ℝ) (s : Set Ω),
      (∀ x : Ω, 0 < R x) ∧
      (∀ x : Ω, closedBall (x : E) (R x) ⊆ Ω) ∧
      s.Countable ∧ Ω ⊆ ⋃ x ∈ s, ball (x : E) (R x / 2) := by
  classical
  have hex : ∀ x : Ω, ∃ R : ℝ, 0 < R ∧ closedBall (x : E) R ⊆ Ω := by
    intro x
    exact Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds x.property)
  let R : Ω → ℝ := fun x => Classical.choose (hex x)
  have hpos (x : Ω) : 0 < R x := (Classical.choose_spec (hex x)).1
  have hsub (x : Ω) : closedBall (x : E) (R x) ⊆ Ω :=
    (Classical.choose_spec (hex x)).2
  have hc : Ω ⊆ ⋃ x : Ω, ball (x : E) (R x / 2) := by
    intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, by simpa using half_pos (hpos ⟨x, hx⟩)⟩
  obtain ⟨s, hs, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
      (fun x : Ω => ball (x : E) (R x / 2)) (fun _ => isOpen_ball) hc
  exact ⟨R, s, hpos, hsub, hs, hcover⟩

end FunctionalInequalities.Analysis

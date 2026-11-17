/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Order.Disjointed

/-! # Countable measurable partitions subordinate to open covers

A nonempty measurable subset of a second-countable space is partitioned into
countably many measurable pieces, each inside one member of an open cover
indexed by the points of a containing set. No measure or finiteness is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace FunctionalInequalities.Analysis

theorem exists_measurable_partition_subordinate
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {O S : Set E}
    (hS : MeasurableSet S) (hSO : S ⊆ O) (hSne : S.Nonempty)
    (N : O → Set E) (hN : ∀ z, IsOpen (N z))
    (hzN : ∀ z : O, (z : E) ∈ N z) (hNO : ∀ z, N z ⊆ O) :
    ∃ (σ : ℕ → O) (P : ℕ → Set E),
      (∀ n, MeasurableSet (P n)) ∧ Pairwise (Function.onFun Disjoint P) ∧
      (⋃ n, P n) = S ∧ ∀ n, P n ⊆ N (σ n) := by
  classical
  obtain ⟨z₀, hz₀⟩ := hSne
  obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable N hN
  have hOcov : ⋃ z : O, N z = O :=
    Set.Subset.antisymm (Set.iUnion_subset hNO) fun y hy =>
      Set.mem_iUnion.2 ⟨⟨y, hy⟩, hzN ⟨y, hy⟩⟩
  have hTne : T.Nonempty := by
    have : z₀ ∈ ⋃ z ∈ T, N z := by rw [hTu, hOcov]; exact hSO hz₀
    obtain ⟨z, hzT, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨z, hzT⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hTne
  have hcov : O ⊆ ⋃ n, N (σ n) := by rw [← hOcov, ← hTu, hσ, Set.biUnion_range]
  let P : ℕ → Set E := disjointed fun n => S ∩ N (σ n)
  refine ⟨σ, P, MeasurableSet.disjointed (fun n => hS.inter (hN (σ n)).measurableSet),
    disjoint_disjointed _, ?_, fun n => (disjointed_subset _ n).trans Set.inter_subset_right⟩
  change (⋃ n, disjointed (fun n => S ∩ N (σ n)) n) = S
  rw [iUnion_disjointed, ← Set.inter_iUnion]
  exact Set.inter_eq_self_of_subset_left (hSO.trans hcov)

end FunctionalInequalities.Analysis

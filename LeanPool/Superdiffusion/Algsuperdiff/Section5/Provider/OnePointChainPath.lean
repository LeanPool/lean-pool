/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.HitExitBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.LiveRestrictionMarginals
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Process
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.StoppedDirichlet

/-!
# OnePointChainPath

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Reading the cube geometry inside a larger carrier

The hit-then-exit chaining estimate is stated for a process of the state space in which the cubes
live.  The process produced by the divergence-form chain is a process of a larger carrier, the
state space being read inside it by an open embedding.  This file supplies the two deterministic
ingredients needed to move the chaining input across that reading.

The first is a corestriction: a continuous path of the larger carrier all of whose values are
images is the image of a continuous path of the state space.  Only the fact that the reading is a
topological embedding is used, through `Topology.IsEmbedding.continuous_iff`.

The second is the geometry of the padded cube families read inside the carrier.  The padded closed
cells are compact, so their images are compact and their union is closed; the padded enlargements
are open, so their images are open; and the overlap count is unchanged because the reading is
injective.

## Main results

* `exists_pathPostcomp_eq_of_forall_mem_range` — the corestriction of a path with image values.
* `exists_pathPostcomp_eq_of_exitTime_range_eq_top` — the same from an infinite exit time from the
  image of the state space.
* `isClosed_iUnion_image_enumeratedClosedCubeFamily`,
  `isOpen_image_enumeratedOpenEnlargementFamily`, `image_enumeratedCubeFamily_overlap` — the
  hypotheses of the chaining estimate for the read families.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section5.Trace
open DivergenceFormProcess.LiveRestriction
open HCPolySupport MarkovProcess MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. Corestriction of a continuous path along an embedding -/

section Corestriction

variable {alpha beta : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]

/-- **A path with image values is an image path.**  If every value of a continuous path of `beta`
lies in the range of a topological embedding `e`, the path is the post-composition of a continuous
path of `alpha` with `e`.  Continuity of the corestriction is exactly the embedding criterion. -/
theorem exists_pathPostcomp_eq_of_forall_mem_range (e : C(alpha, beta))
    (he : Topology.IsEmbedding e) (omega : ContinuousPath beta)
    (hmem : ∀ t : NNReal, omega t ∈ Set.range e) :
    ∃ w : ContinuousPath alpha, pathPostcomp e w = omega := by
  have hchoice : ∀ t : NNReal, e ((hmem t).choose) = omega t := fun t => (hmem t).choose_spec
  have hcont : Continuous fun t : NNReal => (hmem t).choose := by
    refine he.continuous_iff.mpr ?_
    have hfun : (e ∘ fun t : NNReal => (hmem t).choose) = fun t => omega t := by
      funext t
      exact hchoice t
    rw [hfun]
    exact omega.continuous
  refine ⟨⟨fun t => (hmem t).choose, hcont⟩, ?_⟩
  ext t
  exact hchoice t

end Corestriction

section CorestrictionMetric

variable {alpha beta : Type*} [TopologicalSpace alpha] [PseudoMetricSpace beta]

/-- **A path that never leaves the image is an image path.**  An infinite exit time from the range
of the reading map says exactly that every value of the path is an image. -/
theorem exists_pathPostcomp_eq_of_exitTime_range_eq_top (e : C(alpha, beta))
    (he : Topology.IsEmbedding e) (omega : ContinuousPath beta)
    (htop : ContinuousPath.exitTime (Set.range e) omega = ⊤) :
    ∃ w : ContinuousPath alpha, pathPostcomp e w = omega :=
  exists_pathPostcomp_eq_of_forall_mem_range e he omega
    ((ContinuousPath.exitTime_eq_top_iff (Set.range e) omega).mp htop)

end CorestrictionMetric

/-! ## 2. The padded cube families read inside a carrier -/

section ImageFamily

variable {d r : ℕ} {alpha : Type*} [MetricSpace alpha]

/-- The padded closed cells are compact: each is a closed ball of the state space or empty. -/
theorem isCompact_enumeratedClosedCubeFamily (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) (i : ℕ) :
    IsCompact (enumeratedClosedCubeFamily n sites i) := by
  unfold enumeratedClosedCubeFamily
  split
  · exact isCompact_closedBall _ _
  · exact isCompact_empty

/-- The union of the padded closed cells is compact: only finitely many members are nonempty. -/
theorem isCompact_iUnion_enumeratedClosedCubeFamily (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) :
    IsCompact (⋃ i, enumeratedClosedCubeFamily n sites i) := by
  have heq : (⋃ i, enumeratedClosedCubeFamily n sites i) =
      ⋃ j : Fin r, closedPartitionCube n (sites j) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rw [enumeratedClosedCubeFamily] at hi
      split at hi
      · exact ⟨⟨i, by assumption⟩, hi⟩
      · exact False.elim hi
    · rintro ⟨j, hj⟩
      refine ⟨j.1, ?_⟩
      rw [enumeratedClosedCubeFamily, dite_eq_left j.2]
      exact hj
  rw [heq]
  exact isCompact_iUnion fun _ => isCompact_closedBall _ _

variable (emb : C(Vec d, alpha))

/-- Every read padded cell is measurable, being the continuous image of a compact set. -/
theorem measurableSet_image_enumeratedClosedCubeFamily [MeasurableSpace alpha]
    [BorelSpace alpha] (n : ℤ) (sites : Fin r ↪ Section5.Percolation.Site d) (i : ℕ) :
    MeasurableSet (emb '' enumeratedClosedCubeFamily n sites i) :=
  (((isCompact_enumeratedClosedCubeFamily n sites i).image emb.continuous).isClosed).measurableSet

/-- The union of the read padded cells is closed, being the continuous image of a compact set. -/
theorem isClosed_iUnion_image_enumeratedClosedCubeFamily (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) :
    IsClosed (⋃ i, emb '' enumeratedClosedCubeFamily n sites i) := by
  rw [← Set.image_iUnion]
  exact ((isCompact_iUnion_enumeratedClosedCubeFamily n sites).image emb.continuous).isClosed

/-- Every read padded enlargement is open, the reading being an open map. -/
theorem isOpen_image_enumeratedOpenEnlargementFamily
    (hemb : Topology.IsOpenEmbedding emb) (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) (i : ℕ) :
    IsOpen (emb '' enumeratedOpenEnlargementFamily n sites i) :=
  hemb.isOpenMap _ (isOpen_enumeratedOpenEnlargementFamily n sites i)

/-- The overlap count of the read families is the overlap count of the families themselves: an
injective reading neither creates nor destroys an intersection. -/
theorem image_enumeratedCubeFamily_overlap (hemb : Function.Injective emb) (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) (i : ℕ) :
    ∃ s : Finset ℕ, s.card ≤ 3 ^ d ∧ ∀ j,
      (emb '' enumeratedClosedCubeFamily n sites j ∩
        emb '' enumeratedOpenEnlargementFamily n sites i).Nonempty → j ∈ s := by
  obtain ⟨s, hs, hmem⟩ := enumeratedCubeFamily_overlap n sites i
  refine ⟨s, hs, fun j hj => hmem j ?_⟩
  rw [← Set.image_inter hemb] at hj
  exact hj.of_image

end ImageFamily

end

end Algsuperdiff.Section5.Provider

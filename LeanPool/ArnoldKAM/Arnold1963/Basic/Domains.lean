/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Spaces
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Thickening

/-!
Closed-ball neighborhoods, erosion, complex angle strips, and real slices. Radii are nonnegative.
The neighborhood is a union of actual closed balls; its zero-radius value is the original set.
Compactness hypotheses justify closedness when it is needed.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963

section MetricDomains

variable {E : Type*} [MetricSpace E]

/-- The union of closed balls of a fixed radius centered at points of the set. -/
def closedBallNeighborhood (U : Set E) (r : ℝ≥0) : Set E :=
  {x | ∃ y ∈ U, dist x y ≤ (r : ℝ)}

/-- The points whose closed ball of the specified radius remains inside the set. -/
def erosion (U : Set E) (r : ℝ≥0) : Set E :=
  {x | Metric.closedBall x (r : ℝ) ⊆ U}

@[simp] theorem erosion_zero (U : Set E) : erosion U 0 = U := by
  ext x
  simp [erosion]

@[simp] theorem closedBallNeighborhood_zero (U : Set E) :
    closedBallNeighborhood U 0 = U := by
  ext x
  simp [closedBallNeighborhood]

theorem erosion_subset (U : Set E) (r : ℝ≥0) : erosion U r ⊆ U := by
  intro x hx
  exact hx (Metric.mem_closedBall_self r.coe_nonneg)

theorem subset_closedBallNeighborhood (U : Set E) (r : ℝ≥0) :
    U ⊆ closedBallNeighborhood U r := by
  intro x hx
  exact ⟨x, hx, by simp⟩

theorem erosion_mono {U V : Set E} (hUV : U ⊆ V) (r : ℝ≥0) :
    erosion U r ⊆ erosion V r := by
  intro x hx y hy
  exact hUV (hx hy)

theorem erosion_antitone_radius (U : Set E) {r s : ℝ≥0} (hrs : r ≤ s) :
    erosion U s ⊆ erosion U r := by
  intro x hx y hy
  apply hx
  exact le_trans hy (show (r : ℝ) ≤ (s : ℝ) from hrs)

theorem erosion_inter (U V : Set E) (r : ℝ≥0) :
    erosion (U ∩ V) r = erosion U r ∩ erosion V r := by
  ext x
  simp only [erosion, Set.mem_ofPred_eq, Set.subset_inter_iff, Set.mem_inter_iff]

theorem mem_of_mem_erosion {U : Set E} {r : ℝ≥0} {x y : E}
    (hx : x ∈ erosion U r) (hxy : dist y x ≤ (r : ℝ)) : y ∈ U :=
  hx hxy

end MetricDomains

section CompactDomains

variable {E : Type*} [MetricSpace E] {U : Set E}

theorem closedBallNeighborhood_eq_cthickening_of_isCompact (hU : IsCompact U)
    (r : ℝ≥0) : closedBallNeighborhood U r = Metric.cthickening (r : ℝ) U := by
  rw [hU.cthickening_eq_biUnion_closedBall r.coe_nonneg]
  ext x
  simp [closedBallNeighborhood, Metric.mem_closedBall]

theorem isClosed_closedBallNeighborhood_of_isCompact (hU : IsCompact U) (r : ℝ≥0) :
    IsClosed (closedBallNeighborhood U r) := by
  rw [closedBallNeighborhood_eq_cthickening_of_isCompact hU]
  exact Metric.isClosed_cthickening

theorem isCompact_closedBallNeighborhood [ProperSpace E] (hU : IsCompact U)
    (r : ℝ≥0) : IsCompact (closedBallNeighborhood U r) := by
  rw [closedBallNeighborhood_eq_cthickening_of_isCompact hU]
  exact hU.cthickening

theorem isClosed_closedBallNeighborhood [ProperSpace E] (hU : IsClosed U) (r : ℝ≥0) :
    IsClosed (closedBallNeighborhood U r) := by
  have heq : closedBallNeighborhood U r = Metric.cthickening (r : ℝ) U := by
    rw [hU.cthickening_eq_biUnion_closedBall r.coe_nonneg]
    ext x
    simp [closedBallNeighborhood, Metric.mem_closedBall]
  rw [heq]
  exact Metric.isClosed_cthickening

end CompactDomains

/-- The closed complex angle strip bounded in the supremum norm of imaginary coordinates. -/
def angleStrip (n : ℕ) (ρ : ℝ≥0) : Set (ComplexSpace n) :=
  {q | ‖imagPart q‖ ≤ (ρ : ℝ)}

/-- The product of an action domain and a closed complex angle strip. -/
def phaseDomain {n : ℕ} (G : Set (ComplexSpace n)) (ρ : ℝ≥0) :
    Set (ComplexPhaseSpace n) := G ×ˢ angleStrip n ρ

/-- The real actions whose complexifications belong to the complex domain. -/
def realSlice {n : ℕ} (G : Set (ComplexSpace n)) : Set (RealSpace n) :=
  complexify ⁻¹' G

theorem isOpen_realSlice {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsOpen G) :
    IsOpen (realSlice G) := hG.preimage (continuous_complexify n)

theorem isClosed_realSlice {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsClosed G) :
    IsClosed (realSlice G) := hG.preimage (continuous_complexify n)

theorem isCompact_realSlice {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsCompact G) :
    IsCompact (realSlice G) :=
  (isometry_complexify n).isClosedEmbedding.isCompact_preimage hG

/-- Closure of a complex action domain under coordinatewise conjugation. -/
def ConjInvariant {n : ℕ} (G : Set (ComplexSpace n)) : Prop :=
  ∀ p ∈ G, conjVec p ∈ G

theorem mem_angleStrip_iff {n : ℕ} (q : ComplexSpace n) (ρ : ℝ≥0) :
    q ∈ angleStrip n ρ ↔ ∀ j, |(q j).im| ≤ (ρ : ℝ) := by
  simp only [angleStrip, Set.mem_ofPred_eq, pi_norm_le_iff_of_nonneg ρ.coe_nonneg,
    imagPart, Real.norm_eq_abs]

theorem complexify_mem_angleStrip {n : ℕ} (q : RealSpace n) (ρ : ℝ≥0) :
    complexify q ∈ angleStrip n ρ := by
  simp [angleStrip]

theorem angleStrip_mono {n : ℕ} {ρ σ : ℝ≥0} (h : ρ ≤ σ) :
    angleStrip n ρ ⊆ angleStrip n σ := by
  intro q hq
  exact le_trans hq (show (ρ : ℝ) ≤ (σ : ℝ) from h)

end KamProject.Arnold1963

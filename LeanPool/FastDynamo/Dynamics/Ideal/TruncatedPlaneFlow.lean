/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Flow.PlaneFlowRegularity

/-!
# The truncated flow of the plane

`FastDynamo/Dynamics/Flow/PlaneFlow.lean` builds the transverse displacement of the explicit
particle flow of `prop:particle-flow` as the sum
`∑' n, d_n(t, ·)` of the displacements of *all* the cells.  The sum is locally finite, but the
cells accumulate at `accumulationPoint`, so the lift of the flow is not `C¹` there.

This module builds the plane half of the **truncated** flow `Φ^{(N)}_t`, obtained by keeping
only the first `N` cells:

```
  planeTruncatedTransverseDisplacement N t x = ∑_{n < N} d_n(t, x) .
```

A *finite* sum of compactly supported smooth displacements has no accumulation point, so the
truncated flow is `C^∞` everywhere — that is the whole point of the truncation, and it is what
lets `FastDynamo/Dynamics/Ideal/TruncatedFlow.lean` feed the descended flow to the lemma
`inner_gradient_mFourier_comp_eq_zero_of_mem_literalSolenoidalSubspace` of
`FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`, which asks a test flow for
`IsLiteralTorusLift Φ L` together with `ContDiff ℝ 1 L`.  This is step (S2) of the invariance of
`literalSolenoidalSubspace` under the Cauchy transport (in the paper: the paragraph "The
formula preserves the divergence constraint" of the proof of `cor:ideal-growth`, which uses no
truncation).

The module mirrors `FastDynamo/Dynamics/Flow/PlaneFlow.lean` and
`FastDynamo/Dynamics/Flow/PlaneFlowRegularity.lean` with the `tsum` replaced by a `Finset.range`
sum:

1. the chart-side objects `planeTruncatedTransverseFlow`, `planeTruncatedAxialShift`, with the
   single-cell reduction, invariance of the buffer discs, the group law, the axial cocycle,
   smoothness, and the unit Jacobian determinant of the proof of `cor:ideal-growth`;
2. their `ℤ²`-periodisations `planePeriodizedTruncatedFlow`, `planePeriodizedTruncatedShift` —
   the chart-side family is supported in `ScaleFamily.placementChart` and is *not* equivariant,
   exactly as in the untruncated case — with the same package of facts.

The generic periodisation machinery (`UnitBoxPeriodization.periodization`,
`eventuallyEq_translate`, `isPeriodic_periodization`) and `PlaneFlowRegularity`'s
`chartTranslation`, `localTranslationIndex_sub_chartTranslation` and
`localTranslationIndex_eq_zero_of_mem_placementChart` are reused verbatim.
-/

@[expose] public section
namespace FastDynamo

noncomputable section

open Filter

open scoped Topology

namespace ScaleFamily.TorusCellPlacement

open UnitBoxPeriodization

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The truncated plane objects -/

/-- **The truncated transverse displacement of the plane**: the displacement of the first `N`
cells only (`eq:explicit-particle-flow`, with the sum over the cells cut at `N`). -/
def planeTruncatedTransverseDisplacement (N : ℕ) (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ∑ n ∈ Finset.range N, cellTransverseDisplacement h P angularSpeed n t x

/-- **The truncated transverse flow of the plane.** -/
def planeTruncatedTransverseFlow (N : ℕ) (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  x + planeTruncatedTransverseDisplacement h P angularSpeed N t x

/-- **The truncated axial shift of the plane** (`eq:explicit-particle-flow`, second
component). -/
def planeTruncatedAxialShift (N : ℕ) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, cellAxialDisplacement h P axialSpeed tau n t x

/-- The truncated flow is the identity plus the truncated displacement. -/
theorem planeTruncatedTransverseFlow_eq_add_displacement (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planeTruncatedTransverseFlow h P angularSpeed N t x =
      x + planeTruncatedTransverseDisplacement h P angularSpeed N t x := rfl

/-- The buffer discs are metric balls, hence open, so membership persists near every point. -/
theorem isOpen_bufferDisk (n : ℕ) : IsOpen (P.scaleFamily.bufferDisk n) := Metric.isOpen_ball

/-- **Single-cell reduction of the truncated displacement**, on one of the retained discs. -/
theorem planeTruncatedTransverseDisplacement_eq_cell (N : ℕ) (t : ℝ) {k : ℕ} (hk : k < N)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk k) :
    planeTruncatedTransverseDisplacement h P angularSpeed N t x =
      cellTransverseDisplacement h P angularSpeed k t x :=
  Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hk) fun _m _ hmk ↦
    cellTransverseDisplacement_eq_zero_on_distinct_buffer h P angularSpeed hmk t hx

/-- **Single-cell reduction of the truncated flow**, on one of the retained discs. -/
theorem planeTruncatedTransverseFlow_eq_cell (N : ℕ) (t : ℝ) {k : ℕ} (hk : k < N) {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk k) :
    planeTruncatedTransverseFlow h P angularSpeed N t x =
      cellTransverseFlow h P angularSpeed k t x := by
  rw [planeTruncatedTransverseFlow,
    planeTruncatedTransverseDisplacement_eq_cell h P angularSpeed N t hk hx]
  rfl

/-- **Single-cell reduction of the truncated axial shift**, on one of the retained discs. -/
theorem planeTruncatedAxialShift_eq_cell (N : ℕ) (t : ℝ) {k : ℕ} (hk : k < N) {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk k) :
    planeTruncatedAxialShift h P axialSpeed tau N t x =
      cellAxialDisplacement h P axialSpeed tau k t x :=
  Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hk) fun _m _ hmk ↦
    cellAxialDisplacement_eq_zero_on_distinct_buffer h P axialSpeed tau hmk t hx

/-- Off every retained buffer disc the truncated displacement vanishes. -/
theorem planeTruncatedTransverseDisplacement_eq_zero (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, n < N → x ∉ P.scaleFamily.bufferDisk n) :
    planeTruncatedTransverseDisplacement h P angularSpeed N t x = 0 :=
  Finset.sum_eq_zero fun m hm ↦
    cellTransverseDisplacement_eq_zero_of_not_mem_bufferDisk h P angularSpeed m t
      (hx m (Finset.mem_range.1 hm))

/-- Off every retained buffer disc the truncated flow is the identity. -/
theorem planeTruncatedTransverseFlow_eq_self (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, n < N → x ∉ P.scaleFamily.bufferDisk n) :
    planeTruncatedTransverseFlow h P angularSpeed N t x = x := by
  rw [planeTruncatedTransverseFlow,
    planeTruncatedTransverseDisplacement_eq_zero h P angularSpeed N t hx, add_zero]

/-- Off every retained buffer disc the truncated axial shift vanishes. -/
theorem planeTruncatedAxialShift_eq_zero (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, n < N → x ∉ P.scaleFamily.bufferDisk n) :
    planeTruncatedAxialShift h P axialSpeed tau N t x = 0 :=
  Finset.sum_eq_zero fun m hm ↦
    cellAxialDisplacement_eq_zero_of_not_mem_bufferDisk h P axialSpeed tau m t
      (hx m (Finset.mem_range.1 hm))

/-- A point of a *discarded* buffer disc lies in no retained one, by disjointness. -/
theorem not_mem_bufferDisk_of_le_of_mem {N k : ℕ} (hk : N ≤ k) {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk k) (n : ℕ) (hn : n < N) :
    x ∉ P.scaleFamily.bufferDisk n := by
  intro hmem
  have hlt : n < k := lt_of_lt_of_le hn hk
  exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hlt)) hmem hx

/-- **Every buffer disc is invariant under the truncated flow**: on a retained disc the flow is
the cell flow, which preserves it; a discarded disc meets no retained one, so the flow is the
identity there. -/
theorem planeTruncatedTransverseFlow_mem_bufferDisk (N : ℕ) (t : ℝ) {k : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk k) :
    planeTruncatedTransverseFlow h P angularSpeed N t x ∈ P.scaleFamily.bufferDisk k := by
  by_cases hk : k < N
  · rw [planeTruncatedTransverseFlow_eq_cell h P angularSpeed N t hk hx]
    exact cellTransverseFlow_mem_bufferDisk h P angularSpeed k t hx
  · rw [planeTruncatedTransverseFlow_eq_self h P angularSpeed N t
      (not_mem_bufferDisk_of_le_of_mem h P (Nat.not_lt.1 hk) hx)]
    exact hx

/-- The truncated displacement is supported in the placement chart. -/
theorem supportedInPlacementChart_planeTruncatedTransverseDisplacement (N : ℕ) (t : ℝ) :
    SupportedInPlacementChart (planeTruncatedTransverseDisplacement h P angularSpeed N t) := by
  intro x hx
  by_cases hbuf : ∃ k : ℕ, k < N ∧ x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, -, hk⟩ := hbuf
    exact P.bufferDisk_subset_chart k hk
  · exact absurd (planeTruncatedTransverseDisplacement_eq_zero h P angularSpeed N t
      fun n hn hmem ↦ hbuf ⟨n, hn, hmem⟩) hx

/-- The truncated axial shift is supported in the placement chart. -/
theorem supportedInPlacementChart_planeTruncatedAxialShift (N : ℕ) (t : ℝ) :
    SupportedInPlacementChart (planeTruncatedAxialShift h P axialSpeed tau N t) := by
  intro x hx
  by_cases hbuf : ∃ k : ℕ, k < N ∧ x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, -, hk⟩ := hbuf
    exact P.bufferDisk_subset_chart k hk
  · exact absurd (planeTruncatedAxialShift_eq_zero h P axialSpeed tau N t
      fun n hn hmem ↦ hbuf ⟨n, hn, hmem⟩) hx

/-! ### The group law of the truncated plane flow -/

/-- At time zero the truncated displacement vanishes. -/
@[simp] theorem planeTruncatedTransverseDisplacement_zero (N : ℕ) (x : ℝ × ℝ) :
    planeTruncatedTransverseDisplacement h P angularSpeed N 0 x = 0 :=
  Finset.sum_eq_zero fun m _ ↦ cellTransverseDisplacement_zero h P angularSpeed m x

/-- At time zero the truncated flow is the identity. -/
@[simp] theorem planeTruncatedTransverseFlow_zero (N : ℕ) (x : ℝ × ℝ) :
    planeTruncatedTransverseFlow h P angularSpeed N 0 x = x := by
  rw [planeTruncatedTransverseFlow, planeTruncatedTransverseDisplacement_zero, add_zero]

/-- At time zero the truncated axial shift vanishes. -/
@[simp] theorem planeTruncatedAxialShift_zero (N : ℕ) (x : ℝ × ℝ) :
    planeTruncatedAxialShift h P axialSpeed tau N 0 x = 0 :=
  Finset.sum_eq_zero fun m _ ↦ cellAxialDisplacement_zero h P axialSpeed tau m x

/-- **The group law of the truncated plane flow.**  Both sides are read cell by cell: on a
retained disc the flow is the cell flow, which obeys the cell group law and stays in the disc;
elsewhere both sides are the identity. -/
theorem planeTruncatedTransverseFlow_comp (N : ℕ) (s t : ℝ) (x : ℝ × ℝ) :
    planeTruncatedTransverseFlow h P angularSpeed N s
        (planeTruncatedTransverseFlow h P angularSpeed N t x) =
      planeTruncatedTransverseFlow h P angularSpeed N (s + t) x := by
  by_cases hbuf : ∃ k : ℕ, k < N ∧ x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk, hx⟩ := hbuf
    rw [planeTruncatedTransverseFlow_eq_cell h P angularSpeed N t hk hx,
      planeTruncatedTransverseFlow_eq_cell h P angularSpeed N s hk
        (cellTransverseFlow_mem_bufferDisk h P angularSpeed k t hx),
      planeTruncatedTransverseFlow_eq_cell h P angularSpeed N (s + t) hk hx,
      cellTransverseFlow_cellTransverseFlow]
  · have hout : ∀ n : ℕ, n < N → x ∉ P.scaleFamily.bufferDisk n :=
      fun n hn hmem ↦ hbuf ⟨n, hn, hmem⟩
    rw [planeTruncatedTransverseFlow_eq_self h P angularSpeed N t hout,
      planeTruncatedTransverseFlow_eq_self h P angularSpeed N s hout,
      planeTruncatedTransverseFlow_eq_self h P angularSpeed N (s + t) hout]

/-- **The axial cocycle of the truncated plane flow.** -/
theorem planeTruncatedAxialShift_comp (N : ℕ) (s t : ℝ) (x : ℝ × ℝ) :
    planeTruncatedAxialShift h P axialSpeed tau N s
        (planeTruncatedTransverseFlow h P angularSpeed N t x) +
      planeTruncatedAxialShift h P axialSpeed tau N t x =
      planeTruncatedAxialShift h P axialSpeed tau N (s + t) x := by
  by_cases hbuf : ∃ k : ℕ, k < N ∧ x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk, hx⟩ := hbuf
    rw [planeTruncatedTransverseFlow_eq_cell h P angularSpeed N t hk hx,
      planeTruncatedAxialShift_eq_cell h P axialSpeed tau N s hk
        (cellTransverseFlow_mem_bufferDisk h P angularSpeed k t hx),
      planeTruncatedAxialShift_eq_cell h P axialSpeed tau N t hk hx,
      planeTruncatedAxialShift_eq_cell h P axialSpeed tau N (s + t) hk hx,
      cellAxialDisplacement_cellTransverseFlow_add]
  · have hout : ∀ n : ℕ, n < N → x ∉ P.scaleFamily.bufferDisk n :=
      fun n hn hmem ↦ hbuf ⟨n, hn, hmem⟩
    rw [planeTruncatedTransverseFlow_eq_self h P angularSpeed N t hout,
      planeTruncatedAxialShift_eq_zero h P axialSpeed tau N s hout,
      planeTruncatedAxialShift_eq_zero h P axialSpeed tau N t hout,
      planeTruncatedAxialShift_eq_zero h P axialSpeed tau N (s + t) hout, add_zero]

/-- The truncated flow at `-t` undoes the truncated flow at `t`. -/
@[simp] theorem planeTruncatedTransverseFlow_neg (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planeTruncatedTransverseFlow h P angularSpeed N (-t)
      (planeTruncatedTransverseFlow h P angularSpeed N t x) = x := by
  rw [planeTruncatedTransverseFlow_comp, neg_add_cancel, planeTruncatedTransverseFlow_zero]

/-! ### Smoothness and the Jacobian determinant -/

/-- **The truncated displacement is `C^∞`**: it is a *finite* sum of the smooth cell
displacements of `FastDynamo/Dynamics/Flow/CellFlowMap.lean`, so the accumulation point of the
cells plays no role. -/
theorem contDiff_planeTruncatedTransverseDisplacement (N : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeTruncatedTransverseDisplacement h P angularSpeed N t) :=
  ContDiff.sum fun n _ ↦ contDiff_cellTransverseDisplacement h P angularSpeed n t

/-- **The truncated plane flow is `C^∞`.** -/
theorem contDiff_planeTruncatedTransverseFlow (N : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeTruncatedTransverseFlow h P angularSpeed N t) :=
  contDiff_id.add (contDiff_planeTruncatedTransverseDisplacement h P angularSpeed N t)

/-- **The truncated axial shift is `C^∞`.** -/
theorem contDiff_planeTruncatedAxialShift (N : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeTruncatedAxialShift h P axialSpeed tau N t) :=
  ContDiff.sum fun n _ ↦ contDiff_cellAxialDisplacement h P axialSpeed tau n t

/-- The truncated plane flow is differentiable everywhere. -/
theorem differentiable_planeTruncatedTransverseFlow (N : ℕ) (t : ℝ) :
    Differentiable ℝ (planeTruncatedTransverseFlow h P angularSpeed N t) :=
  (contDiff_planeTruncatedTransverseFlow h P angularSpeed N t).differentiable (by simp)

/-- The truncated axial shift is differentiable everywhere. -/
theorem differentiable_planeTruncatedAxialShift (N : ℕ) (t : ℝ) :
    Differentiable ℝ (planeTruncatedAxialShift h P axialSpeed tau N t) :=
  (contDiff_planeTruncatedAxialShift h P axialSpeed tau N t).differentiable (by simp)

/-- On a retained buffer disc — an open set — the truncated flow *is* the cell flow. -/
theorem planeTruncatedTransverseFlow_eventuallyEq_cell (N : ℕ) (t : ℝ) {k : ℕ} (hk : k < N)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk k) :
    planeTruncatedTransverseFlow h P angularSpeed N t =ᶠ[𝓝 x]
      cellTransverseFlow h P angularSpeed k t := by
  filter_upwards [(isOpen_bufferDisk h P k).mem_nhds hx] with y hy
  exact planeTruncatedTransverseFlow_eq_cell h P angularSpeed N t hk hy

/-- On a retained buffer disc the truncated axial shift *is* the cell axial displacement. -/
theorem planeTruncatedAxialShift_eventuallyEq_cell (N : ℕ) (t : ℝ) {k : ℕ} (hk : k < N)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk k) :
    planeTruncatedAxialShift h P axialSpeed tau N t =ᶠ[𝓝 x]
      cellAxialDisplacement h P axialSpeed tau k t := by
  filter_upwards [(isOpen_bufferDisk h P k).mem_nhds hx] with y hy
  exact planeTruncatedAxialShift_eq_cell h P axialSpeed tau N t hk hy

/-- Off every retained buffer disc the truncated flow is the identity on a whole neighbourhood:
each retained transverse cell displacement vanishes near such a point. -/
theorem planeTruncatedTransverseFlow_eventuallyEq_id (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, n < N → x ∉ P.scaleFamily.bufferDisk n) :
    planeTruncatedTransverseFlow h P angularSpeed N t =ᶠ[𝓝 x] id := by
  have hall : ∀ᶠ y in 𝓝 x, ∀ m ∈ Finset.range N,
      cellTransverseDisplacement h P angularSpeed m t y = 0 := by
    refine (Filter.eventually_all_finset (Finset.range N)).2 fun m hm ↦ ?_
    filter_upwards [cellTransverseDisplacement_eventuallyEq_zero_of_not_mem_bufferDisk
      h P angularSpeed m t (hx m (Finset.mem_range.1 hm))] with y hy using hy
  filter_upwards [hall] with y hy
  change y + ∑ m ∈ Finset.range N, cellTransverseDisplacement h P angularSpeed m t y = y
  rw [Finset.sum_eq_zero hy, add_zero]

/-- On a retained buffer disc the truncated differential is the cell differential. -/
theorem fderiv_planeTruncatedTransverseFlow_eq_cell (N : ℕ) (t : ℝ) {k : ℕ} (hk : k < N)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk k) :
    fderiv ℝ (planeTruncatedTransverseFlow h P angularSpeed N t) x =
      fderiv ℝ (cellTransverseFlow h P angularSpeed k t) x :=
  (planeTruncatedTransverseFlow_eventuallyEq_cell h P angularSpeed N t hk hx).fderiv_eq

/-- Off every retained buffer disc the truncated differential is the identity. -/
theorem fderiv_planeTruncatedTransverseFlow_eq_id (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, n < N → x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (planeTruncatedTransverseFlow h P angularSpeed N t) x =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  rw [(planeTruncatedTransverseFlow_eventuallyEq_id h P angularSpeed N t hx).fderiv_eq]
  exact fderiv_id

/-- **`det DΦ^{(N)}_t = 1` on the plane** (the proof of `cor:ideal-growth`): on a retained disc
the differential is the cell one, whose determinant is `1`; elsewhere it is the identity. -/
theorem det_fderiv_planeTruncatedTransverseFlow (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    LinearMap.det ((fderiv ℝ (planeTruncatedTransverseFlow h P angularSpeed N t) x :
      (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
  by_cases hbuf : ∃ k : ℕ, k < N ∧ x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk, hx⟩ := hbuf
    rw [fderiv_planeTruncatedTransverseFlow_eq_cell h P angularSpeed N t hk hx]
    exact det_fderiv_cellTransverseFlow h P angularSpeed k t x
  · rw [fderiv_planeTruncatedTransverseFlow_eq_id h P angularSpeed N t
      fun n hn hmem ↦ hbuf ⟨n, hn, hmem⟩]
    simp

/-! ## The `ℤ²`-periodisation of the truncated plane flow -/

/-- The `ℤ²`-periodisation of the truncated transverse displacement. -/
def planePeriodizedTruncatedDisplacement (N : ℕ) (t : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  periodization (planeTruncatedTransverseDisplacement h P angularSpeed N t)

/-- **The `ℤ²`-equivariant truncated transverse flow of the plane**, the map that descends to the
transverse two-torus. -/
def planePeriodizedTruncatedFlow (N : ℕ) (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  x + planePeriodizedTruncatedDisplacement h P angularSpeed N t x

/-- **The `ℤ²`-periodic truncated axial shift of the plane.** -/
def planePeriodizedTruncatedShift (N : ℕ) (t : ℝ) : ℝ × ℝ → ℝ :=
  periodization (planeTruncatedAxialShift h P axialSpeed tau N t)

/-- The periodised truncated displacement is `ℤ²`-periodic. -/
theorem isPeriodic_planePeriodizedTruncatedDisplacement (N : ℕ) (t : ℝ) :
    LatticePeriodic.IsPeriodic (planePeriodizedTruncatedDisplacement h P angularSpeed N t) :=
  isPeriodic_periodization _

/-- The periodised truncated axial shift is `ℤ²`-periodic, hence descends. -/
theorem isPeriodic_planePeriodizedTruncatedShift (N : ℕ) (t : ℝ) :
    LatticePeriodic.IsPeriodic (planePeriodizedTruncatedShift h P axialSpeed tau N t) :=
  isPeriodic_periodization _

/-- **`ℤ²`-equivariance of the periodised truncated flow.** -/
theorem planePeriodizedTruncatedFlow_add_int (N : ℕ) (t : ℝ) (x : ℝ × ℝ) (m n : ℤ) :
    planePeriodizedTruncatedFlow h P angularSpeed N t ((x.1 + m, x.2 + n)) =
      ((planePeriodizedTruncatedFlow h P angularSpeed N t x).1 + m,
        (planePeriodizedTruncatedFlow h P angularSpeed N t x).2 + n) := by
  have hper := isPeriodic_planePeriodizedTruncatedDisplacement h P angularSpeed N t x m n
  rw [planePeriodizedTruncatedFlow, planePeriodizedTruncatedFlow, hper]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- **The periodised truncated flow descends to the transverse two-torus.** -/
theorem isPeriodic_transverseTorusPoint_planePeriodizedTruncatedFlow (N : ℕ) (t : ℝ) :
    LatticePeriodic.IsPeriodic
      fun x : ℝ × ℝ ↦
        transverseTorusPoint (planePeriodizedTruncatedFlow h P angularSpeed N t x) := by
  intro x m n
  change transverseTorusPoint
      (planePeriodizedTruncatedFlow h P angularSpeed N t ((x.1 + m, x.2 + n))) = _
  rw [planePeriodizedTruncatedFlow_add_int]
  exact transverseTorusPoint_add_int _ m n

/-- **The periodised truncated displacement is a single translate of the chart-side one.** -/
theorem planePeriodizedTruncatedDisplacement_eq (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedDisplacement h P angularSpeed N t x =
      planeTruncatedTransverseDisplacement h P angularSpeed N t (x - chartTranslation x) :=
  (eventuallyEq_translate
    (supportedInPlacementChart_planeTruncatedTransverseDisplacement h P angularSpeed N t)
      x).self_of_nhds

/-- **The periodised truncated axial shift is a single translate of the chart-side one.** -/
theorem planePeriodizedTruncatedShift_eq (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedShift h P axialSpeed tau N t x =
      planeTruncatedAxialShift h P axialSpeed tau N t (x - chartTranslation x) :=
  (eventuallyEq_translate
    (supportedInPlacementChart_planeTruncatedAxialShift h P axialSpeed tau N t) x).self_of_nhds

/-- **The periodised truncated flow is the chart-side flow of the recentred point, translated
back.** -/
theorem planePeriodizedTruncatedFlow_eq (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedFlow h P angularSpeed N t x =
      planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x) +
        chartTranslation x := by
  rw [planePeriodizedTruncatedFlow, planePeriodizedTruncatedDisplacement_eq,
    planeTruncatedTransverseFlow_eq_add_displacement]
  abel

/-- Where the active translate is trivial, the periodised truncated flow is the chart-side one. -/
theorem planePeriodizedTruncatedFlow_eq_planeTruncated {x : ℝ × ℝ}
    (hx : localTranslationIndex x = 0) (N : ℕ) (t : ℝ) :
    planePeriodizedTruncatedFlow h P angularSpeed N t x =
      planeTruncatedTransverseFlow h P angularSpeed N t x := by
  have hzero : chartTranslation x = 0 := by
    rw [chartTranslation, hx]
    simp
  rw [planePeriodizedTruncatedFlow_eq, hzero, sub_zero, add_zero]

/-- Where the active translate is trivial, the periodised truncated axial shift is the chart-side
one. -/
theorem planePeriodizedTruncatedShift_eq_planeTruncated {x : ℝ × ℝ}
    (hx : localTranslationIndex x = 0) (N : ℕ) (t : ℝ) :
    planePeriodizedTruncatedShift h P axialSpeed tau N t x =
      planeTruncatedAxialShift h P axialSpeed tau N t x := by
  have hzero : chartTranslation x = 0 := by
    rw [chartTranslation, hx]
    simp
  rw [planePeriodizedTruncatedShift_eq, hzero, sub_zero]

/-- The chart-side truncated flow keeps the active translate trivial. -/
theorem localTranslationIndex_planeTruncatedTransverseFlow {x : ℝ × ℝ}
    (hx : localTranslationIndex x = 0) (N : ℕ) (t : ℝ) :
    localTranslationIndex (planeTruncatedTransverseFlow h P angularSpeed N t x) = 0 := by
  by_cases hbuf : ∃ k : ℕ, x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk⟩ := hbuf
    exact localTranslationIndex_eq_zero_of_mem_placementChart
      (P.bufferDisk_subset_chart k
        (planeTruncatedTransverseFlow_mem_bufferDisk h P angularSpeed N t hk))
  · rw [planeTruncatedTransverseFlow_eq_self h P angularSpeed N t
      fun n _ hmem ↦ hbuf ⟨n, hmem⟩]
    exact hx

/-- At time zero the periodised truncated flow is the identity. -/
@[simp] theorem planePeriodizedTruncatedFlow_zero (N : ℕ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedFlow h P angularSpeed N 0 x = x := by
  rw [planePeriodizedTruncatedFlow_eq, planeTruncatedTransverseFlow_zero]
  abel

/-- At time zero the periodised truncated axial shift vanishes. -/
@[simp] theorem planePeriodizedTruncatedShift_zero (N : ℕ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedShift h P axialSpeed tau N 0 x = 0 := by
  rw [planePeriodizedTruncatedShift_eq, planeTruncatedAxialShift_zero]

/-- **The group law of the periodised truncated plane flow.** -/
theorem planePeriodizedTruncatedFlow_comp (N : ℕ) (s t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedFlow h P angularSpeed N s
        (planePeriodizedTruncatedFlow h P angularSpeed N t x) =
      planePeriodizedTruncatedFlow h P angularSpeed N (s + t) x := by
  have hw := localTranslationIndex_sub_chartTranslation x
  have hflow := localTranslationIndex_planeTruncatedTransverseFlow h P angularSpeed hw N t
  have hpair : planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x) +
      chartTranslation x =
      ((planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x)).1 +
          ((localTranslationIndex x).1 : ℝ),
        (planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x)).2 +
          ((localTranslationIndex x).2 : ℝ)) := rfl
  have hshift : planePeriodizedTruncatedFlow h P angularSpeed N s
      (planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x) +
        chartTranslation x) =
      planePeriodizedTruncatedFlow h P angularSpeed N s
        (planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x)) +
        chartTranslation x := by
    have hper := isPeriodic_planePeriodizedTruncatedDisplacement h P angularSpeed N s
      (planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x))
      (localTranslationIndex x).1 (localTranslationIndex x).2
    rw [planePeriodizedTruncatedFlow, planePeriodizedTruncatedFlow, hpair, hper, ← hpair]
    abel
  rw [planePeriodizedTruncatedFlow_eq h P angularSpeed N t x, hshift,
    planePeriodizedTruncatedFlow_eq_planeTruncated h P angularSpeed hflow N s,
    planeTruncatedTransverseFlow_comp,
    planePeriodizedTruncatedFlow_eq h P angularSpeed N (s + t) x]

/-- **The axial cocycle of the periodised truncated plane flow.** -/
theorem planePeriodizedTruncatedShift_comp (N : ℕ) (s t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedShift h P axialSpeed tau N s
        (planePeriodizedTruncatedFlow h P angularSpeed N t x) +
      planePeriodizedTruncatedShift h P axialSpeed tau N t x =
      planePeriodizedTruncatedShift h P axialSpeed tau N (s + t) x := by
  have hw := localTranslationIndex_sub_chartTranslation x
  have hflow := localTranslationIndex_planeTruncatedTransverseFlow h P angularSpeed hw N t
  have hpair : planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x) +
      chartTranslation x =
      ((planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x)).1 +
          ((localTranslationIndex x).1 : ℝ),
        (planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x)).2 +
          ((localTranslationIndex x).2 : ℝ)) := rfl
  have hshift : planePeriodizedTruncatedShift h P axialSpeed tau N s
      (planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x) +
        chartTranslation x) =
      planePeriodizedTruncatedShift h P axialSpeed tau N s
        (planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x)) := by
    have hper := isPeriodic_planePeriodizedTruncatedShift h P axialSpeed tau N s
      (planeTruncatedTransverseFlow h P angularSpeed N t (x - chartTranslation x))
      (localTranslationIndex x).1 (localTranslationIndex x).2
    rw [hpair]
    exact hper
  rw [planePeriodizedTruncatedFlow_eq h P angularSpeed N t x, hshift,
    planePeriodizedTruncatedShift_eq_planeTruncated h P axialSpeed tau hflow N s,
    planePeriodizedTruncatedShift_eq h P axialSpeed tau N t x,
    planePeriodizedTruncatedShift_eq h P axialSpeed tau N (s + t) x,
    planeTruncatedAxialShift_comp]

/-- The periodised truncated flow at `-t` undoes the one at `t`. -/
@[simp] theorem planePeriodizedTruncatedFlow_neg (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedFlow h P angularSpeed N (-t)
      (planePeriodizedTruncatedFlow h P angularSpeed N t x) = x := by
  rw [planePeriodizedTruncatedFlow_comp, neg_add_cancel, planePeriodizedTruncatedFlow_zero]

/-- Near every point the periodised truncated displacement is a single translate of the
chart-side one. -/
theorem planePeriodizedTruncatedDisplacement_eventuallyEq (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedDisplacement h P angularSpeed N t =ᶠ[𝓝 x]
      fun y ↦
        planeTruncatedTransverseDisplacement h P angularSpeed N t (y - chartTranslation x) :=
  eventuallyEq_translate
    (supportedInPlacementChart_planeTruncatedTransverseDisplacement h P angularSpeed N t) x

/-- Near every point the periodised truncated axial shift is a single translate of the chart-side
one. -/
theorem planePeriodizedTruncatedShift_eventuallyEq (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedShift h P axialSpeed tau N t =ᶠ[𝓝 x]
      fun y ↦ planeTruncatedAxialShift h P axialSpeed tau N t (y - chartTranslation x) :=
  eventuallyEq_translate
    (supportedInPlacementChart_planeTruncatedAxialShift h P axialSpeed tau N t) x

/-- Near every point the periodised truncated flow is a single translate of the chart-side one. -/
theorem planePeriodizedTruncatedFlow_eventuallyEq (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTruncatedFlow h P angularSpeed N t =ᶠ[𝓝 x]
      fun y ↦ planeTruncatedTransverseFlow h P angularSpeed N t (y - chartTranslation x) +
        chartTranslation x := by
  filter_upwards [planePeriodizedTruncatedDisplacement_eventuallyEq h P angularSpeed N t x]
    with y hy
  rw [planePeriodizedTruncatedFlow, hy, planeTruncatedTransverseFlow_eq_add_displacement]
  abel

/-- **The periodised truncated flow is `C^∞`**, being locally a translate of a `C^∞` map. -/
theorem contDiff_planePeriodizedTruncatedFlow (N : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planePeriodizedTruncatedFlow h P angularSpeed N t) := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  refine ContDiffAt.congr_of_eventuallyEq ?_
    (planePeriodizedTruncatedFlow_eventuallyEq h P angularSpeed N t x)
  exact (((contDiff_planeTruncatedTransverseFlow h P angularSpeed N t).comp
    (contDiff_id.sub contDiff_const)).add contDiff_const).contDiffAt

/-- **The periodised truncated axial shift is `C^∞`.** -/
theorem contDiff_planePeriodizedTruncatedShift (N : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planePeriodizedTruncatedShift h P axialSpeed tau N t) := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  refine ContDiffAt.congr_of_eventuallyEq ?_
    (planePeriodizedTruncatedShift_eventuallyEq h P axialSpeed tau N t x)
  exact ((contDiff_planeTruncatedAxialShift h P axialSpeed tau N t).comp
    (contDiff_id.sub contDiff_const)).contDiffAt

/-- The periodised truncated flow is differentiable everywhere. -/
theorem differentiable_planePeriodizedTruncatedFlow (N : ℕ) (t : ℝ) :
    Differentiable ℝ (planePeriodizedTruncatedFlow h P angularSpeed N t) :=
  (contDiff_planePeriodizedTruncatedFlow h P angularSpeed N t).differentiable (by simp)

/-- The differential of the periodised truncated flow is the chart-side one at the recentred
point: translation has the identity differential. -/
theorem fderiv_planePeriodizedTruncatedFlow (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    fderiv ℝ (planePeriodizedTruncatedFlow h P angularSpeed N t) x =
      fderiv ℝ (planeTruncatedTransverseFlow h P angularSpeed N t) (x - chartTranslation x) := by
  have hsub : HasFDerivAt (fun y : ℝ × ℝ ↦ y - chartTranslation x)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := (hasFDerivAt_id x).sub_const _
  have hcomp := ((differentiable_planeTruncatedTransverseFlow h P angularSpeed N t
    (x - chartTranslation x)).hasFDerivAt).comp x hsub
  have hadd := hcomp.add_const (chartTranslation x)
  rw [ContinuousLinearMap.comp_id] at hadd
  exact ((planePeriodizedTruncatedFlow_eventuallyEq h P angularSpeed N t x).hasFDerivAt_iff.2
    hadd).fderiv

/-- **`det DΦ^{(N)}_t = 1` for the `ℤ²`-equivariant truncated plane flow.** -/
theorem det_fderiv_planePeriodizedTruncatedFlow (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    LinearMap.det ((fderiv ℝ (planePeriodizedTruncatedFlow h P angularSpeed N t) x :
      (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
  rw [fderiv_planePeriodizedTruncatedFlow h P angularSpeed N t x]
  exact det_fderiv_planeTruncatedTransverseFlow h P angularSpeed N t _

end ScaleFamily.TorusCellPlacement

end

end FastDynamo

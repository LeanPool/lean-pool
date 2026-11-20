/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Flow.PlaneFlow
public import LeanPool.FastDynamo.Global.TorusGlobalVelocityLipschitz

/-!
# Regularity and `ℤ²`-periodisation of the explicit particle flow

`FastDynamo/Dynamics/Flow/PlaneFlow.lean` builds the chart-side plane flow
`planeTransverseFlow` and `planeAxialShift` of `prop:particle-flow` and proves
its algebraic properties.  This file adds the two things the assembly needs.

**Regularity.**  The proof of `prop:particle-flow` obtains the Lipschitz bound from the global
Lipschitz property of the periodic lift (by `lem:global-velocity`) and its almost-everywhere
derivative; the quantitative statements below are the formalisation's own route to the same
bound: the flow is shown to be differentiable at *every* point, by the quadratic-decay argument
that the proof of `lem:global-velocity` applies to the velocity at the accumulation circle.  The
module follows the velocity's template `Global/TorusGlobalVelocityRegularity.lean` step by
step:

* away from the accumulation point `p_infinity = (0, 1/2)` the flow is locally the identity plus a
  *finite* sum of smooth cell displacements, hence `ContDiffAt ℝ (⊤ : ℕ∞)`;
* at `p_infinity` the `n`th displacement is `O(|t| ell_n) = O(|t| R_n^2)` while the `n`th disc sits
  at distance at least `R_n`, so the displacement is `O(dist(x, p_infinity)^2)` and the flow is
  differentiable there with derivative the **identity** — the flow counterpart of `Du(p_∞) = 0`;
* consequently `Differentiable ℝ (planeTransverseFlow t)` and
  `Differentiable ℝ (planeAxialShift t)` everywhere, with `fderiv` equal to the cell derivative
  of `Flow/CellFlowMap.lean` on each buffer disc, to the identity (resp. zero) off every buffer
  disc.

**`ℤ²`-periodisation.**  The chart-side flow is *not* `ℤ²`-equivariant: its
displacement is supported in `placementChart ⊆ (0,1/4) × (1/4,3/4)`, which meets no integer
translate of itself, exactly as for the velocity.  As there, the fix is the periodisation
`UnitBoxPeriodization.periodization` of `Global/TorusGlobalVelocityLipschitz.lean`:

`planePeriodizedTransverseFlow t x = x + sum_{k ∈ ℤ²} d(t, x - k)`,
`planePeriodizedAxialShift t = periodization (planeAxialShift t)`.

These *are* equivariant, `transverseTorusPoint ∘ planePeriodizedTransverseFlow t` and
`planePeriodizedAxialShift t` are `LatticePeriodic.IsPeriodic`, and they also satisfy the group
law and the axial cocycle: near every point the periodised object is a single translate of the
chart-side one, the recentred point has trivial translate index, and the chart-side flow keeps the
translate index trivial because it preserves both the placement chart and the complement of the
buffer discs.  This is the form `transverseDescent`
(`Analysis/LiteralThreeTorus.lean`) consumes.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## Local finiteness and smoothness away from the accumulation point -/

/-- Near any point other than the accumulation point the transverse displacement is a *finite*
sum of cell displacements (copy of
`exists_eventuallyEq_finsetSum_of_ne_accumulationPoint` for the flow). -/
theorem exists_eventuallyEq_finsetSum_planeTransverseDisplacement (t : ℝ) {x : ℝ × ℝ}
    (hx : x ≠ accumulationPoint) :
    ∃ N : ℕ, planeTransverseDisplacement h P angularSpeed t =ᶠ[nhds x]
      fun y ↦ ∑ n ∈ Finset.range N, cellTransverseDisplacement h P angularSpeed n t y := by
  obtain ⟨N, hN⟩ :=
    exists_forall_not_mem_bufferDisk_of_ne_accumulationPoint P.scaleFamily hx
  refine ⟨N, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (half_pos (dist_pos.mpr hx))] with y hy
  refine tsum_eq_sum ?_
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  exact cellTransverseDisplacement_eq_zero_of_not_mem_bufferDisk h P angularSpeed n t
    (hN n hn y hy)

/-- Near any point other than the accumulation point the axial shift is a *finite* sum of cell
displacements. -/
theorem exists_eventuallyEq_finsetSum_planeAxialShift (t : ℝ) {x : ℝ × ℝ}
    (hx : x ≠ accumulationPoint) :
    ∃ N : ℕ, planeAxialShift h P axialSpeed tau t =ᶠ[nhds x]
      fun y ↦ ∑ n ∈ Finset.range N, cellAxialDisplacement h P axialSpeed tau n t y := by
  obtain ⟨N, hN⟩ :=
    exists_forall_not_mem_bufferDisk_of_ne_accumulationPoint P.scaleFamily hx
  refine ⟨N, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (half_pos (dist_pos.mpr hx))] with y hy
  refine tsum_eq_sum ?_
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  exact cellAxialDisplacement_eq_zero_of_not_mem_bufferDisk h P axialSpeed tau n t (hN n hn y hy)

/-- **The plane flow is `C^infinity` away from the accumulation point**: locally it is the
identity plus a finite sum of smooth cell displacements. -/
theorem contDiffAt_planeTransverseFlow (t : ℝ) {x : ℝ × ℝ} (hx : x ≠ accumulationPoint) :
    ContDiffAt ℝ (⊤ : ℕ∞) (planeTransverseFlow h P angularSpeed t) x := by
  obtain ⟨N, heq⟩ :=
    exists_eventuallyEq_finsetSum_planeTransverseDisplacement h P angularSpeed t hx
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ ↦ y + ∑ n ∈ Finset.range N,
        cellTransverseDisplacement h P angularSpeed n t y) x :=
    contDiff_id.contDiffAt.add
      (ContDiffAt.sum fun n _ ↦
        (contDiff_cellTransverseDisplacement h P angularSpeed n t).contDiffAt)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [heq] with y hy
  rw [planeTransverseFlow_eq_add_displacement, hy]

/-- **The axial shift is `C^infinity` away from the accumulation point.** -/
theorem contDiffAt_planeAxialShift (t : ℝ) {x : ℝ × ℝ} (hx : x ≠ accumulationPoint) :
    ContDiffAt ℝ (⊤ : ℕ∞) (planeAxialShift h P axialSpeed tau t) x := by
  obtain ⟨N, heq⟩ := exists_eventuallyEq_finsetSum_planeAxialShift h P axialSpeed tau t hx
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ ↦ ∑ n ∈ Finset.range N,
        cellAxialDisplacement h P axialSpeed tau n t y) x :=
    ContDiffAt.sum fun n _ ↦
      (contDiff_cellAxialDisplacement h P axialSpeed tau n t).contDiffAt
  exact hsum.congr_of_eventuallyEq heq

/-! ## The accumulation point: quadratic decay and the derivative -/

/-- The transverse displacement obeys quadratic decay at the accumulation point: the `n`th
displacement is `O(|t| ell_n) = O(|t| R_n^2)` on a disc at distance at least `R_n` from
`p_infinity` (the flow analogue of the estimate `|u(y, x_3)| ≤ C |y - p_∞|²` in the proof of
`lem:global-velocity`; the proof of `prop:particle-flow` does not use it). -/
theorem norm_planeTransverseDisplacement_le_dist_sq (t : ℝ) (x : ℝ × ℝ) :
    ‖planeTransverseDisplacement h P angularSpeed t x‖ ≤
      2 * (|t| * |angularSpeed| * (1 + (h : ℝ))) * dist x accumulationPoint ^ 2 := by
  have hh : (0 : ℝ) < 1 + (h : ℝ) := by have := h.2.1; linarith
  have hconst : (0 : ℝ) ≤ 2 * (|t| * |angularSpeed| * (1 + (h : ℝ))) := by positivity
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [planeTransverseDisplacement_eq_cell_of_mem_bufferDisk h P angularSpeed t hn]
    calc ‖cellTransverseDisplacement h P angularSpeed n t x‖
        ≤ 2 * (|t| * |angularSpeed| * ((1 + (h : ℝ)) * P.scaleFamily.ell n)) :=
          norm_cellTransverseDisplacement_le_ell h P angularSpeed n t x
      _ = 2 * (|t| * |angularSpeed| * (1 + (h : ℝ))) * P.scaleFamily.ell n := by ring
      _ ≤ 2 * (|t| * |angularSpeed| * (1 + (h : ℝ))) * dist x accumulationPoint ^ 2 :=
          mul_le_mul_of_nonneg_left (ell_le_dist_accumulationPoint_sq h P hn) hconst
  · push Not at hbuffer
    rw [planeTransverseDisplacement_eq_zero_of_outside_buffers h P angularSpeed t hbuffer,
      norm_zero]
    positivity

/-- The axial shift obeys the same quadratic decay at the accumulation point. -/
theorem abs_planeAxialShift_le_dist_sq (t : ℝ) (x : ℝ × ℝ) :
    |planeAxialShift h P axialSpeed tau t x| ≤
      |t| * (|axialSpeed| + |tau| / p.wavenumber) * dist x accumulationPoint ^ 2 := by
  have hw := p.wavenumber_pos
  have hconst : (0 : ℝ) ≤ |t| * (|axialSpeed| + |tau| / p.wavenumber) := by positivity
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hn]
    calc |cellAxialDisplacement h P axialSpeed tau n t x|
        ≤ |t| * ((|axialSpeed| + |tau| / p.wavenumber) * P.scaleFamily.ell n) :=
          abs_cellAxialDisplacement_le h P axialSpeed tau n t x
      _ = |t| * (|axialSpeed| + |tau| / p.wavenumber) * P.scaleFamily.ell n := by ring
      _ ≤ |t| * (|axialSpeed| + |tau| / p.wavenumber) * dist x accumulationPoint ^ 2 :=
          mul_le_mul_of_nonneg_left (ell_le_dist_accumulationPoint_sq h P hn) hconst
  · push Not at hbuffer
    rw [planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t hbuffer, abs_zero]
    positivity

/-- The transverse displacement is Fréchet differentiable at the accumulation point with
derivative zero. -/
theorem hasFDerivAt_planeTransverseDisplacement_accumulationPoint (t : ℝ) :
    HasFDerivAt (planeTransverseDisplacement h P angularSpeed t)
      (0 : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) accumulationPoint := by
  have hbigO : planeTransverseDisplacement h P angularSpeed t =O[nhds accumulationPoint]
      fun x : ℝ × ℝ ↦ ‖x - accumulationPoint‖ ^ 2 := by
    apply Asymptotics.IsBigO.of_bound (2 * (|t| * |angularSpeed| * (1 + (h : ℝ))))
    filter_upwards [] with x
    have hbound := norm_planeTransverseDisplacement_le_dist_sq h P angularSpeed t x
    simpa only [dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖x - accumulationPoint‖)] using hbound
  exact hbigO.hasFDerivAt (by norm_num)

/-- **The plane flow is differentiable at the accumulation point, with derivative the identity.**
This is the flow counterpart of `Du(p_infinity) = 0` (`lem:global-velocity`, §3.4). -/
theorem hasFDerivAt_planeTransverseFlow_accumulationPoint (t : ℝ) :
    HasFDerivAt (planeTransverseFlow h P angularSpeed t)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) accumulationPoint := by
  have hsum := (hasFDerivAt_id (𝕜 := ℝ) accumulationPoint).add
    (hasFDerivAt_planeTransverseDisplacement_accumulationPoint h P angularSpeed t)
  rw [add_zero] at hsum
  exact hsum

/-- **The axial shift is differentiable at the accumulation point, with derivative zero.** -/
theorem hasFDerivAt_planeAxialShift_accumulationPoint (t : ℝ) :
    HasFDerivAt (planeAxialShift h P axialSpeed tau t)
      (0 : (ℝ × ℝ) →L[ℝ] ℝ) accumulationPoint := by
  have hbigO : planeAxialShift h P axialSpeed tau t =O[nhds accumulationPoint]
      fun x : ℝ × ℝ ↦ ‖x - accumulationPoint‖ ^ 2 := by
    apply Asymptotics.IsBigO.of_bound (|t| * (|axialSpeed| + |tau| / p.wavenumber))
    filter_upwards [] with x
    have hbound := abs_planeAxialShift_le_dist_sq h P axialSpeed tau t x
    simpa only [dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖x - accumulationPoint‖)] using hbound
  exact hbigO.hasFDerivAt (by norm_num)

/-! ## Differentiability everywhere, and the derivative cell by cell -/

/-- **The plane flow is differentiable at every point of the plane**, including the accumulation
point where it is not `C^1`. -/
theorem differentiable_planeTransverseFlow (t : ℝ) :
    Differentiable ℝ (planeTransverseFlow h P angularSpeed t) := by
  intro x
  by_cases hx : x = accumulationPoint
  · subst hx
    exact (hasFDerivAt_planeTransverseFlow_accumulationPoint h P angularSpeed t).differentiableAt
  · exact (contDiffAt_planeTransverseFlow h P angularSpeed t hx).differentiableAt (by simp)

/-- **The axial shift is differentiable at every point of the plane.** -/
theorem differentiable_planeAxialShift (t : ℝ) :
    Differentiable ℝ (planeAxialShift h P axialSpeed tau t) := by
  intro x
  by_cases hx : x = accumulationPoint
  · subst hx
    exact (hasFDerivAt_planeAxialShift_accumulationPoint h P axialSpeed tau t).differentiableAt
  · exact (contDiffAt_planeAxialShift h P axialSpeed tau t hx).differentiableAt (by simp)

/-- The derivative of the plane flow at the accumulation point is the identity. -/
theorem fderiv_planeTransverseFlow_accumulationPoint (t : ℝ) :
    fderiv ℝ (planeTransverseFlow h P angularSpeed t) accumulationPoint =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) :=
  (hasFDerivAt_planeTransverseFlow_accumulationPoint h P angularSpeed t).fderiv

/-- The derivative of the axial shift at the accumulation point vanishes. -/
theorem fderiv_planeAxialShift_accumulationPoint (t : ℝ) :
    fderiv ℝ (planeAxialShift h P axialSpeed tau t) accumulationPoint = 0 :=
  (hasFDerivAt_planeAxialShift_accumulationPoint h P axialSpeed tau t).fderiv

/-- **Inside a buffer disc the derivative of the plane flow is the cell derivative** of
`cellTransverseFlow` (`Flow/CellFlowMap.lean`). -/
theorem fderiv_planeTransverseFlow_eq_cell_of_mem_bufferDisk (t : ℝ) {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (planeTransverseFlow h P angularSpeed t) x =
      fderiv ℝ (cellTransverseFlow h P angularSpeed n t) x := by
  apply Filter.EventuallyEq.fderiv_eq
  have hopen : IsOpen (P.scaleFamily.bufferDisk n) := Metric.isOpen_ball
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hy

/-- **Inside a buffer disc the derivative of the axial shift is the cell derivative** of
`cellAxialDisplacement` (`Flow/CellFlowMap.lean`). -/
theorem fderiv_planeAxialShift_eq_cell_of_mem_bufferDisk (t : ℝ) {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (planeAxialShift h P axialSpeed tau t) x =
      fderiv ℝ (cellAxialDisplacement h P axialSpeed tau n t) x := by
  apply Filter.EventuallyEq.fderiv_eq
  have hopen : IsOpen (P.scaleFamily.bufferDisk n) := Metric.isOpen_ball
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hy

/-- Outside the buffer discs and away from the accumulation point the plane flow is the identity
on a whole neighbourhood, the angular profiles being supported in the local core discs. -/
theorem planeTransverseFlow_eventuallyEq_id_of_outside_buffers (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, x ∉ P.scaleFamily.bufferDisk n) (hne : x ≠ accumulationPoint) :
    planeTransverseFlow h P angularSpeed t =ᶠ[nhds x] id := by
  obtain ⟨N, heq⟩ :=
    exists_eventuallyEq_finsetSum_planeTransverseDisplacement h P angularSpeed t hne
  have hall : ∀ᶠ y in nhds x, ∀ n ∈ Finset.range N,
      cellTransverseDisplacement h P angularSpeed n t y = 0 := by
    refine (Filter.eventually_all_finset _).2 fun n _ ↦ ?_
    filter_upwards [cellTransverseDisplacement_eventuallyEq_zero_of_not_mem_bufferDisk
      h P angularSpeed n t (hx n)] with y hy using hy
  filter_upwards [heq, hall] with y hy hy0
  rw [planeTransverseFlow_eq_add_displacement, hy, Finset.sum_eq_zero hy0, add_zero]
  rfl

/-- **Outside the buffer discs the derivative of the plane flow is the identity.** -/
theorem fderiv_planeTransverseFlow_eq_id_of_outside_buffers (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (planeTransverseFlow h P angularSpeed t) x =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  by_cases hne : x = accumulationPoint
  · subst hne
    exact fderiv_planeTransverseFlow_accumulationPoint h P angularSpeed t
  · rw [(planeTransverseFlow_eventuallyEq_id_of_outside_buffers
      h P angularSpeed t hx hne).fderiv_eq]
    exact fderiv_id

/-- **Outside the buffer discs the derivative of the axial shift vanishes.**  The axial plateau
need not vanish on a neighbourhood of a boundary point, so this goes through the pointwise
vanishing of the cell derivatives rather than through a local identity. -/
theorem fderiv_planeAxialShift_eq_zero_of_outside_buffers (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (planeAxialShift h P axialSpeed tau t) x = 0 := by
  by_cases hne : x = accumulationPoint
  · subst hne
    exact fderiv_planeAxialShift_accumulationPoint h P axialSpeed tau t
  · obtain ⟨N, heq⟩ := exists_eventuallyEq_finsetSum_planeAxialShift h P axialSpeed tau t hne
    have hsum : HasFDerivAt
        (fun y : ℝ × ℝ ↦ ∑ n ∈ Finset.range N,
          cellAxialDisplacement h P axialSpeed tau n t y)
        (∑ n ∈ Finset.range N,
          fderiv ℝ (cellAxialDisplacement h P axialSpeed tau n t) x) x :=
      HasFDerivAt.fun_sum fun n _ ↦
        (((contDiff_cellAxialDisplacement h P axialSpeed tau n t).differentiable
          (by simp)) x).hasFDerivAt
    have hzero : ∀ n ∈ Finset.range N,
        fderiv ℝ (cellAxialDisplacement h P axialSpeed tau n t) x = 0 := by
      intro n _
      rw [fderiv_cellAxialDisplacement,
        fderiv_cellAxialSpeed_eq_zero_of_not_mem_bufferDisk h P axialSpeed tau n (hx n),
        smul_zero]
    rw [(hsum.congr_of_eventuallyEq heq).fderiv, Finset.sum_eq_zero hzero]

/-! ## Periodisation and `ℤ²`-equivariance -/

open UnitBoxPeriodization

/-- The transverse displacement is supported in the placement chart: it vanishes outside the
buffer discs, and those lie in `placementChart`. -/
theorem supportedInPlacementChart_planeTransverseDisplacement (t : ℝ) :
    SupportedInPlacementChart (planeTransverseDisplacement h P angularSpeed t) := by
  intro x hx
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    exact P.bufferDisk_subset_chart n hn
  · push Not at hbuffer
    exact absurd
      (planeTransverseDisplacement_eq_zero_of_outside_buffers h P angularSpeed t hbuffer) hx

/-- The axial shift is supported in the placement chart. -/
theorem supportedInPlacementChart_planeAxialShift (t : ℝ) :
    SupportedInPlacementChart (planeAxialShift h P axialSpeed tau t) := by
  intro x hx
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    exact P.bufferDisk_subset_chart n hn
  · push Not at hbuffer
    exact absurd (planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t hbuffer) hx

/-- The `ℤ²`-periodisation of the transverse displacement: the paper's displacement field
repeated over the integer lattice.  At every point the defining series has at most one nonzero
term, the chart being a proper subbox of the unit box. -/
def planePeriodizedTransverseDisplacement (t : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  periodization (planeTransverseDisplacement h P angularSpeed t)

/-- **The `ℤ²`-equivariant transverse flow of the plane**: the map that descends to the
transverse two-torus (the flow `Φ_t : T³ → T³` of `prop:particle-flow`). -/
def planePeriodizedTransverseFlow (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  x + planePeriodizedTransverseDisplacement h P angularSpeed t x

/-- **The `ℤ²`-periodic axial shift of the plane**: the map that descends to the transverse
two-torus. -/
def planePeriodizedAxialShift (t : ℝ) : ℝ × ℝ → ℝ :=
  periodization (planeAxialShift h P axialSpeed tau t)

/-- The periodised transverse displacement is `ℤ²`-periodic. -/
theorem isPeriodic_planePeriodizedTransverseDisplacement (t : ℝ) :
    LatticePeriodic.IsPeriodic (planePeriodizedTransverseDisplacement h P angularSpeed t) :=
  isPeriodic_periodization _

/-- **The periodised axial shift is `ℤ²`-periodic**, hence descends along `transverseDescent`. -/
theorem isPeriodic_planePeriodizedAxialShift (t : ℝ) :
    LatticePeriodic.IsPeriodic (planePeriodizedAxialShift h P axialSpeed tau t) :=
  isPeriodic_periodization _

/-- **`ℤ²`-equivariance of the periodised plane flow**: `Phi_t(x + m) = Phi_t(x) + m`. -/
theorem planePeriodizedTransverseFlow_add_int (t : ℝ) (x : ℝ × ℝ) (m n : ℤ) :
    planePeriodizedTransverseFlow h P angularSpeed t ((x.1 + m, x.2 + n)) =
      ((planePeriodizedTransverseFlow h P angularSpeed t x).1 + m,
        (planePeriodizedTransverseFlow h P angularSpeed t x).2 + n) := by
  have hper := isPeriodic_planePeriodizedTransverseDisplacement h P angularSpeed t x m n
  rw [planePeriodizedTransverseFlow, planePeriodizedTransverseFlow, hper]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- **The periodised flow descends to the transverse two-torus**: the composite with the quotient
map is `ℤ²`-periodic, which is exactly the hypothesis of `transverseDescent`. -/
theorem isPeriodic_transverseTorusPoint_planePeriodizedTransverseFlow (t : ℝ) :
    LatticePeriodic.IsPeriodic
      fun x : ℝ × ℝ ↦
        transverseTorusPoint (planePeriodizedTransverseFlow h P angularSpeed t x) := by
  intro x m n
  change transverseTorusPoint
      (planePeriodizedTransverseFlow h P angularSpeed t ((x.1 + m, x.2 + n))) = _
  rw [planePeriodizedTransverseFlow_add_int]
  exact transverseTorusPoint_add_int _ m n

/-! ### The active translate, and the identification with the chart-side flow -/

/-- The integer translate active near a point of the plane, read as a point of the plane. -/
def chartTranslation (x : ℝ × ℝ) : ℝ × ℝ :=
  (((localTranslationIndex x).1 : ℝ), ((localTranslationIndex x).2 : ℝ))

/-- On the placement chart the active translate is the trivial one. -/
theorem localTranslationIndex_eq_zero_of_mem_placementChart {x : ℝ × ℝ}
    (hx : x ∈ ScaleFamily.placementChart) : localTranslationIndex x = 0 := by
  obtain ⟨h1, h2⟩ := hx
  simp only [Set.mem_Ioo] at h1 h2
  refine Prod.ext ?_ ?_
  · change ⌈x.1 + 1 / 8⌉ - 1 = 0
    have : ⌈x.1 + 1 / 8⌉ = 1 := by
      refine Int.ceil_eq_iff.2 ⟨?_, ?_⟩ <;> push_cast <;> linarith [h1.1, h1.2]
    omega
  · change ⌈x.2⌉ - 1 = 0
    have : ⌈x.2⌉ = 1 := by
      refine Int.ceil_eq_iff.2 ⟨?_, ?_⟩ <;> push_cast <;> linarith [h2.1, h2.2]
    omega

/-- Recentring by the active translate lands in the fundamental position, where the active
translate is trivial. -/
theorem localTranslationIndex_sub_chartTranslation (x : ℝ × ℝ) :
    localTranslationIndex (x - chartTranslation x) = 0 := by
  refine Prod.ext ?_ ?_
  · change ⌈(x - chartTranslation x).1 + 1 / 8⌉ - 1 = 0
    have hrw : (x - chartTranslation x).1 + 1 / 8 =
        (x.1 + 1 / 8) - ((⌈x.1 + 1 / 8⌉ - 1 : ℤ) : ℝ) := by
      change x.1 - ((⌈x.1 + 1 / 8⌉ - 1 : ℤ) : ℝ) + 1 / 8 = _
      ring
    rw [hrw, Int.ceil_sub_intCast]
    omega
  · change ⌈(x - chartTranslation x).2⌉ - 1 = 0
    have hrw : (x - chartTranslation x).2 = x.2 - ((⌈x.2⌉ - 1 : ℤ) : ℝ) := rfl
    rw [hrw, Int.ceil_sub_intCast]
    omega

/-- **The periodised displacement is a single translate of the chart-side one.** -/
theorem planePeriodizedTransverseDisplacement_eq (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTransverseDisplacement h P angularSpeed t x =
      planeTransverseDisplacement h P angularSpeed t (x - chartTranslation x) :=
  (eventuallyEq_translate
    (supportedInPlacementChart_planeTransverseDisplacement h P angularSpeed t) x).self_of_nhds

/-- **The periodised axial shift is a single translate of the chart-side one.** -/
theorem planePeriodizedAxialShift_eq (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedAxialShift h P axialSpeed tau t x =
      planeAxialShift h P axialSpeed tau t (x - chartTranslation x) :=
  (eventuallyEq_translate
    (supportedInPlacementChart_planeAxialShift h P axialSpeed tau t) x).self_of_nhds

/-- Where the active translate is trivial, the periodised flow is the chart-side flow. -/
theorem planePeriodizedTransverseFlow_eq_planeTransverseFlow {x : ℝ × ℝ}
    (hx : localTranslationIndex x = 0) (t : ℝ) :
    planePeriodizedTransverseFlow h P angularSpeed t x =
      planeTransverseFlow h P angularSpeed t x := by
  have hzero : chartTranslation x = 0 := by
    rw [chartTranslation, hx]
    simp
  rw [planePeriodizedTransverseFlow,
    planePeriodizedTransverseDisplacement_eq h P angularSpeed t x, hzero, sub_zero,
    planeTransverseFlow_eq_add_displacement]

/-- Where the active translate is trivial, the periodised axial shift is the chart-side one. -/
theorem planePeriodizedAxialShift_eq_planeAxialShift {x : ℝ × ℝ}
    (hx : localTranslationIndex x = 0) (t : ℝ) :
    planePeriodizedAxialShift h P axialSpeed tau t x =
      planeAxialShift h P axialSpeed tau t x := by
  have hzero : chartTranslation x = 0 := by
    rw [chartTranslation, hx]
    simp
  rw [planePeriodizedAxialShift_eq h P axialSpeed tau t x, hzero, sub_zero]

/-- The chart-side flow keeps the active translate trivial: it is the identity off the buffer
discs, and maps each buffer disc into the placement chart. -/
theorem localTranslationIndex_planeTransverseFlow {x : ℝ × ℝ}
    (hx : localTranslationIndex x = 0) (t : ℝ) :
    localTranslationIndex (planeTransverseFlow h P angularSpeed t x) = 0 := by
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    exact localTranslationIndex_eq_zero_of_mem_placementChart
      (P.bufferDisk_subset_chart n (planeTransverseFlow_mem_bufferDisk h P angularSpeed t hn))
  · push Not at hbuffer
    rw [planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed t hbuffer]
    exact hx

/-- **The periodised flow is the chart-side flow of the recentred point, translated back.** -/
theorem planePeriodizedTransverseFlow_eq (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTransverseFlow h P angularSpeed t x =
      planeTransverseFlow h P angularSpeed t (x - chartTranslation x) + chartTranslation x := by
  rw [planePeriodizedTransverseFlow,
    planePeriodizedTransverseDisplacement_eq h P angularSpeed t x,
    planeTransverseFlow_eq_add_displacement]
  abel

/-! ### The group law of the periodised flow -/

/-- At time zero the periodised flow is the identity. -/
@[simp] theorem planePeriodizedTransverseFlow_zero (x : ℝ × ℝ) :
    planePeriodizedTransverseFlow h P angularSpeed 0 x = x := by
  rw [planePeriodizedTransverseFlow_eq, planeTransverseFlow_zero]
  abel

/-- At time zero the periodised axial shift vanishes. -/
@[simp] theorem planePeriodizedAxialShift_zero (x : ℝ × ℝ) :
    planePeriodizedAxialShift h P axialSpeed tau 0 x = 0 := by
  rw [planePeriodizedAxialShift_eq, planeAxialShift_zero]

/-- **The group law of the periodised plane flow** — the form `transverseDescent` needs for the
torus flow (`prop:particle-flow`). -/
theorem planePeriodizedTransverseFlow_planePeriodizedTransverseFlow (s t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTransverseFlow h P angularSpeed s
        (planePeriodizedTransverseFlow h P angularSpeed t x) =
      planePeriodizedTransverseFlow h P angularSpeed (s + t) x := by
  have hw := localTranslationIndex_sub_chartTranslation x
  have hflow := localTranslationIndex_planeTransverseFlow h P angularSpeed hw t
  have hshift : planePeriodizedTransverseFlow h P angularSpeed s
      (planeTransverseFlow h P angularSpeed t (x - chartTranslation x) + chartTranslation x) =
      planePeriodizedTransverseFlow h P angularSpeed s
        (planeTransverseFlow h P angularSpeed t (x - chartTranslation x)) +
        chartTranslation x := by
    have hpair : planeTransverseFlow h P angularSpeed t (x - chartTranslation x) +
        chartTranslation x =
        ((planeTransverseFlow h P angularSpeed t (x - chartTranslation x)).1 +
            ((localTranslationIndex x).1 : ℝ),
          (planeTransverseFlow h P angularSpeed t (x - chartTranslation x)).2 +
            ((localTranslationIndex x).2 : ℝ)) := rfl
    have hper := isPeriodic_planePeriodizedTransverseDisplacement h P angularSpeed s
      (planeTransverseFlow h P angularSpeed t (x - chartTranslation x))
      (localTranslationIndex x).1 (localTranslationIndex x).2
    rw [planePeriodizedTransverseFlow, planePeriodizedTransverseFlow, hpair, hper, ← hpair]
    abel
  rw [planePeriodizedTransverseFlow_eq h P angularSpeed t x, hshift,
    planePeriodizedTransverseFlow_eq_planeTransverseFlow h P angularSpeed hflow s,
    planeTransverseFlow_planeTransverseFlow,
    planePeriodizedTransverseFlow_eq h P angularSpeed (s + t) x]

/-- **The axial cocycle of the periodised flow.** -/
theorem planePeriodizedAxialShift_planePeriodizedTransverseFlow_add (s t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedAxialShift h P axialSpeed tau s
        (planePeriodizedTransverseFlow h P angularSpeed t x) +
      planePeriodizedAxialShift h P axialSpeed tau t x =
      planePeriodizedAxialShift h P axialSpeed tau (s + t) x := by
  have hw := localTranslationIndex_sub_chartTranslation x
  have hflow := localTranslationIndex_planeTransverseFlow h P angularSpeed hw t
  have hshift : planePeriodizedAxialShift h P axialSpeed tau s
      (planeTransverseFlow h P angularSpeed t (x - chartTranslation x) + chartTranslation x) =
      planePeriodizedAxialShift h P axialSpeed tau s
        (planeTransverseFlow h P angularSpeed t (x - chartTranslation x)) := by
    have hpair : planeTransverseFlow h P angularSpeed t (x - chartTranslation x) +
        chartTranslation x =
        ((planeTransverseFlow h P angularSpeed t (x - chartTranslation x)).1 +
            ((localTranslationIndex x).1 : ℝ),
          (planeTransverseFlow h P angularSpeed t (x - chartTranslation x)).2 +
            ((localTranslationIndex x).2 : ℝ)) := rfl
    have hper := isPeriodic_planePeriodizedAxialShift h P axialSpeed tau s
      (planeTransverseFlow h P angularSpeed t (x - chartTranslation x))
      (localTranslationIndex x).1 (localTranslationIndex x).2
    rw [hpair]
    exact hper
  rw [planePeriodizedTransverseFlow_eq h P angularSpeed t x, hshift,
    planePeriodizedAxialShift_eq_planeAxialShift h P axialSpeed tau hflow s,
    planePeriodizedAxialShift_eq h P axialSpeed tau t x,
    planePeriodizedAxialShift_eq h P axialSpeed tau (s + t) x,
    planeAxialShift_planeTransverseFlow_add]

/-- The periodised flow at `-t` undoes the periodised flow at `t`. -/
@[simp] theorem planePeriodizedTransverseFlow_neg_planePeriodizedTransverseFlow
    (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTransverseFlow h P angularSpeed (-t)
      (planePeriodizedTransverseFlow h P angularSpeed t x) = x := by
  rw [planePeriodizedTransverseFlow_planePeriodizedTransverseFlow, neg_add_cancel,
    planePeriodizedTransverseFlow_zero]

end ScaleFamily.TorusCellPlacement

end

end FastDynamo

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Flow.CellFlowMap

/-!
# The paper's explicit particle flow on the placement chart

`FastDynamo/Dynamics/Flow/CellFlowMap.lean` builds, for each cell `n`, the transverse
displacement `d_n(t, x) = R_{t omega_n(x)}(x - p_n) - (x - p_n)` and the axial displacement
`t g_n(x)` of `eq:explicit-particle-flow`.  This file assembles the *global*
plane flow of `prop:particle-flow`,

`Phi_t(x) = x + sum_n d_n(t, x)`,   `A_t(x) = sum_n t g_n(x)`,

named `planeTransverseFlow` and `planeAxialShift`, on the Euclidean placement chart `ℝ × ℝ`.

The buffer discs `D(p_n, R_n)` are pairwise disjoint, so at every point of the chart the two
series have **at most one nonzero term**; this is the same `tsum` bookkeeping that
`parameterizedFullGlobalEuclideanRealSource` uses for the velocity
(`Global/TorusGlobalVelocityQualitative.lean`), and it yields:

* the single-cell reduction `Phi_t = cellTransverseFlow n t` on `bufferDisk n`, and `Phi_t = id`
  off every buffer disc;
* invariance of each buffer disc — the angular profile is supported in the far smaller *local
  core disc*, where the rotation cannot leave the buffer;
* the group law `Phi_s ∘ Phi_t = Phi_{s+t}`, the axial cocycle
  `A_s(Phi_t x) + A_t(x) = A_{s+t}(x)` and the inverse `Phi_{-t}`;
* the uniform displacement rates `C_transverse`, `C_axial` and the time-Lipschitz estimates
  `dist (Phi_t x) (Phi_s x) ≤ C_transverse |t - s|` and
  `|A_t x - A_s x| ≤ C_axial |t - s|` needed for the strong continuity of the ideal group (the
  paper's `‖Φ_t - id‖_∞ ≤ ‖u‖_∞ |t|` in the proof of `cor:ideal-growth`).

The differential-calculus package (smoothness away from the accumulation point, differentiability
everywhere including at `p_infinity`, the `fderiv` formulas) and the `ℤ²`-periodisation that makes
the flow descend to the transverse two-torus are in
`FastDynamo/Dynamics/Flow/PlaneFlowRegularity.lean`.

**Metric convention.**  `ℝ × ℝ` carries the *sup* metric, so `bufferDisk n` is a square and
`‖·‖` is not the Euclidean radius; every radius that the rotation preserves is
`‖pairToWholePlane ·‖`.  The factor `2` in several constants below is exactly this
sup-versus-Euclidean loss, the same one carried by `globalVelocityLipschitzBound`.
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

/-! ## Euclidean support of the cell profiles -/

/-- The Euclidean cell radius `‖x - p_n‖` reaches the profile's support radius exactly when the
rescaled cell coordinate does. -/
theorem supportRadius_mul_ell_le_norm_iff (n : ℕ) (x : ℝ × ℝ) :
    (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ ↔
    1 + (h : ℝ) ≤ ‖helicalCellCoordinate h P n x‖ := by
  have hell : 0 < P.scaleFamily.ell n := P.scaleFamily.ell_pos n
  rw [norm_helicalCellCoordinate_eq_inv_mul, inv_mul_eq_div, le_div_iff₀ hell]

/-- The angular profile vanishes at Euclidean distance `(1 + h) ell_n` from the cell centre.  This
is the sharp *Euclidean* support statement;
`cellAngularSpeed_eq_zero_of_not_mem_localCoreDisk` (`Flow/CellProfiles.lean`) is its sup-metric
shadow. -/
theorem cellAngularSpeed_eq_zero_of_mul_ell_le_norm (n : ℕ) {x : ℝ × ℝ}
    (hx : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖) :
    cellAngularSpeed h P angularSpeed n x = 0 := by
  rw [cellAngularSpeed, parameterizedRadialCutoff_zero_of_radius_le_norm h
    ((supportRadius_mul_ell_le_norm_iff h P n x).1 hx), mul_zero]

/-- The differential of the angular profile vanishes at Euclidean distance `(1 + h) ell_n` too:
the radial slope `sigma_h` vanishes at and beyond the cutoff radius. -/
theorem fderiv_cellAngularSpeed_eq_zero_of_mul_ell_le_norm (n : ℕ) {x : ℝ × ℝ}
    (hx : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖) :
    fderiv ℝ (cellAngularSpeed h P angularSpeed n) x = 0 := by
  have hslope : parameterizedRadialRealSlope h (helicalCellCoordinate h P n x) = 0 :=
    parameterizedRadialRealSlope_eq_zero_of_radius_le_norm h
      ((supportRadius_mul_ell_le_norm_iff h P n x).1 hx)
  rw [fderiv_cellAngularSpeed, fderiv_parameterizedRadialCutoff, hslope]
  simp

/-- Outside the `n`th buffer disc the Euclidean cell radius already exceeds the angular profile's
support radius, by the placement's support-fit certificate `(1 + h) ell_n < R_n / 10`. -/
theorem mul_ell_le_norm_pairToWholePlane_of_not_mem_bufferDisk (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ := by
  have hfit := P.supportFit n
  have hR : P.scaleFamily.bufferRadius n ≤ dist x (P.scaleFamily.cellCenter n) := by
    simpa [ScaleFamily.bufferDisk, Metric.mem_ball, not_lt] using hx
  have hpair : dist x (P.scaleFamily.cellCenter n) ≤
      ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ := by
    have := dist_le_norm_pairToWholePlane_sub x (P.scaleFamily.cellCenter n)
    rwa [← map_sub] at this
  have hpos := P.scaleFamily.bufferRadius_pos n
  linarith

/-- The angular profile vanishes on a whole *neighbourhood* of every point outside the buffer
disc: its support sits inside the much smaller local core disc. -/
theorem cellAngularSpeed_eventuallyEq_zero_of_not_mem_bufferDisk (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    cellAngularSpeed h P angularSpeed n =ᶠ[nhds x] fun _ ↦ (0 : ℝ) := by
  have hfit := P.supportFit n
  have hRpos := P.scaleFamily.bufferRadius_pos n
  have hR : P.scaleFamily.bufferRadius n ≤ dist x (P.scaleFamily.cellCenter n) := by
    simpa [ScaleFamily.bufferDisk, Metric.mem_ball, not_lt] using hx
  have hrad : 0 < P.scaleFamily.bufferRadius n - (1 + (h : ℝ)) * P.scaleFamily.ell n := by
    linarith
  filter_upwards [Metric.ball_mem_nhds x hrad] with y hy
  have hyx : dist y x < P.scaleFamily.bufferRadius n -
      (1 + (h : ℝ)) * P.scaleFamily.ell n := by
    simpa [Metric.mem_ball] using hy
  have hyc : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤ dist y (P.scaleFamily.cellCenter n) := by
    have := dist_triangle x y (P.scaleFamily.cellCenter n)
    rw [dist_comm x y] at this
    linarith
  have hpair : dist y (P.scaleFamily.cellCenter n) ≤
      ‖pairToWholePlane (y - P.scaleFamily.cellCenter n)‖ := by
    have := dist_le_norm_pairToWholePlane_sub y (P.scaleFamily.cellCenter n)
    rwa [← map_sub] at this
  exact cellAngularSpeed_eq_zero_of_mul_ell_le_norm h P angularSpeed n (hyc.trans hpair)

/-- Where the angular profile is nonzero, the Euclidean cell radius is strictly below the
profile's support radius `(1 + h) ell_n`.  This is the contrapositive of the support statement,
and the geometric heart of the flow's cell-by-cell estimates. -/
theorem norm_pairToWholePlane_lt_of_cellAngularSpeed_ne_zero (n : ℕ) {x : ℝ × ℝ}
    (hx : cellAngularSpeed h P angularSpeed n x ≠ 0) :
    ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ <
      (1 + (h : ℝ)) * P.scaleFamily.ell n := by
  by_contra hge
  exact hx (cellAngularSpeed_eq_zero_of_mul_ell_le_norm h P angularSpeed n (not_lt.mp hge))

/-- The axial profile is the angular profile at the rescaled speed `ell_n * axialSpeed` plus the
axial plateau term; this is a definitional identity. -/
theorem cellAxialSpeed_eq_cellAngularSpeed_add (n : ℕ) :
    cellAxialSpeed h P axialSpeed tau n =
      cellAngularSpeed h P (P.scaleFamily.ell n * axialSpeed) n +
        fun y : ℝ × ℝ ↦ P.scaleFamily.axialAmplitude tau n * P.axialCellCutoff n y := rfl

/-- The differential of the axial plateau cutoff vanishes outside the buffer disc. -/
theorem fderiv_axialCellCutoff_eq_zero_of_not_mem_bufferDisk (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (P.axialCellCutoff n) x = 0 := by
  refine continuousLinearMap_eq_zero_pairBasis ?_ ?_ <;>
    · rw [P.fderiv_axialCellCutoff_apply_pairBasis n]
      exact P.axialCellCutoffDerivative_eq_zero_of_not_mem_bufferDisk n _ hx

/-- The differential of the axial profile vanishes outside the buffer disc. -/
theorem fderiv_cellAxialSpeed_eq_zero_of_not_mem_bufferDisk (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (cellAxialSpeed h P axialSpeed tau n) x = 0 := by
  have hnorm := mul_ell_le_norm_pairToWholePlane_of_not_mem_bufferDisk h P n hx
  have hang : HasFDerivAt
      (cellAngularSpeed h P (P.scaleFamily.ell n * axialSpeed) n)
      (0 : (ℝ × ℝ) →L[ℝ] ℝ) x := by
    have hd := ((differentiable_cellAngularSpeed h P
      (P.scaleFamily.ell n * axialSpeed) n) x).hasFDerivAt
    rwa [fderiv_cellAngularSpeed_eq_zero_of_mul_ell_le_norm h P _ n hnorm] at hd
  have hcut : HasFDerivAt (P.axialCellCutoff n) (0 : (ℝ × ℝ) →L[ℝ] ℝ) x := by
    have hd := (((P.axialCellCutoff_contDiff n).differentiable (by simp)) x).hasFDerivAt
    rwa [fderiv_axialCellCutoff_eq_zero_of_not_mem_bufferDisk h P n hx] at hd
  have hsum := hang.add (hcut.const_mul (P.scaleFamily.axialAmplitude tau n))
  rw [cellAxialSpeed_eq_cellAngularSpeed_add, hsum.fderiv, smul_zero, add_zero]

/-- The axial profile has the paper's `O(ell_n)` amplitude
(`eq:particle-cell-profiles`). -/
theorem abs_cellAxialSpeed_le (n : ℕ) (x : ℝ × ℝ) :
    |cellAxialSpeed h P axialSpeed tau n x| ≤
      (|axialSpeed| + |tau| / p.wavenumber) * P.scaleFamily.ell n := by
  have hell : (0 : ℝ) ≤ P.scaleFamily.ell n := (P.scaleFamily.ell_pos n).le
  have hcut := parameterizedRadialCutoff_mem_Icc h (helicalCellCoordinate h P n x)
  have hplat := P.axialCellCutoff_mem_Icc n x
  have hamp : P.scaleFamily.axialAmplitude tau n =
      (tau / p.wavenumber) * P.scaleFamily.ell n := rfl
  rw [cellAxialSpeed, hamp]
  have h1 : |P.scaleFamily.ell n * axialSpeed *
      parameterizedRadialCutoff h (helicalCellCoordinate h P n x)| ≤
      P.scaleFamily.ell n * |axialSpeed| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hell]
    have hle : |parameterizedRadialCutoff h (helicalCellCoordinate h P n x)| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hcut.1], hcut.2⟩
    exact mul_le_of_le_one_right (mul_nonneg hell (abs_nonneg _)) hle
  have h2 : |tau / p.wavenumber * P.scaleFamily.ell n * P.axialCellCutoff n x| ≤
      |tau| / p.wavenumber * P.scaleFamily.ell n := by
    rw [abs_mul, abs_mul, abs_of_nonneg hell, abs_div, abs_of_pos p.wavenumber_pos]
    have hle : |P.axialCellCutoff n x| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hplat.1], hplat.2⟩
    exact mul_le_of_le_one_right
      (mul_nonneg (div_nonneg (abs_nonneg tau) p.wavenumber_pos.le) hell) hle
  calc |P.scaleFamily.ell n * axialSpeed *
        parameterizedRadialCutoff h (helicalCellCoordinate h P n x) +
        tau / p.wavenumber * P.scaleFamily.ell n * P.axialCellCutoff n x| ≤
      _ + _ := abs_add_le _ _
    _ ≤ P.scaleFamily.ell n * |axialSpeed| + |tau| / p.wavenumber * P.scaleFamily.ell n :=
      add_le_add h1 h2
    _ = (|axialSpeed| + |tau| / p.wavenumber) * P.scaleFamily.ell n := by ring

/-- The angular speed times the Euclidean cell radius is uniformly bounded by
`|Omega| (1 + h) ell_n`: outside the profile's support the first factor vanishes, inside it the
second is below the support radius. -/
theorem abs_cellAngularSpeed_mul_norm_le (n : ℕ) (x : ℝ × ℝ) :
    |cellAngularSpeed h P angularSpeed n x| *
        ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ ≤
      |angularSpeed| * ((1 + (h : ℝ)) * P.scaleFamily.ell n) := by
  by_cases hw : cellAngularSpeed h P angularSpeed n x = 0
  · have hh : (0 : ℝ) < 1 + (h : ℝ) := by have := h.2.1; linarith
    have hell := P.scaleFamily.ell_pos n
    rw [hw, abs_zero, zero_mul]
    positivity
  · exact mul_le_mul (abs_cellAngularSpeed_le h P angularSpeed n x)
      (norm_pairToWholePlane_lt_of_cellAngularSpeed_ne_zero h P angularSpeed n hw).le
      (norm_nonneg _) (abs_nonneg _)

/-- Every point of the `n`th buffer disc is at squared distance at least `ell_n` from the
accumulation point: `ell_n = R_n^2` and `dist(x, p_infinity) > 3 R_n`. -/
theorem ell_le_dist_accumulationPoint_sq {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    P.scaleFamily.ell n ≤ dist x accumulationPoint ^ 2 := by
  have hsep :=
    three_mul_bufferRadius_lt_dist_accumulationPoint_of_mem_bufferDisk P.scaleFamily n hx
  have hRle : P.scaleFamily.bufferRadius n ≤ dist x accumulationPoint := by
    nlinarith [P.scaleFamily.bufferRadius_pos n]
  have hsq := (sq_le_sq₀ (P.scaleFamily.bufferRadius_nonneg n)
    (dist_nonneg : 0 ≤ dist x accumulationPoint)).2 hRle
  rwa [P.scaleFamily.bufferRadius_sq n] at hsq

/-! ## Vanishing and size of the single-cell displacements -/

/-- Outside the `n`th buffer disc the transverse cell displacement vanishes on a whole
neighbourhood: the angular profile is supported in the far smaller local core disc. -/
theorem cellTransverseDisplacement_eventuallyEq_zero_of_not_mem_bufferDisk (n : ℕ) (t : ℝ)
    {x : ℝ × ℝ} (hx : x ∉ P.scaleFamily.bufferDisk n) :
    cellTransverseDisplacement h P angularSpeed n t =ᶠ[nhds x] fun _ ↦ (0 : ℝ × ℝ) := by
  filter_upwards [cellAngularSpeed_eventuallyEq_zero_of_not_mem_bufferDisk h P angularSpeed n hx]
    with y hy
  simp [cellTransverseDisplacement, hy]

/-- On the `n`th buffer disc every *other* transverse cell displacement vanishes, the discs being
pairwise disjoint. -/
theorem cellTransverseDisplacement_eq_zero_on_distinct_buffer {m n : ℕ} (hmn : m ≠ n) (t : ℝ)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk n) :
    cellTransverseDisplacement h P angularSpeed m t x = 0 := by
  apply cellTransverseDisplacement_eq_zero_of_not_mem_bufferDisk
  intro hm
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hlt)) hm hx
  · exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hgt)) hx hm

/-- On the `n`th buffer disc every *other* axial cell displacement vanishes. -/
theorem cellAxialDisplacement_eq_zero_on_distinct_buffer {m n : ℕ} (hmn : m ≠ n) (t : ℝ)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk n) :
    cellAxialDisplacement h P axialSpeed tau m t x = 0 := by
  apply cellAxialDisplacement_eq_zero_of_not_mem_bufferDisk
  intro hm
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hlt)) hm hx
  · exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hgt)) hx hm

/-- The axial cell displacement has the paper's `O(|t| ell_n)` amplitude. -/
theorem abs_cellAxialDisplacement_le (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    |cellAxialDisplacement h P axialSpeed tau n t x| ≤
      |t| * ((|axialSpeed| + |tau| / p.wavenumber) * P.scaleFamily.ell n) := by
  rw [cellAxialDisplacement, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_cellAxialSpeed_le h P axialSpeed tau n x) (abs_nonneg t)

/-! ## The global plane flow -/

/-- The transverse displacement of the paper's explicit particle flow: the sum of the cell
displacements, which has at most one nonzero term at each point
(`eq:explicit-particle-flow`). -/
def planeTransverseDisplacement (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ∑' n : ℕ, cellTransverseDisplacement h P angularSpeed n t x

/-- The transverse part of the paper's explicit particle flow on the placement chart:
`x + sum_n d_n(t, x)` (`eq:explicit-particle-flow`). -/
def planeTransverseFlow (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  x + ∑' n : ℕ, cellTransverseDisplacement h P angularSpeed n t x

/-- The axial shift of the paper's explicit particle flow on the placement chart:
`sum_n t g_n(x)` (`eq:explicit-particle-flow`). -/
def planeAxialShift (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n : ℕ, cellAxialDisplacement h P axialSpeed tau n t x

/-- The transverse flow is the identity plus the transverse displacement. -/
theorem planeTransverseFlow_eq_add_displacement (t : ℝ) (x : ℝ × ℝ) :
    planeTransverseFlow h P angularSpeed t x =
      x + planeTransverseDisplacement h P angularSpeed t x := rfl

/-- **Single-cell reduction, transverse displacement.**  Inside a buffer disc the global
displacement is exactly its unique cell displacement. -/
theorem planeTransverseDisplacement_eq_cell_of_mem_bufferDisk (t : ℝ) {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    planeTransverseDisplacement h P angularSpeed t x =
      cellTransverseDisplacement h P angularSpeed n t x := by
  unfold planeTransverseDisplacement
  exact tsum_eq_single n fun m hmn ↦
    cellTransverseDisplacement_eq_zero_on_distinct_buffer h P angularSpeed hmn t hx

/-- **Single-cell reduction, transverse flow.**  Inside a buffer disc the global plane flow is
exactly the cell flow of that buffer. -/
theorem planeTransverseFlow_eq_cell_of_mem_bufferDisk (t : ℝ) {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    planeTransverseFlow h P angularSpeed t x = cellTransverseFlow h P angularSpeed n t x := by
  rw [planeTransverseFlow_eq_add_displacement,
    planeTransverseDisplacement_eq_cell_of_mem_bufferDisk h P angularSpeed t hx,
    cellTransverseFlow]

/-- **Single-cell reduction, axial shift.**  Inside a buffer disc the global axial shift is
exactly its unique cell contribution. -/
theorem planeAxialShift_eq_cell_of_mem_bufferDisk (t : ℝ) {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    planeAxialShift h P axialSpeed tau t x =
      cellAxialDisplacement h P axialSpeed tau n t x := by
  unfold planeAxialShift
  exact tsum_eq_single n fun m hmn ↦
    cellAxialDisplacement_eq_zero_on_distinct_buffer h P axialSpeed tau hmn t hx

/-- Outside every buffer disc the global transverse displacement vanishes. -/
theorem planeTransverseDisplacement_eq_zero_of_outside_buffers (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, x ∉ P.scaleFamily.bufferDisk n) :
    planeTransverseDisplacement h P angularSpeed t x = 0 := by
  unfold planeTransverseDisplacement
  simp_rw [cellTransverseDisplacement_eq_zero_of_not_mem_bufferDisk h P angularSpeed _ t (hx _)]
  exact tsum_zero

/-- Outside every buffer disc the global plane flow is the identity. -/
theorem planeTransverseFlow_eq_self_of_outside_buffers (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, x ∉ P.scaleFamily.bufferDisk n) :
    planeTransverseFlow h P angularSpeed t x = x := by
  rw [planeTransverseFlow_eq_add_displacement,
    planeTransverseDisplacement_eq_zero_of_outside_buffers h P angularSpeed t hx, add_zero]

/-- Outside every buffer disc the global axial shift vanishes. -/
theorem planeAxialShift_eq_zero_of_outside_buffers (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, x ∉ P.scaleFamily.bufferDisk n) :
    planeAxialShift h P axialSpeed tau t x = 0 := by
  unfold planeAxialShift
  simp_rw [cellAxialDisplacement_eq_zero_of_not_mem_bufferDisk h P axialSpeed tau _ t (hx _)]
  exact tsum_zero

/-! ## Invariance of the cell profile: the buffer discs -/

/-- **The global plane flow preserves every buffer disc.**  Inside the disc the flow is the cell
flow, and the cell flow preserves the disc (`cellTransverseFlow_mem_bufferDisk`,
`Flow/CellFlowMap.lean`). -/
theorem planeTransverseFlow_mem_bufferDisk (t : ℝ) {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    planeTransverseFlow h P angularSpeed t x ∈ P.scaleFamily.bufferDisk n := by
  rw [planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hx]
  exact cellTransverseFlow_mem_bufferDisk h P angularSpeed n t hx

/-! ## The group law and the axial cocycle -/

/-- At time zero the transverse displacement vanishes. -/
@[simp] theorem planeTransverseDisplacement_zero (x : ℝ × ℝ) :
    planeTransverseDisplacement h P angularSpeed 0 x = 0 := by
  unfold planeTransverseDisplacement
  simp

/-- At time zero the plane flow is the identity. -/
@[simp] theorem planeTransverseFlow_zero (x : ℝ × ℝ) :
    planeTransverseFlow h P angularSpeed 0 x = x := by
  rw [planeTransverseFlow_eq_add_displacement, planeTransverseDisplacement_zero, add_zero]

/-- At time zero the axial shift vanishes. -/
@[simp] theorem planeAxialShift_zero (x : ℝ × ℝ) :
    planeAxialShift h P axialSpeed tau 0 x = 0 := by
  unfold planeAxialShift
  simp

/-- **The group law of the plane flow** (`eq:explicit-particle-flow`): the whole
point of freezing the profiles on the invariant circles of each cell. -/
theorem planeTransverseFlow_planeTransverseFlow (s t : ℝ) (x : ℝ × ℝ) :
    planeTransverseFlow h P angularSpeed s (planeTransverseFlow h P angularSpeed t x) =
      planeTransverseFlow h P angularSpeed (s + t) x := by
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hn,
      planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed s
        (cellTransverseFlow_mem_bufferDisk h P angularSpeed n t hn),
      planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed (s + t) hn,
      cellTransverseFlow_cellTransverseFlow]
  · push Not at hbuffer
    rw [planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed t hbuffer,
      planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed s hbuffer,
      planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed (s + t) hbuffer]

/-- **The axial cocycle identity** (`eq:explicit-particle-flow`): the axial shift
accumulates along the transverse orbit. -/
theorem planeAxialShift_planeTransverseFlow_add (s t : ℝ) (x : ℝ × ℝ) :
    planeAxialShift h P axialSpeed tau s (planeTransverseFlow h P angularSpeed t x) +
        planeAxialShift h P axialSpeed tau t x =
      planeAxialShift h P axialSpeed tau (s + t) x := by
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hn,
      planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau s
        (cellTransverseFlow_mem_bufferDisk h P angularSpeed n t hn),
      planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hn,
      planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau (s + t) hn,
      cellAxialDisplacement_cellTransverseFlow_add]
  · push Not at hbuffer
    rw [planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed t hbuffer,
      planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau s hbuffer,
      planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t hbuffer,
      planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau (s + t) hbuffer, add_zero]

/-- The plane flow at `-t` undoes the plane flow at `t`. -/
@[simp] theorem planeTransverseFlow_neg_planeTransverseFlow (t : ℝ) (x : ℝ × ℝ) :
    planeTransverseFlow h P angularSpeed (-t) (planeTransverseFlow h P angularSpeed t x) = x := by
  rw [planeTransverseFlow_planeTransverseFlow, neg_add_cancel,
    planeTransverseFlow_zero]

/-! ## Uniform displacement bounds and the time-Lipschitz estimate -/

/-- The uniform transverse displacement rate of the plane flow: `2 |Omega| (1 + h) ell_0`, twice
the largest cell's angular speed times its largest Euclidean radius.  The factor two is the
sup-versus-Euclidean loss of the pair chart. -/
def planeTransverseSpeedBound : ℝ :=
  2 * (|angularSpeed| * ((1 + (h : ℝ)) * P.scaleFamily.ell 0))

/-- The uniform axial displacement rate of the plane flow:
`(|U| + |tau| / k_*) ell_0` (`eq:particle-cell-profiles`). -/
def planeAxialSpeedBound : ℝ :=
  (|axialSpeed| + |tau| / p.wavenumber) * P.scaleFamily.ell 0

/-- The transverse displacement rate is nonnegative. -/
theorem planeTransverseSpeedBound_nonneg :
    0 ≤ planeTransverseSpeedBound h P angularSpeed := by
  have hh : (0 : ℝ) < 1 + (h : ℝ) := by have := h.2.1; linarith
  have hell := P.scaleFamily.ell_pos 0
  rw [planeTransverseSpeedBound]
  positivity

/-- The axial displacement rate is nonnegative. -/
theorem planeAxialSpeedBound_nonneg :
    0 ≤ planeAxialSpeedBound h P axialSpeed tau := by
  have hell := P.scaleFamily.ell_pos 0
  have hw := p.wavenumber_pos
  rw [planeAxialSpeedBound]
  positivity

/-- The `n`th cell's transverse displacement rate is dominated by the zeroth cell's, the scales
`ell_n` being nonincreasing. -/
theorem cell_le_planeTransverseSpeedBound (n : ℕ) :
    2 * (|angularSpeed| * ((1 + (h : ℝ)) * P.scaleFamily.ell n)) ≤
      planeTransverseSpeedBound h P angularSpeed := by
  have hh : (0 : ℝ) < 1 + (h : ℝ) := by have := h.2.1; linarith
  have hmono : P.scaleFamily.ell n ≤ P.scaleFamily.ell 0 :=
    ScaleFamily.ell_le_ell_zero P.scaleFamily n
  rw [planeTransverseSpeedBound]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hh.le) (abs_nonneg _))
    (by norm_num)

/-- The `n`th cell's axial displacement rate is dominated by the zeroth cell's. -/
theorem cell_le_planeAxialSpeedBound (n : ℕ) :
    (|axialSpeed| + |tau| / p.wavenumber) * P.scaleFamily.ell n ≤
      planeAxialSpeedBound h P axialSpeed tau := by
  have hmono : P.scaleFamily.ell n ≤ P.scaleFamily.ell 0 :=
    ScaleFamily.ell_le_ell_zero P.scaleFamily n
  rw [planeAxialSpeedBound]
  exact mul_le_mul_of_nonneg_left hmono
    (add_nonneg (abs_nonneg _) (div_nonneg (abs_nonneg _) p.wavenumber_pos.le))

/-- **The flow is Lipschitz in time, uniformly in space** (needed for the strong continuity of
the ideal group): two times of the same orbit differ by at most the uniform rate times the time
gap. -/
theorem dist_planeTransverseFlow_le (s t : ℝ) (x : ℝ × ℝ) :
    dist (planeTransverseFlow h P angularSpeed t x)
        (planeTransverseFlow h P angularSpeed s x) ≤
      planeTransverseSpeedBound h P angularSpeed * |t - s| := by
  have hnonneg := planeTransverseSpeedBound_nonneg h P angularSpeed
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    have hgen : ∀ u : ℝ, planeTransverseFlow h P angularSpeed u x -
        P.scaleFamily.cellCenter n =
        planeRotate (u * cellAngularSpeed h P angularSpeed n x)
          (x - P.scaleFamily.cellCenter n) := by
      intro u
      rw [planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed u hn]
      exact cellTransverseFlow_sub_cellCenter h P angularSpeed n u x
    have hkey : planeTransverseFlow h P angularSpeed t x -
        planeTransverseFlow h P angularSpeed s x =
        planeRotate (t * cellAngularSpeed h P angularSpeed n x)
            (x - P.scaleFamily.cellCenter n) -
          planeRotate (s * cellAngularSpeed h P angularSpeed n x)
            (x - P.scaleFamily.cellCenter n) := by
      rw [← hgen t, ← hgen s]
      abel
    rw [dist_eq_norm, hkey]
    calc ‖planeRotate (t * cellAngularSpeed h P angularSpeed n x)
            (x - P.scaleFamily.cellCenter n) -
          planeRotate (s * cellAngularSpeed h P angularSpeed n x)
            (x - P.scaleFamily.cellCenter n)‖
        ≤ 2 * (|t * cellAngularSpeed h P angularSpeed n x -
            s * cellAngularSpeed h P angularSpeed n x| *
            ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖) :=
          norm_planeRotate_sub_planeRotate_le _ _ _
      _ = 2 * (|cellAngularSpeed h P angularSpeed n x| *
            ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖) * |t - s| := by
          rw [← sub_mul, abs_mul]
          ring
      _ ≤ 2 * (|angularSpeed| * ((1 + (h : ℝ)) * P.scaleFamily.ell n)) * |t - s| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (abs_cellAngularSpeed_mul_norm_le h P angularSpeed n x) (by norm_num))
            (abs_nonneg _)
      _ ≤ planeTransverseSpeedBound h P angularSpeed * |t - s| :=
          mul_le_mul_of_nonneg_right
            (cell_le_planeTransverseSpeedBound h P angularSpeed n) (abs_nonneg _)
  · push Not at hbuffer
    rw [planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed t hbuffer,
      planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed s hbuffer, dist_self]
    positivity

/-- **The axial shift is Lipschitz in time, uniformly in space.** -/
theorem abs_planeAxialShift_sub_le (s t : ℝ) (x : ℝ × ℝ) :
    |planeAxialShift h P axialSpeed tau t x - planeAxialShift h P axialSpeed tau s x| ≤
      planeAxialSpeedBound h P axialSpeed tau * |t - s| := by
  have hnonneg := planeAxialSpeedBound_nonneg h P axialSpeed tau
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hn,
      planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau s hn,
      cellAxialDisplacement, cellAxialDisplacement, ← sub_mul, abs_mul]
    rw [mul_comm (planeAxialSpeedBound h P axialSpeed tau)]
    exact mul_le_mul_of_nonneg_left
      ((abs_cellAxialSpeed_le h P axialSpeed tau n x).trans
        (cell_le_planeAxialSpeedBound h P axialSpeed tau n)) (abs_nonneg _)
  · push Not at hbuffer
    rw [planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t hbuffer,
      planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau s hbuffer, sub_self, abs_zero]
    positivity

end ScaleFamily.TorusCellPlacement

end

end FastDynamo

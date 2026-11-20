/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.PairChartRotation
public import LeanPool.FastDynamo.Dynamics.Flow.CellProfiles

/-!
# The explicit particle flow inside one cell

`prop:particle-flow` solves the transport equation of the ideal induction group by an explicit
formula: inside the `n`th buffer disc the velocity is the rigid screw motion
`(omega_n(r) (y - p_n)^perp, g_n(r))` of the first display of its proof, so the trajectory through
`y` rotates around the cell centre `p_n` at the constant angular speed `omega_n(r)` and drifts
axially at the constant speed `g_n(r)`.  In the chart coordinates this is
`eq:explicit-particle-flow`,

`Phi_t (y, x_3) = (p_n + R_{t omega_n(r)} (y - p_n), x_3 + t g_n(r))`.

This module supplies the `n`th cell's two displacement fields and the transverse cell map

* `cellTransverseDisplacement h P angularSpeed n t x = R_{t omega_n} (x - p_n) - (x - p_n)`,
* `cellAxialDisplacement h P axialSpeed tau n t x = t g_n(x)`,
* `cellTransverseFlow h P angularSpeed n t x = x + cellTransverseDisplacement … n t x`,

together with everything the global flow layer and the ideal induction group need from them:

* both displacements vanish at `t = 0`, the transverse one outside the local core disc and the
  axial one outside the buffer disc, and the cell map maps a buffer disc into itself;
* **radius invariance** (the display `d/dt |y - p_n|² = 0` in the proof of
  `prop:particle-flow`): the cell map preserves the Euclidean radius
  `‖pairToWholePlane (x - p_n)‖`, hence it preserves both profiles, which is exactly what turns
  the ODE of the first paragraph of that proof into the closed formula;
* the resulting **group law** `Phi_s ∘ Phi_t = Phi_{s+t}` on a single cell, with inverse `Phi_{-t}`;
* smoothness of both displacements in `x`;
* the **spatial differential** of the proof of `prop:particle-flow`,
  `D_y (R_{t omega_n(r)} z) = R_{t omega_n(r)} [id + t omega_n'(r) J z ⊗ e_r]`, its operator norm
  bound from the shear bound `eq:omega-shear-bound`, and
  `det D Phi_t = 1` (which the proof of `cor:ideal-growth` obtains almost everywhere from
  Liouville's formula and `div u = 0`; here it is proved pointwise from the closed formula);
* the **time derivative**, which verifies that the closed formula solves the ODE (the paper
  instead derives the formula from the ODE in the first paragraph of the proof of
  `prop:particle-flow`).

**Metric warning.**  `ℝ × ℝ` carries the product (sup) metric, so the rotation is *not* an
isometry of `‖·‖`; only the Euclidean radius `‖pairToWholePlane z‖` is preserved, and every
conversion between the two norms costs the factor `2` already carried by
`globalVelocityLipschitzBound`.  Two such factors appear in
`norm_fderiv_cellTransverseFlow_le`: one from `norm_planeRotateCLM_le`, one inside the
angular shear bound `norm_sub_cellCenter_mul_norm_fderiv_cellAngularSpeed_le`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Metric

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The two displacements and the transverse cell map -/

/-- The transverse displacement of `eq:explicit-particle-flow` inside the `n`th
cell: the point `x` is rotated around the cell centre `p_n` through the angle
`t omega_n(r)`, and the displacement is the difference from the identity. -/
def cellTransverseDisplacement (n : ℕ) (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  planeRotate (t * cellAngularSpeed h P angularSpeed n x) (x - P.scaleFamily.cellCenter n) -
    (x - P.scaleFamily.cellCenter n)

/-- The axial displacement of `eq:explicit-particle-flow` inside the `n`th cell:
the axial coordinate translates at the constant speed `g_n(r)`. -/
def cellAxialDisplacement (n : ℕ) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  t * cellAxialSpeed h P axialSpeed tau n x

/-- The transverse component of the `n`th cell's time-`t` flow map,
`x ↦ p_n + R_{t omega_n(r)} (x - p_n)` (`eq:explicit-particle-flow`). -/
def cellTransverseFlow (n : ℕ) (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  x + cellTransverseDisplacement h P angularSpeed n t x

/-- The closed form `p_n + R_{t omega_n(r)} (x - p_n)` of the transverse cell map, the shape in
which `eq:explicit-particle-flow` is displayed. -/
theorem cellTransverseFlow_eq (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    cellTransverseFlow h P angularSpeed n t x =
      P.scaleFamily.cellCenter n +
        planeRotate (t * cellAngularSpeed h P angularSpeed n x)
          (x - P.scaleFamily.cellCenter n) := by
  simp [cellTransverseFlow, cellTransverseDisplacement]
  abel

/-- The transverse cell map, recentred at the cell centre: the rotated radius vector. -/
theorem cellTransverseFlow_sub_cellCenter (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    cellTransverseFlow h P angularSpeed n t x - P.scaleFamily.cellCenter n =
      planeRotate (t * cellAngularSpeed h P angularSpeed n x)
        (x - P.scaleFamily.cellCenter n) := by
  rw [cellTransverseFlow_eq]
  abel

/-! ## The time origin -/

/-- At `t = 0` nothing moves transversally. -/
@[simp] theorem cellTransverseDisplacement_zero (n : ℕ) (x : ℝ × ℝ) :
    cellTransverseDisplacement h P angularSpeed n 0 x = 0 := by
  simp [cellTransverseDisplacement]

/-- At `t = 0` nothing moves axially. -/
@[simp] theorem cellAxialDisplacement_zero (n : ℕ) (x : ℝ × ℝ) :
    cellAxialDisplacement h P axialSpeed tau n 0 x = 0 := by
  simp [cellAxialDisplacement]

/-- The time-zero cell map is the identity. -/
@[simp] theorem cellTransverseFlow_zero (n : ℕ) (x : ℝ × ℝ) :
    cellTransverseFlow h P angularSpeed n 0 x = x := by
  simp [cellTransverseFlow]

/-! ## Radius invariance and invariance of the two profiles

The proof of `prop:particle-flow` verifies `d/dt |y - p_n|^2 = 0` along a trajectory; in the
closed form this is the exact rotation invariance of the Euclidean radius. -/

/-- The cell map preserves the Euclidean radius `|x - p_n|` (proof of `prop:particle-flow`).
The sup norm
`‖·‖` of `ℝ × ℝ` is *not* preserved, only `‖pairToWholePlane ·‖`. -/
theorem norm_pairToWholePlane_cellTransverseFlow_sub_cellCenter (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    ‖pairToWholePlane (cellTransverseFlow h P angularSpeed n t x -
        P.scaleFamily.cellCenter n)‖ =
      ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ := by
  rw [cellTransverseFlow_sub_cellCenter, norm_pairToWholePlane_planeRotate]

/-- The angular profile is constant along a cell trajectory ("`r` is invariant", proof of
`prop:particle-flow`): it depends on `x`
only through the Euclidean radius, which the cell map preserves. -/
theorem cellAngularSpeed_cellTransverseFlow (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    cellAngularSpeed h P angularSpeed n (cellTransverseFlow h P angularSpeed n t x) =
      cellAngularSpeed h P angularSpeed n x :=
  cellAngularSpeed_congr_of_norm_eq h P angularSpeed n
    (norm_pairToWholePlane_cellTransverseFlow_sub_cellCenter h P angularSpeed n t x)

/-- The axial profile is constant along a cell trajectory (proof of `prop:particle-flow`). -/
theorem cellAxialSpeed_cellTransverseFlow (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    cellAxialSpeed h P axialSpeed tau n (cellTransverseFlow h P angularSpeed n t x) =
      cellAxialSpeed h P axialSpeed tau n x :=
  cellAxialSpeed_congr_of_norm_eq h P axialSpeed tau n
    (norm_pairToWholePlane_cellTransverseFlow_sub_cellCenter h P angularSpeed n t x)

/-! ## The group law on a single cell -/

/-- The cell maps form a one-parameter group: rotating through `t omega_n(r)` and then through
`s omega_n(r)` — the radius, hence the angular speed, being unchanged — rotates through
`(s + t) omega_n(r)` (constant angular speed, proof of `prop:particle-flow`). -/
theorem cellTransverseFlow_cellTransverseFlow (n : ℕ) (s t : ℝ) (x : ℝ × ℝ) :
    cellTransverseFlow h P angularSpeed n s (cellTransverseFlow h P angularSpeed n t x) =
      cellTransverseFlow h P angularSpeed n (s + t) x := by
  rw [cellTransverseFlow_eq h P angularSpeed n s, cellTransverseFlow_sub_cellCenter,
    cellAngularSpeed_cellTransverseFlow, planeRotate_planeRotate,
    cellTransverseFlow_eq h P angularSpeed n (s + t)]
  ring_nf

/-- The cell map at `-t` inverts the cell map at `t`. -/
@[simp] theorem cellTransverseFlow_neg_cellTransverseFlow (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    cellTransverseFlow h P angularSpeed n (-t) (cellTransverseFlow h P angularSpeed n t x) = x := by
  rw [cellTransverseFlow_cellTransverseFlow]
  simp

/-- The axial displacements add along the transverse trajectory: the axial speed is constant
along it, so the axial shift over `[0, s + t]` splits as the shift over `[0, t]` plus the shift
over `[0, s]` started at the new point (constant axial speed, proof of
`prop:particle-flow`). -/
theorem cellAxialDisplacement_cellTransverseFlow_add (n : ℕ) (s t : ℝ) (x : ℝ × ℝ) :
    cellAxialDisplacement h P axialSpeed tau n s
        (cellTransverseFlow h P angularSpeed n t x) +
      cellAxialDisplacement h P axialSpeed tau n t x =
      cellAxialDisplacement h P axialSpeed tau n (s + t) x := by
  rw [cellAxialDisplacement, cellAxialDisplacement, cellAxialDisplacement,
    cellAxialSpeed_cellTransverseFlow]
  ring

/-! ## Support

The angular profile is supported in the local core disc and the axial profile in the buffer
disc (proof of `prop:particle-flow`: "The profiles vanish in a neighbourhood of
`∂D(p_n, R_n)`, so the formula agrees with the identity there"). -/

/-- Outside the local core disc the angular speed vanishes, so the transverse cell map is the
identity.  This is the sharpest support statement: the core disc is much smaller than the
buffer disc (`P.supportFit`). -/
theorem cellTransverseDisplacement_eq_zero_of_not_mem_localCoreDisk (n : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    cellTransverseDisplacement h P angularSpeed n t x = 0 := by
  simp [cellTransverseDisplacement,
    cellAngularSpeed_eq_zero_of_not_mem_localCoreDisk h P angularSpeed n hx]

/-- Outside the local core disc the transverse cell map fixes every point. -/
theorem cellTransverseFlow_eq_self_of_not_mem_localCoreDisk (n : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    cellTransverseFlow h P angularSpeed n t x = x := by
  simp [cellTransverseFlow,
    cellTransverseDisplacement_eq_zero_of_not_mem_localCoreDisk h P angularSpeed n t hx]

/-- Outside the buffer disc the transverse displacement vanishes, the local core disc being
inside the buffer disc. -/
theorem cellTransverseDisplacement_eq_zero_of_not_mem_bufferDisk (n : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    cellTransverseDisplacement h P angularSpeed n t x = 0 :=
  cellTransverseDisplacement_eq_zero_of_not_mem_localCoreDisk h P angularSpeed n t
    fun hcore ↦ hx (P.localCoreDisk_subset_bufferDisk n hcore)

/-- Outside the buffer disc the axial displacement vanishes. -/
theorem cellAxialDisplacement_eq_zero_of_not_mem_bufferDisk (n : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    cellAxialDisplacement h P axialSpeed tau n t x = 0 := by
  simp [cellAxialDisplacement,
    cellAxialSpeed_eq_zero_of_not_mem_bufferDisk h P axialSpeed tau n hx]

/-- A trajectory never leaves its own buffer disc (proof of `prop:particle-flow`, "no trajectory
crosses a cell boundary").  Off the core disc the map is the identity; on the core disc the
Euclidean radius is preserved and is at most `2 (1 + h) ell_n < R_n / 5`, by the placement's
support-fit field. -/
theorem cellTransverseFlow_mem_bufferDisk (n : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    cellTransverseFlow h P angularSpeed n t x ∈ P.scaleFamily.bufferDisk n := by
  by_cases hcore : x ∈ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n
  · have hxc : ‖x - P.scaleFamily.cellCenter n‖ < (1 + (h : ℝ)) * P.scaleFamily.ell n := by
      rw [← dist_eq_norm]
      exact hcore
    have hfit := P.supportFit n
    have hpos := P.scaleFamily.bufferRadius_pos n
    have hkey : ‖cellTransverseFlow h P angularSpeed n t x - P.scaleFamily.cellCenter n‖ ≤
        2 * ‖x - P.scaleFamily.cellCenter n‖ := by
      refine (norm_le_norm_pairToWholePlane _).trans ?_
      rw [norm_pairToWholePlane_cellTransverseFlow_sub_cellCenter]
      exact norm_pairToWholePlane_le_two_mul_norm _
    have : dist (cellTransverseFlow h P angularSpeed n t x) (P.scaleFamily.cellCenter n) <
        P.scaleFamily.bufferRadius n := by
      rw [dist_eq_norm]
      nlinarith
    exact this
  · rw [cellTransverseFlow_eq_self_of_not_mem_localCoreDisk h P angularSpeed n t hcore]
    exact hx

/-- The sup-norm size of the transverse displacement: at most the swept angle times the
Euclidean radius (`norm_planeRotate_sub_le`).  Together with the support statement above this
is the cell-displacement estimate `‖d_{n,t}‖_∞ ≤ C_t ell_n`.  The paper's proof of
`prop:particle-flow` makes no such estimate: it argues that the natural lift of `Φ_t` is globally
Lipschitz, that its derivative is obtained by differentiating `eq:explicit-particle-flow` and
equals the identity almost everywhere outside the discs, so the estimate is an ingredient of this
formalisation only. -/
theorem norm_cellTransverseDisplacement_le (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    ‖cellTransverseDisplacement h P angularSpeed n t x‖ ≤
      |t| * |cellAngularSpeed h P angularSpeed n x| *
        ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ := by
  have hbound := norm_planeRotate_sub_le (t * cellAngularSpeed h P angularSpeed n x)
    (x - P.scaleFamily.cellCenter n)
  rw [abs_mul] at hbound
  exact hbound

/-- The angular profile never exceeds the angular-speed parameter in size, the radial cutoff
taking values in `[0, 1]` (`eq:particle-cell-profiles`). -/
theorem abs_cellAngularSpeed_le (n : ℕ) (x : ℝ × ℝ) :
    |cellAngularSpeed h P angularSpeed n x| ≤ |angularSpeed| := by
  have hmem := parameterizedRadialCutoff_mem_Icc h (helicalCellCoordinate h P n x)
  have habs : |parameterizedRadialCutoff h (helicalCellCoordinate h P n x)| ≤ 1 := by
    rw [abs_of_nonneg hmem.1]
    exact hmem.2
  rw [cellAngularSpeed, abs_mul]
  nlinarith [abs_nonneg angularSpeed, abs_nonneg (parameterizedRadialCutoff h
    (helicalCellCoordinate h P n x))]

/-- The displacement estimate `‖d_{n,t}‖_∞ ≤ C_t ell_n` (see above: the paper's proof of
`prop:particle-flow` does not use it), with the explicit constant: outside
the local core disc the displacement
vanishes, and inside it the Euclidean radius is at most `2 (1 + h) ell_n`. -/
theorem norm_cellTransverseDisplacement_le_ell (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    ‖cellTransverseDisplacement h P angularSpeed n t x‖ ≤
      2 * (|t| * |angularSpeed| * ((1 + (h : ℝ)) * P.scaleFamily.ell n)) := by
  have hhpos : (0 : ℝ) < (h : ℝ) := h.2.1
  have hell := P.scaleFamily.ell_pos n
  by_cases hcore : x ∈ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n
  · have hxc : ‖x - P.scaleFamily.cellCenter n‖ < (1 + (h : ℝ)) * P.scaleFamily.ell n := by
      rw [← dist_eq_norm]
      exact hcore
    have hrad : ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ ≤
        2 * ((1 + (h : ℝ)) * P.scaleFamily.ell n) := by
      refine (norm_pairToWholePlane_le_two_mul_norm _).trans ?_
      linarith
    refine (norm_cellTransverseDisplacement_le h P angularSpeed n t x).trans ?_
    have hprof := abs_cellAngularSpeed_le h P angularSpeed n x
    calc |t| * |cellAngularSpeed h P angularSpeed n x| *
          ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖
        ≤ |t| * |angularSpeed| *
            ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprof (abs_nonneg t)) (norm_nonneg _)
      _ ≤ |t| * |angularSpeed| * (2 * ((1 + (h : ℝ)) * P.scaleFamily.ell n)) :=
          mul_le_mul_of_nonneg_left hrad (by positivity)
      _ = 2 * (|t| * |angularSpeed| * ((1 + (h : ℝ)) * P.scaleFamily.ell n)) := by ring
  · rw [cellTransverseDisplacement_eq_zero_of_not_mem_localCoreDisk h P angularSpeed n t hcore,
      norm_zero]
    have : (0 : ℝ) ≤ |t| * |angularSpeed| * ((1 + (h : ℝ)) * P.scaleFamily.ell n) := by
      have := abs_nonneg t
      have := abs_nonneg angularSpeed
      positivity
    linarith

/-! ## Smoothness -/

/-- The transverse displacement is `C^∞` in the chart point: it is the smooth rotation applied to
a smooth angle and a smooth radius vector. -/
theorem contDiff_cellTransverseDisplacement (n : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cellTransverseDisplacement h P angularSpeed n t) := by
  have hpair : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ × ℝ ↦
      (t * cellAngularSpeed h P angularSpeed n x, x - P.scaleFamily.cellCenter n) :=
    (contDiff_const.mul (contDiff_cellAngularSpeed h P angularSpeed n)).prodMk
      (contDiff_id.sub contDiff_const)
  exact (contDiff_planeRotate.comp hpair).sub (contDiff_id.sub contDiff_const)

/-- The axial displacement is `C^∞` in the chart point. -/
theorem contDiff_cellAxialDisplacement (n : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cellAxialDisplacement h P axialSpeed tau n t) :=
  contDiff_const.mul (contDiff_cellAxialSpeed h P axialSpeed tau n)

/-! ## The spatial differential

The proof of `prop:particle-flow` computes
`D_y (R_{t omega_n(r)} z) = R_{t omega_n(r)} [id + t omega_n'(r) J z ⊗ e_r]`.  In Lean the
rank-one term is `(t • ∇omega_n).smulRight (J z)`: `smulRight` takes the functional first. -/

/-- The differential of the transverse cell map, the display for `D_y (R_{t omega_n(r)} z)` in
the proof of `prop:particle-flow`. -/
theorem hasFDerivAt_cellTransverseFlow (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (cellTransverseFlow h P angularSpeed n t)
      ((planeRotateCLM (t * cellAngularSpeed h P angularSpeed n x)).comp
        (ContinuousLinearMap.id ℝ (ℝ × ℝ) +
          (t • fderiv ℝ (cellAngularSpeed h P angularSpeed n) x).smulRight
            (perp (x - P.scaleFamily.cellCenter n)))) x := by
  have hβ : HasFDerivAt (fun y ↦ t * cellAngularSpeed h P angularSpeed n y)
      (t • fderiv ℝ (cellAngularSpeed h P angularSpeed n) x) x :=
    (differentiable_cellAngularSpeed h P angularSpeed n x).hasFDerivAt.const_mul t
  have hg : HasFDerivAt (fun y : ℝ × ℝ ↦ y - P.scaleFamily.cellCenter n)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_id x).sub_const _
  have hrot := hasFDerivAt_planeRotate_comp hβ hg
  have hflow : (fun y ↦ P.scaleFamily.cellCenter n +
      planeRotate (t * cellAngularSpeed h P angularSpeed n y)
        (y - P.scaleFamily.cellCenter n)) = cellTransverseFlow h P angularSpeed n t := by
    funext y
    rw [cellTransverseFlow_eq]
  rw [← hflow]
  refine ((hrot.const_add _).congr_fderiv ?_)
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id]
  congr 1
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp [planeRotate_perp]

/-- The `fderiv` form of the differential of the transverse cell map. -/
theorem fderiv_cellTransverseFlow (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    fderiv ℝ (cellTransverseFlow h P angularSpeed n t) x =
      (planeRotateCLM (t * cellAngularSpeed h P angularSpeed n x)).comp
        (ContinuousLinearMap.id ℝ (ℝ × ℝ) +
          (t • fderiv ℝ (cellAngularSpeed h P angularSpeed n) x).smulRight
            (perp (x - P.scaleFamily.cellCenter n))) :=
  (hasFDerivAt_cellTransverseFlow h P angularSpeed n t x).fderiv

/-- The differential of the axial displacement. -/
theorem hasFDerivAt_cellAxialDisplacement (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (cellAxialDisplacement h P axialSpeed tau n t)
      (t • fderiv ℝ (cellAxialSpeed h P axialSpeed tau n) x) x :=
  (differentiable_cellAxialSpeed h P axialSpeed tau n x).hasFDerivAt.const_mul t

/-- The `fderiv` form of the differential of the axial displacement. -/
theorem fderiv_cellAxialDisplacement (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    fderiv ℝ (cellAxialDisplacement h P axialSpeed tau n t) x =
      t • fderiv ℝ (cellAxialSpeed h P axialSpeed tau n) x :=
  (hasFDerivAt_cellAxialDisplacement h P axialSpeed tau n t x).fderiv

/-! ## The uniform bounds on the differential

The proof of `prop:particle-flow` bounds the differential of the cell formula uniformly in
`n` by the two shear bounds.  Both constants below are *sup-normed* operator norms, so each
carries the sup-versus-Euclidean factor `2` of `globalVelocityLipschitzBound`. -/

/-- The operator-norm bound `‖D Phi_t‖ ≤ C (1 + |t|)` of the proof of `prop:particle-flow` (the
display after `eq:axial-shear-bound`) on one cell, uniform in
`n`: the rotation contributes the factor `2` of `norm_planeRotateCLM_le` and the rank-one term
is controlled by the angular shear bound `eq:omega-shear-bound`. -/
theorem norm_fderiv_cellTransverseFlow_le (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    ‖fderiv ℝ (cellTransverseFlow h P angularSpeed n t) x‖ ≤
      2 * (1 + |t| * (2 * (|angularSpeed| * radialShearBound h))) := by
  have hshear := norm_sub_cellCenter_mul_norm_fderiv_cellAngularSpeed_le h P angularSpeed n x
  have hperp : ‖perp (x - P.scaleFamily.cellCenter n)‖ ≤
      ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ := by
    refine (norm_le_norm_pairToWholePlane _).trans ?_
    rw [norm_pairToWholePlane_perp]
  have hrank : ‖(t • fderiv ℝ (cellAngularSpeed h P angularSpeed n) x).smulRight
      (perp (x - P.scaleFamily.cellCenter n))‖ ≤
      |t| * (2 * (|angularSpeed| * radialShearBound h)) := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
    have hd : (0 : ℝ) ≤ ‖fderiv ℝ (cellAngularSpeed h P angularSpeed n) x‖ := norm_nonneg _
    have ht : (0 : ℝ) ≤ |t| := abs_nonneg t
    have hprod : ‖fderiv ℝ (cellAngularSpeed h P angularSpeed n) x‖ *
        ‖perp (x - P.scaleFamily.cellCenter n)‖ ≤
        2 * (|angularSpeed| * radialShearBound h) := by
      refine le_trans ?_ hshear
      rw [mul_comm ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖]
      exact mul_le_mul_of_nonneg_left hperp hd
    calc |t| * ‖fderiv ℝ (cellAngularSpeed h P angularSpeed n) x‖ *
          ‖perp (x - P.scaleFamily.cellCenter n)‖
        = |t| * (‖fderiv ℝ (cellAngularSpeed h P angularSpeed n) x‖ *
            ‖perp (x - P.scaleFamily.cellCenter n)‖) := by ring
      _ ≤ |t| * (2 * (|angularSpeed| * radialShearBound h)) :=
          mul_le_mul_of_nonneg_left hprod ht
  have hsum : ‖ContinuousLinearMap.id ℝ (ℝ × ℝ) +
      (t • fderiv ℝ (cellAngularSpeed h P angularSpeed n) x).smulRight
        (perp (x - P.scaleFamily.cellCenter n))‖ ≤
      1 + |t| * (2 * (|angularSpeed| * radialShearBound h)) := by
    refine (norm_add_le _ _).trans ?_
    have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ × ℝ)
    linarith
  rw [fderiv_cellTransverseFlow]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hrot := norm_planeRotateCLM_le (t * cellAngularSpeed h P angularSpeed n x)
  have hnn : (0 : ℝ) ≤ 1 + |t| * (2 * (|angularSpeed| * radialShearBound h)) :=
    le_trans (norm_nonneg _) hsum
  nlinarith [norm_nonneg (planeRotateCLM (t * cellAngularSpeed h P angularSpeed n x))]

/-- The operator-norm bound on the differential of the axial displacement, from the axial shear
bound `eq:axial-shear-bound`. -/
theorem norm_fderiv_cellAxialDisplacement_le (htau : 0 ≤ tau) (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    ‖fderiv ℝ (cellAxialDisplacement h P axialSpeed tau n t) x‖ ≤
      |t| * (parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed +
        (axialPlateauLipschitzConstant : ℝ) * P.scaleFamily.axialGradientScale tau 0) := by
  rw [fderiv_cellAxialDisplacement, norm_smul, Real.norm_eq_abs]
  have := norm_fderiv_cellAxialSpeed_le h P angularSpeed axialSpeed tau htau n x
  have ht : (0 : ℝ) ≤ |t| := abs_nonneg t
  nlinarith

/-! ## The Jacobian determinant

`det D Phi_t = 1` holds pointwise and exactly, not merely almost everywhere: the rotation has
determinant `1` and the rank-one perturbation is nilpotent because `∇omega_n` is radial while
`J z` is tangential.  (The proof of `cor:ideal-growth` obtains `det D Phi_t = 1` almost
everywhere from Liouville's formula and `div u = 0`; the closed formula makes that detour
unnecessary.) -/

/-- The gradient of a function of the Euclidean radius alone annihilates the tangential
direction `J (x - p_n)`: the rotated curve `s ↦ p_n + R_s (x - p_n)` has velocity
`J (x - p_n)` at `s = 0` and the function is constant along it. -/
theorem fderiv_apply_perp_eq_zero_of_congr (c : ℝ × ℝ) {f : (ℝ × ℝ) → ℝ}
    (hf : Differentiable ℝ f)
    (hcongr : ∀ y z : ℝ × ℝ,
      ‖pairToWholePlane (y - c)‖ = ‖pairToWholePlane (z - c)‖ → f y = f z)
    (x : ℝ × ℝ) : fderiv ℝ f x (perp (x - c)) = 0 := by
  have hcurve : HasDerivAt (fun s : ℝ ↦ c + planeRotate s (x - c)) (perp (x - c)) 0 := by
    have hr := hasDerivAt_planeRotate_mul 1 (x - c) 0
    simp only [mul_one, planeRotate_zero, one_smul] at hr
    exact hr.const_add c
  have hpt : c + planeRotate 0 (x - c) = x := by simp
  have hcomp : HasDerivAt (fun s : ℝ ↦ f (c + planeRotate s (x - c)))
      (fderiv ℝ f x (perp (x - c))) 0 := by
    have hfx : HasFDerivAt f (fderiv ℝ f x) (c + planeRotate 0 (x - c)) := by
      rw [hpt]
      exact (hf x).hasFDerivAt
    exact hfx.comp_hasDerivAt 0 hcurve
  have hconst : (fun s : ℝ ↦ f (c + planeRotate s (x - c))) = fun _ : ℝ ↦ f x := by
    funext s
    refine hcongr _ _ ?_
    rw [add_sub_cancel_left, norm_pairToWholePlane_planeRotate]
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const 0 (f x))

/-- The angular profile has no tangential derivative: `∇omega_n (J z) = 0`, the identity that
makes the rank-one term of the differential `D_y (R_{t omega_n(r)} z)` nilpotent. -/
theorem fderiv_cellAngularSpeed_apply_perp (n : ℕ) (x : ℝ × ℝ) :
    fderiv ℝ (cellAngularSpeed h P angularSpeed n) x
      (perp (x - P.scaleFamily.cellCenter n)) = 0 :=
  fderiv_apply_perp_eq_zero_of_congr (P.scaleFamily.cellCenter n)
    (differentiable_cellAngularSpeed h P angularSpeed n)
    (fun _ _ hyz ↦ cellAngularSpeed_congr_of_norm_eq h P angularSpeed n hyz) x

/-- `det D Phi_t = 1` on a cell (cf. the proof of `cor:ideal-growth`): the transverse cell map is
volume preserving,
exactly and at every point. -/
theorem det_fderiv_cellTransverseFlow (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    LinearMap.det
        ((fderiv ℝ (cellTransverseFlow h P angularSpeed n t) x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
  rw [fderiv_cellTransverseFlow]
  refine det_planeRotateCLM_comp_id_add_smulRight _ _ _ ?_
  simp [fderiv_cellAngularSpeed_apply_perp h P angularSpeed n x]

/-! ## The time derivative

This is the ODE verification behind `eq:explicit-particle-flow`: together with the cell
velocity formula `parameterizedFullEuclideanCellRealSource_eq_cellProfiles`
(`Flow/CellProfiles.lean`) and the invariance of the two profiles, it says that the closed
formula solves `y' = u(y)`.  (The paper argues in the other direction: it substitutes the
cell velocity into the ODE and reads off the formula from the invariance of `r`.) -/

/-- The transverse cell map solves the transverse equation of motion: its time derivative is
`omega_n(r)` times the tangential vector at the *current* point (the cell velocity displayed at
the start of the proof of `prop:particle-flow`). -/
theorem hasDerivAt_cellTransverseFlow (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ ↦ cellTransverseFlow h P angularSpeed n s x)
      (cellAngularSpeed h P angularSpeed n x •
        perp (cellTransverseFlow h P angularSpeed n t x - P.scaleFamily.cellCenter n)) t := by
  have hr := hasDerivAt_planeRotate_mul (cellAngularSpeed h P angularSpeed n x)
    (x - P.scaleFamily.cellCenter n) t
  have hcurve := hr.const_add (P.scaleFamily.cellCenter n)
  rw [cellTransverseFlow_sub_cellCenter]
  refine hcurve.congr_of_eventuallyEq ?_
  filter_upwards with s
  rw [cellTransverseFlow_eq]

/-- The axial displacement solves the axial equation of motion: its time derivative is the
axial profile at the initial point, which by `cellAxialSpeed_cellTransverseFlow` is also the
axial profile at the current point (the cell velocity displayed at the start of the proof of
`prop:particle-flow`). -/
theorem hasDerivAt_cellAxialDisplacement (n : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ ↦ cellAxialDisplacement h P axialSpeed tau n s x)
      (cellAxialSpeed h P axialSpeed tau n x) t := by
  simpa [cellAxialDisplacement] using
    (hasDerivAt_id t).mul_const (cellAxialSpeed h P axialSpeed tau n x)

end ScaleFamily.TorusCellPlacement

end

end FastDynamo

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusGlobalVelocityRegularity
public import LeanPool.FastDynamo.Global.TorusAxialPlateauRadial
public import LeanPool.FastDynamo.Dynamics.Flow.RadialShear

/-!
# The angular and axial cell profiles of the explicit particle flow

`prop:particle-flow` writes the velocity inside the `n`th buffer disc
as a rigid screw motion around the cell centre `p_n`; the velocity formula quoted below is the
one displayed at the start of its proof.  Its two scalar profiles are
`eq:particle-cell-profiles`,

`ω_n(r) = Ω χ_h(r / ℓ_n)`,   `g_n(r) = ℓ_n U χ_h(r / ℓ_n) + a_n ϑ(r / R_n)`,

read here as functions of the chart point `x : ℝ × ℝ` rather than of the radius
`r = |x - p_n|`; `cellAngularSpeed` and `cellAxialSpeed` are those two functions.

The file proves:

* the **cell velocity formula** displayed at the start of the proof of `prop:particle-flow`,
  `parameterizedFullEuclideanCellRealSource_eq_cellProfiles`: inside the `n`th disc the
  chart-side velocity is `(ω_n(r) (x - p_n)^⊥, g_n(r))`.  This is the bridge between the
  spectral construction's data and the paper's dynamical formulas; everything the flow
  layer says is phrased through the two profiles;
* the support statements (`ω_n` lives in the local core disc, `g_n` in the buffer disc) and
  smoothness of both profiles;
* the **values at the cell centre**, `cellAngularSpeed_cellCenter` and
  `cellAxialSpeed_cellCenter`: `ω_n(0) = Ω` and `g_n(0) = ℓ_n U + a_n`, the centre speed of
  `prop:particle-flow` (the sentence after `eq:explicit-particle-flow`), both cut-offs being
  constant equal to one near `p_n`;
* the **radial factorisation**: both profiles depend on `x` only through the Euclidean radius
  `‖pairToWholePlane (x - p_n)‖`, which is what makes the rotational part of the flow preserve
  them (the invariance of `r` in the proof of `prop:particle-flow`);
* the two **shear bounds** of `eq:omega-shear-bound` and `eq:axial-shear-bound`,
  uniformly in the cell index `n`.

`ℝ × ℝ` carries the product (sup) metric, so every radius is the Euclidean quantity
`‖pairToWholePlane z‖` and never `‖z‖`.  Converting a sup-normed differential into a Euclidean
one costs the factor `2` already present in `globalVelocityLipschitzBound`
(`Global/TorusGlobalVelocityRegularity.lean`); it reappears in
`norm_sub_cellCenter_mul_norm_fderiv_cellAngularSpeed_le`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped LineDeriv

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The two profiles -/

/-- The paper's angular profile `ω_n(r) = Ω χ_h(r / ℓ_n)` of `eq:particle-cell-profiles`,
read as a function of the chart point: the rescaled cell coordinate
`helicalCellCoordinate h P n x` already carries the division by `ℓ_n`, and
`parameterizedRadialCutoff h` is a function of its squared Euclidean norm. -/
def cellAngularSpeed (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  angularSpeed * parameterizedRadialCutoff h (helicalCellCoordinate h P n x)

/-- The paper's axial profile `g_n(r) = ℓ_n U χ_h(r / ℓ_n) + a_n ϑ(r / R_n)` of
`eq:particle-cell-profiles`: the axial component of the rescaled helical copy
plus the added axial velocity of `eq:axial-offset`. -/
def cellAxialSpeed (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  P.scaleFamily.ell n * axialSpeed *
      parameterizedRadialCutoff h (helicalCellCoordinate h P n x) +
    P.scaleFamily.axialAmplitude tau n * P.axialCellCutoff n x

/-! ## The rescaled cell coordinate in Euclidean form -/

/-- The rescaled cell coordinate is `ℓ_n⁻¹` times the Euclidean image of the centred chart
point, `(x - p_n) / ℓ_n` of `eq:local-copy`. -/
theorem helicalCellCoordinate_eq_smul (n : ℕ) (x : ℝ × ℝ) :
    helicalCellCoordinate h P n x =
      (P.scaleFamily.ell n)⁻¹ •
        pairToWholePlane (x - P.scaleFamily.cellCenter n) := by
  simp [helicalCellCoordinate, map_sub]

/-- The first coordinate of the rescaled cell coordinate. -/
theorem helicalCellCoordinate_apply_zero (n : ℕ) (x : ℝ × ℝ) :
    helicalCellCoordinate h P n x (0 : Fin 2) =
      (P.scaleFamily.ell n)⁻¹ * (x - P.scaleFamily.cellCenter n).1 := by
  rw [helicalCellCoordinate_eq_smul]
  simp

/-- The second coordinate of the rescaled cell coordinate. -/
theorem helicalCellCoordinate_apply_one (n : ℕ) (x : ℝ × ℝ) :
    helicalCellCoordinate h P n x (1 : Fin 2) =
      (P.scaleFamily.ell n)⁻¹ * (x - P.scaleFamily.cellCenter n).2 := by
  rw [helicalCellCoordinate_eq_smul]
  simp

/-- The rescaled cell coordinate has Euclidean norm `|x - p_n| / ℓ_n`, the paper's
`r / ℓ_n` (`eq:particle-cell-profiles`). -/
theorem norm_helicalCellCoordinate_eq_inv_mul (n : ℕ) (x : ℝ × ℝ) :
    ‖helicalCellCoordinate h P n x‖ =
      (P.scaleFamily.ell n)⁻¹ *
        ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ := by
  rw [helicalCellCoordinate_eq_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (P.scaleFamily.ell_pos n))]

/-- The Euclidean chart distance is the Euclidean norm of the chart difference; this is the
form in which the radius `r = |x - p_n|` of `eq:particle-cell-profiles` is used below. -/
theorem pairEuclideanDist_eq_norm_pairToWholePlane_sub (x y : ℝ × ℝ) :
    pairEuclideanDist x y = ‖pairToWholePlane (x - y)‖ := by
  rw [pairEuclideanDist, map_sub]

/-! ## The cell centre -/

/-- **`ω_n(0) = Ω`**: at the cell centre both cut-offs are on, so the angular profile of
`eq:particle-cell-profiles` takes its full value. -/
@[simp] theorem cellAngularSpeed_cellCenter (n : ℕ) :
    cellAngularSpeed h P angularSpeed n (P.scaleFamily.cellCenter n) = angularSpeed := by
  have hnorm : ‖(0 : WholePlane)‖ ≤ 1 - (h : ℝ) := by
    rw [norm_zero]
    linarith [h.2.2]
  rw [cellAngularSpeed, helicalCellCoordinate_cellCenter,
    parameterizedRadialCutoff_one_of_norm_le h hnorm, mul_one]

/-- **The centre speed `g_n(0) = ℓ_n U + a_n`** (statement of `prop:particle-flow`: "At
`y = p_n`, the horizontal component is `p_n`, while the axial component translates at speed
`g_n(0) = ℓ_n U + a_n`").

Both cut-offs of `eq:particle-cell-profiles` are constant equal to one near the centre: the
Ponomarenko cutoff `χ_h` is one on the ball of radius `1 - h`
(`parameterizedRadialCutoff_one_of_norm_le`) and the axial plateau `ϑ` is one on
`D(p_n, 3R_n/4)` (`axialCellCutoff_eq_one_of_dist_le_three_quarters`). -/
theorem cellAxialSpeed_cellCenter (n : ℕ) :
    cellAxialSpeed h P axialSpeed tau n (P.scaleFamily.cellCenter n) =
      P.scaleFamily.ell n * axialSpeed + P.scaleFamily.axialAmplitude tau n := by
  have hnorm : ‖(0 : WholePlane)‖ ≤ 1 - (h : ℝ) := by
    rw [norm_zero]
    linarith [h.2.2]
  have hdist : pairEuclideanDist (P.scaleFamily.cellCenter n) (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4 := by
    rw [pairEuclideanDist, sub_self, norm_zero]
    linarith [P.scaleFamily.bufferRadius_pos n]
  rw [cellAxialSpeed, helicalCellCoordinate_cellCenter,
    parameterizedRadialCutoff_one_of_norm_le h hnorm, mul_one,
    P.axialCellCutoff_eq_one_of_dist_le_three_quarters n hdist, mul_one]

/-! ## Support -/

/-- The angular profile is supported in the local core disc: `χ_h` vanishes from radius `1 + h`
on, and outside the core disc the rescaled coordinate has norm at least `1 + h`
(proof of `prop:particle-flow`: the profiles vanish near `∂D(p_n, R_n)`). -/
theorem cellAngularSpeed_eq_zero_of_not_mem_localCoreDisk (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    cellAngularSpeed h P angularSpeed n x = 0 := by
  rw [cellAngularSpeed, parameterizedRadialCutoff_zero_of_radius_le_norm h
    (supportRadius_le_norm_helicalCellCoordinate_of_not_mem h P n hx), mul_zero]

/-- The axial profile is supported in the buffer disc: its helical half already vanishes off the
much smaller local core disc, and its plateau half vanishes off the buffer disc
(proof of `prop:particle-flow`: the profiles vanish near `∂D(p_n, R_n)`). -/
theorem cellAxialSpeed_eq_zero_of_not_mem_bufferDisk (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    cellAxialSpeed h P axialSpeed tau n x = 0 := by
  have hcore : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n :=
    fun hmem ↦ hx (P.localCoreDisk_subset_bufferDisk n hmem)
  rw [cellAxialSpeed, parameterizedRadialCutoff_zero_of_radius_le_norm h
    (supportRadius_le_norm_helicalCellCoordinate_of_not_mem h P n hcore),
    P.axialCellCutoff_eq_zero_of_not_mem_bufferDisk n hx]
  ring

/-! ## Smoothness -/

/-- The angular profile is smooth of every order: the width-`h` cutoff is smooth and the
rescaled cell coordinate is affine. -/
theorem contDiff_cellAngularSpeed (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cellAngularSpeed h P angularSpeed n) := by
  change ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ × ℝ ↦
    angularSpeed * parameterizedRadialCutoff h (helicalCellCoordinate h P n x)
  exact contDiff_const.mul ((parameterizedRadialCutoff_contDiff h).comp
    (contDiff_helicalCellCoordinate h P n))

/-- The axial profile is smooth of every order.  The paper fixes some `ϑ ∈ C_c^∞([0, ∞))` (§3.3);
the Lean plateau `axialPlateauSq` is a concrete such cut-off, built from `Real.smoothTransition`
of the squared radius, hence smooth at the cell centre too. -/
theorem contDiff_cellAxialSpeed (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cellAxialSpeed h P axialSpeed tau n) := by
  change ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ × ℝ ↦
    P.scaleFamily.ell n * axialSpeed *
        parameterizedRadialCutoff h (helicalCellCoordinate h P n x) +
      P.scaleFamily.axialAmplitude tau n * P.axialCellCutoff n x
  exact (contDiff_const.mul ((parameterizedRadialCutoff_contDiff h).comp
      (contDiff_helicalCellCoordinate h P n))).add
    (contDiff_const.mul (P.axialCellCutoff_contDiff n))

/-- The angular profile is differentiable everywhere. -/
theorem differentiable_cellAngularSpeed (n : ℕ) :
    Differentiable ℝ (cellAngularSpeed h P angularSpeed n) :=
  (contDiff_cellAngularSpeed h P angularSpeed n).differentiable (by simp)

/-- The axial profile is differentiable everywhere. -/
theorem differentiable_cellAxialSpeed (n : ℕ) :
    Differentiable ℝ (cellAxialSpeed h P axialSpeed tau n) :=
  (contDiff_cellAxialSpeed h P axialSpeed tau n).differentiable (by simp)

/-! ## Radial factorisation

Both profiles are functions of the Euclidean radius `|x - p_n|` alone.  This is the fact behind
the invariance `d|y - p_n|²/dt = 0` in the proof of `prop:particle-flow`: the rotational part
of the flow does not change either profile, so the trajectory is a circle traversed at
constant speed. -/

/-- The width-`h` cutoff is radial: it depends on its argument only through its Euclidean
norm, being `Real.smoothTransition` of `((1+h)² - ‖·‖²)/(4h)`. -/
theorem parameterizedRadialCutoff_congr_of_norm_eq {w z : WholePlane}
    (hwz : ‖w‖ = ‖z‖) :
    parameterizedRadialCutoff h w = parameterizedRadialCutoff h z := by
  simp [parameterizedRadialCutoff, parameterizedRadialArgument, hwz]

/-- The angular profile depends on the chart point only through the Euclidean distance to the
cell centre (the invariance of `r` in the proof of `prop:particle-flow`). -/
theorem cellAngularSpeed_congr_of_norm_eq (n : ℕ) {x y : ℝ × ℝ}
    (hxy : ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ =
      ‖pairToWholePlane (y - P.scaleFamily.cellCenter n)‖) :
    cellAngularSpeed h P angularSpeed n x =
      cellAngularSpeed h P angularSpeed n y := by
  rw [cellAngularSpeed, cellAngularSpeed,
    parameterizedRadialCutoff_congr_of_norm_eq h
      (w := helicalCellCoordinate h P n x) (z := helicalCellCoordinate h P n y)
      (by rw [norm_helicalCellCoordinate_eq_inv_mul, norm_helicalCellCoordinate_eq_inv_mul, hxy])]

/-- The axial profile depends on the chart point only through the Euclidean distance to the
cell centre: its helical half through `χ_h`, its plateau half through
`axialCellCutoff_eq_axialPlateauRadial` (the invariance of `r` in the proof of
`prop:particle-flow`). -/
theorem cellAxialSpeed_congr_of_norm_eq (n : ℕ) {x y : ℝ × ℝ}
    (hxy : ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ =
      ‖pairToWholePlane (y - P.scaleFamily.cellCenter n)‖) :
    cellAxialSpeed h P axialSpeed tau n x =
      cellAxialSpeed h P axialSpeed tau n y := by
  rw [cellAxialSpeed, cellAxialSpeed,
    parameterizedRadialCutoff_congr_of_norm_eq h
      (w := helicalCellCoordinate h P n x) (z := helicalCellCoordinate h P n y)
      (by rw [norm_helicalCellCoordinate_eq_inv_mul, norm_helicalCellCoordinate_eq_inv_mul, hxy]),
    P.axialCellCutoff_eq_axialPlateauRadial n x,
    P.axialCellCutoff_eq_axialPlateauRadial n y,
    pairEuclideanDist_eq_norm_pairToWholePlane_sub,
    pairEuclideanDist_eq_norm_pairToWholePlane_sub, hxy]

/-! ## The cell velocity formula

`u(y) = (ω_n(r) (y - p_n)^⊥, g_n(r))` inside the `n`th disc (first display of the proof of
`prop:particle-flow`).  The amplitude
`ℓ_n` of the rescaled helical copy cancels the `ℓ_n⁻¹` carried by the cell coordinate, which is
why the transverse components come out as `ω_n` times the *unrescaled* offset `x - p_n`. -/

/-- First transverse component of the rescaled helical copy: `-ω_n(r) (x - p_n)₂`. -/
theorem parameterizedHelicalCellSource_apply_zero (n : ℕ) (x : ℝ × ℝ) :
    parameterizedHelicalCellSource h P angularSpeed axialSpeed n x 0 =
      ((-cellAngularSpeed h P angularSpeed n x *
        (x - P.scaleFamily.cellCenter n).2 : ℝ) : ℂ) := by
  have hell : P.scaleFamily.ell n ≠ 0 := (P.scaleFamily.ell_pos n).ne'
  have hellC : (P.scaleFamily.ell n : ℂ) ≠ 0 := by exact_mod_cast hell
  have hcoord := helicalCellCoordinate_apply_one h P n x
  simp only [parameterizedHelicalCellSource, Pi.smul_apply, Function.comp_apply,
    PiLp.smul_apply, parameterizedSmoothedVelocity,
    squaredRadiusHelicalVelocity_apply_zero, parameterizedRadialProfile,
    parameterizedRadialCutoffSchwartz_apply, cellAngularSpeed, hcoord,
    Complex.real_smul]
  push_cast
  field_simp

/-- Second transverse component of the rescaled helical copy: `ω_n(r) (x - p_n)₁`. -/
theorem parameterizedHelicalCellSource_apply_one (n : ℕ) (x : ℝ × ℝ) :
    parameterizedHelicalCellSource h P angularSpeed axialSpeed n x 1 =
      ((cellAngularSpeed h P angularSpeed n x *
        (x - P.scaleFamily.cellCenter n).1 : ℝ) : ℂ) := by
  have hell : P.scaleFamily.ell n ≠ 0 := (P.scaleFamily.ell_pos n).ne'
  have hellC : (P.scaleFamily.ell n : ℂ) ≠ 0 := by exact_mod_cast hell
  have hcoord := helicalCellCoordinate_apply_zero h P n x
  simp only [parameterizedHelicalCellSource, Pi.smul_apply, Function.comp_apply,
    PiLp.smul_apply, parameterizedSmoothedVelocity,
    squaredRadiusHelicalVelocity_apply_one, parameterizedRadialProfile,
    parameterizedRadialCutoffSchwartz_apply, cellAngularSpeed, hcoord,
    Complex.real_smul]
  push_cast
  field_simp

/-- Axial component of the rescaled helical copy: the helical half `ℓ_n U χ_h(r / ℓ_n)` of the
axial profile `g_n`. -/
theorem parameterizedHelicalCellSource_apply_two (n : ℕ) (x : ℝ × ℝ) :
    parameterizedHelicalCellSource h P angularSpeed axialSpeed n x 2 =
      ((P.scaleFamily.ell n * axialSpeed *
        parameterizedRadialCutoff h (helicalCellCoordinate h P n x) : ℝ) : ℂ) := by
  simp only [parameterizedHelicalCellSource, Pi.smul_apply, Function.comp_apply,
    PiLp.smul_apply, parameterizedSmoothedVelocity,
    squaredRadiusHelicalVelocity_apply_two, parameterizedRadialProfile,
    parameterizedRadialCutoffSchwartz_apply, Complex.real_smul]
  push_cast
  ring

/-- **The cell velocity formula** (first display of the proof of `prop:particle-flow`).  Inside
the `n`th cell
the chart-side real velocity is the rigid screw field `(ω_n(r) (x - p_n)^⊥, g_n(r))` with
`(z₁, z₂)^⊥ = (-z₂, z₁)`.  Every statement of the flow layer is phrased through the two
profiles, so this identity is the bridge between the spectral construction's velocity and the
paper's dynamics. -/
theorem parameterizedFullEuclideanCellRealSource_eq_cellProfiles (n : ℕ)
    (x : ℝ × ℝ) :
    parameterizedFullEuclideanCellRealSource h P angularSpeed axialSpeed tau n x =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![-cellAngularSpeed h P angularSpeed n x *
            (x - P.scaleFamily.cellCenter n).2,
          cellAngularSpeed h P angularSpeed n x *
            (x - P.scaleFamily.cellCenter n).1,
          cellAxialSpeed h P axialSpeed tau n x] := by
  apply PiLp.ext
  intro i
  simp only [parameterizedFullEuclideanCellRealSource, PiLp.add_apply,
    vecRe_apply, axialOffsetEuclidean, PiLp.smul_apply, axialUnitR3_apply,
    smul_eq_mul]
  fin_cases i
  · simp [parameterizedHelicalCellSource_apply_zero h P angularSpeed axialSpeed n x]
  · simp [parameterizedHelicalCellSource_apply_one h P angularSpeed axialSpeed n x]
  · simp [parameterizedHelicalCellSource_apply_two h P angularSpeed axialSpeed n x,
      cellAxialSpeed]

/-- First component of the cell velocity formula: `-ω_n(r) (x - p_n)₂`. -/
theorem parameterizedFullEuclideanCellRealSource_apply_zero (n : ℕ)
    (x : ℝ × ℝ) :
    parameterizedFullEuclideanCellRealSource h P angularSpeed axialSpeed tau n x 0 =
      -cellAngularSpeed h P angularSpeed n x *
        (x - P.scaleFamily.cellCenter n).2 := by
  rw [parameterizedFullEuclideanCellRealSource_eq_cellProfiles]
  simp

/-- Second component of the cell velocity formula: `ω_n(r) (x - p_n)₁`. -/
theorem parameterizedFullEuclideanCellRealSource_apply_one (n : ℕ)
    (x : ℝ × ℝ) :
    parameterizedFullEuclideanCellRealSource h P angularSpeed axialSpeed tau n x 1 =
      cellAngularSpeed h P angularSpeed n x *
        (x - P.scaleFamily.cellCenter n).1 := by
  rw [parameterizedFullEuclideanCellRealSource_eq_cellProfiles]
  simp

/-- Third component of the cell velocity formula: the axial profile `g_n(r)`. -/
theorem parameterizedFullEuclideanCellRealSource_apply_two (n : ℕ)
    (x : ℝ × ℝ) :
    parameterizedFullEuclideanCellRealSource h P angularSpeed axialSpeed tau n x 2 =
      cellAxialSpeed h P axialSpeed tau n x := by
  rw [parameterizedFullEuclideanCellRealSource_eq_cellProfiles]
  simp

/-! ## The angular shear bound

`eq:omega-shear-bound`: `sup_n sup_r r |ω_n'(r)| ≤ |Ω| sup_s s |χ_h'(s)|`.  The
left-hand side is scale invariant — `‖x - p_n‖ = ℓ_n ‖(x - p_n)/ℓ_n‖` while the chain rule
contributes a factor `ℓ_n⁻¹` — which is exactly why the bound is uniform in `n`. -/

/-- The canonical identification of the sup-normed chart with the Euclidean plane has operator
norm at most `2`; this is the sup-versus-Euclidean loss recorded in the module header. -/
theorem norm_pairToWholePlane_le_two :
    ‖(pairToWholePlane : (ℝ × ℝ) →L[ℝ] WholePlane)‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v ↦ ?_
  simpa [dist_zero_right] using norm_pairToWholePlane_sub_le_two_mul_dist v 0

/-- The differential of the rescaled cell coordinate has operator norm at most `2 / ℓ_n`. -/
theorem norm_helicalCellCoordinateFDeriv_le (n : ℕ) :
    ‖helicalCellCoordinateFDeriv P n‖ ≤ 2 * (P.scaleFamily.ell n)⁻¹ := by
  have hL : 0 < P.scaleFamily.ell n := P.scaleFamily.ell_pos n
  rw [helicalCellCoordinateFDeriv]
  refine (norm_smul_le ((P.scaleFamily.ell n)⁻¹)
    (pairToWholePlane : (ℝ × ℝ) →L[ℝ] WholePlane)).trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), mul_comm]
  exact mul_le_mul_of_nonneg_right norm_pairToWholePlane_le_two
    (inv_pos.mpr hL).le

/-- The chain rule for the angular profile: `∇(Ω χ_h ∘ (· - p_n)/ℓ_n) =
Ω (∇χ_h)((x - p_n)/ℓ_n) ∘ (ℓ_n⁻¹ • pairToWholePlane)`. -/
theorem hasFDerivAt_cellAngularSpeed (n : ℕ) (x : ℝ × ℝ) :
    HasFDerivAt (cellAngularSpeed h P angularSpeed n)
      (angularSpeed •
        ((fderiv ℝ (parameterizedRadialCutoff h)
            (helicalCellCoordinate h P n x)).comp
          (helicalCellCoordinateFDeriv P n))) x := by
  have hcut : HasFDerivAt (parameterizedRadialCutoff h)
      (fderiv ℝ (parameterizedRadialCutoff h) (helicalCellCoordinate h P n x))
      (helicalCellCoordinate h P n x) :=
    (((parameterizedRadialCutoff_contDiff h).differentiable (by simp))
      (helicalCellCoordinate h P n x)).hasFDerivAt
  exact (hcut.comp x (helicalCellCoordinate_hasFDerivAt h P n x)).const_mul
    angularSpeed

/-- The differential of the angular profile, as an equation for `fderiv`. -/
theorem fderiv_cellAngularSpeed (n : ℕ) (x : ℝ × ℝ) :
    fderiv ℝ (cellAngularSpeed h P angularSpeed n) x =
      angularSpeed •
        ((fderiv ℝ (parameterizedRadialCutoff h)
            (helicalCellCoordinate h P n x)).comp
          (helicalCellCoordinateFDeriv P n)) :=
  (hasFDerivAt_cellAngularSpeed h P angularSpeed n x).fderiv

/-- **The angular shear bound**, `eq:omega-shear-bound`, uniformly in the cell
index: the scale-invariant product `r |ω_n'(r)|` is bounded by `|Ω| sup_s s |χ_h'(s)|`, up to
the sup-versus-Euclidean factor `2` of `norm_pairToWholePlane_le_two`.  The paper's
constant is `|Ω| * radialShearBound h`; the extra `2` is the same loss that produces the factor
`2` in `globalVelocityLipschitzBound`, and is recorded here rather than hidden. -/
theorem norm_sub_cellCenter_mul_norm_fderiv_cellAngularSpeed_le
    (n : ℕ) (x : ℝ × ℝ) :
    ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ *
        ‖fderiv ℝ (cellAngularSpeed h P angularSpeed n) x‖ ≤
      2 * (|angularSpeed| * radialShearBound h) := by
  have hL : 0 < P.scaleFamily.ell n := P.scaleFamily.ell_pos n
  have hL0 : P.scaleFamily.ell n ≠ 0 := hL.ne'
  have hnorm : ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ =
      P.scaleFamily.ell n * ‖helicalCellCoordinate h P n x‖ := by
    rw [norm_helicalCellCoordinate_eq_inv_mul]
    field_simp
  have hcomp : ‖fderiv ℝ (cellAngularSpeed h P angularSpeed n) x‖ ≤
      |angularSpeed| *
        (‖fderiv ℝ (parameterizedRadialCutoff h)
            (helicalCellCoordinate h P n x)‖ *
          (2 * (P.scaleFamily.ell n)⁻¹)) := by
    rw [fderiv_cellAngularSpeed, norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left
      (norm_helicalCellCoordinateFDeriv_le h P n) (norm_nonneg _)
  calc ‖pairToWholePlane (x - P.scaleFamily.cellCenter n)‖ *
          ‖fderiv ℝ (cellAngularSpeed h P angularSpeed n) x‖
      = P.scaleFamily.ell n * ‖helicalCellCoordinate h P n x‖ *
          ‖fderiv ℝ (cellAngularSpeed h P angularSpeed n) x‖ := by rw [hnorm]
    _ ≤ P.scaleFamily.ell n * ‖helicalCellCoordinate h P n x‖ *
          (|angularSpeed| *
            (‖fderiv ℝ (parameterizedRadialCutoff h)
                (helicalCellCoordinate h P n x)‖ *
              (2 * (P.scaleFamily.ell n)⁻¹))) :=
        mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = 2 * (|angularSpeed| *
          (‖helicalCellCoordinate h P n x‖ *
            ‖fderiv ℝ (parameterizedRadialCutoff h)
              (helicalCellCoordinate h P n x)‖)) := by
        field_simp
    _ ≤ 2 * (|angularSpeed| * radialShearBound h) := by
        gcongr
        exact norm_mul_norm_fderiv_parameterizedRadialCutoff_le h
          (helicalCellCoordinate h P n x)

/-! ## The axial shear bound

`eq:axial-shear-bound`: `sup_n sup_r |g_n'(r)| ≤ |U| ‖χ_h'‖_∞ + η_ax`.  Both halves
come from bounds of the velocity construction: the helical half through the Schwartz
seminorms assembled into `parameterizedHelicalFirstDerivativeBound` (the `ℓ_n`-cancellation is built
into `parameterizedHelicalCellSourceDeriv`), the plateau half through `norm_fderiv_axialPlateau_le`
and the monotone gradient scale `a_n / R_n ≤ a_0 / R_0`. -/

/-- The axial profile splits into the third component of the rescaled helical copy and the
plateau term; this is the decomposition used for the axial shear bound. -/
theorem cellAxialSpeed_eq_helical_add_plateau (n : ℕ) :
    cellAxialSpeed h P axialSpeed tau n = fun y : ℝ × ℝ ↦
      vecRe (parameterizedHelicalCellSource h P angularSpeed axialSpeed n y) 2 +
        P.scaleFamily.axialAmplitude tau n * P.axialCellCutoff n y := by
  funext y
  rw [cellAxialSpeed]
  congr 1
  rw [vecRe_apply,
    parameterizedHelicalCellSource_apply_two h P angularSpeed axialSpeed n y,
    Complex.ofReal_re]

/-- **The axial shear bound**, `eq:axial-shear-bound`, uniformly in the cell
index `n`: the differential of `g_n` is bounded by the scale-invariant profile gradient plus the
paper's `η_ax = ‖ϑ'‖_∞ a_0 / R_0` (§3.3).  This is the same constant as
`globalVelocityCoordinateDerivativeBound`, with no sup-versus-Euclidean loss: the helical half is
estimated coordinatewise against the two Schwartz seminorms that already make up
`parameterizedHelicalFirstDerivativeBound`, and the plateau half against the operator norm of
`fderiv axialPlateauBump`, which is a sup-metric Lipschitz bound. -/
theorem norm_fderiv_cellAxialSpeed_le (htau : 0 ≤ tau) (n : ℕ) (x : ℝ × ℝ) :
    ‖fderiv ℝ (cellAxialSpeed h P axialSpeed tau n) x‖ ≤
      parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed +
        (axialPlateauLipschitzConstant : ℝ) *
          P.scaleFamily.axialGradientScale tau 0 := by
  have hR : 0 < P.scaleFamily.bufferRadius n := P.scaleFamily.bufferRadius_pos n
  have ha : 0 ≤ P.scaleFamily.axialAmplitude tau n := by
    unfold ScaleFamily.axialAmplitude
    exact mul_nonneg (div_nonneg htau p.wavenumber_pos.le)
      (P.scaleFamily.ell_pos n).le
  set DA : (ℝ × ℝ) →L[ℝ] ℝ :=
    (((EuclideanSpace.proj (2 : Fin 3)).comp vecReCLM).comp
      (parameterizedHelicalCellSourceFDeriv h P angularSpeed axialSpeed n x))
    with hDAdef
  set Dcut : (ℝ × ℝ) →L[ℝ] ℝ :=
    (fderiv ℝ axialPlateauBump (P.axialBufferCoordinate n x)).comp
      ((P.scaleFamily.bufferRadius n)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ))
    with hDcutdef
  have hDA : HasFDerivAt (fun y : ℝ × ℝ ↦
      vecRe (parameterizedHelicalCellSource h P angularSpeed axialSpeed n y) 2)
      DA x :=
    (((EuclideanSpace.proj (2 : Fin 3)).comp vecReCLM).hasFDerivAt).comp x
      (parameterizedHelicalCellSource_hasFDerivAt h P angularSpeed axialSpeed n x)
  have hDB : HasFDerivAt (fun y : ℝ × ℝ ↦
      P.scaleFamily.axialAmplitude tau n * P.axialCellCutoff n y)
      (P.scaleFamily.axialAmplitude tau n • Dcut) x :=
    (P.axialCellCutoff_hasFDerivAt n x).const_mul _
  have hsum : HasFDerivAt (cellAxialSpeed h P axialSpeed tau n)
      (DA + P.scaleFamily.axialAmplitude tau n • Dcut) x := by
    rw [cellAxialSpeed_eq_helical_add_plateau h P angularSpeed axialSpeed tau n]
    exact hDA.add hDB
  rw [hsum.fderiv]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (opNorm_le_add_pairBasis DA).trans ?_
    have hj : ∀ j : Fin 2, ‖DA (pairBasis j)‖ ≤
        SchwartzMap.seminorm ℝ 0 0 (∂_{wholePlaneBasis j}
          (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) := by
      intro j
      have hval : DA (pairBasis j) =
          vecRe (parameterizedHelicalCellSourceDeriv
            h P angularSpeed axialSpeed n j x) 2 := by
        rw [hDAdef]
        simp [parameterizedHelicalCellSourceFDeriv_apply_pairBasis]
      rw [hval]
      calc ‖vecRe (parameterizedHelicalCellSourceDeriv
              h P angularSpeed axialSpeed n j x) 2‖
          ≤ ‖vecRe (parameterizedHelicalCellSourceDeriv
              h P angularSpeed axialSpeed n j x)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖parameterizedHelicalCellSourceDeriv
              h P angularSpeed axialSpeed n j x‖ := norm_vecRe_le _
        _ ≤ SchwartzMap.seminorm ℝ 0 0 (∂_{wholePlaneBasis j}
              (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) :=
            SchwartzMap.norm_le_seminorm ℝ
              (∂_{wholePlaneBasis j}
                (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
              (helicalCellCoordinate h P n x)
    rw [parameterizedHelicalFirstDerivativeBound]
    exact add_le_add (hj 0) (hj 1)
  · have hDcut : ‖Dcut‖ ≤
        (axialPlateauLipschitzConstant : ℝ) *
          (P.scaleFamily.bufferRadius n)⁻¹ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h2 : ‖((P.scaleFamily.bufferRadius n)⁻¹ •
          ContinuousLinearMap.id ℝ (ℝ × ℝ))‖ ≤
          (P.scaleFamily.bufferRadius n)⁻¹ := by
        refine (norm_smul_le ((P.scaleFamily.bufferRadius n)⁻¹)
          (ContinuousLinearMap.id ℝ (ℝ × ℝ))).trans ?_
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
        simp
      exact mul_le_mul (norm_fderiv_axialPlateau_le _) h2 (norm_nonneg _)
        (NNReal.coe_nonneg _)
    calc ‖P.scaleFamily.axialAmplitude tau n • Dcut‖
        = P.scaleFamily.axialAmplitude tau n * ‖Dcut‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      _ ≤ P.scaleFamily.axialAmplitude tau n *
          ((axialPlateauLipschitzConstant : ℝ) *
            (P.scaleFamily.bufferRadius n)⁻¹) :=
          mul_le_mul_of_nonneg_left hDcut ha
      _ = (axialPlateauLipschitzConstant : ℝ) *
            P.scaleFamily.axialGradientScale tau n := by
          unfold ScaleFamily.axialGradientScale
          field_simp
      _ ≤ (axialPlateauLipschitzConstant : ℝ) *
            P.scaleFamily.axialGradientScale tau 0 :=
          mul_le_mul_of_nonneg_left
            (P.scaleFamily.axialGradientScale_le_zero htau n)
            (NNReal.coe_nonneg _)

end ScaleFamily.TorusCellPlacement

end

end FastDynamo

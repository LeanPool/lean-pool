/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusAxialVelocityChartFields
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Determinant

/-!
# Rigid rotations of the transverse chart plane

The explicit particle flow of `prop:particle-flow` moves a point of the
placement chart along a circle centred at the cell centre: by
`eq:explicit-particle-flow`,

`Phi_t (y, x_3) = (p_n + R_{t omega_n(r)} (y - p_n), x_3 + t g_n(r))`,

where `R_alpha` is the rotation of the transverse plane through the angle `alpha`.  This
module supplies `R_alpha` and the rotation `J` by a right angle on the chart coordinate type
`ℝ × ℝ`, together with every fact about them that the flow modules use:

* the group law `R_alpha ∘ R_beta = R_{alpha + beta}` and the inverse `R_{-alpha}`;
* invariance of the Euclidean radius `‖pairToWholePlane z‖`, which is what makes the cell
  profiles `omega_n` and `g_n` constant along a trajectory (proof of `prop:particle-flow`);
* the `t`-derivative `d/dt R_{t omega} z = omega J (R_{t omega} z)`, the ODE verification in
  the proof of `prop:particle-flow`;
* the `z`-derivative as the continuous linear map `planeRotateCLM`, entering the differential
  `D_y (R_{t omega_n(r)} z) = R_{t omega_n(r)} [id + t omega_n'(r) J z ⊗ e_r]` of the proof of
  `prop:particle-flow`;
* the determinants needed for `det D Phi_t = 1`: `det R_alpha = 1` and
  `det (id + phi ⊗ u) = 1` for a rank-one perturbation with `phi u = 0`.  The paper obtains
  `det D Phi_t = 1` in the proof of `cor:ideal-growth` from Liouville's formula and `Div u = 0`;
  the Lean computes the determinant of the explicit differential instead.

**Metric warning.**  `ℝ × ℝ` carries the product (sup) metric, so `‖·‖` on `ℝ × ℝ` is *not*
the Euclidean radius of the chart; the Euclidean radius is `‖pairToWholePlane z‖`
(`Global/TorusHelicalSource.lean`).  Rotation invariance is exact only for the latter, and the
displacement bound `‖R_alpha z - z‖ ≤ |alpha| ‖pairToWholePlane z‖` mixes the two norms:
the sup norm on the left is what the Lipschitz estimates of `prop:particle-flow`
need, and it is dominated by the Euclidean norm.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open ScaleFamily.TorusCellPlacement
open scoped RealInnerProductSpace NNReal

/-! ## The rotation and the right-angle rotation -/

/-- The rotation `R_alpha` of the chart plane `ℝ × ℝ` through the angle `alpha`
(statement of `prop:particle-flow`). -/
def planeRotate (α : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos α * z.1 - Real.sin α * z.2, Real.sin α * z.1 + Real.cos α * z.2)

/-- The first coordinate of `planeRotate`. -/
@[simp] theorem planeRotate_fst (α : ℝ) (z : ℝ × ℝ) :
    (planeRotate α z).1 = Real.cos α * z.1 - Real.sin α * z.2 := rfl

/-- The second coordinate of `planeRotate`. -/
@[simp] theorem planeRotate_snd (α : ℝ) (z : ℝ × ℝ) :
    (planeRotate α z).2 = Real.sin α * z.1 + Real.cos α * z.2 := rfl

/-- The rotation `J` of the chart plane by a right angle, `J z = z^⊥`
(proof of `prop:particle-flow`). -/
def perp (z : ℝ × ℝ) : ℝ × ℝ := (-z.2, z.1)

/-- The first coordinate of `perp`. -/
@[simp] theorem perp_fst (z : ℝ × ℝ) : (perp z).1 = -z.2 := rfl

/-- The second coordinate of `perp`. -/
@[simp] theorem perp_snd (z : ℝ × ℝ) : (perp z).2 = z.1 := rfl

/-! ## The group law -/

/-- `R_0` is the identity. -/
@[simp] theorem planeRotate_zero (z : ℝ × ℝ) : planeRotate 0 z = z := by
  simp [planeRotate]

/-- The rotation group law `R_alpha ∘ R_beta = R_{alpha + beta}`
(`prop:particle-flow`).  Consumed by `cellTransverseFlow_cellTransverseFlow`
(`Flow/CellFlowMap.lean`) and by the group law of the plane flow. -/
theorem planeRotate_planeRotate (α β : ℝ) (z : ℝ × ℝ) :
    planeRotate α (planeRotate β z) = planeRotate (α + β) z := by
  simp only [planeRotate, Real.cos_add, Real.sin_add, Prod.mk.injEq]
  constructor <;> ring

/-- `R_{-alpha}` inverts `R_alpha` (the inverse `Phi_t^{-1} = Phi_{-t}` in the proof of
`prop:particle-flow`). -/
@[simp] theorem planeRotate_neg_planeRotate (α : ℝ) (z : ℝ × ℝ) :
    planeRotate (-α) (planeRotate α z) = z := by
  rw [planeRotate_planeRotate, neg_add_cancel, planeRotate_zero]

/-- `R_alpha` inverts `R_{-alpha}`. -/
@[simp] theorem planeRotate_planeRotate_neg (α : ℝ) (z : ℝ × ℝ) :
    planeRotate α (planeRotate (-α) z) = z := by
  rw [planeRotate_planeRotate, add_neg_cancel, planeRotate_zero]

/-- Rotations commute with the right-angle rotation `J`. -/
theorem planeRotate_perp (α : ℝ) (z : ℝ × ℝ) :
    planeRotate α (perp z) = perp (planeRotate α z) := by
  simp only [planeRotate, perp, Prod.mk.injEq]
  constructor <;> ring

/-- `R_alpha` is additive, so it commutes with differences of chart points. -/
theorem planeRotate_sub (α : ℝ) (z w : ℝ × ℝ) :
    planeRotate α (z - w) = planeRotate α z - planeRotate α w := by
  simp only [planeRotate, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor <;> ring

/-- `R_alpha` fixes the origin of the chart. -/
@[simp] theorem planeRotate_apply_zero (α : ℝ) : planeRotate α (0 : ℝ × ℝ) = 0 := by
  simp [planeRotate]

/-! ## Euclidean invariance -/

/-- The product (sup) norm of the chart is dominated by its Euclidean norm. -/
theorem norm_le_norm_pairToWholePlane (z : ℝ × ℝ) : ‖z‖ ≤ ‖pairToWholePlane z‖ := by
  simpa using dist_le_norm_pairToWholePlane_sub z 0

/-- The Euclidean norm of the chart is at most twice its product (sup) norm.  The factor two
is the sup-versus-Euclidean loss already carried by `globalVelocityLipschitzBound`. -/
theorem norm_pairToWholePlane_le_two_mul_norm (z : ℝ × ℝ) :
    ‖pairToWholePlane z‖ ≤ 2 * ‖z‖ := by
  simpa using norm_pairToWholePlane_sub_le_two_mul_dist z 0

/-- Rotations preserve the Euclidean radius of the chart, which is the statement
that `r = |y - p_n|` is invariant along a trajectory (proof of `prop:particle-flow`).
Consumed by `norm_pairToWholePlane_cellTransverseFlow_sub_cellCenter`
(`Flow/CellFlowMap.lean`), the invariance of the two cell profiles along the flow. -/
theorem norm_pairToWholePlane_planeRotate (α : ℝ) (z : ℝ × ℝ) :
    ‖pairToWholePlane (planeRotate α z)‖ = ‖pairToWholePlane z‖ := by
  have hsq : ‖pairToWholePlane (planeRotate α z)‖ ^ 2 = ‖pairToWholePlane z‖ ^ 2 := by
    rw [norm_pairToWholePlane_sq, norm_pairToWholePlane_sq, planeRotate_fst, planeRotate_snd]
    nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg z.1, sq_nonneg z.2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (two_ne_zero)).mp hsq

/-- `J` preserves the Euclidean radius of the chart. -/
theorem norm_pairToWholePlane_perp (z : ℝ × ℝ) :
    ‖pairToWholePlane (perp z)‖ = ‖pairToWholePlane z‖ := by
  have hsq : ‖pairToWholePlane (perp z)‖ ^ 2 = ‖pairToWholePlane z‖ ^ 2 := by
    rw [norm_pairToWholePlane_sq, norm_pairToWholePlane_sq, perp_fst, perp_snd]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (two_ne_zero)).mp hsq

/-! ## Differentiability in the angle -/

/-- The time derivative of the rotating trajectory:
`d/ds R_{s omega} z = omega · J (R_{s omega} z)`.  This is the transverse half of the ODE
verification in the proof of `prop:particle-flow`.  Consumed by
`hasDerivAt_cellTransverseFlow` (`Flow/CellFlowMap.lean`). -/
theorem hasDerivAt_planeRotate_mul (ω : ℝ) (z : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ planeRotate (s * ω) z)
      (ω • perp (planeRotate (t * ω) z)) t := by
  have hs : HasDerivAt (fun s : ℝ ↦ s * ω) ω t := by
    simpa using (hasDerivAt_id t).mul_const ω
  have hcos : HasDerivAt (fun s : ℝ ↦ Real.cos (s * ω)) (-Real.sin (t * ω) * ω) t := hs.cos
  have hsin : HasDerivAt (fun s : ℝ ↦ Real.sin (s * ω)) (Real.cos (t * ω) * ω) t := hs.sin
  have h1 : HasDerivAt (fun s : ℝ ↦ Real.cos (s * ω) * z.1 - Real.sin (s * ω) * z.2)
      (-Real.sin (t * ω) * ω * z.1 - Real.cos (t * ω) * ω * z.2) t :=
    (hcos.mul_const z.1).sub (hsin.mul_const z.2)
  have h2 : HasDerivAt (fun s : ℝ ↦ Real.sin (s * ω) * z.1 + Real.cos (s * ω) * z.2)
      (Real.cos (t * ω) * ω * z.1 + -Real.sin (t * ω) * ω * z.2) t :=
    (hsin.mul_const z.1).add (hcos.mul_const z.2)
  have hfun : (fun s : ℝ ↦ planeRotate (s * ω) z) =
      fun s : ℝ ↦ (Real.cos (s * ω) * z.1 - Real.sin (s * ω) * z.2,
        Real.sin (s * ω) * z.1 + Real.cos (s * ω) * z.2) := rfl
  have hval : (ω • perp (planeRotate (t * ω) z) : ℝ × ℝ) =
      (-Real.sin (t * ω) * ω * z.1 - Real.cos (t * ω) * ω * z.2,
        Real.cos (t * ω) * ω * z.1 + -Real.sin (t * ω) * ω * z.2) := by
    simp only [perp, planeRotate_fst, planeRotate_snd, Prod.smul_mk, smul_eq_mul,
      Prod.mk.injEq]
    constructor <;> ring
  rw [hfun, hval]
  exact h1.prodMk h2

/-- The rotation is jointly smooth in the angle and the point. -/
theorem contDiff_planeRotate {n : WithTop ℕ∞} :
    ContDiff ℝ n (Function.uncurry planeRotate) := by
  have hα : ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) ↦ q.1 := contDiff_fst
  have hz1 : ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) ↦ q.2.1 := contDiff_fst.comp contDiff_snd
  have hz2 : ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) ↦ q.2.2 := contDiff_snd.comp contDiff_snd
  have hcos : ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) ↦ Real.cos q.1 := Real.contDiff_cos.comp hα
  have hsin : ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) ↦ Real.sin q.1 := Real.contDiff_sin.comp hα
  have hfun : Function.uncurry planeRotate = fun q : ℝ × (ℝ × ℝ) ↦
      (Real.cos q.1 * q.2.1 - Real.sin q.1 * q.2.2,
        Real.sin q.1 * q.2.1 + Real.cos q.1 * q.2.2) := rfl
  rw [hfun]
  exact ((hcos.mul hz1).sub (hsin.mul hz2)).prodMk ((hsin.mul hz1).add (hcos.mul hz2))

/-! ## The linear side -/

/-- The rotation `R_alpha` as a continuous linear map of the chart plane. -/
def planeRotateCLM (α : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  ContinuousLinearMap.prod
    (Real.cos α • ContinuousLinearMap.fst ℝ ℝ ℝ - Real.sin α • ContinuousLinearMap.snd ℝ ℝ ℝ)
    (Real.sin α • ContinuousLinearMap.fst ℝ ℝ ℝ + Real.cos α • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- `planeRotateCLM` is `planeRotate`. -/
@[simp] theorem planeRotateCLM_apply (α : ℝ) (z : ℝ × ℝ) :
    planeRotateCLM α z = planeRotate α z := rfl

/-- `planeRotateCLM` is `planeRotate` as a function. -/
theorem coe_planeRotateCLM (α : ℝ) : ⇑(planeRotateCLM α) = planeRotate α :=
  funext (planeRotateCLM_apply α)

/-- The Fréchet derivative of `R_alpha` is `R_alpha` itself: the rotation is linear. -/
theorem hasFDerivAt_planeRotate (α : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (planeRotate α) (planeRotateCLM α) z := by
  rw [← coe_planeRotateCLM]
  exact (planeRotateCLM α).hasFDerivAt

/-- The Fréchet derivative of `R_alpha`, in `fderiv` form. -/
@[simp] theorem fderiv_planeRotate (α : ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (planeRotate α) z = planeRotateCLM α :=
  (hasFDerivAt_planeRotate α z).fderiv

/-! ## Norm bounds -/

/-- The displacement bound `‖R_alpha z - z‖ ≤ |alpha| ‖z‖_euclid`, with the **sup** norm on the
left.  It is the transverse ingredient of the Lipschitz estimate of `prop:particle-flow`;
on the mixed norms see the module docstring. -/
theorem norm_planeRotate_sub_le (α : ℝ) (z : ℝ × ℝ) :
    ‖planeRotate α z - z‖ ≤ |α| * ‖pairToWholePlane z‖ := by
  have hnn : (0 : ℝ) ≤ |α| * ‖pairToWholePlane z‖ :=
    mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hkey : ‖pairToWholePlane (planeRotate α z - z)‖ ^ 2
      ≤ (|α| * ‖pairToWholePlane z‖) ^ 2 := by
    rw [norm_pairToWholePlane_sq, mul_pow, sq_abs, norm_pairToWholePlane_sq]
    simp only [Prod.fst_sub, Prod.snd_sub, planeRotate_fst, planeRotate_snd]
    nlinarith [Real.sin_sq_add_cos_sq α, Real.one_sub_sq_div_two_le_cos (x := α),
      sq_nonneg z.1, sq_nonneg z.2, sq_nonneg (z.1 ^ 2 + z.2 ^ 2)]
  have heuc : ‖pairToWholePlane (planeRotate α z - z)‖ ≤ |α| * ‖pairToWholePlane z‖ :=
    (abs_le_of_sq_le_sq' hkey hnn).2
  exact le_trans (norm_le_norm_pairToWholePlane _) heuc

/-- The Euclidean-exact form of rotation invariance for the linear map. -/
theorem norm_pairToWholePlane_planeRotateCLM (α : ℝ) (w : ℝ × ℝ) :
    ‖pairToWholePlane (planeRotateCLM α w)‖ = ‖pairToWholePlane w‖ := by
  rw [planeRotateCLM_apply, norm_pairToWholePlane_planeRotate]

/-- The operator norm of `R_alpha` in the product (sup) metric of the chart is at most `2`.
The loss relative to the Euclidean isometry is the sup-versus-Euclidean factor of
`globalVelocityLipschitzBound`. -/
theorem norm_planeRotateCLM_le (α : ℝ) : ‖planeRotateCLM α‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w ↦ ?_
  calc ‖planeRotateCLM α w‖ ≤ ‖pairToWholePlane (planeRotateCLM α w)‖ :=
        norm_le_norm_pairToWholePlane _
    _ = ‖pairToWholePlane w‖ := norm_pairToWholePlane_planeRotateCLM α w
    _ ≤ 2 * ‖w‖ := norm_pairToWholePlane_le_two_mul_norm w

/-! ## Determinants -/

/-- A linear functional on the chart plane is determined by its values on the standard basis. -/
theorem linearFunctional_pair_apply (φ : (ℝ × ℝ) →L[ℝ] ℝ) (u : ℝ × ℝ) :
    φ u = u.1 * φ (1, 0) + u.2 * φ (0, 1) := by
  have hu : u = u.1 • ((1 : ℝ), (0 : ℝ)) + u.2 • ((0 : ℝ), (1 : ℝ)) := by
    simp
  calc φ u = φ (u.1 • ((1 : ℝ), (0 : ℝ)) + u.2 • ((0 : ℝ), (1 : ℝ))) := by rw [← hu]
    _ = u.1 * φ (1, 0) + u.2 * φ (0, 1) := by
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **Liouville, rotation part** (proof of `cor:ideal-growth`): a plane rotation has
determinant `1`. -/
theorem det_planeRotateCLM (α : ℝ) :
    LinearMap.det ((planeRotateCLM α : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
  have hmat : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      ((planeRotateCLM α : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) =
      !![Real.cos α, -Real.sin α; Real.sin α, Real.cos α] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr]
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), hmat, Matrix.det_fin_two_of]
  linear_combination Real.sin_sq_add_cos_sq α

/-- **Liouville, shear part** (proof of `cor:ideal-growth`): a rank-one perturbation
`w ↦ phi w • u` of the identity has determinant `1` as soon as `phi u = 0`.  This is the shape
in which the differential `id + t omega_n'(r) J z ⊗ e_r` of the proof of `prop:particle-flow`
occurs, with `u = J z` and
`phi = t omega_n'(r) e_r` orthogonal to `J z`. -/
theorem det_id_add_smulRight (φ : (ℝ × ℝ) →L[ℝ] ℝ) (u : ℝ × ℝ) (hu : φ u = 0) :
    LinearMap.det (LinearMap.id (R := ℝ) (M := ℝ × ℝ) +
      LinearMap.smulRight (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) u) = 1 := by
  have hexp : u.1 * φ (1, 0) + u.2 * φ (0, 1) = 0 := by
    rw [← linearFunctional_pair_apply]; exact hu
  have hmat : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (LinearMap.id (R := ℝ) (M := ℝ × ℝ) + LinearMap.smulRight (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) u) =
      !![1 + φ (1, 0) * u.1, φ (0, 1) * u.1; φ (1, 0) * u.2, 1 + φ (0, 1) * u.2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr]
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), hmat, Matrix.det_fin_two_of]
  linear_combination hexp

/-- **Liouville for the cell flow** (proof of `cor:ideal-growth`): the differential
`R_alpha [id + phi ⊗ u]` of the proof of `prop:particle-flow` has determinant `1` whenever
`phi u = 0`.  This is the composite shape in which the transverse Jacobian of `Phi_t` occurs. -/
theorem det_planeRotateCLM_comp_id_add_smulRight
    (α : ℝ) (φ : (ℝ × ℝ) →L[ℝ] ℝ) (u : ℝ × ℝ) (hu : φ u = 0) :
    LinearMap.det (((planeRotateCLM α).comp
      (ContinuousLinearMap.id ℝ (ℝ × ℝ) + φ.smulRight u) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
  have hcomp : (((planeRotateCLM α).comp
      (ContinuousLinearMap.id ℝ (ℝ × ℝ) + φ.smulRight u) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) =
      ((planeRotateCLM α : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)).comp
        ((ContinuousLinearMap.id ℝ (ℝ × ℝ) + φ.smulRight u : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) := rfl
  rw [hcomp, LinearMap.det_comp, det_planeRotateCLM, one_mul]
  exact det_id_add_smulRight φ u hu

/-! ## Two rotations of the same vector -/

/-- Two rotations of the same vector differ by at most twice the angle gap times the Euclidean
radius.  The factor two is the sup-versus-Euclidean loss of the pair chart; the identity behind
it is `R_alpha z - R_beta z = R_beta (R_{alpha-beta} z - z)`. -/
theorem norm_planeRotate_sub_planeRotate_le (alpha beta : ℝ) (z : ℝ × ℝ) :
    ‖planeRotate alpha z - planeRotate beta z‖ ≤
      2 * (|alpha - beta| * ‖pairToWholePlane z‖) := by
  have hangle : beta + (alpha - beta) = alpha := by ring
  have hrot : planeRotate alpha z - planeRotate beta z =
      planeRotate beta (planeRotate (alpha - beta) z - z) := by
    rw [planeRotate_sub, planeRotate_planeRotate, hangle]
  rw [hrot]
  calc ‖planeRotate beta (planeRotate (alpha - beta) z - z)‖
      ≤ ‖pairToWholePlane (planeRotate beta (planeRotate (alpha - beta) z - z))‖ :=
        norm_le_norm_pairToWholePlane _
    _ = ‖pairToWholePlane (planeRotate (alpha - beta) z - z)‖ :=
        norm_pairToWholePlane_planeRotate _ _
    _ ≤ 2 * ‖planeRotate (alpha - beta) z - z‖ := norm_pairToWholePlane_le_two_mul_norm _
    _ ≤ 2 * (|alpha - beta| * ‖pairToWholePlane z‖) :=
        mul_le_mul_of_nonneg_left (norm_planeRotate_sub_le _ _) (by norm_num)

/-! ## Continuity of the plane rotation in the angle -/

/-- The rotation, as a continuous linear map of the sup-normed chart plane, is a Lipschitz
function of its angle: two factors `2` are the sup-versus-Euclidean losses of
`norm_planeRotate_sub_planeRotate_le` and `norm_pairToWholePlane_le_two_mul_norm`. -/
theorem lipschitzWith_planeRotateCLM : LipschitzWith 4 planeRotateCLM := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  rw [dist_eq_norm]
  have hcoe : ((4 : ℝ≥0) : ℝ) = 4 := by norm_num
  rw [hcoe, Real.dist_eq]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z ↦ ?_
  have hval : (planeRotateCLM a - planeRotateCLM b) z = planeRotate a z - planeRotate b z := by
    simp
  rw [hval]
  have h1 := norm_planeRotate_sub_planeRotate_le a b z
  have h2 := norm_pairToWholePlane_le_two_mul_norm z
  have h3 : (0 : ℝ) ≤ |a - b| := abs_nonneg _
  nlinarith

/-- The rotation is a continuous function of its angle. -/
theorem continuous_planeRotateCLM : Continuous planeRotateCLM :=
  lipschitzWith_planeRotateCLM.continuous

/-! ## A chain rule for the plane rotation

Differentiating `y ↦ R_{beta y} (g y)` needs the derivative of the rotation in its *angle*,
`∂_alpha R_alpha z = J (R_alpha z)`, next to the derivative in the point.  Both appear in the
cell differential in the proof of `prop:particle-flow`, so the two-variable chain rule is
isolated here. -/

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chain rule for a rotation whose angle and whose argument both vary: if `beta` has
derivative `beta'` and `g` has derivative `g'` at `x`, then `y ↦ R_{beta y} (g y)` has
derivative `R_{beta x} ∘ g' + beta' ⊗ J (R_{beta x} (g x))`.  The second summand is the
rank-one term `t omega_n'(r) J z ⊗ e_r` of the proof of `prop:particle-flow`. -/
theorem hasFDerivAt_planeRotate_comp {β : E → ℝ} {β' : E →L[ℝ] ℝ}
    {g : E → ℝ × ℝ} {g' : E →L[ℝ] ℝ × ℝ} {x : E}
    (hβ : HasFDerivAt β β' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y ↦ planeRotate (β y) (g y))
      ((planeRotateCLM (β x)).comp g' +
        β'.smulRight (perp (planeRotate (β x) (g x)))) x := by
  have hg1 : HasFDerivAt (fun y ↦ (g y).1) ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp g') x :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp x hg
  have hg2 : HasFDerivAt (fun y ↦ (g y).2) ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp g') x :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp x hg
  have hc := hβ.cos
  have hs := hβ.sin
  have h1 := (hc.mul hg1).sub (hs.mul hg2)
  have h2 := (hs.mul hg1).add (hc.mul hg2)
  refine (h1.prodMk h2).congr_fderiv ?_
  ext w
  · simp [planeRotate]
    ring
  · simp [planeRotate]
    ring

end ChainRule

end

end FastDynamo
